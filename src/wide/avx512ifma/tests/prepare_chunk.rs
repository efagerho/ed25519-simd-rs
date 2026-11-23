use super::*;
use crate::edwards::IDENTITY_TABLE;
use crate::wide::avx512ifma::prepare::{ChunkInputs, PreparedLanes};
use crate::{DalekPolicy, VerificationPolicy, VerifyInput, VerifyPolicy, Zip215Policy};

unsafe extern "C" {
    fn ed25519_simd_prepare_chunk(
        scratch: *mut u8,
        inputs: &ChunkInputs<'_>,
        identity: &PointTable,
        lanes: *mut PreparedLanes<'_>,
    ) -> u32;
    fn ed25519_simd_dalek_prepare_chunk(
        scratch: *mut u8,
        inputs: &ChunkInputs<'_>,
        identity: &PointTable,
        lanes: *mut PreparedLanes<'_>,
    ) -> u32;
}

fn prepare_chunk<'a, P: VerificationPolicy>(
    inputs: &[VerifyInput<'_>; LANES],
    scratch: &'a mut MaybeUninit<ChunkScratch>,
) -> Option<(&'a ChunkScratch, PreparedLanes<'a>)> {
    let lanes = ChunkInputs {
        keys: inputs.each_ref().map(|input| &input.public_key),
        signatures: inputs.each_ref().map(|input| &input.signature),
    };
    let mut selected = MaybeUninit::uninit();
    let prepare = match P::POLICY {
        VerifyPolicy::Zip215 => ed25519_simd_prepare_chunk,
        VerifyPolicy::Dalek => ed25519_simd_dalek_prepare_chunk,
    };
    // SAFETY: the inputs remain readable for the call. Both outputs are
    // aligned, exclusive and disjoint. Success initializes every field,
    // including 0/1 eligibility bytes and references into scratch or identity.
    // A rejected chunk may leave partial outputs and exposes neither.
    unsafe {
        let ready = prepare(
            scratch.as_mut_ptr().cast(),
            &lanes,
            &IDENTITY_TABLE,
            selected.as_mut_ptr(),
        );
        (ready != 0).then(|| (scratch.assume_init_ref(), selected.assume_init()))
    }
}

fn check_lanes<P: VerificationPolicy>(
    inputs: &[VerifyInput<'_>; LANES],
    scratch: &mut MaybeUninit<ChunkScratch>,
) {
    let (chunk, lanes) = prepare_chunk::<P>(inputs, scratch).unwrap();
    let keys = inputs.each_ref().map(|i| i.public_key);
    let encodings = inputs
        .each_ref()
        .map(|i| *i.signature.first_chunk().unwrap());
    let (s_mask, digits) = crate::scalar::prepare_signature_scalars(
        inputs.each_ref().map(|i| i.signature.last_chunk().unwrap()),
    );
    let (mut a, a_mask) = decompress_points_wide(&keys);
    let (r, r_mask) = decompress_points_wide(&encodings);
    let mut storage = MaybeUninit::uninit();
    let tables = decode::build_key_tables::<LANES>(&mut a, &mut storage);

    assert_eq!(chunk.public_keys, keys);
    assert_eq!(chunk.r_bytes, encodings);
    assert_eq!(chunk.s_digits, digits);
    assert_eq!(lanes.r_valid, r_mask);
    for (actual, expected) in coordinates(&chunk.r).into_iter().zip(coordinates(&r)) {
        assert_eq!(wide_rows(actual), wide_rows(expected));
    }
    for j in 0..LANES {
        let key_ok = a_mask & (1 << j) != 0;
        let weak = keys[j] == [0; 32]; // the only small-order key in this fixture
        assert_eq!(
            lanes.valid[j],
            key_ok
                && (s_mask & r_mask) & (1 << j) != 0
                && (P::POLICY == VerifyPolicy::Zip215 || !weak)
        );
        let selected = lanes.tables[j];
        assert_eq!(core::ptr::eq(selected, &IDENTITY_TABLE), !key_ok);
        if key_ok {
            for digit in -8..=8 {
                let limbs = |table: &PointTable| {
                    let (plus, minus, z2, t2d) = table.select_signed_cached_ref(digit).coords();
                    [plus, minus, z2, t2d].map(|field| field.loose_limbs())
                };
                assert_eq!(
                    limbs(selected),
                    limbs(&tables[j]),
                    "lane {j}, digit {digit}"
                );
            }
        }
    }
}

#[test]
fn prepared_chunk_matches_component_outputs_in_every_lane() {
    use curve25519::{edwards::EdwardsPoint, scalar::Scalar};

    let mut inputs = core::array::from_fn(|j| {
        let multiple = |n| {
            EdwardsPoint::mul_base(&Scalar::from(n))
                .compress()
                .to_bytes()
        };
        let mut signature = [0; 64];
        signature[..32].copy_from_slice(&multiple(9 + j as u64));
        signature[32] = 0x81 + j as u8;
        VerifyInput {
            public_key: multiple(1 + j as u64),
            signature,
            message: &[],
        }
    });
    inputs[1].public_key = [0; 32];
    inputs[2].public_key = [2; 32]; // off curve
    inputs[3].signature[32..].fill(0xff);
    inputs[4].signature[..32].fill(2); // off-curve R
    inputs[5].signature[..32].fill(0xff);
    inputs[5].signature[0] = 0xee; // noncanonical identity, negative zero

    let mut scratch = Box::<ChunkScratch>::new_uninit();
    for _ in 0..LANES {
        check_lanes::<Zip215Policy>(&inputs, &mut scratch);
        check_lanes::<DalekPolicy>(&inputs, &mut scratch);
        inputs.rotate_left(1);
    }
}

#[test]
fn empty_preparations_do_not_expose_stale_scratch() {
    let base = VerifyInput {
        public_key: BASEPOINT_COMPRESSED,
        signature: [0; 64],
        message: &[],
    };
    let mut inputs = [base; LANES];
    let mut scratch = Box::<ChunkScratch>::new_uninit();
    assert!(prepare_chunk::<DalekPolicy>(&inputs, &mut scratch).is_some());

    for input in &mut inputs {
        input.signature[32..].fill(0xff);
    }
    assert!(prepare_chunk::<Zip215Policy>(&inputs, &mut scratch).is_none());
    for input in &mut inputs {
        input.signature = base.signature;
        input.public_key = [2; 32];
    }
    assert!(prepare_chunk::<Zip215Policy>(&inputs, &mut scratch).is_none());
    // Each mask has passing lanes, but no lane passes all three checks.
    for (j, input) in inputs.iter_mut().enumerate() {
        *input = base;
        match j % 3 {
            0 => input.signature[32..].fill(0xff),
            1 => input.public_key = [2; 32],
            _ => input.signature[..32].fill(2),
        }
    }
    assert!(prepare_chunk::<Zip215Policy>(&inputs, &mut scratch).is_none());
    assert!(prepare_chunk::<DalekPolicy>(&inputs, &mut scratch).is_none());
    for input in &mut inputs {
        *input = base;
        input.public_key = [0; 32];
    }
    assert!(prepare_chunk::<DalekPolicy>(&inputs, &mut scratch).is_none());
    assert!(prepare_chunk::<Zip215Policy>(&inputs, &mut scratch).is_some());
}
