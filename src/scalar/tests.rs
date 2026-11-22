use super::*;
use curve25519::scalar::Scalar;
use rand::{RngCore, SeedableRng, rngs::StdRng};

pub(super) const L_BYTES: [u8; 32] = [
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
];

// Independent digit-by-digit carry for the digest conversion tests.
pub(super) fn reference_radix16(bytes: [u8; 32]) -> Radix16 {
    let mut carry = 0;
    let digits = core::array::from_fn(|i| {
        let nibble = (bytes[i / 2] >> (4 * (i % 2))) & 15;
        let value = nibble as i8 + carry;
        carry = (value + 8) >> 4;
        value - 16 * carry
    });
    assert_eq!(carry, 0);
    digits
}

fn check_preparation(scalars: [&[u8; 32]; LANES]) -> u8 {
    let (mask, rows) = prepare_signature_scalars(scalars);
    for (lane, (bytes, digits)) in scalars.into_iter().zip(rows).enumerate() {
        let valid = bool::from(Scalar::from_canonical_bytes(*bytes).is_some());
        assert_eq!(mask & (1 << lane) != 0, valid, "lane {lane}, S={bytes:x?}");
        if !valid {
            assert_eq!(digits, [0; 64], "rejected lane {lane}");
            continue;
        }
        // Evaluate the signed digits in base 256 and compare each byte of S.
        // The final carry checks equality as integers over the full 256 bits.
        let mut carry = 0i16;
        for (pair, &byte) in digits.chunks_exact(2).zip(bytes) {
            assert!(pair.iter().all(|d| (-8..=7).contains(d)));
            let value = i16::from(pair[0]) + 16 * i16::from(pair[1]) + carry;
            assert_eq!(value as u8, byte, "lane {lane}, S={bytes:x?}");
            carry = value >> 8;
        }
        assert_eq!(carry, 0, "lane {lane}");
    }
    mask
}

#[test]
fn signature_scalar_order_boundary_and_all_lane_masks() {
    let mut below = L_BYTES;
    below[0] -= 1;
    let mut above = L_BYTES;
    above[0] += 1;
    for mask in 0..=u8::MAX {
        let scalars = core::array::from_fn(|lane| match (mask & (1 << lane) != 0, lane % 2) {
            (true, _) => &below,
            (false, 0) => &L_BYTES,
            (false, _) => &above,
        });
        assert_eq!(check_preparation(scalars), mask);
    }
}

#[test]
fn signature_scalar_digits_and_most_significant_differing_word() {
    let mut rng = StdRng::seed_from_u64(0x243f_6a88_85a3_08d3);
    let mut cases = vec![[0u8; 32], [0xff; 32]];
    // These nibbles propagate the bias carry from word 0 through words 1 and 2.
    let mut carry_chain = [0x77; 32];
    carry_chain[0] = 0x78;
    carry_chain[31] = 0x07;
    cases.push(carry_chain);
    for bit in 0..256 {
        let mut bytes = L_BYTES;
        bytes[bit / 8] ^= 1 << (bit % 8);
        rng.fill_bytes(&mut bytes[..bit / 8]);
        cases.push(bytes);
    }
    for i in 0..4096 {
        let mut bytes = [0; 32];
        rng.fill_bytes(&mut bytes);
        if i % 2 == 0 {
            bytes[31] &= 0x0f;
        }
        cases.push(bytes);
    }
    for lanes in cases.chunks(LANES) {
        check_preparation(core::array::from_fn(|i| &lanes[i % lanes.len()]));
    }
}
