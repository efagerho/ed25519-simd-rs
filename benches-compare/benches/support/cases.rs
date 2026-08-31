use curve25519::ed_sigs::{SigningKey, VerificationKeyBytes};
use ed25519_simd::VerifyInput;
use rand::{RngCore, SeedableRng, rngs::StdRng};

pub(super) const SIZES: [usize; 4] = [8, 16, 32, 64];
pub(super) const RAGGED_SIZES: [usize; 4] = [1, 2, 4, 7];
pub(super) fn signing_key_from_index(index: u64) -> SigningKey {
    let mut seed = [0u8; 32];
    seed[..8].copy_from_slice(&index.to_le_bytes());
    SigningKey::from(seed)
}

/// An owned public-key, signature, and message benchmark fixture.
pub(super) struct OwnedCase {
    pk: [u8; 32],
    sig: [u8; 64],
    msg: Vec<u8>,
}

/// Message-length distribution generated for a benchmark case set.
#[derive(Clone, Copy)]
pub(super) enum MsgLen {
    Fixed(usize),
    Mixed,
}

/// Kind of invalid input injected into a benchmark case set.
#[derive(Clone, Copy)]
pub(super) enum InvalidKind {
    MalformedSignature,
    WellFormedWrongMessage,
}

pub(super) fn generate_distinct_key_cases(n: usize, msg_len: MsgLen) -> Vec<OwnedCase> {
    let mut rng = StdRng::seed_from_u64(0x5eed_1234);
    (0..n)
        .map(|i| {
            let key = signing_key_from_index(i as u64);
            let pk = <[u8; 32]>::from(VerificationKeyBytes::from(&key));
            let len = match msg_len {
                MsgLen::Fixed(l) => l,
                MsgLen::Mixed => (rng.next_u64() % 257) as usize,
            };
            let mut msg = vec![0u8; len];
            rng.fill_bytes(&mut msg);
            let sig = key.sign(&msg).to_bytes();
            OwnedCase { pk, sig, msg }
        })
        .collect()
}

/// Fill a batch by cycling through a small set of hot keys.
pub(super) fn generate_hot_key_cases(
    n: usize,
    hot_key_count: usize,
    msg_len: MsgLen,
) -> Vec<OwnedCase> {
    let mut rng = StdRng::seed_from_u64(0x5eed_1234);
    let hot_keys: Vec<SigningKey> = (0..hot_key_count)
        .map(|i| signing_key_from_index(i as u64))
        .collect();
    (0..n)
        .map(|i| {
            let key = &hot_keys[i % hot_key_count];
            let pk = <[u8; 32]>::from(VerificationKeyBytes::from(key));
            let len = match msg_len {
                MsgLen::Fixed(l) => l,
                MsgLen::Mixed => (rng.next_u64() % 257) as usize,
            };
            let mut msg = vec![0u8; len];
            rng.fill_bytes(&mut msg);
            let sig = key.sign(&msg).to_bytes();
            OwnedCase { pk, sig, msg }
        })
        .collect()
}

pub(super) fn invalidate_fraction(cases: &mut [OwnedCase], invalid_pct: u64, kind: InvalidKind) {
    let mut rng = StdRng::seed_from_u64(0x9e37_79b9_7f4a_7c15);
    for case in cases.iter_mut() {
        if rng.next_u64() % 100 < invalid_pct {
            match kind {
                InvalidKind::MalformedSignature => case.sig[32..].fill(0xff),
                InvalidKind::WellFormedWrongMessage => {
                    if case.msg.is_empty() {
                        case.msg.push(1);
                    } else {
                        case.msg[0] ^= 1;
                    }
                }
            }
        }
    }
}

pub(super) fn inputs_of(cases: &[OwnedCase]) -> Vec<VerifyInput<'_>> {
    cases
        .iter()
        .map(|c| VerifyInput {
            public_key: c.pk,
            signature: c.sig,
            message: &c.msg,
        })
        .collect()
}
