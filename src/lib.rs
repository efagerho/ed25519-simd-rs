#[cfg(not(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512dq",
    target_feature = "avx512ifma",
)))]
compile_error!("ed25519-simd requires x86_64 with AVX-512F, AVX-512DQ, and AVX-512IFMA enabled");

mod batch;
mod cache;
mod edwards;
mod field;
mod scalar;
mod sha512;
mod wide;

pub use batch::{PUBLIC_KEY_LEN, SIGNATURE_LEN, VerifyInput, VerifyPolicy};
pub use cache::{CacheStats, CachedPublicKey, KeyCache, LruKeyCache, NullKeyCache, Verifier};

#[cfg(test)]
mod tests {
    use super::*;

    fn hex<const N: usize>(s: &str) -> [u8; N] {
        assert_eq!(s.len(), N * 2);
        let mut out = [0u8; N];
        let bytes = s.as_bytes();
        let mut i = 0;
        while i < N {
            out[i] = (hex_nibble(bytes[i * 2]) << 4) | hex_nibble(bytes[i * 2 + 1]);
            i += 1;
        }
        out
    }

    fn hex_nibble(b: u8) -> u8 {
        match b {
            b'0'..=b'9' => b - b'0',
            b'a'..=b'f' => b - b'a' + 10,
            b'A'..=b'F' => b - b'A' + 10,
            _ => panic!("bad hex"),
        }
    }

    #[test]
    fn rfc8032_empty_message() {
        let public_key = hex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a");
        let signature = hex(
            "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155\
             5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
        );
        let mut out = [false];
        Verifier::new().verify_batch(
            &[VerifyInput {
                public_key,
                signature,
                message: b"",
            }],
            &mut out,
        );
        assert_eq!(out, [true]);
    }

    #[test]
    fn rfc8032_one_byte_message() {
        let public_key = hex("3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c");
        let signature = hex(
            "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da\
             085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00",
        );
        let mut out = [false];
        Verifier::new().verify_batch(
            &[VerifyInput {
                public_key,
                signature,
                message: &[0x72],
            }],
            &mut out,
        );
        assert_eq!(out, [true]);
    }

    #[test]
    fn rejects_mutated_signature() {
        let public_key = hex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a");
        let mut signature = hex(
            "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155\
             5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
        );
        signature[3] ^= 1;
        let mut out = [true];
        Verifier::new().verify_batch(
            &[VerifyInput {
                public_key,
                signature,
                message: b"",
            }],
            &mut out,
        );
        assert_eq!(out, [false]);
    }

    #[test]
    fn cached_verifier_accepts_batch() {
        let public_key = hex("3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c");
        let signature = hex(
            "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da\
             085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00",
        );

        let inputs = [VerifyInput {
            public_key,
            signature,
            message: &[0x72],
        }];
        let mut out = [false];
        let mut verifier = Verifier::new();
        verifier.preload_public_keys(&[public_key]);
        verifier.verify_batch(&inputs, &mut out);
        assert_eq!(out, [true]);
    }

    #[test]
    fn cached_verifier_accepts_simd_sized_batch() {
        let public_key = hex("3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c");
        let signature = hex(
            "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da\
             085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00",
        );
        let inputs = [VerifyInput {
            public_key,
            signature,
            message: &[0x72],
        }; 8];
        let mut out = [false; 8];
        let mut verifier = Verifier::new();
        verifier.preload_public_keys(&[public_key]);
        verifier.verify_batch(&inputs, &mut out);
        assert_eq!(out, [true; 8]);
    }

    #[test]
    fn cached_verifier_rejects_one_bad_lane_in_simd_batch() {
        let public_key = hex("3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c");
        let signature = hex(
            "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da\
             085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00",
        );
        let mut inputs = [VerifyInput {
            public_key,
            signature,
            message: &[0x72],
        }; 8];
        inputs[3].signature[40] ^= 1;

        let mut out = [false; 8];
        let mut verifier = Verifier::new();
        verifier.preload_public_keys(&[public_key]);
        verifier.verify_batch(&inputs, &mut out);

        assert_eq!(out, [true, true, true, false, true, true, true, true]);
    }

    #[test]
    fn cached_verifier_rejects_bad_r_lane_in_simd_batch() {
        let public_key = hex("3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c");
        let signature = hex(
            "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da\
             085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00",
        );
        let mut inputs = [VerifyInput {
            public_key,
            signature,
            message: &[0x72],
        }; 8];
        inputs[5].signature[..32].copy_from_slice(&[0xff; 32]);

        let mut out = [false; 8];
        let mut verifier = Verifier::new();
        verifier.preload_public_keys(&[public_key]);
        verifier.verify_batch(&inputs, &mut out);

        assert_eq!(out, [true, true, true, true, true, false, true, true]);
    }

    #[test]
    fn verifier_tracks_hot_keys_and_cache_capacity() {
        let public_key0 = hex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a");
        let signature0 = hex(
            "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155\
             5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
        );
        let public_key1 = hex("3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c");
        let signature1 = hex(
            "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da\
             085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00",
        );

        let mut verifier = Verifier::with_policy_and_cache_capacity(VerifyPolicy::default(), 1);
        assert!(verifier.verify_one(VerifyInput {
            public_key: public_key0,
            signature: signature0,
            message: b"",
        }));
        assert!(verifier.verify_one(VerifyInput {
            public_key: public_key1,
            signature: signature1,
            message: &[0x72],
        }));

        let stats = verifier.cache_stats();
        assert_eq!(stats.keys, 1);
        assert_eq!(stats.evictions, 1);
        assert_eq!(verifier.hot_public_keys(1), [public_key1]);

        verifier.preload_public_keys(&[public_key0]);
        let stats = verifier.cache_stats();
        assert_eq!(stats.keys, 1);
        assert_eq!(stats.pinned_keys, 1);
        assert_eq!(verifier.hot_public_keys(1), [public_key0]);
    }
}
