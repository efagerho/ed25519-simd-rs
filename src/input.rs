/// Byte length of an encoded Ed25519 public key: a compressed Edwards point.
pub const PUBLIC_KEY_LEN: usize = crate::edwards::POINT_ENCODING_LEN;

/// Byte length of an encoded Ed25519 signature.
pub const SIGNATURE_LEN: usize = 64;

/// One public key, signature, and message to verify.
#[derive(Clone, Copy, Debug)]
pub struct VerifyInput<'a> {
    /// Encoded Ed25519 public key.
    pub public_key: [u8; 32],
    /// Encoded Ed25519 signature (`R || S`).
    pub signature: [u8; 64],
    /// The signed message.
    pub message: &'a [u8],
}

// Spell the public field lengths as literals so downstream struct-update
// syntax does not expose unevaluated cross-crate constants in rustc's MIR.
const _: () = assert!(PUBLIC_KEY_LEN == 32);
const _: () = assert!(SIGNATURE_LEN == 64);
