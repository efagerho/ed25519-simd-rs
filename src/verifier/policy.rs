/// Which acceptance rules a [`Verifier`](crate::Verifier) applies.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum VerifyPolicy {
    /// ZIP-215 cofactored verification; accepts non-canonical point encodings.
    #[default]
    Zip215,
    /// Strict Dalek-style verification with canonical `R` and no small-order points.
    Dalek,
}

/// ZIP-215 cofactored verification policy.
///
/// Use this as the policy parameter of [`Verifier`](crate::Verifier), or use
/// the [`Zip215Verifier`](crate::Zip215Verifier) alias.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Zip215Policy;

/// Dalek-compatible verification policy.
///
/// Use this as the policy parameter of [`Verifier`](crate::Verifier), or use
/// the [`DalekVerifier`](crate::DalekVerifier) alias.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct DalekPolicy;

mod sealed {
    /// Prevents downstream crates from defining verification policies.
    pub trait Sealed {}

    impl Sealed for super::Zip215Policy {}
    impl Sealed for super::DalekPolicy {}
}

/// A compile-time verification policy.
///
/// Use [`Zip215Policy`] or [`DalekPolicy`] to select the verification equation.
pub trait VerificationPolicy: sealed::Sealed + Copy + core::fmt::Debug + Default + 'static {
    /// The corresponding runtime policy value.
    const POLICY: VerifyPolicy;
}

impl VerificationPolicy for Zip215Policy {
    const POLICY: VerifyPolicy = VerifyPolicy::Zip215;
}

impl VerificationPolicy for DalekPolicy {
    const POLICY: VerifyPolicy = VerifyPolicy::Dalek;
}
