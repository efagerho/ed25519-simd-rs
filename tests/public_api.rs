use ed25519_simd::{DalekVerifier, RuntimeVerifier, VerifyInput, VerifyPolicy, Zip215Verifier};

#[test]
fn verify_input_supports_struct_update_syntax_downstream() {
    let base = VerifyInput {
        public_key: [0; 32],
        signature: [0; 64],
        message: b"base",
    };
    let inputs: Vec<_> = [b"first".as_slice(), b"second".as_slice()]
        .into_iter()
        .map(|message| VerifyInput { message, ..base })
        .collect();

    assert_eq!(inputs[0].message, b"first");
    assert_eq!(inputs[1].message, b"second");
}

#[test]
fn verifiers_expose_the_selected_policy() {
    assert_eq!(Zip215Verifier::new().policy(), VerifyPolicy::Zip215);
    assert_eq!(DalekVerifier::new().policy(), VerifyPolicy::Dalek);
    assert_eq!(RuntimeVerifier::new().policy(), VerifyPolicy::Zip215);
    for policy in [VerifyPolicy::Zip215, VerifyPolicy::Dalek] {
        assert_eq!(RuntimeVerifier::with_policy(policy).policy(), policy);
    }
}
