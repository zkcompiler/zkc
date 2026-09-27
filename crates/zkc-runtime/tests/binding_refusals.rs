//! Refusal order is observable even when several binding fields are invalid.
use zkc_runtime::interactive::{ErrorCode, OperationBinding};

#[test]
fn malformed_bindings_keep_their_first_refusal() {
    for (contract, arguments, implementation, physical, code, detail) in [
        (
            "field.add",
            vec!["unknown", "extra"],
            "wrong/field.add",
            true,
            ErrorCode::Type,
            "uninstalled nominal identity",
        ),
        (
            "field.add",
            vec!["bls12-381.fr", "extra"],
            "wrong/field.add",
            true,
            ErrorCode::Signature,
            "uninstalled operation binding",
        ),
        (
            "bool.and",
            vec!["unknown"],
            "wrong/bool.and",
            true,
            ErrorCode::Signature,
            "uninstalled operation binding",
        ),
        (
            "poly.domain_root",
            vec!["bls12-381.fr", "extra"],
            "arkworks/poly.domain_root",
            true,
            ErrorCode::Signature,
            "uninstalled operation binding",
        ),
        (
            "transcript.observe.field",
            vec!["merlin3.bls12-381.fr64be/1", "unknown", "wrong"],
            "wrong/transcript.observe.field",
            true,
            ErrorCode::Type,
            "uninstalled nominal identity",
        ),
        (
            "transcript.observe.field",
            vec!["bls12-381.fr", "unknown", "wrong"],
            "wrong/transcript.observe.field",
            true,
            ErrorCode::Signature,
            "uninstalled operation binding",
        ),
        (
            "pairing.check",
            vec!["unknown", "extra"],
            "wrong/pairing.check",
            true,
            ErrorCode::Signature,
            "uninstalled operation binding",
        ),
        (
            "table.relayout",
            vec!["bls12-381.fr", "unknown", "arkworks.mle-msb/1"],
            "arkworks/table.relayout",
            true,
            ErrorCode::Representation,
            "uninstalled representation",
        ),
        (
            "table.relayout",
            vec!["unknown"],
            "wrong/table.relayout",
            false,
            ErrorCode::Signature,
            "binding-adapter-at-logical-stage",
        ),
    ] {
        let binding = OperationBinding {
            contract: contract.into(),
            arguments: arguments.into_iter().map(str::to_owned).collect(),
            implementation: implementation.into(),
        };
        let error = if physical {
            binding.signature().unwrap_err()
        } else {
            binding.logical_signature().unwrap_err()
        };
        assert_eq!(error.code, code, "{binding:?}");
        assert_eq!(error.detail, detail, "{binding:?}");
    }
}
