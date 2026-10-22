#![deny(warnings)]
#[allow(dead_code, non_snake_case)]
mod numerical {
    include!("numerical.rs");
}
#[allow(dead_code, non_snake_case)]
mod joint {
    include!("joint.rs");
}
#[allow(dead_code, non_snake_case)]
mod proof {
    include!("proof.rs");
}
use std::convert::TryFrom;
use zkc::entry::{
    BindingPolicy, FunctionInterface, InvocationBinding, InvocationContext, NamedValues, Package,
    ProofOptions, ProofRequest, RoleInputs, RunContext, SetupAuthority, Value,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    assert!(!zkc::EXECUTION_COUNTS_ENABLED);
    let bytes = include_bytes!("numerical.zkpkg");
    let host = numerical::admit(bytes, Default::default(), Default::default())?;
    let arguments =
        || numerical::Arguments::try_from(NamedValues::from([("値".into(), Value::from(7u64))]));
    host.check_inputs(zkc::entry::FunctionRequest {
        arguments: arguments()?.into(),
        context: Default::default(),
    })?;
    for _ in 0..2 {
        let result = numerical::call(&host, arguments()?, Default::default())?;
        assert_eq!(result.value, Some(9));
        assert!(result.report.is_success() && result.conversion_error.is_none());
    }
    let mut wrong = bytes.to_vec();
    wrong.push(b' ');
    assert_eq!(
        numerical::admit(&wrong, Default::default(), Default::default())
            .err()
            .unwrap()
            .code(),
        "entry-package-identity"
    );

    let bytes = include_bytes!("joint.zkpkg");
    let package = Package::capture(bytes, &joint::PACKAGE_SHA256, Package::MAX_BYTES)?;
    let inventory = FunctionInterface::deployment_interfaces(&package)?;
    let authorities = inventory
        .iter()
        .map(|d| (d.id().into(), SetupAuthority::default()))
        .collect();
    let host = joint::admit(bytes, Default::default(), authorities)?;
    let context = || InvocationContext {
        deployments: host
            .deployments()
            .map(|(id, _)| (id.into(), InvocationBinding::Run(RunContext::default())))
            .collect(),
    };
    let arguments = || {
        joint::Arguments::try_from(NamedValues::from([(
            "inputs".into(),
            Value::Record(
                [
                    (
                        "P".into(),
                        Value::Record([("value".into(), Value::from(true))].into()),
                    ),
                    ("V".into(), Value::Record(Default::default())),
                ]
                .into(),
            ),
        )]))
    };
    let prepared = host.prepare(zkc::entry::FunctionRequest {
        arguments: arguments()?.into(),
        context: context(),
    })?;
    assert!(prepared.execute().is_success());
    let result = joint::call(&host, arguments()?, context())?;
    assert!(result.report.is_success() && result.conversion_error.is_none());
    let Value::Record(mut roles) = Value::from(result.value.unwrap()) else {
        panic!("roles")
    };
    let Value::Record(mut values) = roles.remove("V").unwrap() else {
        panic!("results")
    };
    assert!(bool::try_from(values.remove("received").unwrap())?);

    let options = ProofOptions {
        binding: BindingPolicy::AllowAuthored,
        ..Default::default()
    };
    let bytes = include_bytes!("proof.zkpkg");
    let prover = proof::admit(bytes, options, Default::default())?;
    let verifier = proof::admit(bytes, options, Default::default())?;
    let proving = |expected, candidate| ProofRequest {
        public: proof::PublicInputs { expected }.into(),
        private: RoleInputs {
            inputs: proof::PInputs { candidate }.into(),
            ..Default::default()
        },
        ..Default::default()
    };
    // The verifier's statement is supplied independently of proof bytes.
    let verifying = |expected| ProofRequest {
        public: proof::PublicInputs { expected }.into(),
        ..Default::default()
    };
    prover.check_inputs(proving(true, true), zkc::entry::ProofOperation::Prove, None)?;
    for _ in 0..2 {
        let produced = prover.prove(proving(true, true))?;
        assert!(produced.is_success());
        let candidate = produced.native.outcome.unwrap();
        let checked = verifier.verify(verifying(true), &candidate)?;
        assert!(checked.is_success());
        assert_eq!(checked.verification_result(), Some(true));
        let changed = verifier.verify(verifying(false), &candidate)?;
        assert!(!changed.is_success());
        assert_eq!(
            changed.native.outcome.as_ref().err().map(String::as_str),
            Some("proof-header")
        );
        let bad = prover.prove(proving(true, false))?;
        assert!(bad.is_success());
        let rejected = verifier.verify(verifying(true), &bad.native.outcome.unwrap())?;
        assert_eq!(rejected.verification_result(), Some(false));
        assert!(!rejected.is_success());
    }
    println!(
        "normal-feature staged SDK: Unicode, numerical, joint, preparation, independent statements, repeated calls and refusals passed"
    );
    Ok(())
}
