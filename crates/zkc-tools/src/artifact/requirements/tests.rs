use super::*;
use crate::artifact::{
    CacheLimits, CheckerInstallation, InvocationInputs, InvocationOptions,
    inputs::tests::{Case, compile, write},
};
use serde_json::json;

#[test]
fn bounded_authority_ingress() {
    assert!(ClaimRequirements::from_slices(b"{}", b"[]").is_err());
    assert!(ClaimRequirements::from_slices(&vec![b' '; (1 << 20) + 1], b"[]").is_err());
    assert!(
        PhysicalChoices::default()
            .with_implementations(b"{}")
            .is_err()
    );
}

#[test]
fn retained_requirements_bind_the_actual_prepared_candidate() {
    let compiler = zkc_test_support::compiler().display().to_string();
    let lean = zkc_test_support::checker("interactive-protocol")
        .display()
        .to_string();
    let case = Case::new(0, 0, 0);
    let mut source = case.bundle.source.clone();
    source[1] = json!([["control.require", "control.require", [], ""]]);
    source[2][0][4].as_array_mut().unwrap().insert(
        0,
        json!(["op", "require", "control.require", [], ["ok"], []]),
    );
    let dir = case.dir.path();
    let sp = write(dir, "source.json", &source);
    let dp = write(dir, "descriptor.json", &case.bundle.descriptor);
    let construction = compile(&compiler, &["protocol-construct", &sp, &dp]);
    let cp = write(dir, "construction.json", &construction);
    let common = write(dir, "common.json", &construction[2]);
    let physical = compile(&compiler, &["protocol-compile", &common]);
    let pp = write(dir, "physical.json", &physical);
    let catalog = compile(&compiler, &["claim-inspect", &sp, "main"]);
    let guard = &catalog["guards"][0];
    let contract = json!([
        "zkc.claim-contract/1",
        catalog["source_digest"],
        "main",
        "V",
        [],
        [["accepted", "guard", [guard["value"]]]],
        ["accepted"],
        [["accepted", guard["path"]]],
        [],
        [],
    ]);
    let authority = write(dir, "contract.json", &contract);
    let certificate = compile(&compiler, &["claim-derive", &sp, &authority]);
    let cb = serde_json::to_vec(&contract).unwrap();
    let cert = serde_json::to_vec(&certificate).unwrap();
    let installation = CheckerInstallation::new(&compiler, &lean);
    let checked = || CheckedBundle::load(&sp, &dp, &cp, &pp, &compiler, &lean).unwrap();
    let make = || installation.prepare_checked(checked(), CacheLimits::default());
    let mut prepared = make()
        .with_requirements(
            &installation,
            ClaimRequirements::from_slices(&cb, &cert).unwrap(),
            PhysicalChoices::default(),
        )
        .unwrap();
    assert_eq!(prepared.checked_requirements().unwrap().contract(), cb);
    let input = InvocationInputs::from_slice(&serde_json::to_vec(&case.input).unwrap()).unwrap();
    for _ in 0..2 {
        let proof = prepared
            .produce(&installation, &input, InvocationOptions::new(0))
            .unwrap()
            .execution
            .outcome
            .unwrap();
        prepared
            .validate(&installation, &input, &proof, InvocationOptions::new(0))
            .unwrap()
            .execution
            .outcome
            .unwrap();
    }
    assert!(
        prepared
            .with_requirements(
                &installation,
                ClaimRequirements::from_slices(&cb, &cert).unwrap(),
                PhysicalChoices::default(),
            )
            .is_err()
    );
    for mutate_contract in [true, false] {
        let mut a = contract.clone();
        let mut c = certificate.clone();
        if mutate_contract {
            a[1] = json!("0".repeat(64));
        } else {
            c[1] = json!("0".repeat(64));
        }
        assert!(
            make()
                .with_requirements(
                    &installation,
                    ClaimRequirements::from_slices(
                        &serde_json::to_vec(&a).unwrap(),
                        &serde_json::to_vec(&c).unwrap(),
                    )
                    .unwrap(),
                    PhysicalChoices::default(),
                )
                .is_err()
        );
    }
    let wrong = PhysicalChoices::default()
        .with_implementations(br#"[["missing","arkworks/control.require"]]"#)
        .unwrap();
    assert!(
        make()
            .with_requirements(
                &installation,
                ClaimRequirements::from_slices(&cb, &cert).unwrap(),
                wrong,
            )
            .is_err()
    );
    assert!(
        make()
            .with_requirements(
                &CheckerInstallation::new(&compiler, &lean),
                ClaimRequirements::from_slices(&cb, &cert).unwrap(),
                PhysicalChoices::default(),
            )
            .is_err()
    );
    let frozen = make();
    std::fs::write(&sp, b"corrupted pathname contents").unwrap();
    assert!(
        frozen
            .with_requirements(
                &installation,
                ClaimRequirements::from_slices(&cb, &cert).unwrap(),
                PhysicalChoices::default(),
            )
            .is_ok()
    );
}
