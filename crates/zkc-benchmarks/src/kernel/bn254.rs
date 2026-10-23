//! BN254 controls use typed resident buffers, the common timer and installed VM.
use super::{Boundary, Family, Group, Kernel, Provider, fail, installed};
use crate::{Failure, Operation, Report, Request, Result, measure};
use ark_ff::PrimeField;
use serde_json::json;
use sha2::{Digest, Sha256};
use zkc_kernels::{arkworks::bn254 as ark, halo2curves::bn254 as halo};
use zkc_native::Value;

fn scalars(n: usize) -> Vec<ark::Scalar> {
    (0..n)
        .map(|i| {
            let mut hash = Sha256::new();
            hash.update(b"zkc.benchmark/bn254/0");
            hash.update((i as u64).to_le_bytes());
            let scalar = ark::Scalar::from_le_bytes_mod_order(&hash.finalize());
            // Keep every generated base a nonidentity generator multiple.
            if scalar == ark::Scalar::from(0) {
                ark::Scalar::from(1)
            } else {
                scalar
            }
        })
        .collect()
}
fn import_scalars(values: &[ark::Scalar]) -> Result<halo::ScalarVector> {
    halo::ScalarVector::try_from_fn(values.len(), |i| halo::arkworks::import_scalar(values[i]))
        .map_err(fail)
}
fn export_scalars(values: &halo::ScalarVector) -> Result<Vec<ark::Scalar>> {
    values
        .iter()
        .map(|s| halo::arkworks::export_scalar(s).map_err(fail))
        .collect()
}
fn check<T: PartialEq>(actual: T, expected: &T) -> Result<()> {
    if &actual == expected {
        Ok(())
    } else {
        Err(Failure::IncorrectResult)
    }
}

// Only the group-specific typed adapters differ. Scheduling, timing, conversion
// placement, chain semantics and result checks are shared by both source groups.
trait Curve: Copy + PartialEq {
    type Point: Copy;
    type Bulk;
    const DOMAIN: &'static str;
    fn bases(scalars: &[ark::Scalar]) -> Vec<Self>;
    fn import(points: &[Self]) -> Result<Self::Bulk>;
    fn export(points: &Self::Bulk) -> Result<Vec<Self>>;
    fn export_point(point: Self::Point) -> Result<Self>;
    fn arithmetic(op: Kernel, s: &[ark::Scalar], p: &[Self], length: usize) -> Result<Self>;
    fn resident(
        op: Kernel,
        s: &halo::ScalarVector,
        p: &Self::Bulk,
        length: usize,
    ) -> Result<Self::Point>;
    fn value(self) -> Value;
    fn values(points: Vec<Self>) -> Value;
}
macro_rules! curve {
    ($point:ident, $bulk:ident, $import:ident, $export:ident, $domain:literal, $single:ident, $vector:ident) => {
        impl Curve for ark::$point {
            type Point = halo::$point;
            type Bulk = halo::$bulk;
            const DOMAIN: &'static str = $domain;
            fn bases(s: &[ark::Scalar]) -> Vec<Self> {
                s.iter()
                    .rev()
                    .map(|&s| Self::generator().scale(s))
                    .collect()
            }
            fn import(p: &[Self]) -> Result<Self::Bulk> {
                halo::$bulk::try_from_fn(p.len(), |i| halo::arkworks::$import(p[i])).map_err(fail)
            }
            fn export(p: &Self::Bulk) -> Result<Vec<Self>> {
                p.iter().map(Self::export_point).collect()
            }
            fn export_point(p: Self::Point) -> Result<Self> {
                halo::arkworks::$export(p).map_err(fail)
            }
            fn arithmetic(
                op: Kernel,
                s: &[ark::Scalar],
                p: &[Self],
                length: usize,
            ) -> Result<Self> {
                let mut result = if op == Kernel::Msm {
                    Self::msm(s, p).map_err(fail)?
                } else {
                    p[0].scale(s[0])
                };
                for _ in 1..length {
                    result = if op == Kernel::Msm {
                        result.add(&Self::msm(s, p).map_err(fail)?)
                    } else {
                        result.scale(s[0])
                    };
                }
                Ok(result)
            }
            fn resident(
                op: Kernel,
                s: &halo::ScalarVector,
                p: &Self::Bulk,
                length: usize,
            ) -> Result<Self::Point> {
                let mut result = if op == Kernel::Msm {
                    p.msm(s).map_err(fail)?
                } else {
                    p.get(0).unwrap().scale(s.get(0).unwrap())
                };
                for _ in 1..length {
                    result = if op == Kernel::Msm {
                        result.add(&p.msm(s).map_err(fail)?)
                    } else {
                        result.scale(s.get(0).unwrap())
                    };
                }
                Ok(result)
            }
            fn value(self) -> Value {
                Value::$single(self)
            }
            fn values(p: Vec<Self>) -> Value {
                Value::$vector(p.into())
            }
        }
    };
}
curve!(
    G1,
    G1Vector,
    import_g1,
    export_g1,
    "bn254.g1",
    Bn254G1,
    Bn254G1Vector
);
curve!(
    G2,
    G2Vector,
    import_g2,
    export_g2,
    "bn254.g2",
    Bn254G2,
    Bn254G2Vector
);

fn curve_run<G: Curve>(
    request: &Request,
    provider: Provider,
    boundary: Boundary,
    op: Kernel,
    n: usize,
    length: usize,
) -> Result<Report> {
    let s = scalars(n);
    let p = G::bases(&s);
    let fs = import_scalars(&s)?;
    let fp = G::import(&p)?;
    let conversion = matches!(boundary, Boundary::Import | Boundary::Export);
    let expected = if conversion {
        p.clone()
    } else {
        vec![G::arithmetic(op, &s, &p, length)?]
    };
    if is_installed(boundary) {
        let inputs = if op == Kernel::Scale {
            vec![p[0].value(), Value::Bn254Field(s[0])]
        } else {
            vec![Value::Bn254Vector(s.into()), G::values(p)]
        };
        return installed::run(
            request,
            provider,
            boundary,
            op,
            G::DOMAIN,
            inputs,
            expected[0].value(),
            n,
            length,
        );
    }
    enum Output<G: Curve> {
        Canonical(Vec<G>),
        CanonicalPoint(G),
        Point(G::Point),
        Imported(G::Bulk, halo::ScalarVector),
    }
    let samples = measure::measure(
        request.plan,
        || Ok(()),
        |_| {
            Ok(if provider == Provider::Arkworks {
                Output::CanonicalPoint(G::arithmetic(op, &s, &p, length)?)
            } else {
                match boundary {
                    Boundary::Resident => Output::Point(G::resident(op, &fs, &fp, length)?),
                    Boundary::Converted => {
                        let p = G::import(&p)?;
                        let s = import_scalars(&s)?;
                        Output::CanonicalPoint(G::export_point(G::resident(op, &s, &p, length)?)?)
                    }
                    Boundary::Import => Output::Imported(G::import(&p)?, import_scalars(&s)?),
                    Boundary::Export => Output::Canonical(G::export(&fp)?),
                    _ => unreachable!(),
                }
            })
        },
        |out| {
            let actual = match out {
                Output::Canonical(out) => out,
                Output::CanonicalPoint(out) => vec![out],
                Output::Point(out) => vec![G::export_point(out)?],
                Output::Imported(out, imported) => {
                    check(export_scalars(&imported)?, &s)?;
                    G::export(&out)?
                }
            };
            check(actual, &expected)
        },
    )?;
    Ok(Report::new(boundary.name(), samples, 0))
}

fn scalar_run(
    request: &Request,
    provider: Provider,
    boundary: Boundary,
    op: Kernel,
    n: usize,
    length: usize,
) -> Result<Report> {
    let a = scalars(n);
    let b: Vec<_> = a.iter().rev().copied().collect();
    let arithmetic = || {
        let mut out = a.clone();
        for _ in 0..length {
            for (out, factor) in out.iter_mut().zip(&b) {
                *out *= factor;
            }
        }
        out
    };
    let expected = arithmetic();
    let value = |s: Vec<ark::Scalar>| {
        if op == Kernel::FieldMul {
            Value::Bn254Field(s[0])
        } else {
            Value::Bn254Vector(s.into())
        }
    };
    if is_installed(boundary) {
        return installed::run(
            request,
            provider,
            boundary,
            op,
            "bn254.fr",
            vec![value(a), value(b)],
            value(expected),
            n,
            length,
        );
    }
    let fa = import_scalars(&a)?;
    let fb = import_scalars(&b)?;
    enum Output {
        Canonical(Vec<ark::Scalar>),
        CanonicalField(ark::Scalar),
        Field(halo::Scalar),
        Vector(halo::ScalarVector),
    }
    let resident = |a: &halo::ScalarVector, b: &halo::ScalarVector| -> Result<Output> {
        if op == Kernel::FieldMul {
            let mut out = a.get(0).unwrap();
            for _ in 0..length {
                out *= b.get(0).unwrap();
            }
            Ok(Output::Field(out))
        } else {
            let mut out = halo::ScalarVector::filled(n, halo::Scalar::ZERO).map_err(fail)?;
            a.mul_into(b, &mut out).map_err(fail)?;
            for _ in 1..length {
                let mut next = halo::ScalarVector::filled(n, halo::Scalar::ZERO).map_err(fail)?;
                out.mul_into(b, &mut next).map_err(fail)?;
                out = next;
            }
            Ok(Output::Vector(out))
        }
    };
    let canonical = |out| -> Result<Output> {
        match out {
            Output::Field(out) => Ok(Output::CanonicalField(
                halo::arkworks::export_scalar(out).map_err(fail)?,
            )),
            Output::Vector(out) => Ok(Output::Canonical(export_scalars(&out)?)),
            out => Ok(out),
        }
    };
    let samples = measure::measure(
        request.plan,
        || Ok(()),
        |_| {
            if provider == Provider::Arkworks {
                if op == Kernel::FieldMul {
                    let mut out = a[0];
                    for _ in 0..length {
                        out *= b[0];
                    }
                    Ok(Output::CanonicalField(out))
                } else {
                    let mut out = vec![ark::Scalar::from(0); n];
                    zkc_kernels::vector::mul(&a, &b, &mut out).map_err(fail)?;
                    for _ in 1..length {
                        let mut next = vec![ark::Scalar::from(0); n];
                        zkc_kernels::vector::mul(&out, &b, &mut next).map_err(fail)?;
                        out = next;
                    }
                    Ok(Output::Canonical(out))
                }
            } else if boundary == Boundary::Converted {
                let a = import_scalars(&a)?;
                let b = import_scalars(&b)?;
                canonical(resident(&a, &b)?)
            } else {
                resident(&fa, &fb)
            }
        },
        |out| {
            let out = match canonical(out)? {
                Output::Canonical(out) => out,
                Output::CanonicalField(out) => vec![out],
                _ => unreachable!(),
            };
            check(out, &expected)
        },
    )?;
    Ok(Report::new(boundary.name(), samples, 0))
}

fn pairing_inputs(n: usize, cancel: bool) -> (Vec<ark::G1>, Vec<ark::G2>) {
    let s = scalars(n);
    let mut p = <ark::G1 as Curve>::bases(&s);
    let mut q = <ark::G2 as Curve>::bases(&s);
    if cancel {
        for i in (0..n.saturating_sub(1)).step_by(2) {
            p[i + 1] = p[i].neg();
            q[i + 1] = q[i];
        }
    }
    (p, q)
}
fn pairing_run(
    request: &Request,
    provider: Provider,
    boundary: Boundary,
    n: usize,
    length: usize,
) -> Result<Report> {
    let (p, q) = pairing_inputs(n, length > 1);
    let fp = <ark::G1 as Curve>::import(&p)?;
    let fq = <ark::G2 as Curve>::import(&q)?;
    let expected = ark::pairing_check(&p, &q).map_err(fail)?;
    if is_installed(boundary) {
        return installed::run(
            request,
            provider,
            boundary,
            Kernel::PairingCheck,
            "bn254.fr",
            vec![
                Value::Bn254G1Vector(p.into()),
                Value::Bn254G2Vector(q.into()),
            ],
            Value::Bool(expected),
            n,
            length,
        );
    }
    let samples = measure::measure(
        request.plan,
        || Ok(()),
        |_| {
            if provider == Provider::Arkworks {
                (0..length)
                    .map(|_| ark::pairing_check(&p, &q).map_err(fail))
                    .collect::<Result<Vec<_>>>()
            } else if boundary == Boundary::Converted {
                let p = <ark::G1 as Curve>::import(&p)?;
                let q = <ark::G2 as Curve>::import(&q)?;
                (0..length)
                    .map(|_| halo::pairing_check_bulk(&p, &q).map_err(fail))
                    .collect()
            } else {
                (0..length)
                    .map(|_| halo::pairing_check_bulk(&fp, &fq).map_err(fail))
                    .collect()
            }
        },
        |out| check(out, &vec![expected; length]),
    )?;
    Ok(Report::new(boundary.name(), samples, 0))
}
fn is_installed(boundary: Boundary) -> bool {
    matches!(
        boundary,
        Boundary::Installed | Boundary::ResidentInstalledChain | Boundary::WireResidentChain
    )
}

pub(super) fn scheduling_work(kernel: Kernel, n: usize) -> Result<Option<u64>> {
    match kernel {
        Kernel::Msm => halo::msm_work(n).map(Some).map_err(fail),
        Kernel::PairingCheck => halo::pairing_work(n).map(Some).map_err(fail),
        _ => Ok(None),
    }
}
pub(super) fn workspace(kernel: Kernel, n: usize) -> Result<Option<usize>> {
    match kernel {
        Kernel::Msm => halo::msm_workspace_bytes(n).map(Some).map_err(fail),
        Kernel::PairingCheck => halo::pairing_workspace_bytes(n).map(Some).map_err(fail),
        _ => Ok(None),
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn run(
    request: &Request,
    provider: Provider,
    group: Group,
    kernel: Kernel,
    boundary: Boundary,
    n: usize,
    length: usize,
) -> Result<Report> {
    if request.operation != Operation::Run
        || !Family::Bn254.supports(provider)
        || !(1..=4096).contains(&n)
        || !(1..=32).contains(&length)
        || matches!(kernel, Kernel::Scale | Kernel::FieldMul) && n != 1
        || !matches!(
            (group, kernel),
            (Group::Scalar, Kernel::FieldMul | Kernel::VectorMul)
                | (Group::G1 | Group::G2, Kernel::Scale | Kernel::Msm)
                | (Group::Pairing, Kernel::PairingCheck)
        )
        || matches!(boundary, Boundary::Import | Boundary::Export)
            && (provider != Provider::Halo2curvesAxiom || !matches!(group, Group::G1 | Group::G2))
        || length != 1
            && !matches!(
                boundary,
                Boundary::Resident
                    | Boundary::Converted
                    | Boundary::ResidentInstalledChain
                    | Boundary::WireResidentChain
            )
        || zkc_runtime::vm::ExecutionCounts::ENABLED
    {
        return Err("unsupported BN254 provider benchmark request".into());
    }
    let mut report = match group {
        Group::Scalar => scalar_run(request, provider, boundary, kernel, n, length),
        Group::G1 => curve_run::<ark::G1>(request, provider, boundary, kernel, n, length),
        Group::G2 => curve_run::<ark::G2>(request, provider, boundary, kernel, n, length),
        Group::Pairing => pairing_run(request, provider, boundary, n, length),
    }?;
    if !is_installed(boundary) {
        report.diagnostics =
            super::kernel_diagnostics(Family::Bn254, provider, group, kernel, boundary, n, length)?;
    }
    report.diagnostics["family"] = json!("bn254");
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request(group: &str, kernel: &str, boundary: &str, n: usize, length: usize) -> Request {
        let mut request: Request = serde_json::from_value(json!({
            "format":"zkc.benchmark-job/0", "backend":{
                "kind":"kernel", "family":"bn254", "provider":"halo2curves-axiom",
                "group":group, "kernel":kernel, "boundary":boundary, "elements":n, "chain_length":length},
            "operation":"run", "plan":{"warmups":1,"samples":1,"iterations":1}, "proof":"unused"
        })).unwrap();
        request.cpu = Some(zkc::execution::CpuExecution::serial().unwrap());
        request
    }

    #[test]
    fn generated_inputs_are_full_width_nonzero_and_repeatable() {
        let s = scalars(256);
        assert_eq!(s, scalars(256));
        for value in &s {
            assert_ne!(*value, ark::Scalar::from(0));
            let bytes = ark::encode_scalar(value).unwrap();
            assert!(bytes[16..].iter().any(|&b| b != 0));
        }
        for p in <ark::G1 as Curve>::bases(&s) {
            assert_ne!(p, ark::G1::identity());
        }
        for p in <ark::G2 as Curve>::bases(&s) {
            assert_ne!(p, ark::G2::identity());
        }
    }

    #[test]
    fn empty_identity_and_mismatched_operands_have_mathematical_results_or_refusals() {
        let empty = halo::ScalarVector::default();
        let mut empty_result = halo::ScalarVector::default();
        empty.mul_into(&empty, &mut empty_result).unwrap();
        assert!(empty_result.is_empty());
        let zero = halo::ScalarVector::filled(2, halo::Scalar::ZERO).unwrap();
        macro_rules! group {
            ($point:ident, $bulk:ident, $import:ident, $export:ident) => {
                let points = halo::$bulk::filled(2, halo::$point::identity()).unwrap();
                assert!(halo::$bulk::default().msm(&empty).unwrap().is_identity());
                assert!(points.msm(&zero).unwrap().is_identity());
                assert!(points.msm(&empty).is_err());
                let resident = halo::arkworks::$import(ark::$point::identity()).unwrap();
                assert!(resident.is_identity());
                assert_eq!(
                    halo::arkworks::$export(resident).unwrap(),
                    ark::$point::identity()
                );
            };
        }
        group!(G1, G1Vector, import_g1, export_g1);
        group!(G2, G2Vector, import_g2, export_g2);
        assert!(
            halo::pairing_check_bulk(&halo::G1Vector::default(), &halo::G2Vector::default())
                .unwrap()
        );
        let p = halo::G1Vector::filled(1, halo::G1::identity()).unwrap();
        let q = halo::G2Vector::filled(1, halo::G2::generator()).unwrap();
        assert!(halo::pairing_check_bulk(&p, &q).unwrap());
        assert!(halo::pairing_check_bulk(&p, &halo::G2Vector::default()).is_err());
        assert!(halo::decode_scalar(&[255; 32]).is_err());
        assert!(check(vec![false], &vec![true]).is_err());
    }

    #[test]
    fn pairing_controls_include_true_and_false_nonidentity_products() {
        for cancel in [false, true] {
            let (p, q) = pairing_inputs(2, cancel);
            let fp = <ark::G1 as Curve>::import(&p).unwrap();
            let fq = <ark::G2 as Curve>::import(&q).unwrap();
            assert_eq!(ark::pairing_check(&p, &q).unwrap(), cancel);
            assert_eq!(halo::pairing_check_bulk(&fp, &fq).unwrap(), cancel);
            assert!(fp.iter().all(|p| !p.is_identity()));
            assert!(fq.iter().all(|p| !p.is_identity()));
        }
    }

    #[test]
    fn family_inventory_defaults_to_bls_and_refuses_cross_family_providers() {
        let bn = request("g1", "msm", "resident", 2, 1);
        for (family, provider) in [
            (Family::Bls12381, Provider::Halo2curvesAxiom),
            (Family::Bn254, Provider::Blst),
        ] {
            assert!(
                super::super::run_family(
                    &bn,
                    family,
                    provider,
                    Group::G1,
                    Kernel::Msm,
                    Boundary::Resident,
                    2,
                    1
                )
                .is_err()
            );
        }
        let mut job =
            serde_json::to_value(json!({"kind":"kernel", "provider":"blst", "group":"g1",
            "kernel":"scale", "boundary":"resident", "elements":1}))
            .unwrap();
        let backend: crate::Backend = serde_json::from_value(job.clone()).unwrap();
        assert!(matches!(
            backend,
            crate::Backend::Kernel {
                family: Family::Bls12381,
                ..
            }
        ));
        job["family"] = json!("invented");
        assert!(serde_json::from_value::<crate::Backend>(job).is_err());
        for (group, op, boundary, n, length) in [
            (Group::Scalar, Kernel::Msm, Boundary::Resident, 2, 1),
            (Group::G1, Kernel::ScaleEach, Boundary::Resident, 2, 1),
            (Group::G1, Kernel::Scale, Boundary::Resident, 2, 1),
            (Group::Pairing, Kernel::PairingCheck, Boundary::Import, 2, 1),
            (Group::G1, Kernel::Msm, Boundary::Resident, 0, 1),
            (Group::G1, Kernel::Msm, Boundary::Installed, 2, 4),
        ] {
            assert!(
                run(
                    &bn,
                    Provider::Halo2curvesAxiom,
                    group,
                    op,
                    boundary,
                    n,
                    length
                )
                .is_err()
            );
        }
    }

    #[cfg(not(feature = "execution-counts"))]
    #[test]
    fn every_bn254_boundary_uses_the_common_gate_and_accurate_receipts() {
        for (group, op, group_name, op_name, n) in [
            (Group::Scalar, Kernel::FieldMul, "scalar", "field_mul", 1),
            (Group::Scalar, Kernel::VectorMul, "scalar", "vector_mul", 2),
            (Group::G1, Kernel::Scale, "g1", "scale", 1),
            (Group::G2, Kernel::Scale, "g2", "scale", 1),
            (Group::G1, Kernel::Msm, "g1", "msm", 2),
            (Group::G2, Kernel::Msm, "g2", "msm", 2),
            (
                Group::Pairing,
                Kernel::PairingCheck,
                "pairing",
                "pairing_check",
                2,
            ),
        ] {
            for (boundary, name, length) in [
                (Boundary::Resident, "resident", 3),
                (Boundary::Converted, "converted", 3),
                (Boundary::Installed, "installed", 1),
                (
                    Boundary::ResidentInstalledChain,
                    "resident_installed_chain",
                    3,
                ),
                (Boundary::WireResidentChain, "wire_resident_chain", 3),
            ] {
                let request = request(group_name, op_name, name, n, length);
                let cpu = request.cpu().unwrap();
                for provider in [Provider::Arkworks, Provider::Halo2curvesAxiom] {
                    let report = cpu
                        .enter(|| run(&request, provider, group, op, boundary, n, length))
                        .unwrap();
                    assert_eq!(report.samples.len(), 2);
                    assert_eq!(report.diagnostics["family"], "bn254");
                    assert_eq!(report.diagnostics["provider"], provider.name());
                    if !is_installed(boundary) {
                        let storage = report.diagnostics["bulk_storage"].as_str().unwrap();
                        assert_eq!(
                            storage.starts_with("halo2curves-axiom"),
                            provider == Provider::Halo2curvesAxiom
                        );
                        assert_eq!(
                            storage.starts_with("Arkworks"),
                            provider == Provider::Arkworks
                        );
                    }
                    assert_eq!(
                        report.diagnostics["arithmetic_calls"],
                        length + if op == Kernel::Msm { length - 1 } else { 0 }
                    );
                    let workspace = if provider == Provider::Halo2curvesAxiom {
                        workspace(op, n).unwrap()
                    } else {
                        None
                    };
                    assert_eq!(
                        report.diagnostics["managed"]["provider_workspace_admission_bound_bytes_per_call"],
                        json!(workspace)
                    );
                    if is_installed(boundary) {
                        let conversions = report.diagnostics["explicit_conversions"]
                            .as_array()
                            .unwrap();
                        assert_eq!(
                            !conversions.is_empty(),
                            provider == Provider::Halo2curvesAxiom
                                && boundary == Boundary::Installed
                        );
                        if group == Group::G2
                            && boundary == Boundary::Installed
                            && provider == Provider::Halo2curvesAxiom
                        {
                            assert!(conversions.iter().any(|row| row["canonical_payload_bytes"]
                                == json!(if op == Kernel::Msm { n * 64 } else { 64 })));
                        }
                    }
                }
            }
        }
        for (group, name) in [(Group::G1, "g1"), (Group::G2, "g2")] {
            for (boundary, spelling) in [(Boundary::Import, "import"), (Boundary::Export, "export")]
            {
                let request = request(name, "msm", spelling, 2, 1);
                let report = run(
                    &request,
                    Provider::Halo2curvesAxiom,
                    group,
                    Kernel::Msm,
                    boundary,
                    2,
                    1,
                )
                .unwrap();
                assert_eq!(report.diagnostics["arithmetic_calls"], 0);
                assert!(report.diagnostics["managed"]["provider_workspace_admission_bound_bytes_per_call"].is_null());
            }
        }
    }
}
