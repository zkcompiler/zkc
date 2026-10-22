//! Provider controls reuse the process scheduler and per-call measurement protocol.
//! All arithmetic results are checked outside the timer against Arkworks. Import,
//! export, resident arithmetic and the complete installed operation are distinct.
use crate::{Failure, Operation, Report, Request, Result, measure};
use ark_ff::PrimeField;
use serde::Deserialize;
use serde_json::json;
use sha2::{Digest, Sha256};
use zkc_kernels::{arkworks::bls12_381 as ark, blst::bls12_381 as blst};
use zkc_native::{Domain, EntryPolicy, NativeBackend, Policy, Value};
use zkc_runtime::{
    interpreter::Runner,
    vm::{Action, OperationBinding, Program},
};

#[derive(Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Provider {
    Arkworks,
    Blst,
}
#[derive(Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Boundary {
    Resident,
    Converted,
    Import,
    Export,
    Installed,
}
impl Boundary {
    fn name(self) -> &'static str {
        match self {
            Self::Resident => "resident_kernel_call",
            Self::Converted => "converted_kernel_call",
            Self::Import => "provider_import",
            Self::Export => "provider_export",
            Self::Installed => "installed_operation_call",
        }
    }
}
#[derive(Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Group {
    G1,
    G2,
    Pairing,
}
#[derive(Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Kernel {
    Scale,
    ScaleEach,
    VectorScale,
    Msm,
    PairingCheck,
}
impl Kernel {
    fn contract(self) -> &'static str {
        match self {
            Self::Scale => "curve.scale",
            Self::ScaleEach => "curve.scale_each",
            Self::VectorScale => "curve.vector_scale",
            Self::Msm => "curve.msm",
            Self::PairingCheck => "pairing.check",
        }
    }
}
fn fail(e: impl std::fmt::Display) -> Failure {
    Failure::Failed(e.to_string())
}

trait Curve: Copy + PartialEq {
    type Foreign: Copy;
    const DOMAIN: &'static str;
    fn generator() -> Self;
    fn scale(self, scalar: ark::Scalar) -> Self;
    fn import(self) -> Result<Self::Foreign>;
    fn export(point: Self::Foreign) -> Result<Self>;
    fn foreign_scale(point: Self::Foreign, scalar: blst::Scalar) -> Self::Foreign;
    fn msm(s: &[ark::Scalar], p: &[Self]) -> Result<Self>;
    fn foreign_msm(s: &[blst::Scalar], p: &[Self::Foreign]) -> Result<Self::Foreign>;
    fn scale_into(p: &[Self], s: &[ark::Scalar], shared: bool) -> Result<Vec<Self>>;
    fn value(self) -> Value;
    fn values(p: Vec<Self>) -> Value;
}
macro_rules! curve {
    ($point:ident, $import:ident, $export:ident, $domain:literal, $single:ident, $vector:ident) => {
        impl Curve for ark::$point {
            type Foreign = blst::$point;
            const DOMAIN: &'static str = $domain;
            fn generator() -> Self {
                Self::generator()
            }
            fn scale(self, scalar: ark::Scalar) -> Self {
                Self::scale(&self, scalar)
            }
            fn import(self) -> Result<Self::Foreign> {
                blst::arkworks::$import(self).map_err(fail)
            }
            fn export(p: Self::Foreign) -> Result<Self> {
                blst::arkworks::$export(p).map_err(fail)
            }
            fn foreign_scale(p: Self::Foreign, s: blst::Scalar) -> Self::Foreign {
                p.scale(s)
            }
            fn msm(s: &[ark::Scalar], p: &[Self]) -> Result<Self> {
                Self::msm(s, p).map_err(fail)
            }
            fn foreign_msm(s: &[blst::Scalar], p: &[Self::Foreign]) -> Result<Self::Foreign> {
                blst::$point::msm(s, p).map_err(fail)
            }
            fn scale_into(p: &[Self], s: &[ark::Scalar], shared: bool) -> Result<Vec<Self>> {
                let mut plan = Self::scaling_plan(
                    p.len(),
                    zkc_kernels::arkworks::scaling::Selection::Automatic {
                        max_workspace: 256 << 20,
                    },
                )
                .map_err(fail)?;
                let mut out = vec![Self::identity(); p.len()];
                if shared {
                    Self::scale_many_into(p, s[0], &mut out, &mut plan)
                } else {
                    Self::scale_each_into(s, p, &mut out, &mut plan)
                }
                .map_err(fail)?;
                Ok(out)
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
curve!(G1, import_g1, export_g1, "bls12-381.g1", Curve, Groups);
curve!(
    G2,
    import_g2,
    export_g2,
    "bls12-381.g2",
    Bls12381G2,
    Bls12381G2Vector
);

fn scalars(n: usize) -> Vec<ark::Scalar> {
    (0..n)
        .map(|i| ark::Scalar::from_le_bytes_mod_order(&Sha256::digest((i as u64).to_le_bytes())))
        .collect()
}
fn arithmetic<G: Curve>(op: Kernel, s: &[ark::Scalar], p: &[G]) -> Result<Vec<G>> {
    match op {
        Kernel::Msm => Ok(vec![G::msm(s, p)?]),
        Kernel::Scale => Ok(vec![p[0].scale(s[0])]),
        _ => G::scale_into(p, s, op == Kernel::VectorScale),
    }
}
fn foreign<G: Curve>(op: Kernel, s: &[blst::Scalar], p: &[G::Foreign]) -> Result<Vec<G::Foreign>> {
    match op {
        Kernel::Msm => Ok(vec![G::foreign_msm(s, p)?]),
        Kernel::Scale => Ok(vec![G::foreign_scale(p[0], s[0])]),
        _ => Ok(p
            .iter()
            .enumerate()
            .map(|(i, &p)| G::foreign_scale(p, s[if op == Kernel::VectorScale { 0 } else { i }]))
            .collect()),
    }
}
fn import_scalars(s: &[ark::Scalar]) -> Result<Vec<blst::Scalar>> {
    s.iter()
        .map(|&s| blst::arkworks::import_scalar(s).map_err(fail))
        .collect()
}
enum Output<G: Curve> {
    Native(Vec<G>),
    Foreign(Vec<G::Foreign>, Vec<blst::Scalar>),
}

fn curve_run<G: Curve>(
    request: &Request,
    provider: Provider,
    boundary: Boundary,
    op: Kernel,
    n: usize,
) -> Result<Report> {
    let mut s = scalars(n);
    let p: Vec<_> = s.iter().rev().map(|&s| G::generator().scale(s)).collect();
    if op == Kernel::VectorScale {
        s.truncate(1);
    }
    let fp: Vec<_> = p.iter().copied().map(G::import).collect::<Result<_>>()?;
    let fs = import_scalars(&s)?;
    let conversion = matches!(boundary, Boundary::Import | Boundary::Export);
    let expected = if conversion {
        p.clone()
    } else {
        arithmetic::<G>(op, &s, &p)?
    };
    if boundary == Boundary::Installed {
        let inputs = match op {
            Kernel::Scale => vec![p[0].value(), Value::Field(s[0])],
            Kernel::VectorScale => vec![G::values(p), Value::Field(s[0])],
            _ => vec![Value::Vector(s.into()), G::values(p)],
        };
        let expected = if matches!(op, Kernel::Scale | Kernel::Msm) {
            expected[0].value()
        } else {
            G::values(expected)
        };
        return installed(request, provider, op, G::DOMAIN, inputs, expected);
    }
    let samples = measure::measure(
        request.plan,
        || Ok(()),
        |_| {
            Ok(if provider == Provider::Arkworks {
                Output::Native(arithmetic::<G>(op, &s, &p)?)
            } else {
                match boundary {
                    Boundary::Resident => Output::Foreign(foreign::<G>(op, &fs, &fp)?, vec![]),
                    Boundary::Import => Output::Foreign(
                        p.iter().copied().map(G::import).collect::<Result<_>>()?,
                        import_scalars(&s)?,
                    ),
                    Boundary::Export => {
                        Output::Native(fp.iter().copied().map(G::export).collect::<Result<_>>()?)
                    }
                    Boundary::Converted => {
                        let points = p
                            .iter()
                            .copied()
                            .map(G::import)
                            .collect::<Result<Vec<_>>>()?;
                        let scalars = import_scalars(&s)?;
                        Output::Native(
                            foreign::<G>(op, &scalars, &points)?
                                .into_iter()
                                .map(G::export)
                                .collect::<Result<_>>()?,
                        )
                    }
                    Boundary::Installed => unreachable!(),
                }
            })
        },
        |out| {
            let out = match out {
                Output::Native(out) => out,
                Output::Foreign(out, scalars) => {
                    if boundary == Boundary::Import
                        && scalars.iter().map(|s| s.to_bytes_le()).collect::<Vec<_>>()
                            != fs.iter().map(|s| s.to_bytes_le()).collect::<Vec<_>>()
                    {
                        return Err(Failure::IncorrectResult);
                    }
                    out.into_iter().map(G::export).collect::<Result<_>>()?
                }
            };
            if out == expected {
                Ok(())
            } else {
                Err(Failure::IncorrectResult)
            }
        },
    )?;
    Ok(Report::new(boundary.name(), samples, 0))
}

fn native() -> Result<NativeBackend> {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "benchmark", "main", None), None),
        Default::default(),
    )
    .map_err(fail)
}
fn installed(
    request: &Request,
    provider: Provider,
    op: Kernel,
    domain: &str,
    inputs: Vec<Value>,
    expected: Value,
) -> Result<Report> {
    let owner = if provider == Provider::Blst {
        "blst"
    } else {
        "arkworks"
    };
    let binding = OperationBinding {
        contract: op.contract().into(),
        arguments: vec![domain.into()],
        implementation: format!("{owner}/{}", op.contract()),
    };
    let sig = binding.signature().map_err(fail)?;
    let names: Vec<_> = (0..sig.inputs.len()).map(|i| format!("a{i}")).collect();
    let ports: Vec<_> = names
        .iter()
        .zip(&sig.inputs)
        .map(|(n, t)| json!([n, t.spelling()]))
        .collect();
    let output = sig.outputs[0].spelling();
    let carrier = json!([
        "zkc.program/0",
        [[
            "b",
            binding.contract,
            binding.arguments,
            binding.implementation
        ]],
        [[
            "function",
            "f",
            ports,
            [output],
            [["op", "site", "b", [], names, ["r"]], ["return", ["r"]]],
            ["f", []]
        ]],
        [[
            "participant",
            "actor",
            "instance",
            "P",
            ports,
            [output],
            [["local", "work", "f", names, ["r"]], ["return", ["r"]]],
            []
        ]],
        [["entry", "main", [["P", "actor"]]]]
    ]);
    let program = Program::decode(&serde_json::to_vec(&carrier).map_err(fail)?).map_err(fail)?;
    program.check_installation(&native()?).map_err(fail)?;
    let expected = native()?.encode_native_value(&expected).map_err(fail)?;
    let samples = measure::measure(
        request.plan,
        || {
            Runner::new(
                &program,
                "main",
                "P",
                "benchmark",
                native()?,
                inputs.clone(),
            )
            .map_err(|e| fail(e.error))
        },
        |mut runner| loop {
            match runner.poll() {
                Action::Local(action) => runner.execute_local(&action.cut).map_err(fail)?,
                Action::Returned(values) => break Ok(values),
                other => break Err(fail(format!("unexpected kernel action: {other:?}"))),
            }
        },
        |out| {
            if out.len() != 1 || native()?.encode_native_value(&out[0]).map_err(fail)? != expected {
                Err(Failure::IncorrectResult)
            } else {
                Ok(())
            }
        },
    )?;
    Ok(Report::new(Boundary::Installed.name(), samples, 0))
}

fn pairing_run(
    request: &Request,
    provider: Provider,
    boundary: Boundary,
    n: usize,
) -> Result<Report> {
    let scalars = scalars(n);
    let left: Vec<_> = scalars
        .iter()
        .map(|&s| ark::G1::generator().scale(s))
        .collect();
    let right: Vec<_> = scalars
        .iter()
        .rev()
        .map(|&s| ark::G2::generator().scale(s))
        .collect();
    let p: Vec<_> = left
        .iter()
        .copied()
        .map(|p| blst::arkworks::import_g1(p).map_err(fail))
        .collect::<Result<_>>()?;
    let q: Vec<_> = right
        .iter()
        .copied()
        .map(|q| blst::arkworks::import_g2(q).map_err(fail))
        .collect::<Result<_>>()?;
    let expected = ark::pairing_check(&left, &right).map_err(fail)?;
    if boundary == Boundary::Installed {
        return installed(
            request,
            provider,
            Kernel::PairingCheck,
            "bls12-381.fr",
            vec![
                Value::Groups(left.into()),
                Value::Bls12381G2Vector(right.into()),
            ],
            Value::Bool(expected),
        );
    }
    let samples = measure::measure(
        request.plan,
        || Ok(()),
        |_| {
            if provider == Provider::Arkworks {
                ark::pairing_check(&left, &right).map_err(fail)
            } else if boundary == Boundary::Resident {
                blst::pairing_check(&p, &q).map_err(fail)
            } else {
                let p = left
                    .iter()
                    .copied()
                    .map(|p| blst::arkworks::import_g1(p).map_err(fail))
                    .collect::<Result<Vec<_>>>()?;
                let q = right
                    .iter()
                    .copied()
                    .map(|q| blst::arkworks::import_g2(q).map_err(fail))
                    .collect::<Result<Vec<_>>>()?;
                blst::pairing_check(&p, &q).map_err(fail)
            }
        },
        |out| {
            if out == expected {
                Ok(())
            } else {
                Err(Failure::IncorrectResult)
            }
        },
    )?;
    Ok(Report::new(boundary.name(), samples, 0))
}

pub fn run(
    request: &Request,
    provider: Provider,
    group: Group,
    kernel: Kernel,
    boundary: Boundary,
    elements: usize,
) -> Result<Report> {
    if request.operation != Operation::Run
        || !(1..=4096).contains(&elements)
        || kernel == Kernel::Scale && elements != 1
        || (group == Group::Pairing) != (kernel == Kernel::PairingCheck)
        || group == Group::Pairing && matches!(boundary, Boundary::Import | Boundary::Export)
        || provider == Provider::Arkworks && matches!(boundary, Boundary::Import | Boundary::Export)
        || zkc_runtime::vm::ExecutionCounts::ENABLED
    {
        return Err("unsupported provider benchmark request".into());
    }
    match group {
        Group::G1 => curve_run::<ark::G1>(request, provider, boundary, kernel, elements),
        Group::G2 => curve_run::<ark::G2>(request, provider, boundary, kernel, elements),
        Group::Pairing => pairing_run(request, provider, boundary, elements),
    }
}
