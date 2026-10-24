//! Provider controls reuse the process scheduler and per-call measurement protocol.
//! All arithmetic results are checked outside the timer against Arkworks. Import,
//! export, resident arithmetic and the complete installed operation are distinct.
use crate::{Failure, Operation, Report, Request, Result, measure};
use ark_ff::PrimeField;
use serde::Deserialize;
use serde_json::json;
use sha2::{Digest, Sha256};
use zkc_kernels::{arkworks::bls12_381 as ark, blst::bls12_381 as blst};
use zkc_native::Value;

mod bn254;
mod installed;

pub fn single_call() -> usize {
    1
}

#[derive(Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Provider {
    Arkworks,
    Blst,
    #[serde(rename = "halo2curves-axiom")]
    Halo2curvesAxiom,
}
impl Provider {
    fn name(self) -> &'static str {
        match self {
            Self::Arkworks => "arkworks",
            Self::Blst => "blst",
            Self::Halo2curvesAxiom => "halo2curves-axiom",
        }
    }
}

#[derive(Clone, Copy, Default, Deserialize, PartialEq, Eq)]
pub enum Family {
    #[default]
    #[serde(rename = "bls12-381")]
    Bls12381,
    #[serde(rename = "bn254")]
    Bn254,
}
impl Family {
    fn supports(self, provider: Provider) -> bool {
        matches!(
            (self, provider),
            (_, Provider::Arkworks)
                | (Self::Bls12381, Provider::Blst)
                | (Self::Bn254, Provider::Halo2curvesAxiom)
        )
    }
}
#[derive(Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Boundary {
    Resident,
    Converted,
    Import,
    Export,
    Installed,
    ResidentInstalledChain,
    WireResidentChain,
}
impl Boundary {
    fn name(self) -> &'static str {
        match self {
            Self::Resident => "resident_kernel_call",
            Self::Converted => "converted_kernel_call",
            Self::Import => "provider_import",
            Self::Export => "provider_export",
            Self::Installed => "installed_operation_call",
            Self::ResidentInstalledChain => "resident_installed_chain",
            Self::WireResidentChain => "wire_decode_resident_execute_wire_encode",
        }
    }
}
#[derive(Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Group {
    G1,
    G2,
    Pairing,
    Scalar,
}
#[derive(Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Kernel {
    Scale,
    ScaleEach,
    VectorScale,
    Msm,
    PairingCheck,
    FieldMul,
    VectorMul,
}
impl Kernel {
    fn max_elements(self) -> usize {
        if self == Self::VectorMul {
            65_536
        } else {
            4096
        }
    }

    fn contract(self) -> &'static str {
        match self {
            Self::Scale => "curve.scale",
            Self::ScaleEach => "curve.scale_each",
            Self::VectorScale => "curve.vector_scale",
            Self::Msm => "curve.msm",
            Self::PairingCheck => "pairing.check",
            Self::FieldMul => "field.mul",
            Self::VectorMul => "vector.mul",
        }
    }
}
fn fail(e: impl std::fmt::Display) -> Failure {
    Failure::Failed(e.to_string())
}

trait Curve: Copy + PartialEq {
    type Foreign: Copy;
    type ForeignBulk;
    const DOMAIN: &'static str;
    fn generator() -> Self;
    fn identity() -> Self;
    fn scale(self, scalar: ark::Scalar) -> Self;
    fn export(point: Self::Foreign) -> Result<Self>;
    fn foreign_scale(point: Self::Foreign, scalar: blst::Scalar) -> Self::Foreign;
    fn foreign_add(left: Self::Foreign, right: Self::Foreign) -> Self::Foreign;
    fn bulk_import(points: &[Self]) -> Result<Self::ForeignBulk>;
    fn bulk_export(points: &Self::ForeignBulk) -> Result<Vec<Self>>;
    fn bulk_arithmetic(
        op: Kernel,
        scalars: &blst::ScalarVector,
        points: &Self::ForeignBulk,
    ) -> Result<ForeignOutput<Self>>;
    fn msm(s: &[ark::Scalar], p: &[Self]) -> Result<Self>;
    fn scale_into(p: &[Self], s: &[ark::Scalar], shared: bool) -> Result<Vec<Self>>;
    fn add(self, rhs: Self) -> Self;
    fn value(self) -> Value;
    fn values(p: Vec<Self>) -> Value;
}
macro_rules! curve {
    ($point:ident, $bulk:ident, $import:ident, $export:ident, $domain:literal, $single:ident, $vector:ident) => {
        impl Curve for ark::$point {
            type Foreign = blst::$point;
            type ForeignBulk = blst::$bulk;
            const DOMAIN: &'static str = $domain;
            fn generator() -> Self {
                Self::generator()
            }
            fn identity() -> Self {
                Self::identity()
            }
            fn scale(self, scalar: ark::Scalar) -> Self {
                Self::scale(&self, scalar)
            }
            fn export(p: Self::Foreign) -> Result<Self> {
                blst::arkworks::$export(p).map_err(fail)
            }
            fn foreign_scale(point: Self::Foreign, scalar: blst::Scalar) -> Self::Foreign {
                point.scale(scalar)
            }
            fn foreign_add(left: Self::Foreign, right: Self::Foreign) -> Self::Foreign {
                left.add(&right)
            }
            fn bulk_import(points: &[Self]) -> Result<Self::ForeignBulk> {
                blst::$bulk::try_from_fn(points.len(), |i| blst::arkworks::$import(points[i]))
                    .map_err(fail)
            }
            fn bulk_export(points: &Self::ForeignBulk) -> Result<Vec<Self>> {
                points.iter().map(Self::export).collect()
            }
            fn bulk_arithmetic(
                op: Kernel,
                scalars: &blst::ScalarVector,
                points: &Self::ForeignBulk,
            ) -> Result<ForeignOutput<Self>> {
                match op {
                    Kernel::Msm => Ok(ForeignOutput::Point(points.msm(scalars).map_err(fail)?)),
                    Kernel::Scale => Ok(ForeignOutput::Point(
                        points.get(0).unwrap().scale(scalars.get(0).unwrap()),
                    )),
                    Kernel::ScaleEach | Kernel::VectorScale => {
                        let mut out = blst::$bulk::filled(points.len(), blst::$point::identity())
                            .map_err(fail)?;
                        if op == Kernel::VectorScale {
                            points.scale_into(scalars.get(0).unwrap(), &mut out)
                        } else {
                            points.scale_each_into(scalars, &mut out)
                        }
                        .map_err(fail)?;
                        Ok(ForeignOutput::Points(out))
                    }
                    _ => Err("unsupported resident curve kernel".into()),
                }
            }
            fn msm(s: &[ark::Scalar], p: &[Self]) -> Result<Self> {
                Self::msm(s, p).map_err(fail)
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
            fn add(self, rhs: Self) -> Self {
                Self::add(&self, &rhs)
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
    "bls12-381.g1",
    Curve,
    Groups
);
curve!(
    G2,
    G2Vector,
    import_g2,
    export_g2,
    "bls12-381.g2",
    Bls12381G2,
    Bls12381G2Vector
);

fn scalars(n: usize) -> Vec<ark::Scalar> {
    scalars_for(b"scalars", n)
}
fn scalars_for(domain: &[u8], n: usize) -> Vec<ark::Scalar> {
    (0..n)
        .map(|i| {
            let mut hash = Sha256::new();
            hash.update(b"zkc.benchmark/bls12-381/0");
            hash.update(domain);
            hash.update((i as u64).to_le_bytes());
            let scalar = ark::Scalar::from_le_bytes_mod_order(&hash.finalize());
            if scalar == ark::Scalar::from(0) {
                ark::Scalar::from(1)
            } else {
                scalar
            }
        })
        .collect()
}
// Keep point results inline through timing and conversion. Only the untimed
// observer normalizes them to singleton vectors. Both curve families use this.
enum CanonicalOutput<G> {
    Point(G),
    Points(Vec<G>),
}
impl<G> CanonicalOutput<G> {
    fn into_points(self) -> Vec<G> {
        match self {
            Self::Point(point) => vec![point],
            Self::Points(points) => points,
        }
    }
}
fn arithmetic<G: Curve>(op: Kernel, s: &[ark::Scalar], p: &[G]) -> Result<CanonicalOutput<G>> {
    match op {
        Kernel::Msm => Ok(CanonicalOutput::Point(G::msm(s, p)?)),
        Kernel::Scale => Ok(CanonicalOutput::Point(p[0].scale(s[0]))),
        _ => G::scale_into(p, s, op == Kernel::VectorScale).map(CanonicalOutput::Points),
    }
}
fn arithmetic_chain<G: Curve>(
    op: Kernel,
    scalars: &[ark::Scalar],
    points: &[G],
    length: usize,
) -> Result<CanonicalOutput<G>> {
    let mut result = arithmetic::<G>(op, scalars, points)?;
    for _ in 1..length {
        result = match result {
            CanonicalOutput::Point(previous) if op == Kernel::Msm => {
                CanonicalOutput::Point(previous.add(G::msm(scalars, points)?))
            }
            CanonicalOutput::Point(previous) => CanonicalOutput::Point(previous.scale(scalars[0])),
            CanonicalOutput::Points(previous) => arithmetic::<G>(op, scalars, &previous)?,
        };
    }
    Ok(result)
}

// Check bulk scaling and MSM through scalar multiplication and addition rather
// than reusing the timed plan. Both providers share the scalar arithmetic oracle.
fn expected_curve<G: Curve>(
    op: Kernel,
    scalars: &[ark::Scalar],
    points: &[G],
    length: usize,
) -> Result<Vec<G>> {
    match op {
        Kernel::Msm => {
            let term = points
                .iter()
                .zip(scalars)
                .fold(G::identity(), |sum, (&point, &scalar)| {
                    sum.add(point.scale(scalar))
                });
            Ok(vec![
                (0..length).fold(G::identity(), |sum, _| sum.add(term)),
            ])
        }
        Kernel::Scale | Kernel::ScaleEach | Kernel::VectorScale => {
            let mut result = points.to_vec();
            for _ in 0..length {
                for (i, point) in result.iter_mut().enumerate() {
                    *point = point.scale(scalars[if op == Kernel::ScaleEach { i } else { 0 }]);
                }
            }
            Ok(result)
        }
        _ => Err("unsupported BLS12-381 curve oracle".into()),
    }
}

fn foreign_chain<G: Curve>(
    op: Kernel,
    scalars: &blst::ScalarVector,
    points: &G::ForeignBulk,
    length: usize,
) -> Result<ForeignOutput<G>> {
    let mut result = G::bulk_arithmetic(op, scalars, points)?;
    for _ in 1..length {
        result = match result {
            ForeignOutput::Point(previous) if op == Kernel::Msm => {
                let ForeignOutput::Point(next) = G::bulk_arithmetic(op, scalars, points)? else {
                    unreachable!()
                };
                ForeignOutput::Point(G::foreign_add(previous, next))
            }
            ForeignOutput::Point(previous) => {
                ForeignOutput::Point(G::foreign_scale(previous, scalars.get(0).unwrap()))
            }
            ForeignOutput::Points(previous) => G::bulk_arithmetic(op, scalars, &previous)?,
        };
    }
    Ok(result)
}
fn import_scalars(s: &[ark::Scalar]) -> Result<blst::ScalarVector> {
    blst::ScalarVector::try_from_fn(s.len(), |i| blst::arkworks::import_scalar(s[i])).map_err(fail)
}
enum ForeignOutput<G: Curve> {
    Point(G::Foreign),
    Points(G::ForeignBulk),
}
impl<G: Curve> ForeignOutput<G> {
    fn export(self) -> Result<CanonicalOutput<G>> {
        match self {
            Self::Point(p) => G::export(p).map(CanonicalOutput::Point),
            Self::Points(p) => G::bulk_export(&p).map(CanonicalOutput::Points),
        }
    }
}
enum Output<G: Curve> {
    Native(CanonicalOutput<G>),
    Foreign(ForeignOutput<G>, Option<blst::ScalarVector>),
}

fn curve_run<G: Curve>(
    request: &Request,
    provider: Provider,
    boundary: Boundary,
    op: Kernel,
    n: usize,
    chain_length: usize,
) -> Result<Report> {
    let mut s = scalars(n);
    let p: Vec<_> = scalars_for(b"bases", n)
        .iter()
        .map(|&s| G::generator().scale(s))
        .collect();
    if op == Kernel::VectorScale {
        s.truncate(1);
    }
    let conversion = matches!(boundary, Boundary::Import | Boundary::Export);
    let expected = if conversion {
        p.clone()
    } else {
        expected_curve::<G>(op, &s, &p, chain_length)?
    };
    if matches!(
        boundary,
        Boundary::Installed | Boundary::ResidentInstalledChain | Boundary::WireResidentChain
    ) {
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
        return installed::run(
            request,
            provider,
            boundary,
            op,
            G::DOMAIN,
            inputs,
            expected,
            n,
            chain_length,
        );
    }
    let fp = (provider == Provider::Blst
        && matches!(boundary, Boundary::Resident | Boundary::Export))
    .then(|| G::bulk_import(&p))
    .transpose()?;
    let fs = (provider == Provider::Blst && boundary == Boundary::Resident)
        .then(|| import_scalars(&s))
        .transpose()?;
    let samples = measure::measure(
        request.plan,
        || Ok(()),
        |_| {
            Ok(if provider == Provider::Arkworks {
                Output::Native(arithmetic_chain::<G>(op, &s, &p, chain_length)?)
            } else {
                match boundary {
                    Boundary::Resident => Output::Foreign(
                        foreign_chain::<G>(
                            op,
                            fs.as_ref().unwrap(),
                            fp.as_ref().unwrap(),
                            chain_length,
                        )?,
                        None,
                    ),
                    Boundary::Import => Output::Foreign(
                        ForeignOutput::Points(G::bulk_import(&p)?),
                        Some(import_scalars(&s)?),
                    ),
                    Boundary::Export => Output::Native(CanonicalOutput::Points(G::bulk_export(
                        fp.as_ref().unwrap(),
                    )?)),
                    Boundary::Converted => {
                        let points = G::bulk_import(&p)?;
                        let scalars = import_scalars(&s)?;
                        Output::Native(
                            foreign_chain::<G>(op, &scalars, &points, chain_length)?.export()?,
                        )
                    }
                    Boundary::Installed
                    | Boundary::ResidentInstalledChain
                    | Boundary::WireResidentChain => unreachable!(),
                }
            })
        },
        |out| {
            let out = match out {
                Output::Native(out) => out.into_points(),
                Output::Foreign(out, scalars) => {
                    if let Some(scalars) = scalars {
                        let actual = scalars
                            .iter()
                            .map(|value| blst::arkworks::export_scalar(value).map_err(fail))
                            .collect::<Result<Vec<_>>>()?;
                        if actual != s {
                            return Err(Failure::IncorrectResult);
                        }
                    }
                    out.export()?.into_points()
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

fn pairing_run(
    request: &Request,
    provider: Provider,
    boundary: Boundary,
    n: usize,
    chain_length: usize,
) -> Result<Report> {
    let scalars = scalars(n);
    let mut left: Vec<_> = scalars
        .iter()
        .map(|&s| ark::G1::generator().scale(s))
        .collect();
    let mut right: Vec<_> = scalars
        .iter()
        .rev()
        .map(|&s| ark::G2::generator().scale(s))
        .collect();
    // Preserve the existing nontrivial false single-call control. Repeated
    // controls also exercise a true product through nonidentity cancellation.
    if chain_length > 1 {
        for i in (0..n.saturating_sub(1)).step_by(2) {
            left[i + 1] = left[i].neg();
            right[i + 1] = right[i];
        }
    }
    let expected = ark::pairing_check(&left, &right).map_err(fail)?;
    if matches!(
        boundary,
        Boundary::Installed | Boundary::ResidentInstalledChain | Boundary::WireResidentChain
    ) {
        return installed::run(
            request,
            provider,
            boundary,
            Kernel::PairingCheck,
            "bls12-381.fr",
            vec![
                Value::Groups(left.into()),
                Value::Bls12381G2Vector(right.into()),
            ],
            Value::Bool(expected),
            n,
            chain_length,
        );
    }
    let resident = (provider == Provider::Blst && boundary == Boundary::Resident)
        .then(|| {
            Ok::<_, Failure>((
                blst::G1Vector::try_from_fn(n, |i| blst::arkworks::import_g1(left[i]))
                    .map_err(fail)?,
                blst::G2Vector::try_from_fn(n, |i| blst::arkworks::import_g2(right[i]))
                    .map_err(fail)?,
            ))
        })
        .transpose()?;
    let samples = measure::measure(
        request.plan,
        || Ok(()),
        |_| {
            if provider == Provider::Arkworks {
                (0..chain_length)
                    .map(|_| ark::pairing_check(&left, &right).map_err(fail))
                    .collect::<Result<Vec<_>>>()
            } else if boundary == Boundary::Resident {
                let (p, q) = resident.as_ref().unwrap();
                (0..chain_length)
                    .map(|_| blst::pairing_check_bulk(p, q).map_err(fail))
                    .collect()
            } else {
                let p = blst::G1Vector::try_from_fn(n, |i| blst::arkworks::import_g1(left[i]))
                    .map_err(fail)?;
                let q = blst::G2Vector::try_from_fn(n, |i| blst::arkworks::import_g2(right[i]))
                    .map_err(fail)?;
                (0..chain_length)
                    .map(|_| blst::pairing_check_bulk(&p, &q).map_err(fail))
                    .collect()
            }
        },
        |out| {
            if out == vec![expected; chain_length] {
                Ok(())
            } else {
                Err(Failure::IncorrectResult)
            }
        },
    )?;
    Ok(Report::new(boundary.name(), samples, 0))
}

#[allow(clippy::too_many_arguments)]
pub fn run_family(
    request: &Request,
    family: Family,
    provider: Provider,
    group: Group,
    kernel: Kernel,
    boundary: Boundary,
    elements: usize,
    chain_length: usize,
) -> Result<Report> {
    if !family.supports(provider) {
        return Err("unsupported provider and curve family".into());
    }
    match family {
        Family::Bls12381 => run(
            request,
            provider,
            group,
            kernel,
            boundary,
            elements,
            chain_length,
        ),
        Family::Bn254 => bn254::run(
            request,
            provider,
            group,
            kernel,
            boundary,
            elements,
            chain_length,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
pub fn run(
    request: &Request,
    provider: Provider,
    group: Group,
    kernel: Kernel,
    boundary: Boundary,
    elements: usize,
    chain_length: usize,
) -> Result<Report> {
    if !Family::Bls12381.supports(provider)
        || request.operation != Operation::Run
        || !(1..=kernel.max_elements()).contains(&elements)
        || matches!(kernel, Kernel::Scale | Kernel::FieldMul) && elements != 1
        || !(1..=32).contains(&chain_length)
        || chain_length != 1
            && !matches!(
                boundary,
                Boundary::Resident
                    | Boundary::Converted
                    | Boundary::ResidentInstalledChain
                    | Boundary::WireResidentChain
            )
        || (group == Group::Scalar) != matches!(kernel, Kernel::FieldMul | Kernel::VectorMul)
        || group == Group::Scalar && matches!(boundary, Boundary::Import | Boundary::Export)
        || (group == Group::Pairing) != (kernel == Kernel::PairingCheck)
        || group == Group::Pairing && matches!(boundary, Boundary::Import | Boundary::Export)
        || provider == Provider::Arkworks && matches!(boundary, Boundary::Import | Boundary::Export)
        || zkc_runtime::vm::ExecutionCounts::ENABLED
    {
        return Err("unsupported provider benchmark request".into());
    }
    let mut report = match group {
        Group::G1 => {
            curve_run::<ark::G1>(request, provider, boundary, kernel, elements, chain_length)
        }
        Group::G2 => {
            curve_run::<ark::G2>(request, provider, boundary, kernel, elements, chain_length)
        }
        Group::Pairing => pairing_run(request, provider, boundary, elements, chain_length),
        Group::Scalar => scalar_run(request, provider, boundary, kernel, elements, chain_length),
    }?;
    if report.diagnostics.is_null() {
        report.diagnostics = kernel_diagnostics(
            Family::Bls12381,
            provider,
            group,
            kernel,
            boundary,
            elements,
            chain_length,
        )?;
    }
    Ok(report)
}

fn kernel_diagnostics(
    family: Family,
    provider: Provider,
    group: Group,
    kernel: Kernel,
    boundary: Boundary,
    n: usize,
    chain_length: usize,
) -> Result<serde_json::Value> {
    use zkc_runtime::vm::{ExecutionPolicy, PhysicalType, Type};
    let contracts = zkc_native::native_contracts_with_policy(ExecutionPolicy {
        allow_unspecified_timing: true,
        allow_variable_time: kernel == Kernel::Msm,
    });
    let (domain, foreign_provider) = match family {
        Family::Bls12381 => (
            match group {
                Group::G1 => "bls12-381.g1",
                Group::G2 => "bls12-381.g2",
                _ => "bls12-381.fr",
            },
            Provider::Blst,
        ),
        Family::Bn254 => (
            match group {
                Group::G1 => "bn254.g1",
                Group::G2 => "bn254.g2",
                _ => "bn254.fr",
            },
            Provider::Halo2curvesAxiom,
        ),
    };
    let ark = contracts
        .resolve(installed::binding(
            Provider::Arkworks,
            kernel.contract(),
            domain,
        ))
        .map_err(fail)?;
    let foreign = contracts
        .resolve(installed::binding(
            foreign_provider,
            kernel.contract(),
            domain,
        ))
        .map_err(fail)?;
    let elements = |ty: &PhysicalType| {
        if matches!(ty.kind(), Type::Vector | Type::Groups) {
            n
        } else {
            1
        }
    };
    let mut conversions = vec![];
    let mut record = |source: &PhysicalType, target: &PhysicalType| {
        if source == target {
            return;
        }
        let width = match source.logical().identity() {
            zkc_runtime::vm::Identity::Bls12381G1 => 48,
            zkc_runtime::vm::Identity::Bls12381G2 => 96,
            zkc_runtime::vm::Identity::Bn254G2 => 64,
            _ => 32,
        };
        let mut row = json!({"source":source.spelling(), "target":target.spelling(),
            "calls":elements(source), "elements":elements(source),
            "canonical_payload_bytes":elements(source) * width});
        if family == Family::Bn254 {
            row["logical_type"] = json!(source.logical().spelling());
        }
        conversions.push(row);
    };
    if provider == foreign_provider {
        if matches!(boundary, Boundary::Converted | Boundary::Import) {
            for (source, target) in ark
                .signature()
                .inputs
                .iter()
                .zip(&foreign.signature().inputs)
            {
                record(source, target);
            }
        }
        if boundary == Boundary::Converted {
            for (source, target) in foreign
                .signature()
                .outputs
                .iter()
                .zip(&ark.signature().outputs)
            {
                record(source, target);
            }
        }
        if boundary == Boundary::Export {
            for (source, target) in foreign
                .signature()
                .inputs
                .iter()
                .zip(&ark.signature().inputs)
            {
                if matches!(source.kind(), Type::Group | Type::Groups) {
                    record(source, target);
                }
            }
        }
    }
    let foreign_arithmetic =
        provider == foreign_provider && !matches!(boundary, Boundary::Import | Boundary::Export);
    let bulk_storage = match provider {
        Provider::Arkworks => {
            "Arkworks owned scalar/affine buffers; resident calls borrow Arkworks mathematical storage"
        }
        Provider::Blst => {
            "blst resident upstream ScalarVector/G1Vector/G2Vector; no wrapper-vector reconstruction in timed resident calls"
        }
        Provider::Halo2curvesAxiom => {
            "halo2curves-axiom owned Fr/G1Affine/G2Affine buffers; resident calls borrow upstream ABI storage"
        }
    };
    let mut diagnostics = json!({"chain_length":chain_length,
        "family":match family { Family::Bls12381 => "bls12-381", Family::Bn254 => "bn254" },
        "provider":provider.name(),
        "arithmetic_calls":if matches!(boundary, Boundary::Import | Boundary::Export) { 0 }
            else { chain_length + if kernel == Kernel::Msm { chain_length - 1 } else { 0 } },
        "kernel_adapter_conversions":conversions,
        "conversion_observation":"equivalent logical ports; direct canonical adapter calls counted per element; bulk inputs may contain one element; bytes exclude framing",
        "bulk_storage":bulk_storage,
        "construction_copies":if provider == Provider::Arkworks {
            "not allocator-instrumented; Arkworks MSM stages affine bases"
        } else { "not allocator-instrumented; imports allocate final upstream buffers" },
        "managed":{"peak_retained_payload_bytes":null,"peak_scratch_bytes":null,
            "provider_workspace_admission_bound_bytes_per_call":if foreign_arithmetic && provider == Provider::Blst && kernel == Kernel::Msm {
                Some(blst::msm_workspace_bytes(n).map_err(fail)?)
            } else if foreign_arithmetic && provider == Provider::Blst && kernel == Kernel::PairingCheck { Some(blst::PAIRING_WORKSPACE_BYTES) } else { None }},
        "provider_hidden_allocations":"not allocator-instrumented; process peak RSS includes setup and mathematical oracle"});
    if family == Family::Bn254 {
        diagnostics["managed"]["provider_workspace_admission_bound_bytes_per_call"] =
            json!(if foreign_arithmetic {
                bn254::workspace(kernel, n)?
            } else {
                None
            });
        diagnostics["provider_scheduling_work_units_per_arithmetic_call"] =
            json!(if foreign_arithmetic {
                bn254::scheduling_work(kernel, n)?
            } else {
                None
            });
        diagnostics["work_observation"] = json!(
            "provider public-shape scheduling score only; direct calls do not charge Native/VM budgets; MSM chain additions excluded from this per-call score"
        );
    }
    Ok(diagnostics)
}

fn scalar_run(
    request: &Request,
    provider: Provider,
    boundary: Boundary,
    op: Kernel,
    n: usize,
    chain_length: usize,
) -> Result<Report> {
    let left = scalars(n);
    let right = scalars_for(b"factors", n);
    let mut expected = left.clone();
    for _ in 0..chain_length {
        for (out, factor) in expected.iter_mut().zip(&right) {
            *out *= factor;
        }
    }
    let value = |v: Vec<ark::Scalar>| {
        if op == Kernel::FieldMul {
            Value::Field(v[0])
        } else {
            Value::Vector(v.into())
        }
    };
    if matches!(
        boundary,
        Boundary::Installed | Boundary::ResidentInstalledChain | Boundary::WireResidentChain
    ) {
        return installed::run(
            request,
            provider,
            boundary,
            op,
            "bls12-381.fr",
            vec![value(left), value(right)],
            value(expected),
            n,
            chain_length,
        );
    }
    let resident = (provider == Provider::Blst && boundary == Boundary::Resident)
        .then(|| Ok::<_, Failure>((import_scalars(&left)?, import_scalars(&right)?)))
        .transpose()?;
    enum ScalarOutput {
        NativeField(ark::Scalar),
        ForeignField(blst::Scalar),
        NativeVector(Vec<ark::Scalar>),
        ForeignVector(blst::ScalarVector),
    }
    let compute = |a: &blst::ScalarVector, b: &blst::ScalarVector| -> Result<ScalarOutput> {
        if op == Kernel::FieldMul {
            let mut result = a.get(0).unwrap();
            for _ in 0..chain_length {
                result *= b.get(0).unwrap();
            }
            Ok(ScalarOutput::ForeignField(result))
        } else {
            let mut out = blst::ScalarVector::filled(n, blst::Scalar::ZERO).map_err(fail)?;
            a.mul_into(b, &mut out).map_err(fail)?;
            for _ in 1..chain_length {
                let mut next = blst::ScalarVector::filled(n, blst::Scalar::ZERO).map_err(fail)?;
                out.mul_into(b, &mut next).map_err(fail)?;
                out = next;
            }
            Ok(ScalarOutput::ForeignVector(out))
        }
    };
    let export = |out: ScalarOutput| -> Result<Vec<ark::Scalar>> {
        match out {
            ScalarOutput::NativeField(value) => Ok(vec![value]),
            ScalarOutput::NativeVector(value) => Ok(value),
            ScalarOutput::ForeignField(value) => {
                Ok(vec![blst::arkworks::export_scalar(value).map_err(fail)?])
            }
            ScalarOutput::ForeignVector(values) => values
                .iter()
                .map(|v| blst::arkworks::export_scalar(v).map_err(fail))
                .collect(),
        }
    };
    let samples = measure::measure(
        request.plan,
        || Ok(()),
        |_| {
            if provider == Provider::Arkworks {
                if op == Kernel::FieldMul {
                    let mut result = left[0];
                    for _ in 0..chain_length {
                        result *= right[0];
                    }
                    Ok(ScalarOutput::NativeField(result))
                } else {
                    let mut result = vec![ark::Scalar::from(0); n];
                    zkc_kernels::vector::mul(&left, &right, &mut result).map_err(fail)?;
                    for _ in 1..chain_length {
                        let mut next = vec![ark::Scalar::from(0); n];
                        zkc_kernels::vector::mul(&result, &right, &mut next).map_err(fail)?;
                        result = next;
                    }
                    Ok(ScalarOutput::NativeVector(result))
                }
            } else if boundary == Boundary::Converted {
                let a = import_scalars(&left)?;
                let b = import_scalars(&right)?;
                Ok(ScalarOutput::NativeVector(export(compute(&a, &b)?)?))
            } else {
                let (a, b) = resident.as_ref().unwrap();
                compute(a, b)
            }
        },
        |out| {
            if export(out)? == expected {
                Ok(())
            } else {
                Err(Failure::IncorrectResult)
            }
        },
    )?;
    Ok(Report::new(boundary.name(), samples, 0))
}

#[cfg(all(test, not(feature = "execution-counts")))]
mod tests {
    use super::*;
    use serde_json::json;

    fn request(
        group: &str,
        kernel: &str,
        boundary: &str,
        n: usize,
        chain_length: usize,
    ) -> Request {
        let mut request: Request =
            serde_json::from_value(json!({"format":"zkc.benchmark-job/0", "backend":{
            "kind":"kernel", "provider":"blst", "group":group, "kernel":kernel,
            "boundary":boundary, "elements":n, "chain_length":chain_length},
            "operation":"run", "plan":{"warmups":1,"samples":1,"iterations":1}, "proof":"unused"}))
            .unwrap();
        request.cpu = Some(zkc::execution::CpuExecution::serial().unwrap());
        request
    }

    #[test]
    fn single_step_fixtures_detect_reversed_outputs() {
        let s = scalars(4);
        let factors = scalars_for(b"factors", 4);
        let product: Vec<_> = s.iter().zip(&factors).map(|(a, b)| *a * b).collect();
        assert_ne!(product, product.iter().rev().copied().collect::<Vec<_>>());
        fn group<G: Curve>() {
            let s = scalars(4);
            let p: Vec<_> = scalars_for(b"bases", 4)
                .iter()
                .map(|&s| G::generator().scale(s))
                .collect();
            let expected = expected_curve(Kernel::ScaleEach, &s, &p, 1).unwrap();
            assert!(expected != expected.iter().rev().copied().collect::<Vec<_>>());
            for (op, points) in [
                (Kernel::Scale, &p[..1]),
                (Kernel::Msm, &p[..]),
                (Kernel::ScaleEach, &p[..]),
                (Kernel::VectorScale, &p[..]),
            ] {
                let out = arithmetic_chain(op, &s, points, 3).unwrap();
                assert_eq!(
                    matches!(&out, CanonicalOutput::Point(_)),
                    matches!(op, Kernel::Scale | Kernel::Msm)
                );
                assert!(out.into_points() == expected_curve(op, &s, points, 3).unwrap());
            }
        }
        group::<ark::G1>();
        group::<ark::G2>();
    }

    #[test]
    fn installed_resident_and_full_wire_results_match_independent_arkworks_oracles() {
        let cases = [
            (Group::Scalar, Kernel::FieldMul, "scalar", "field_mul", 1),
            (Group::Scalar, Kernel::VectorMul, "scalar", "vector_mul", 2),
            (Group::G1, Kernel::Scale, "g1", "scale", 1),
            (Group::G1, Kernel::ScaleEach, "g1", "scale_each", 2),
            (Group::G1, Kernel::VectorScale, "g1", "vector_scale", 2),
            (Group::G1, Kernel::Msm, "g1", "msm", 2),
            (Group::G2, Kernel::Scale, "g2", "scale", 1),
            (Group::G2, Kernel::ScaleEach, "g2", "scale_each", 2),
            (Group::G2, Kernel::VectorScale, "g2", "vector_scale", 2),
            (Group::G2, Kernel::Msm, "g2", "msm", 2),
            (
                Group::Pairing,
                Kernel::PairingCheck,
                "pairing",
                "pairing_check",
                2,
            ),
        ];
        for (group, kernel, group_name, kernel_name, n) in cases {
            for (boundary, boundary_name, chain_length) in [
                (Boundary::Installed, "installed", 1),
                (
                    Boundary::ResidentInstalledChain,
                    "resident_installed_chain",
                    3,
                ),
                (Boundary::WireResidentChain, "wire_resident_chain", 3),
            ] {
                let request = request(group_name, kernel_name, boundary_name, n, chain_length);
                for provider in [Provider::Arkworks, Provider::Blst] {
                    let report = run(&request, provider, group, kernel, boundary, n, chain_length)
                        .unwrap_or_else(|e| {
                            panic!("{group_name}/{kernel_name}/{boundary_name}: {e:?}")
                        });
                    assert_eq!(report.samples.len(), 2);
                    let conversions = report.diagnostics["explicit_conversions"]
                        .as_array()
                        .unwrap();
                    if provider == Provider::Blst && boundary == Boundary::Installed {
                        assert!(!conversions.is_empty());
                    } else {
                        assert!(conversions.is_empty());
                    }
                    assert_eq!(
                        report.diagnostics["managed"]["peak_scratch_bytes"],
                        json!(null)
                    );
                }
            }
        }
    }

    #[test]
    fn resident_kernel_and_direct_conversion_controls_match_arkworks() {
        for (group, kernel, name, op, n) in [
            (Group::Scalar, Kernel::FieldMul, "scalar", "field_mul", 1),
            (Group::Scalar, Kernel::VectorMul, "scalar", "vector_mul", 2),
            (Group::G1, Kernel::Msm, "g1", "msm", 2),
            (Group::G2, Kernel::Msm, "g2", "msm", 2),
            (Group::G1, Kernel::ScaleEach, "g1", "scale_each", 33),
            (Group::G2, Kernel::ScaleEach, "g2", "scale_each", 33),
            (Group::G1, Kernel::VectorScale, "g1", "vector_scale", 33),
            (Group::G2, Kernel::VectorScale, "g2", "vector_scale", 33),
            (
                Group::Pairing,
                Kernel::PairingCheck,
                "pairing",
                "pairing_check",
                2,
            ),
        ] {
            for (boundary, spelling) in [
                (Boundary::Resident, "resident"),
                (Boundary::Converted, "converted"),
            ] {
                for length in [1, 3] {
                    let request = request(name, op, spelling, n, length);
                    for provider in [Provider::Arkworks, Provider::Blst] {
                        let report =
                            run(&request, provider, group, kernel, boundary, n, length).unwrap();
                        assert_eq!(report.diagnostics["provider"], provider.name());
                        assert_eq!(report.diagnostics["family"], "bls12-381");
                        let storage = report.diagnostics["bulk_storage"].as_str().unwrap();
                        assert!(storage.starts_with(if provider == Provider::Arkworks {
                            "Arkworks "
                        } else {
                            "blst "
                        }));
                    }
                }
            }
        }
    }

    #[test]
    fn vector_controls_cross_parallel_grains_at_each_execution_boundary() {
        let cpu = zkc::execution::CpuExecution::new(4).unwrap();
        for (family, provider) in [
            (Family::Bls12381, Provider::Arkworks),
            (Family::Bls12381, Provider::Blst),
            (Family::Bn254, Provider::Arkworks),
            (Family::Bn254, Provider::Halo2curvesAxiom),
        ] {
            for (boundary, spelling) in [
                (Boundary::Resident, "resident"),
                (Boundary::Converted, "converted"),
                (Boundary::Installed, "installed"),
                (Boundary::ResidentInstalledChain, "resident_installed_chain"),
                (Boundary::WireResidentChain, "wire_resident_chain"),
            ] {
                // Cover a nonempty chunk tail and the largest catalog chains.
                let shapes: &[(usize, usize)] = if boundary == Boundary::Installed {
                    &[(8193, 1)]
                } else {
                    &[(8193, 2), (32_768, 4)]
                };
                for &(n, length) in shapes {
                    let mut request = request("scalar", "vector_mul", spelling, n, length);
                    request.cpu = Some(cpu.clone());
                    request.backend = crate::Backend::Kernel {
                        family,
                        provider,
                        group: Group::Scalar,
                        kernel: Kernel::VectorMul,
                        boundary,
                        elements: n,
                        chain_length: length,
                    };
                    let result = cpu.enter(|| {
                        run_family(
                            &request,
                            family,
                            provider,
                            Group::Scalar,
                            Kernel::VectorMul,
                            boundary,
                            n,
                            length,
                        )
                    });
                    assert_eq!(result.unwrap().samples.len(), 2);
                    if boundary == Boundary::Installed && provider != Provider::Arkworks {
                        let refused = cpu.enter(|| {
                            run_family(
                                &request,
                                family,
                                provider,
                                Group::Scalar,
                                Kernel::VectorMul,
                                boundary,
                                32_768,
                                1,
                            )
                        });
                        assert!(matches!(refused, Err(Failure::Failed(message))
                            if message.contains("numerical-work")));
                    }
                    for (group, kernel, elements) in [
                        (Group::Scalar, Kernel::VectorMul, 65_537),
                        (Group::G1, Kernel::Msm, 4097),
                    ] {
                        assert!(
                            run_family(
                                &request, family, provider, group, kernel, boundary, elements, 2,
                            )
                            .is_err()
                        );
                    }
                }
            }
        }
    }
}

#[cfg(all(test, feature = "execution-counts"))]
#[test]
fn timed_provider_measurements_refuse_execution_counters() {
    let request: Request = serde_json::from_value(json!({
        "format":"zkc.benchmark-job/0", "backend":{
            "kind":"kernel", "provider":"blst", "group":"scalar", "kernel":"field_mul",
            "boundary":"resident", "elements":1, "chain_length":1},
        "operation":"run", "plan":{"warmups":0,"samples":1,"iterations":1}, "proof":"unused"
    }))
    .unwrap();
    assert!(
        run(
            &request,
            Provider::Blst,
            Group::Scalar,
            Kernel::FieldMul,
            Boundary::Resident,
            1,
            1
        )
        .is_err()
    );
}
