//! Admitted provider controls use the ordinary Native composition and Runner.
use super::{Boundary, Kernel, Provider, fail};
use crate::{Failure, Report, Request, Result, measure};
use serde_json::{Value as Json, json};
use std::time::Instant;
use zkc_cpu::{CpuBackend, Domain, EntryPolicy, Policy, Value};
use zkc_runtime::{
    interpreter::Runner,
    vm::{Action, Contracts, ExecutionPolicy, OperationBinding, PhysicalType, Usage, Value as _},
};

fn native(contracts: &Contracts, cpu: &zkc::execution::CpuExecution) -> Result<CpuBackend> {
    CpuBackend::new_with_cpu(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "benchmark", "main", None), None),
        Default::default(),
        cpu.clone(),
    )
    .map_err(fail)?
    .with_contracts(contracts.clone())
    .map_err(fail)
}

pub(super) fn binding(provider: Provider, contract: &str, domain: &str) -> OperationBinding {
    let owner = match provider {
        Provider::Blst => "blst/resident",
        Provider::Halo2curvesAxiom => "halo2curves-axiom/resident",
        Provider::Arkworks => "arkworks",
    };
    OperationBinding {
        contract: contract.into(),
        arguments: vec![domain.into()],
        implementation: format!("{owner}/{contract}"),
        physical_arguments: Vec::new(),
    }
}

struct Builder<'a> {
    contracts: &'a Contracts,
    bindings: Vec<Json>,
    body: Vec<Json>,
    conversions: Vec<Json>,
}
impl Builder<'_> {
    fn call(&mut self, binding: OperationBinding, inputs: &[String]) -> Result<String> {
        let signature = self.contracts.resolve(binding.clone()).map_err(fail)?;
        if signature.signature().inputs.len() != inputs.len()
            || signature.signature().outputs.len() != 1
        {
            return Err("benchmark operation requires exact input arity and one output".into());
        }
        let declaration = json!([
            binding.contract,
            binding.arguments,
            binding.implementation,
            binding.physical_arguments
        ]);
        let slot = if let Some(slot) = self
            .bindings
            .iter()
            .position(|b| b.as_array().unwrap()[1..] == declaration.as_array().unwrap()[..])
        {
            slot
        } else {
            let slot = self.bindings.len();
            self.bindings.push(json!([
                format!("b{slot}"),
                declaration[0],
                declaration[1],
                declaration[2],
                declaration[3]
            ]));
            slot
        };
        let result = format!("v{}", self.body.len());
        self.body.push(json!([
            "op",
            format!("site{}", self.body.len()),
            format!("b{slot}"),
            [],
            inputs,
            [&result]
        ]));
        Ok(result)
    }
    fn convert(
        &mut self,
        input: String,
        source: &PhysicalType,
        target: &PhysicalType,
        elements: usize,
    ) -> Result<String> {
        if source == target {
            return Ok(input);
        }
        if source.logical() != target.logical() {
            return Err("conversion changed the mathematical type".into());
        }
        let logical = source.logical().spelling();
        let width = match source.logical().identity() {
            zkc_runtime::vm::Identity::Bls12381G2 => 96,
            zkc_runtime::vm::Identity::Bls12381G1 => 48,
            zkc_runtime::vm::Identity::Bn254G2 => 64,
            _ => 32,
        };
        let conversion = OperationBinding {
            contract: "representation.convert".into(),
            arguments: vec![logical.clone()],
            implementation: "native/representation.convert".into(),
            physical_arguments: vec![source.spelling(), target.spelling()],
        };
        self.conversions
            .push(json!({"logical_type":logical, "source":source.spelling(),
            "target":target.spelling(), "calls":1, "elements":elements,
            "canonical_payload_bytes":elements * width}));
        self.call(conversion, &[input])
    }
}

struct Fixture {
    carrier: Json,
    inputs: Vec<PhysicalType>,
    outputs: Vec<PhysicalType>,
    conversions: Vec<Json>,
    arithmetic_calls: usize,
}
fn elements(ty: &PhysicalType, n: usize) -> usize {
    if matches!(
        ty.kind(),
        zkc_runtime::vm::Type::Vector | zkc_runtime::vm::Type::Groups
    ) {
        n
    } else {
        1
    }
}

#[allow(clippy::too_many_arguments)]
fn fixture(
    contracts: &Contracts,
    provider: Provider,
    boundary: Boundary,
    kernel: Kernel,
    domain: &str,
    n: usize,
    chain_length: usize,
) -> Result<Fixture> {
    let selected = binding(provider, kernel.contract(), domain);
    let selected_signature = contracts
        .resolve(selected.clone())
        .map_err(fail)?
        .signature()
        .clone();
    let default_signature = contracts
        .resolve(binding(Provider::Arkworks, kernel.contract(), domain))
        .map_err(fail)?
        .signature()
        .clone();
    let boundary_signature = if boundary == Boundary::Installed {
        &default_signature
    } else {
        &selected_signature
    };
    let mut builder = Builder {
        contracts,
        bindings: vec![],
        body: vec![],
        conversions: vec![],
    };
    let names: Vec<_> = (0..boundary_signature.inputs.len())
        .map(|i| format!("a{i}"))
        .collect();
    let mut operands = vec![];
    for ((name, source), target) in names
        .iter()
        .zip(&boundary_signature.inputs)
        .zip(&selected_signature.inputs)
    {
        operands.push(builder.convert(name.clone(), source, target, elements(source, n))?);
    }
    let original = operands.clone();
    let mut result = None;
    let mut results = vec![];
    let mut arithmetic_calls = 0;
    for _ in 0..chain_length {
        let next = builder.call(selected.clone(), &operands)?;
        arithmetic_calls += 1;
        result = Some(if let Some(previous) = result {
            if kernel == Kernel::Msm {
                arithmetic_calls += 1;
                builder.call(binding(provider, "curve.add", domain), &[previous, next])?
            } else {
                next
            }
        } else {
            next
        });
        let current = result.as_ref().unwrap().clone();
        match kernel {
            Kernel::Scale | Kernel::VectorScale | Kernel::FieldMul | Kernel::VectorMul => {
                operands[0] = current
            }
            Kernel::ScaleEach => operands[1] = current,
            Kernel::PairingCheck => results.push(current),
            Kernel::Msm => operands = original.clone(),
        }
    }
    if kernel != Kernel::PairingCheck {
        results.push(result.unwrap());
    }
    for result in &mut results {
        *result = builder.convert(
            result.clone(),
            &selected_signature.outputs[0],
            &boundary_signature.outputs[0],
            elements(&selected_signature.outputs[0], n),
        )?;
    }
    let ports: Vec<_> = names
        .iter()
        .zip(&boundary_signature.inputs)
        .map(|(name, ty)| json!([name, ty.spelling()]))
        .collect();
    let outputs = vec![boundary_signature.outputs[0].clone(); results.len()];
    let output_spellings: Vec<_> = outputs.iter().map(PhysicalType::spelling).collect();
    builder.body.push(json!(["return", results]));
    let carrier = json!([
        "zkc.program/0",
        builder.bindings,
        [[
            "function",
            "f",
            ports,
            output_spellings,
            builder.body,
            ["f", []]
        ]],
        [[
            "participant",
            "actor",
            "instance",
            "P",
            ports,
            output_spellings,
            [["local", "work", "f", names, results], ["return", results]],
            []
        ]],
        [["entry", "main", [["P", "actor"]]]]
    ]);
    Ok(Fixture {
        carrier,
        inputs: boundary_signature.inputs.clone(),
        outputs,
        conversions: builder.conversions,
        arithmetic_calls,
    })
}

fn execute(runner: &mut Runner<CpuBackend>) -> Result<()> {
    loop {
        match runner.poll() {
            Action::Local(action) => runner.execute_local(&action.cut).map_err(fail)?,
            Action::Returned(_) => return Ok(()),
            other => return Err(fail(format!("unexpected provider action: {other:?}"))),
        }
    }
}
fn decode(backend: &CpuBackend, types: &[PhysicalType], bytes: &[Vec<u8>]) -> Result<Vec<Value>> {
    types
        .iter()
        .zip(bytes)
        .map(|(ty, data)| backend.decode_native_value(ty, data).map_err(fail))
        .collect()
}
fn encode(runner: &Runner<CpuBackend>) -> Result<Vec<Vec<u8>>> {
    runner
        .returned_values()
        .ok_or("missing terminal values")?
        .iter()
        .map(|v| runner.backend().encode_native_value(v).map_err(fail))
        .collect()
}
fn usage(usage: Usage) -> Json {
    json!({"instructions":usage.instructions, "iterations":usage.iterations,
        "live_values":usage.live_values, "live_retained_payload_bytes":usage.live_value_bytes,
        "cumulative_fresh_payload_bytes":usage.total_value_bytes, "logical_bytes":usage.logical_bytes})
}

#[allow(clippy::too_many_arguments)]
pub(super) fn run(
    request: &Request,
    provider: Provider,
    boundary: Boundary,
    kernel: Kernel,
    domain: &str,
    inputs: Vec<Value>,
    expected: Value,
    n: usize,
    chain_length: usize,
) -> Result<Report> {
    // Deterministic public benchmark operands explicitly authorize MSM timing.
    // The artifact cannot install implementations or supply this permission.
    let policy = ExecutionPolicy {
        allow_unspecified_timing: true,
        allow_variable_time: kernel == Kernel::Msm,
    };
    let contracts = zkc_cpu::cpu_contracts_with_policy(policy);
    let backend = native(&contracts, request.cpu()?)?;
    let fixture = fixture(
        &contracts,
        provider,
        boundary,
        kernel,
        domain,
        n,
        chain_length,
    )?;
    let input_bytes = inputs
        .iter()
        .map(|v| backend.encode_native_value(v).map_err(fail))
        .collect::<Result<Vec<_>>>()?;
    drop(inputs);
    let expected_bytes = backend.encode_native_value(&expected).map_err(fail)?;
    drop(expected);
    let expected = vec![expected_bytes; fixture.outputs.len()];
    let start = Instant::now();
    let program = zkc_runtime::vm::Program::decode(
        &serde_json::to_vec(&fixture.carrier).map_err(fail)?,
        &contracts,
    )
    .map_err(fail)?;
    program.check_installation(&backend).map_err(fail)?;
    let admission_ns = start.elapsed().as_nanos();
    // Construct every selected value through the public codec. No resident Value
    // variant or provider-private payload assumption enters the benchmark ABI.
    let values = decode(&backend, &fixture.inputs, &input_bytes)?;
    let input_retained: usize = values.iter().map(|v| v.retained_bytes()).sum();
    let load = |values| {
        Runner::new(
            &program,
            "main",
            "P",
            "benchmark",
            native(&contracts, request.cpu()?)?,
            values,
        )
        .map_err(|e| fail(e.error))
    };
    let mut observed_usage = Json::Null;
    let samples = if boundary == Boundary::WireResidentChain {
        drop(values);
        measure::measure(
            request.plan,
            || native(&contracts, request.cpu()?),
            |backend| {
                let values = decode(&backend, &fixture.inputs, &input_bytes)?;
                let mut runner = Runner::new(&program, "main", "P", "benchmark", backend, values)
                    .map_err(|e| fail(e.error))?;
                execute(&mut runner)?;
                let bytes = encode(&runner)?;
                Ok((bytes, runner.usage()))
            },
            |(bytes, used)| {
                observed_usage = usage(used);
                if bytes == expected {
                    Ok(())
                } else {
                    Err(Failure::IncorrectResult)
                }
            },
        )?
    } else {
        measure::measure(
            request.plan,
            || load(values.clone()),
            |mut runner| {
                execute(&mut runner)?;
                let values = runner
                    .returned_values()
                    .ok_or("missing terminal values")?
                    .to_vec();
                let used = runner.usage();
                drop(runner);
                Ok((values, used))
            },
            |(values, used)| {
                observed_usage = usage(used);
                let bytes = values
                    .iter()
                    .map(|v| backend.encode_native_value(v).map_err(fail))
                    .collect::<Result<Vec<_>>>()?;
                if bytes == expected {
                    Ok(())
                } else {
                    Err(Failure::IncorrectResult)
                }
            },
        )?
    };
    let workspace_bound = if provider == Provider::Blst {
        match kernel {
            Kernel::Msm => {
                Some(zkc_kernels::blst::bls12_381::msm_workspace_bytes(n).map_err(fail)?)
            }
            Kernel::PairingCheck => Some(zkc_kernels::blst::bls12_381::PAIRING_WORKSPACE_BYTES),
            _ => None,
        }
    } else if provider == Provider::Halo2curvesAxiom {
        super::bn254::workspace(kernel, n)?
    } else {
        None
    };
    let mut report = Report::new(boundary.name(), samples, 0);
    report.admission_ns = Some(admission_ns);
    report.diagnostics = json!({"provider":provider.name(),
        "chain_length":chain_length, "arithmetic_calls":fixture.arithmetic_calls,
        "input_physical_types":fixture.inputs.iter().map(PhysicalType::spelling).collect::<Vec<_>>(),
        "output_physical_types":fixture.outputs.iter().map(PhysicalType::spelling).collect::<Vec<_>>(),
        "explicit_conversions":fixture.conversions,
        "conversion_observation":"exact reached straight-line program occurrences; canonical payload bytes exclude framing",
        "input_wire_bytes":input_bytes.iter().map(Vec::len).sum::<usize>(),
        "output_wire_bytes":expected.iter().map(Vec::len).sum::<usize>(),
        "trusted_timing_authorization":{"allow_unspecified_timing":policy.allow_unspecified_timing,
            "allow_variable_time":policy.allow_variable_time},
        "managed":{"input_retained_payload_bytes":input_retained, "terminal_runner_usage":observed_usage,
            "peak_retained_payload_bytes":null, "peak_scratch_bytes":null,
            "provider_workspace_admission_bound_bytes_per_call":workspace_bound,
            "peak_observation":"not exposed by current public Runner/Native APIs; cumulative fresh charges are not a peak"},
        "provider_hidden_allocations":"not allocator-instrumented; process lifetime peak RSS includes setup and oracle",
        "program":fixture.carrier});
    if domain.starts_with("bn254.") {
        // Record the actual selected codec output, including nominal frame tags.
        // A family name alone does not establish that a BN254 codec was used.
        let tags = |frames: &[Vec<u8>]| -> Result<Vec<u8>> {
            frames
                .iter()
                .map(|frame| {
                    if frame.len() < 6 || &frame[..5] != b"ZKCV\x00" {
                        return Err("provider codec did not produce a nominal ZKCV/0 frame".into());
                    }
                    Ok(frame[5])
                })
                .collect()
        };
        report.diagnostics["input_wire_tags"] = json!(tags(&input_bytes)?);
        report.diagnostics["output_wire_tags"] = json!(tags(&expected)?);
        report.diagnostics["provider_scheduling_work_units_per_arithmetic_call"] =
            json!(if provider == Provider::Halo2curvesAxiom {
                super::bn254::scheduling_work(kernel, n)?
            } else {
                None
            });
        report.diagnostics["work_observation"] = json!(
            "provider public-shape scheduling score per primary arithmetic call; excludes chain additions and conversions; terminal_runner_usage.logical_bytes is the separately observed VM charge"
        );
    }
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn explicit_bridge_and_resident_chain_have_distinct_ports_and_calls() {
        let contracts = zkc_cpu::cpu_contracts_with_policy(ExecutionPolicy::general_purpose());
        let bridge = fixture(
            &contracts,
            Provider::Blst,
            Boundary::Installed,
            Kernel::Scale,
            "bls12-381.g1",
            1,
            1,
        )
        .unwrap();
        assert_eq!(bridge.conversions.len(), 3);
        assert!(
            bridge
                .inputs
                .iter()
                .all(|ty| !ty.spelling().contains("@blst/"))
        );
        let resident = fixture(
            &contracts,
            Provider::Blst,
            Boundary::ResidentInstalledChain,
            Kernel::Scale,
            "bls12-381.g1",
            1,
            4,
        )
        .unwrap();
        assert_eq!(resident.arithmetic_calls, 4);
        assert!(resident.conversions.is_empty());
        assert!(
            resident
                .inputs
                .iter()
                .all(|ty| ty.spelling().contains("@blst/"))
        );
        for fixture in [bridge, resident] {
            let bytes = serde_json::to_vec(&fixture.carrier).unwrap();
            zkc_runtime::vm::Program::decode(&bytes, &contracts).unwrap();
        }
    }

    #[test]
    fn msm_requires_explicit_trusted_variable_time_permission() {
        let contracts = zkc_cpu::cpu_contracts_with_policy(ExecutionPolicy {
            allow_unspecified_timing: true,
            allow_variable_time: false,
        });
        for (provider, domain) in [
            (Provider::Blst, "bls12-381.g1"),
            (Provider::Halo2curvesAxiom, "bn254.g1"),
        ] {
            assert!(
                fixture(
                    &contracts,
                    provider,
                    Boundary::ResidentInstalledChain,
                    Kernel::Msm,
                    domain,
                    2,
                    4
                )
                .is_err()
            );
        }
    }

    #[test]
    fn bn254_installs_actual_resident_ports_and_decodes_nominal_frames() {
        use zkc_kernels::arkworks::bn254 as ark;
        let contracts = zkc_cpu::cpu_contracts_with_policy(ExecutionPolicy::general_purpose());
        let cpu = zkc::execution::CpuExecution::serial().unwrap();
        let backend = native(&contracts, &cpu).unwrap();
        let resident = fixture(
            &contracts,
            Provider::Halo2curvesAxiom,
            Boundary::ResidentInstalledChain,
            Kernel::Msm,
            "bn254.g2",
            2,
            4,
        )
        .unwrap();
        assert_eq!(resident.arithmetic_calls, 7);
        assert!(resident.conversions.is_empty());
        assert_eq!(
            resident
                .inputs
                .iter()
                .map(PhysicalType::spelling)
                .collect::<Vec<_>>(),
            [
                "vector:bn254.fr@halo2curves-axiom/bn254.fr",
                "groups:bn254.g2@halo2curves-axiom/bn254.g2"
            ]
        );
        let program = zkc_runtime::vm::Program::decode(
            &serde_json::to_vec(&resident.carrier).unwrap(),
            &contracts,
        )
        .unwrap();
        program.check_installation(&backend).unwrap();
        let inputs = [
            Value::Bn254Vector(vec![ark::Scalar::from(0), ark::Scalar::from(7)].into()),
            Value::Bn254G2Vector(vec![ark::G2::identity(), ark::G2::generator()].into()),
        ];
        let bytes: Vec<_> = inputs
            .iter()
            .map(|v| backend.encode_native_value(v).unwrap())
            .collect();
        assert_eq!(&bytes[0][..6], b"ZKCV\x00\x29");
        assert_eq!(&bytes[1][..6], b"ZKCV\x00\x31");
        let values = decode(&backend, &resident.inputs, &bytes).unwrap();
        assert_eq!(
            values.iter().map(Value::physical_type).collect::<Vec<_>>(),
            resident.inputs
        );
        for (value, bytes) in values.iter().zip(&bytes) {
            assert_eq!(backend.encode_native_value(value).unwrap(), *bytes);
        }
        let bls = contracts
            .resolve(binding(Provider::Blst, "curve.msm", "bls12-381.g2"))
            .unwrap();
        assert!(
            backend
                .decode_native_value(&bls.signature().inputs[0], &bytes[0])
                .is_err()
        );
        assert!(
            backend
                .decode_native_value(&bls.signature().inputs[1], &bytes[1])
                .is_err()
        );
        let bridge = fixture(
            &contracts,
            Provider::Halo2curvesAxiom,
            Boundary::Installed,
            Kernel::Msm,
            "bn254.g2",
            2,
            1,
        )
        .unwrap();
        assert_eq!(
            bridge
                .conversions
                .iter()
                .map(|row| row["canonical_payload_bytes"].as_u64().unwrap())
                .collect::<Vec<_>>(),
            [64, 128, 64]
        );
        assert!(bridge.conversions.iter().all(|row| row["calls"] == 1));
    }
}
