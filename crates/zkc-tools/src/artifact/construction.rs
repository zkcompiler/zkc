//! Immutable checked bundle. The native checker is a trusted recomputation
//! boundary; Lean independently checks ordinary projection, not construction.
use super::identity::Identity;
use super::io::*;
use crate::protocol::ParticipantChecker;
use serde_json::Value as Json;
use std::{collections::BTreeMap, process::Command, time::Duration};
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, PublicInputs, SetupRegistry};
use zkc_runtime::interactive::{
    Admitted, ArtifactFormat, EntryRole, LogicalType, Type, admit_physical,
};

#[derive(Clone)]
pub(super) struct Port {
    pub name: String,
    pub role: String,
    pub ty: LogicalType,
}
pub struct CheckedBundle {
    pub(super) source: Json,
    /// Source-shaped elaboration, used for ports and observation coordinates.
    /// Under normalized identity this is prepared from independently site-resolved source.
    pub(super) common: Json,
    pub(super) descriptor: Json,
    /// Opt-in structural interpretation; original source and descriptor above
    /// remain the custody subject of native construction recomputation.
    pub(super) identity: Option<Identity>,
    pub(super) manifest: Json,
    pub(super) admitted: Admitted,
    pub(super) ports: Vec<Port>,
    pub(super) generated_ports: Vec<Port>,
    pub(super) entry: String,
    pub(super) producer: String,
    pub(super) validator: String,
    pub(super) selected_rng: String,
    pub(super) acceptance: usize,
}
impl CheckedBundle {
    pub fn load(
        source: &str,
        descriptor: &str,
        construction: &str,
        participants: &str,
        compiler: &str,
        lean: &str,
    ) -> Result<Self> {
        let source_bytes = read(source, 1 << 20)?;
        let source = parse(&source_bytes, 1 << 20)?;
        let descriptor_bytes = read(descriptor, 1 << 20)?;
        let descriptor = parse(&descriptor_bytes, 1 << 20)?;
        let construction_bytes = read(construction, INPUT_LIMIT)?;
        let manifest = parse(&construction_bytes, INPUT_LIMIT)?;
        let result = array(&manifest, 6)?;
        if !matches!(result[0].as_str(), Some("zkc.construction-result/1"))
            || result[1] != descriptor
        {
            return Err("artifact-construction-result".into());
        }
        // All subprocess inputs are the exact bytes retained above, immune to
        // path replacement between checks and use. Child output is bounded.
        check_construction(
            compiler,
            &source_bytes,
            &descriptor_bytes,
            &construction_bytes,
        )?;
        let d = array(&descriptor, 9)?;
        if d[0] != "zkc.construction/1"
            || !matches!(d[8].as_str(), Some("exact" | "normalized"))
            || !matches!(
                d[7].as_str(),
                Some(
                    "merlin3.bls12-381.fr64be/1"
                        | "merlin3.ristretto255.scalar64le/1"
                        | "merlin3.koala-bear.ext8-binomial3.rejection31le/1"
                        | "spongefish0.7.4.keccak.bls12-381.fr64be/1"
                )
            )
        {
            return Err("artifact-descriptor".into());
        }
        // The complete original source has been admitted above. Never resolve
        // a candidate-supplied view or use normalization as source admission.
        let identity = if d[8] == "normalized" {
            Some(Identity::derive(&source, &descriptor)?)
        } else {
            None
        };
        let resolved = identity.as_ref().map_or(&source, |i| &i.source);
        let entry = text(&d[1])?.to_owned();
        let producer = text(&d[2])?.to_owned();
        let validator = text(&d[3])?.to_owned();
        let selected_rng = text(&array(&d[5], 2)?[0])?.to_owned();
        let resolved_common = if resolved[0] == "zkc.library/1" {
            &resolved[3]
        } else {
            resolved
        };
        let has_algorithms = list(&resolved_common[2])?.iter().any(|f| {
            f.get(4).and_then(Json::as_array).is_some_and(|body| {
                body.iter()
                    .any(|i| i.get(0).and_then(Json::as_str) == Some("apply"))
            })
        });
        let common =
            if source.get(0).and_then(Json::as_str) == Some("zkc.library/1") || has_algorithms {
                let resolved_bytes;
                let preparation_bytes = if let Some(identity) = &identity {
                    resolved_bytes = identity.source_bytes()?;
                    &resolved_bytes
                } else {
                    &source_bytes
                };
                parse(
                    &compiler_run(
                        compiler,
                        "protocol-prepare",
                        &[("source", preparation_bytes)],
                        &[],
                        1 << 20,
                    )?,
                    1 << 20,
                )?
            } else {
                resolved.clone()
            };
        // Preparation is a convenience view for source ports/observations. Its
        // retained definitions and bindings must be the exact records already
        // authenticated by recomputing construction from the frozen source.
        for record in list(&common[2])? {
            if !list(&result[2][2])?.contains(record) {
                return Err("artifact-prepared-function".into());
            }
        }
        if common[0] == "zkc.protocol/1" {
            for record in list(&common[1])? {
                if !list(&result[2][1])?.contains(record) {
                    return Err("artifact-prepared-binding".into());
                }
            }
        }
        if source[0] == "zkc.library/1" {
            for index in 3..6 {
                if common[index] != resolved[3][index] {
                    return Err("artifact-prepared-control".into());
                }
            }
        }
        let format = source_format(&common)?;
        let expected = "zkc.construction-result/1";
        if result[0] != expected || source_format(&result[2])? != format {
            return Err("artifact-construction-format".into());
        }
        let entry_policy = EntryPolicy::new(
            Domain::new("admission", "admission", "admission", None),
            None,
            PublicInputs::LocalOnly,
        );
        let a_backend = NativeBackend::with_setups(
            Policy::default(),
            entry_policy,
            SetupRegistry::new(vec![], &Policy::default()).map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())?;
        let candidate = read(participants, 1 << 20)?;
        parse(&candidate, 1 << 20)?;
        let constructed = serde_json::to_vec(&result[2]).map_err(|_| "artifact-json")?;
        let checker = ParticipantChecker::new(lean).map_err(|_| "artifact-checker-io")?;
        let admitted = admit_physical(&constructed, &candidate, &a_backend, &checker)
            .map_err(|e| e.to_string())?;
        if admitted.format() != format {
            return Err("artifact-profile".into());
        }
        let ports = entry_ports(&common, &d[1], format)?;
        check_artifact_profile(&common, d, &ports, &validator, &selected_rng)?;
        // The checked profile makes the selected validator's data public, not
        // an arbitrary role called V. Reject private/producer placement before
        // issuing resources or reading a proof, including shared local functions.
        check_public_implementations(&admitted, &entry, &validator)?;
        // Preparation omits undemanded definitions, but artifact-profile
        // admission still covers signatures in the entire original library.
        if source.get(0).and_then(Json::as_str) == Some("zkc.library/1") {
            for definition in list(&array(&source, 4)?[1])? {
                let definition = array(definition, 7)?;
                check_unconstructed_signature(&definition[4], &definition[5])?;
            }
        }
        let generated_ports = entry_ports(&result[2], &d[1], format)?;
        let suite = zkc_runtime::interactive::Identity::parse(text(&d[7])?)
            .map_err(|_| "artifact-transcript-suite")?;
        if ports
            .iter()
            .filter(|p| p.role == validator && p.name == selected_rng)
            .any(|p| p.ty.kind() != Type::Rng || Some(p.ty.identity()) != suite.scalar_field())
        {
            return Err("artifact-challenge-field".into());
        }
        if generated_ports
            .iter()
            .any(|p| p.ty.kind() == Type::Transcript && p.ty.identity() != suite)
        {
            return Err("artifact-transcript-suite".into());
        }
        let mut acceptance = None;
        for row in list(&result[5])? {
            let row = array(row, 3)?;
            let output = list(&row[2])?;
            if row[0] == d[3] && output == [Json::String("source".into()), d[6].clone()] {
                let index =
                    usize::try_from(natural(&row[1])?).map_err(|_| "artifact-output-map")?;
                if acceptance.replace(index).is_some() {
                    return Err("artifact-output-map".into());
                }
            }
        }
        let acceptance = acceptance.ok_or("artifact-output-map")?;
        let roles = admitted.entry(&entry).ok_or("artifact-entry")?;
        if roles.len() != 2
            || !roles.iter().any(|r| r.role == producer)
            || !roles.iter().any(|r| {
                r.role == validator
                    && r.outputs
                        .get(acceptance)
                        .is_some_and(|t| t.kind() == Type::Bool)
            })
        {
            return Err("artifact-output-map".into());
        }
        Ok(Self {
            source,
            common,
            descriptor,
            identity,
            manifest,
            admitted,
            ports,
            generated_ports,
            entry,
            producer,
            validator,
            selected_rng,
            acceptance,
        })
    }
    pub(super) fn role(&self, producer: bool) -> Result<EntryRole> {
        let name = if producer {
            &self.producer
        } else {
            &self.validator
        };
        self.admitted
            .entry(&self.entry)
            .and_then(|r| r.into_iter().find(|r| &r.role == name))
            .ok_or("artifact-role".into())
    }
}

// Common construction also represents transformations with private verifier
// state. Independent public validation has a stricter entry contract: no
// unbound statement inputs or additional private verifier resources. Keep this
// check at artifact admission, rather than changing the common PIR language.
fn check_artifact_profile(
    source: &Json,
    descriptor: &[Json],
    ports: &[Port],
    validator: &str,
    selected_rng: &str,
) -> Result<()> {
    let module = array(source, 6)?;
    source_format(source)?;
    for function in list(&module[2])? {
        let f = array(function, 6)?;
        check_unconstructed_signature(&f[2], &f[3])?;
    }
    for protocol in list(&module[3])? {
        let p = array(protocol, 8)?;
        if list(&p[4])?.iter().any(|p| {
            p.get(2).is_some_and(|t| {
                t.as_str()
                    .is_some_and(|s| s.split(':').next() == Some("transcript"))
            })
        }) || list(&p[5])?.iter().any(|p| {
            p.get(1).is_some_and(|t| {
                t.as_str()
                    .is_some_and(|s| s.split(':').next() == Some("transcript"))
            })
        }) {
            return Err("artifact-source-transcript".into());
        }
    }
    let bindings = list(&descriptor[4])?;
    for port in ports.iter().filter(|p| p.role == validator) {
        if port.ty.kind().is_serializable() {
            let mut bound = false;
            for binding in bindings {
                for target in list(&array(binding, 2)?[1])? {
                    let target = array(target, 2)?;
                    bound |= text(&target[0])? == validator && text(&target[1])? == port.name;
                }
            }
            if !bound {
                return Err("artifact-unbound-verifier-input".into());
            }
        } else if port.ty.kind() != Type::VerifierKey
            && !(port.ty.kind() == Type::Rng && port.name == selected_rng)
        {
            return Err("artifact-verifier-resource".into());
        }
    }
    Ok(())
}
fn check_public_implementations(admitted: &Admitted, entry: &str, validator: &str) -> Result<()> {
    for (implementation, roles) in admitted
        .executable_implementation_roles(entry)
        .ok_or("artifact-entry")?
    {
        if zkc_backends::requires_public_operands(&implementation)
            && roles.iter().any(|role| role != validator)
        {
            return Err("artifact-public-implementation-role".into());
        }
    }
    Ok(())
}
fn check_unconstructed_signature(inputs: &Json, outputs: &Json) -> Result<()> {
    let transcript = |ty: &Json| {
        ty.as_str()
            .is_some_and(|s| s.split(':').next() == Some("transcript"))
    };
    if list(inputs)?
        .iter()
        .any(|p| p.get(1).is_some_and(transcript))
        || list(outputs)?.iter().any(transcript)
    {
        return Err("artifact-source-transcript".into());
    }
    Ok(())
}

fn check_construction(
    executable: &str,
    source: &[u8],
    descriptor: &[u8],
    candidate: &[u8],
) -> Result<()> {
    let response = compiler_run(
        executable,
        "protocol-check-construction",
        &[
            ("source", source),
            ("descriptor", descriptor),
            ("candidate", candidate),
        ],
        &[],
        4096,
    )?;
    if response != b"construction-checked\n" {
        return Err("artifact-checker-response".into());
    }
    Ok(())
}

pub(super) fn compiler_run(
    executable: &str,
    command: &str,
    inputs: &[(&str, &[u8])],
    options: &[(&str, Option<&[u8]>)],
    limit: usize,
) -> Result<Vec<u8>> {
    let temp = tempfile::tempdir().map_err(|_| "artifact-checker-io")?;
    let mut paths = Vec::new();
    for (name, bytes) in inputs {
        let path = temp.path().join(name);
        std::fs::write(&path, bytes).map_err(|_| "artifact-checker-io")?;
        paths.push(path);
    }
    let mut arguments = Vec::new();
    for (index, (flag, bytes)) in options.iter().enumerate() {
        arguments.push(if let Some(bytes) = bytes {
            let path = temp.path().join(format!("option{index}"));
            std::fs::write(&path, bytes).map_err(|_| "artifact-checker-io")?;
            format!("{flag}={}", path.display())
        } else {
            (*flag).to_owned()
        });
    }
    let mut invocation = Command::new(executable);
    invocation.arg(command).args(paths).args(arguments);
    let output = crate::host::process::capture(
        &mut invocation,
        temp.path(),
        |elapsed| elapsed > Duration::from_secs(120),
        limit,
        false,
    )
    .map_err(|failure| match failure {
        crate::host::process::Error::Process(_) | crate::host::process::Error::Io(_) => {
            "artifact-checker-io"
        }
        crate::host::process::Error::Timeout => "artifact-checker-timeout",
        crate::host::process::Error::OutputLimit => "artifact-checker-limit",
    })?;
    if !output.status.success() {
        return Err("artifact-construction-refused".into());
    }
    read(output.stdout.path(), limit)
}

fn source_format(source: &Json) -> Result<ArtifactFormat> {
    let module = array(source, 6)?;
    match text(&module[0])? {
        "zkc.protocol/1" => Ok(ArtifactFormat::ExplicitBindings),
        _ => Err("artifact-source-format".into()),
    }
}

pub(super) fn type_spelling(ty: LogicalType, _format: ArtifactFormat) -> String {
    ty.spelling()
}

fn entry_ports(source: &Json, entry: &Json, _format: ArtifactFormat) -> Result<Vec<Port>> {
    let s = array(source, 6)?;
    let entry_record = list(&s[5])?
        .iter()
        .find(|e| e.get(1) == Some(entry))
        .ok_or("artifact-entry")?;
    let instance_name = &array(entry_record, 3)?[2];
    let instance = list(&s[4])?
        .iter()
        .find(|i| i.get(1) == Some(instance_name))
        .ok_or("artifact-instance")?;
    let instance = array(instance, 6)?;
    let definition = list(&s[3])?
        .iter()
        .find(|p| p.get(1) == Some(&instance[2]))
        .ok_or("artifact-protocol")?;
    let definition = array(definition, 8)?;
    let roles: BTreeMap<_, _> = list(&instance[5])?
        .iter()
        .map(|p| {
            let p = array(p, 2)?;
            Ok((text(&p[0])?, text(&p[1])?))
        })
        .collect::<Result<_>>()?;
    let ports = list(&definition[4])?
        .iter()
        .map(|p| {
            let p = array(p, 3)?;
            Ok(Port {
                name: text(&p[0])?.into(),
                role: roles.get(text(&p[1])?).ok_or("artifact-role")?.to_string(),
                ty: LogicalType::parse(text(&p[2])?).map_err(|e| e.to_string())?,
            })
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(ports)
}
