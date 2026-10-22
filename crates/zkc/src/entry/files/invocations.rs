//! Exact static child bindings, kept separate from source argument data.
use super::{self as files, *};
use crate::entry::{InvocationBinding, InvocationContext, ProofContext, RunContext};
use crate::entry::{RoleInputs, SetupAuthority};
use crate::files::Outputs;
use crate::host::inputs::read_regular as read;
use serde::Deserialize;
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Document {
    format: String,
    deployments: BTreeMap<String, Binding>,
}
#[derive(Deserialize)]
#[serde(tag = "operation", rename_all = "lowercase", deny_unknown_fields)]
enum Binding {
    Run {
        authority: Json,
        #[serde(default)]
        session: Option<String>,
        services: BTreeMap<String, BTreeMap<String, u64>>,
        setups: BTreeMap<String, String>,
        #[serde(default)]
        inputs: BTreeMap<String, Json>,
    },
    Prove {
        authority: Json,
        context: String,
        services: BTreeMap<String, u64>,
        transcript_budget: Option<u64>,
        setups: BTreeMap<String, String>,
        #[serde(default)]
        inputs: BTreeMap<String, Json>,
    },
    Verify {
        authority: Json,
        context: String,
        services: BTreeMap<String, u64>,
        transcript_budget: Option<u64>,
        setups: BTreeMap<String, String>,
        #[serde(default)]
        inputs: BTreeMap<String, Json>,
    },
}
pub struct Invocations {
    authority: BTreeMap<String, SetupAuthority>,
    context: InvocationContext,
    output_setups: zkc_native::SetupRegistry,
    operations: BTreeMap<String, &'static str>,
    paths: Vec<PathBuf>,
    inputs: BTreeMap<String, BTreeMap<String, Json>>,
    document: Option<PathBuf>,
    capacity: crate::execution::Capacity,
}
/// Result encoding retains the imported setup material and its original limits.
/// It grants no execution authority.
pub struct FunctionResultEncoder {
    setups: zkc_native::SetupRegistry,
    capacity: crate::execution::Capacity,
}
impl FunctionResultEncoder {
    pub fn encode(&self, value: &crate::entry::Value) -> Result<Vec<u8>> {
        files::function_output(value, self.capacity, self.setups.clone())
    }
}
/// Input refusal with the checked document and logical input location, if known.
#[derive(Debug)]
pub struct InvocationInputError {
    pub code: String,
    pub document: Option<PathBuf>,
    pub path: Option<String>,
}
impl From<&str> for InvocationInputError {
    fn from(code: &str) -> Self {
        Self {
            code: code.into(),
            document: None,
            path: None,
        }
    }
}
impl From<String> for InvocationInputError {
    fn from(code: String) -> Self {
        Self {
            code,
            document: None,
            path: None,
        }
    }
}
impl std::fmt::Display for InvocationInputError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.code)
    }
}
impl std::error::Error for InvocationInputError {}
impl Invocations {
    pub fn authority(&self) -> &BTreeMap<String, SetupAuthority> {
        &self.authority
    }

    /// Transfer the loaded pins and invocation values to admission and execution.
    /// Complete the deployment inventory and decode inputs before consuming it.
    pub fn into_parts(
        self,
    ) -> (
        BTreeMap<String, SetupAuthority>,
        InvocationContext,
        FunctionResultEncoder,
    ) {
        (
            self.authority,
            self.context,
            FunctionResultEncoder {
                setups: self.output_setups,
                capacity: self.capacity,
            },
        )
    }

    pub fn decode_inputs(
        &mut self,
        deployments: &[crate::entry::DeploymentInterface],
        documents: &mut files::Documents,
    ) -> std::result::Result<(), InvocationInputError> {
        for deployment in deployments {
            let id = deployment.id();
            let operation = deployment.operation();
            let interface = deployment.interface();
            let mut supplied = self.inputs.remove(id).unwrap_or_default();
            let groups = interface.context_input_groups(operation);
            if operation == "run"
                && supplied
                    .keys()
                    .any(|role| !groups.iter().any(|group| group.name() == role))
            {
                return Err("entry-host-context-role".into());
            }
            for group in &groups {
                let value = if operation == "run" {
                    supplied.remove(group.name()).unwrap_or_else(|| json!({}))
                } else {
                    json!(std::mem::take(&mut supplied))
                };
                let values = if group.is_empty() && value == json!({}) {
                    Default::default()
                } else {
                    let path = self.document.as_deref().ok_or("entry-input-missing")?;
                    documents
                        .decode_at(
                            group,
                            &serde_json::to_vec(&value).map_err(|_| "entry-invocation-format")?,
                            path,
                        )
                        .map_err(|e| InvocationInputError {
                            document: Some(path.into()),
                            path: Some(if operation == "run" {
                                format!("invocations.{id}.inputs.{}", e.path)
                            } else {
                                let name = e.path.strip_prefix(group.name()).unwrap_or(&e.path);
                                format!("invocations.{id}.inputs{name}")
                            }),
                            code: e.code,
                        })?
                };
                match self
                    .context
                    .deployments
                    .get_mut(id)
                    .ok_or("entry-host-context")?
                {
                    InvocationBinding::Run(context) => {
                        if !values.is_empty() {
                            context.roles.entry(group.name().into()).or_default().inputs = values;
                        }
                    }
                    InvocationBinding::Proof(context) => context.private.inputs = values,
                }
            }
            if !supplied.is_empty() {
                return Err("entry-host-context-role".into());
            }
        }
        if !self.inputs.is_empty() {
            return Err("entry-invocation-deployments".into());
        }
        Ok(())
    }
    /// Consume the Host owner's checked inventory, never diagnostic JSON.
    pub fn complete(&mut self, deployments: &[crate::entry::DeploymentInterface]) -> Result<()> {
        self.defaults(deployments.iter().map(|child| {
            (
                child.id(),
                child.operation(),
                child.interface().setup_names().len() != 0,
            )
        }))?;
        for child in deployments {
            let interface = child.interface();
            let check = |role, services: &BTreeMap<String, u64>| -> Result<()> {
                if services
                    .keys()
                    .any(|name| !interface.services(role).any(|s| s.name == *name))
                {
                    return Err("entry-service-names".into());
                }
                Ok(())
            };
            match &self.context.deployments[child.id()] {
                InvocationBinding::Run(context) => {
                    for (name, values) in &context.roles {
                        let role = interface
                            .roles()
                            .iter()
                            .find(|r| r.name == *name)
                            .ok_or("entry-host-context-role")?;
                        check(role, &values.services)?;
                    }
                }
                InvocationBinding::Proof(context) => {
                    let proof = interface.proof().ok_or("entry-invocation-format")?;
                    let role = if child.operation() == "prove" {
                        proof.prover
                    } else {
                        proof.verifier
                    };
                    check(&interface.roles()[role], &context.private.services)?;
                }
            }
        }
        Ok(())
    }
    /// Fill native invocation policy only for children that need no setup pins.
    /// Explicit deployment bindings retain their complete independent policy.
    fn defaults<'a>(
        &mut self,
        deployments: impl Iterator<Item = (&'a str, &'a str, bool)>,
    ) -> Result<()> {
        let deployments = deployments.collect::<Vec<_>>();
        for &(id, operation, needs_setup) in &deployments {
            if self.context.deployments.contains_key(id) {
                continue;
            }
            if needs_setup {
                return Err("entry-setup-authority".into());
            }
            let operation = match operation {
                "run" => "run",
                "prove" => "prove",
                "verify" => "verify",
                _ => return Err("entry-invocation-deployments".into()),
            };
            let context = if operation == "run" {
                InvocationBinding::Run(RunContext::default())
            } else {
                InvocationBinding::Proof(ProofContext::default())
            };
            self.context.deployments.insert(id.into(), context);
            self.authority.insert(id.into(), SetupAuthority::default());
            self.operations.insert(id.into(), operation);
        }
        self.check_operations(
            deployments
                .iter()
                .map(|&(id, operation, _)| (id, operation)),
        )
    }
    pub fn load(
        path: Option<&Path>,
        capacity: crate::execution::Capacity,
        output_setups: bool,
    ) -> Result<Self> {
        let mut result = Self {
            authority: BTreeMap::new(),
            context: InvocationContext::default(),
            output_setups: Default::default(),
            operations: BTreeMap::new(),
            paths: Vec::new(),
            inputs: BTreeMap::new(),
            document: None,
            capacity,
        };
        let Some(path) = path else {
            return Ok(result);
        };
        result.document = Some(path.into());
        let value = crate::host::document::read(
            &read(path, files::MAX_REQUEST_BYTES)?,
            files::MAX_REQUEST_BYTES,
        )?;
        if !value.is_object() {
            return Err("entry-invocation-format".into());
        }
        let document: Document =
            serde_json::from_value(value).map_err(|_| "entry-invocation-format")?;
        if document.format != "zkc.entry-invocations/0" || document.deployments.len() > 4096 {
            return Err("entry-invocation-format".into());
        }
        let directory = path.parent().unwrap_or(Path::new("."));
        let mut material_bytes = 0usize;
        let mut all_material = BTreeMap::new();
        let mut all_authority = SetupAuthority::default();
        for (id, binding) in document.deployments {
            if id.is_empty() || id.len() > 256 * 1024 {
                return Err("entry-invocation-format".into());
            }
            let operation = match &binding {
                Binding::Run { .. } => "run",
                Binding::Prove { .. } => "prove",
                Binding::Verify { .. } => "verify",
            };
            result.operations.insert(id.clone(), operation);
            let (authority, setups, context) = match binding {
                Binding::Run {
                    authority,
                    session,
                    services,
                    setups,
                    inputs,
                } => {
                    result.inputs.insert(id.clone(), inputs);
                    for budgets in services.values() {
                        check_services(budgets)?;
                    }
                    let roles = services
                        .into_iter()
                        .map(|(role, services)| {
                            (
                                role,
                                RoleInputs {
                                    inputs: Default::default(),
                                    services,
                                },
                            )
                        })
                        .collect();
                    (
                        authority,
                        setups,
                        InvocationBinding::Run(RunContext {
                            session,
                            roles,
                            setups: Default::default(),
                        }),
                    )
                }
                Binding::Prove {
                    authority,
                    context,
                    services,
                    transcript_budget,
                    setups,
                    inputs,
                }
                | Binding::Verify {
                    authority,
                    context,
                    services,
                    transcript_budget,
                    setups,
                    inputs,
                } => {
                    result.inputs.insert(id.clone(), inputs);
                    check_services(&services)?;
                    if context.len() > 8192 {
                        return Err("native-proof-context-limit".into());
                    }
                    if transcript_budget.is_some_and(|n| n > crate::entry::DEFAULT_DRAW_BUDGET) {
                        return Err("native-proof-budget".into());
                    }
                    let context = crate::host::inputs::unhex(&json!(context))?;
                    (
                        authority,
                        setups,
                        InvocationBinding::Proof(ProofContext {
                            context,
                            private: RoleInputs {
                                inputs: Default::default(),
                                services,
                            },
                            transcript_budget,
                            setups: Default::default(),
                        }),
                    )
                }
            };
            let authority = files::authority(
                &serde_json::to_vec(&authority).map_err(|_| "entry-invocation-format")?,
            )?;
            let mut material = BTreeMap::new();
            for (slot, path) in setups {
                if path.is_empty() {
                    return Err("entry-setup-material".into());
                }
                let path = directory.join(path);
                let remaining = capacity.values.total_bytes.saturating_sub(material_bytes);
                let bytes = read(
                    path.to_str().ok_or("entry-setup-material")?,
                    capacity.wire_bytes.min(remaining),
                )?;
                material_bytes += bytes.len();
                result.paths.push(path);
                material.insert(slot, bytes);
            }
            // Check material against this deployment's independent authority before
            // combining serialization keys. Never resolve a pin by a bare slot name.
            files::output_setups(&material, &authority, capacity)?;
            if output_setups {
                for (slot, bytes) in &material {
                    let key = format!("{}:{id}{slot}", id.len());
                    all_material.insert(key.clone(), bytes.clone());
                    all_authority.keys.insert(key, authority.keys[slot]);
                }
            }
            let mut context = context;
            match &mut context {
                InvocationBinding::Run(c) => c.setups = material,
                InvocationBinding::Proof(c) => c.setups = material,
            }
            result.authority.insert(id.clone(), authority);
            result.context.deployments.insert(id, context);
        }
        result.output_setups = files::output_setups(&all_material, &all_authority, capacity)?;
        Ok(result)
    }
    pub fn protect(&self, outputs: &mut Outputs) -> Result<()> {
        for path in &self.paths {
            outputs.protect([path.to_str().ok_or("entry-setup-material")?])?;
        }
        Ok(())
    }
    fn check_operations<'a>(
        &self,
        deployments: impl Iterator<Item = (&'a str, &'a str)>,
    ) -> Result<()> {
        let expected = deployments.collect::<BTreeMap<_, _>>();
        if expected.len() != self.operations.len()
            || self
                .operations
                .iter()
                .any(|(id, op)| expected.get(id.as_str()).copied() != Some(*op))
        {
            return Err("entry-invocation-deployments".into());
        }
        Ok(())
    }
}
fn check_services(services: &BTreeMap<String, u64>) -> Result<()> {
    for (name, count) in services {
        if name.len() > 128 || !crate::source_names::is_source_identifier(name) {
            return Err("entry-service-names".into());
        }
        if *count > crate::entry::DEFAULT_DRAW_BUDGET {
            return Err("entry-service-budget".into());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::files::hex;
    fn load(directory: &Path, value: &Json) -> Result<Invocations> {
        let path = directory.join("invocations.json");
        std::fs::write(&path, value.to_string()).unwrap();
        let path = path.to_str().unwrap();
        Invocations::load(Some(Path::new(path)), Default::default(), true)
    }
    fn proof() -> Json {
        json!({"operation":"verify","authority":{"format":"zkc.entry-setups/0","keys":{}},
            "context":"0102","services":{"rng":0},"transcript_budget":0,"setups":{}})
    }
    #[test]
    fn native_defaults_preserve_explicit_policy_and_never_supply_setup_authority() {
        let dir = tempfile::tempdir().unwrap();
        let document = json!({"format":"zkc.entry-invocations/0","deployments":{
            "explicit":proof()
        }});
        let mut bindings = load(dir.path(), &document).unwrap();
        let inventory = [
            ("explicit", "verify", false),
            ("joint", "run", false),
            ("producer", "prove", false),
        ];
        bindings.defaults(inventory.into_iter()).unwrap();
        let InvocationBinding::Run(joint) = &bindings.context.deployments["joint"] else {
            panic!()
        };
        assert_eq!(joint.session, None);
        assert!(joint.roles.is_empty());
        let InvocationBinding::Proof(producer) = &bindings.context.deployments["producer"] else {
            panic!()
        };
        assert!(producer.context.is_empty());
        assert!(producer.private.services.is_empty());
        assert_eq!(producer.transcript_budget, None);
        let InvocationBinding::Proof(explicit) = &bindings.context.deployments["explicit"] else {
            panic!()
        };
        assert_eq!(explicit.context, [1, 2]);
        assert_eq!(explicit.private.services["rng"], 0);
        assert_eq!(explicit.transcript_budget, Some(0));
        assert!(bindings.authority.values().all(|a| a.keys.is_empty()));
        let mut another = load(dir.path(), &document).unwrap();
        another.defaults(inventory.into_iter()).unwrap();
        let InvocationBinding::Run(other) = &another.context.deployments["joint"] else {
            panic!()
        };
        assert_eq!(other.session, None);
        assert_eq!(
            bindings
                .defaults([("needs-pins", "run", true)].into_iter())
                .unwrap_err(),
            "entry-setup-authority"
        );
        assert!(!bindings.authority.contains_key("needs-pins"));
        assert_eq!(
            another
                .defaults([("explicit", "prove", false)].into_iter())
                .unwrap_err(),
            "entry-invocation-deployments"
        );
    }
    #[test]
    fn consumed_invocations_retain_the_result_encoding_capacity() {
        let value = crate::entry::Value::from(zkc_native::Value::Bool(true));
        let (_, context, encoder) = Invocations::load(None, Default::default(), false)
            .unwrap()
            .into_parts();
        assert!(context.deployments.is_empty());
        let encoded: Json = serde_json::from_slice(&encoder.encode(&value).unwrap()).unwrap();
        assert_eq!(encoded["format"], "zkc.entry-outputs/0");

        let capacity = crate::execution::Capacity {
            wire_bytes: 6,
            ..Default::default()
        };
        let (_, _, encoder) = Invocations::load(None, capacity, false)
            .unwrap()
            .into_parts();
        assert_eq!(encoder.encode(&value).unwrap_err(), "entry-output-encoding");
    }
    #[test]
    fn deployment_context_is_exact_and_operation_qualified() {
        let dir = tempfile::tempdir().unwrap();
        let value = json!({"format":"zkc.entry-invocations/0","deployments":{
            "static.verify":proof(),
            "static.run":{"operation":"run","authority":{"format":"zkc.entry-setups/0","keys":{}},
                "session":"explicit","services":{"P":{"rng":0}},"setups":{}}
        }});
        let bindings = load(dir.path(), &value).unwrap();
        bindings
            .check_operations([("static.verify", "verify"), ("static.run", "run")].into_iter())
            .unwrap();
        for expected in [
            vec![],
            vec![("static.verify", "prove"), ("static.run", "run")],
            vec![("static.verify", "verify")],
        ] {
            assert_eq!(
                bindings.check_operations(expected.into_iter()).unwrap_err(),
                "entry-invocation-deployments"
            );
        }
        let InvocationBinding::Proof(c) = &bindings.context.deployments["static.verify"] else {
            panic!()
        };
        assert_eq!(c.context, [1, 2]);
        assert_eq!(c.transcript_budget, Some(0));
        assert_eq!(c.private.services["rng"], 0);
        assert!(c.private.inputs.is_empty());
        let InvocationBinding::Run(c) = &bindings.context.deployments["static.run"] else {
            panic!()
        };
        assert_eq!(c.session.as_deref(), Some("explicit"));
        assert!(c.roles["P"].inputs.is_empty());
    }
    #[test]
    fn setup_slots_keep_each_deployments_independent_pins_and_material() {
        let dir = tempfile::tempdir().unwrap();
        let bounds = crate::execution::Capacity::default().backend().ark_bounds();
        let mut document = json!({"format":"zkc.entry-invocations/0","deployments":{}});
        let mut materials = Vec::new();
        let mut commitments = Vec::new();
        for (arity, id) in [(1, "first"), (2, "second")] {
            let keys =
                zkc_kernels::arkworks::bls12_381::Keys::setup_for_development(arity, &bounds)
                    .unwrap();
            let table = zkc_kernels::arkworks::bls12_381::Table::from_logical_vec(
                vec![zkc_native::Scalar::from(1); 1 << arity],
                &bounds,
            )
            .unwrap();
            let committed = keys.prover_key().commit(&table).unwrap();
            commitments.push(crate::entry::Value::from(zkc_native::Value::Commitment(
                std::sync::Arc::new(committed.commitment().clone()),
            )));
            let key = keys.verifier_key();
            let bytes = key.to_bytes(&bounds).unwrap();
            let filename = format!("{id}.zkvk");
            std::fs::write(dir.path().join(&filename), &bytes).unwrap();
            let mut binding = proof();
            binding["authority"]["keys"] = json!({"setup":hex(&key.metadata().key_id())});
            binding["setups"] = json!({"setup":filename});
            document["deployments"][id] = binding;
            materials.push((id, key.metadata(), bytes));
        }
        let bindings = load(dir.path(), &document).unwrap();
        for (id, metadata, bytes) in &materials {
            assert_eq!(bindings.authority[*id].keys["setup"], metadata.key_id());
            assert!(bindings.output_setups.get(*metadata).is_some());
            let InvocationBinding::Proof(context) = &bindings.context.deployments[*id] else {
                panic!()
            };
            assert_eq!(&context.setups["setup"], bytes);
        }
        let destination = dir.path().join("first.zkvk");
        let mut outputs = Outputs::new(&[destination.to_str().unwrap()], &[]).unwrap();
        assert_eq!(
            bindings.protect(&mut outputs).unwrap_err(),
            "artifact-output-path"
        );
        document["deployments"]["first"]["authority"] =
            document["deployments"]["second"]["authority"].clone();
        assert!(load(dir.path(), &document).is_err());

        let (authority, context, encoder) = bindings.into_parts();
        assert_eq!(authority.len(), 2);
        assert_eq!(context.deployments.len(), 2);
        let value = crate::entry::Value::Array(commitments);
        let encoded: Json = serde_json::from_slice(&encoder.encode(&value).unwrap()).unwrap();
        assert_eq!(encoded["value"].as_array().unwrap().len(), 2);
        let (_, _, empty) = Invocations::load(None, Default::default(), false)
            .unwrap()
            .into_parts();
        assert_eq!(empty.encode(&value).unwrap_err(), "entry-output-encoding");
    }
    #[test]
    fn malformed_contexts_and_unbacked_authority_refuse() {
        let dir = tempfile::tempdir().unwrap();
        for (pointer, value, code) in [
            ("/unknown", json!(true), "entry-invocation-format"),
            (
                "/format",
                json!("zkc.entry-invocations/1"),
                "entry-invocation-format",
            ),
            (
                "/deployments/child/extra",
                json!({}),
                "entry-invocation-format",
            ),
            ("/deployments/child/context", json!("zz"), "artifact-hex"),
            (
                "/deployments/child/transcript_budget",
                json!(crate::entry::DEFAULT_DRAW_BUDGET + 1),
                "native-proof-budget",
            ),
            (
                "/deployments/child/services/rng",
                json!(crate::entry::DEFAULT_DRAW_BUDGET + 1),
                "entry-service-budget",
            ),
            (
                "/deployments/child/services/bad.name",
                json!(0),
                "entry-service-names",
            ),
            (
                "/deployments/child/authority/keys/slot",
                json!("0".repeat(64)),
                "entry-setup-material",
            ),
        ] {
            let mut document =
                json!({"format":"zkc.entry-invocations/0","deployments":{"child":proof()}});
            let (parent, field) = pointer.rsplit_once('/').unwrap();
            let object = document
                .pointer_mut(parent)
                .unwrap()
                .as_object_mut()
                .unwrap();
            object.insert(field.into(), value);
            let error = load(dir.path(), &document).err().expect(pointer);
            assert_eq!(error, code, "{pointer}");
        }
    }
}
