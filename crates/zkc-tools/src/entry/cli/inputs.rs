use super::*;
use std::{collections::BTreeMap, path::Path};
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Operation {
    Run,
    Prove,
    Verify,
}
impl Operation {
    pub fn parse(name: &str) -> Result<Self> {
        match name {
            "run" => Ok(Self::Run),
            "prove" => Ok(Self::Prove),
            "verify" => Ok(Self::Verify),
            _ => Err("cli-usage".into()),
        }
    }
    pub fn kind(self) -> crate::project::EntryKind {
        if self == Self::Run {
            crate::project::EntryKind::Run
        } else {
            crate::project::EntryKind::Proof
        }
    }
    pub fn validate(self, args: &Arguments<'_>, checking: bool) -> Result<()> {
        let forbidden: &[&str] = match self {
            Self::Run => &[
                "--public",
                "--witness",
                "--context",
                "--transcript-budget",
                "--allow-header-only",
                "--attempts",
            ],
            Self::Prove => &["--session", "--input", "--limits"],
            Self::Verify => &[
                "--session",
                "--input",
                "--limits",
                "--witness",
                "--attempts",
            ],
        };
        if forbidden.iter().any(|f| args.has(f)) {
            return Err("cli-option".into());
        }
        if self == Self::Run && !args.has("--session")
            || !checking && self == Self::Prove && !args.has("--output")
            || !checking && self == Self::Verify && !args.has("--proof")
        {
            return Err("cli-usage".into());
        }
        Ok(())
    }
}
pub(super) struct Options {
    pub setups: SetupAuthority,
    pub proof: ProofOptions,
    pub run: HostLimits,
    pub attempts: Option<AttemptOptions>,
    pub material: BTreeMap<String, Vec<u8>>,
    pub services: BTreeMap<String, BTreeMap<String, u64>>,
    pub context: Vec<u8>,
    pub transcript_budget: Option<u64>,
}
impl Options {
    pub fn parse(args: &Arguments<'_>) -> Result<Self> {
        let mut options = Self {
            setups: Default::default(),
            proof: Default::default(),
            run: Default::default(),
            attempts: None,
            material: BTreeMap::new(),
            services: BTreeMap::new(),
            context: vec![],
            transcript_budget: None,
        };
        if let Some(file) = args.value("--capacity") {
            let capacity = crate::execution::Capacity::parse(&read(file, 4096)?)?;
            options.proof.capacity = capacity;
            options.run.capacity = capacity;
        }
        if let Some(file) = args.value("--limits") {
            options.run = options.run.with_work_limits(&read(file, 4096)?)?;
        }
        if let Some(file) = args.value("--setups") {
            options.setups = files::authority(&read(file, 65536)?)?;
        }
        if args.has("--allow-header-only") {
            options.proof.binding = BindingPolicy::AllowHeaderOnly;
        }
        if let Some(count) = args.value("--attempts") {
            options.attempts = Some(AttemptOptions {
                count: count.parse().expect("admitted count"),
                ..Default::default()
            });
        }
        let mut material_bytes = 0usize;
        for &(key, value) in &args.options {
            let value = value.unwrap_or("");
            match key {
                "--key" => {
                    let (name, path) = assignment(value)?;
                    let capacity = options.proof.capacity;
                    let remaining = capacity.values.total_bytes.saturating_sub(material_bytes);
                    let bytes = read(path, capacity.wire_bytes.min(remaining))?;
                    material_bytes += bytes.len();
                    if options.material.insert(name.into(), bytes).is_some() {
                        return Err("entry-setup-material".into());
                    }
                }
                "--service" => {
                    let (selector, count) = assignment(value)?;
                    let (role, name) = selector.split_once('.').ok_or("entry-service-names")?;
                    if !identifier(role) || !identifier(name) {
                        return Err("entry-service-names".into());
                    }
                    let count = count
                        .parse::<u64>()
                        .ok()
                        .filter(|n| *n <= super::super::DEFAULT_DRAW_BUDGET)
                        .ok_or("entry-service-budget")?;
                    if options
                        .services
                        .entry(role.into())
                        .or_default()
                        .insert(name.into(), count)
                        .is_some()
                    {
                        return Err("entry-service-names".into());
                    }
                }
                "--context" => {
                    if value.len() > 8192 {
                        return Err("native-proof-context-limit".into());
                    }
                    options.context = crate::host::inputs::unhex(&json!(value))?;
                }
                "--transcript-budget" => {
                    let n = value.parse::<u64>().expect("admitted count");
                    if n > super::super::DEFAULT_DRAW_BUDGET {
                        return Err("native-proof-budget".into());
                    }
                    options.transcript_budget = Some(n);
                }
                _ => {}
            }
        }
        Ok(options)
    }
    pub fn request(
        &mut self,
        interface: &Interface,
        args: &Arguments<'_>,
        operation: Operation,
        documents: &mut files::Documents,
        report: &mut Json,
    ) -> Result<Request> {
        let mut load = |group: &super::super::inputs::InputGroup<'_>, path: Option<&str>| {
            documents.load(group, path.map(Path::new)).map_err(|e| {
                report["input_path"] = json!(e.path);
                e.code
            })
        };
        if operation == Operation::Run {
            let mut paths = BTreeMap::new();
            for (_, value) in args.options.iter().filter(|(k, _)| *k == "--input") {
                let (role, path) = assignment(value.unwrap())?;
                if !interface.roles().iter().any(|r| r.name == role)
                    || paths.insert(role, path).is_some()
                {
                    return Err("entry-input-roles".into());
                }
            }
            let mut roles = BTreeMap::new();
            for group in interface.input_groups() {
                let input = load(&group, paths.remove(group.name()))?;
                roles.insert(
                    group.name().into(),
                    RoleInputs {
                        inputs: input,
                        services: self.services.remove(group.name()).unwrap_or_default(),
                    },
                );
            }
            if !self.services.is_empty() {
                return Err("entry-service-names".into());
            }
            Ok(Request::Run(RunRequest {
                session: args.value("--session").unwrap().into(),
                roles,
                setups: std::mem::take(&mut self.material),
            }))
        } else {
            let groups = interface.input_groups();
            let public = load(&groups[0], args.value("--public"))?;
            let private = if operation == Operation::Prove {
                load(&groups[1], args.value("--witness"))?
            } else {
                Default::default()
            };
            let proof = interface.proof().ok_or("entry-job-kind")?;
            let role = &interface.roles()[if operation == Operation::Prove {
                proof.prover
            } else {
                proof.verifier
            }]
            .name;
            let services = self.services.remove(role).unwrap_or_default();
            if !self.services.is_empty() {
                return Err("entry-service-names".into());
            }
            Ok(Request::Proof(ProofRequest {
                public,
                private: RoleInputs {
                    inputs: private,
                    services,
                },
                context: std::mem::take(&mut self.context),
                transcript_budget: self.transcript_budget,
                setups: std::mem::take(&mut self.material),
            }))
        }
    }
}
pub(super) enum Request {
    Run(RunRequest),
    Proof(ProofRequest),
}
pub(super) fn assignment(value: &str) -> Result<(&str, &str)> {
    let (name, path) = value.split_once('=').ok_or("cli-usage")?;
    if name.is_empty() || path.is_empty() {
        return Err("cli-usage".into());
    }
    Ok((name, path))
}
fn identifier(value: &str) -> bool {
    let mut b = value.bytes();
    b.next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == b'_')
        && b.all(|c| c.is_ascii_alphanumeric() || c == b'_')
}
