use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use zkc_backends::has_native_wire;
use zkc_runtime::interactive::{Admitted, Backend, ProgramAction, ProgramRole, admit_supplied};

/// Structural admission ceilings. Every count is independent; bytes measure UTF-8
/// or carrier bytes, depth counts containers, and nodes include object keys.
/// Defaults equal installed hard maxima; oversized requests refuse.
#[derive(Clone, Copy, Debug)]
pub struct BundleLimits {
    pub bytes: usize,
    pub candidate_bytes: usize,
    pub roles: usize,
    pub steps: usize,
    pub depth: usize,
    pub nodes: usize,
    pub string_bytes: usize,
}
impl Default for BundleLimits {
    fn default() -> Self {
        Self::HARD_MAX
    }
}
impl BundleLimits {
    pub const HARD_MAX: Self = Self {
        bytes: 16 * 1024 * 1024,
        candidate_bytes: 1024 * 1024,
        roles: 1024,
        steps: 32768,
        depth: 256,
        nodes: 250_000,
        string_bytes: 4096,
    };
    pub fn validate(&self) -> Result<(), BundleError> {
        let hard = Self::HARD_MAX;
        if self.bytes > hard.bytes
            || self.candidate_bytes > hard.candidate_bytes
            || self.roles > hard.roles
            || self.steps > hard.steps
            || self.depth > hard.depth
            || self.nodes > hard.nodes
            || self.string_bytes > hard.string_bytes
        {
            return Err(BundleError::Limit);
        }
        Ok(())
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BundleError {
    Limit,
    Identity,
    Json,
    Format,
    Candidate(String),
    Entry,
    Roles,
    Coverage,
    Shape,
    Exchange,
    WireType,
}
impl std::fmt::Display for BundleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "run-{self:?}")
    }
}
impl std::error::Error for BundleError {}
/// An exact translated-carrier coordinate. Public access is read-only through Bundle.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Step {
    pub role: usize,
    pub instruction: usize,
    pub anchor: Option<usize>,
}
#[derive(Clone, Debug)]
pub enum Segment {
    Action(usize),
    Loop {
        entries: Vec<usize>,
        body: Vec<Segment>,
        exits: Vec<usize>,
    },
}
#[derive(Clone, Debug)]
pub struct Bundle {
    pub(super) admitted: Admitted,
    pub(super) entry: String,
    pub(super) roles: Vec<ProgramRole>,
    pub(super) steps: Vec<Step>,
    pub(super) segments: Vec<Segment>,
}
impl Bundle {
    /// Authenticate exact bundle bytes against an independently trusted digest,
    /// then perform structural admission. The caller owns the digest's origin;
    /// hashing incoming bytes does not establish source correspondence.
    pub fn admit_pinned<B: Backend>(
        bytes: &[u8],
        expected_sha256: &[u8; 32],
        backend: &B,
        limits: BundleLimits,
    ) -> Result<Self, BundleError> {
        limits.validate()?;
        if bytes.len() > limits.bytes {
            return Err(BundleError::Limit);
        }
        let actual: [u8; 32] = Sha256::digest(bytes).into();
        if &actual != expected_sha256 {
            return Err(BundleError::Identity);
        }
        Self::admit(bytes, backend, limits)
    }
    /// Decode outer bounds, then let Runtime admit and type the exact candidate.
    /// Every schedule check runs before any runner or backend root is created.
    pub fn admit<B: Backend>(
        bytes: &[u8],
        backend: &B,
        limits: BundleLimits,
    ) -> Result<Self, BundleError> {
        limits.validate()?;
        let raw = super::decode::bundle(bytes, limits)?;
        if raw.format != "zkc.run/0" {
            return Err(BundleError::Format);
        }
        let admitted = admit_supplied(raw.candidate.as_bytes(), backend)
            .map_err(|e| BundleError::Candidate(e.to_string()))?;
        let layout = admitted
            .program_entry(&raw.entry)
            .map_err(|_| BundleError::Entry)?;
        let mut by_name: BTreeMap<_, _> = layout
            .into_iter()
            .map(|r| (r.entry.role.clone(), r))
            .collect();
        if raw.roles.is_empty() || raw.roles.len() != by_name.len() {
            return Err(BundleError::Roles);
        }
        let mut roles = Vec::new();
        roles
            .try_reserve_exact(raw.roles.len())
            .map_err(|_| BundleError::Limit)?;
        for name in raw.roles {
            roles.push(by_name.remove(&name).ok_or(BundleError::Roles)?);
        }
        let bundle = Self {
            admitted,
            entry: raw.entry,
            roles,
            steps: raw.steps,
            segments: raw.segments,
        };
        bundle.validate()?;
        Ok(bundle)
    }
    pub fn admitted(&self) -> &Admitted {
        &self.admitted
    }
    pub fn entry(&self) -> &str {
        &self.entry
    }
    pub fn roles(&self) -> &[ProgramRole] {
        &self.roles
    }
    /// Static preorder coordinates, not the sequence of runtime occurrences.
    pub fn steps(&self) -> &[Step] {
        &self.steps
    }
    /// Compact admitted schedule. Loop entries/exits index `steps()`.
    pub fn segments(&self) -> &[Segment] {
        &self.segments
    }

    pub fn action(&self, step: &Step) -> Option<&ProgramAction> {
        self.roles.get(step.role)?.actions.get(step.instruction)
    }
    fn validate(&self) -> Result<(), BundleError> {
        validate_preorder(&self.segments, self.steps.len())?;
        let mut cursors = vec![0; self.roles.len()];
        let mut names = BTreeSet::new();
        for r in &self.roles {
            if !names.insert(&r.entry.role)
                || !matches!(r.actions.last(), Some(ProgramAction::Finish))
                || r.actions[..r.actions.len() - 1]
                    .iter()
                    .any(|a| matches!(a, ProgramAction::Finish))
            {
                return Err(BundleError::Coverage);
            }
            for action in &r.actions {
                if let ProgramAction::Send { ty, .. } | ProgramAction::Receive { ty, .. } = action
                    && !has_native_wire(ty)
                {
                    return Err(BundleError::WireType);
                }
            }
        }
        for step in &self.steps {
            let cursor = cursors.get_mut(step.role).ok_or(BundleError::Coverage)?;
            if step.instruction != *cursor || self.action(step).is_none() {
                return Err(BundleError::Coverage);
            }
            *cursor += 1;
        }
        if cursors
            .iter()
            .zip(&self.roles)
            .any(|(n, r)| *n != r.actions.len())
        {
            return Err(BundleError::Coverage);
        }
        self.validate_segments()
    }
    pub(super) fn group(&self, group: &[Step]) -> Result<(), BundleError> {
        let local = |s: &Step| matches!(self.action(s), Some(ProgramAction::Local { .. }));
        let query = |s: &Step| matches!(self.action(s), Some(ProgramAction::Query { .. }));
        let returning = |s: &Step| matches!(self.action(s), Some(ProgramAction::ReturnIf { .. }));
        match group {
            [a] if local(a) || query(a) || returning(a) => Ok(()),
            [a, b] if local(a) && (local(b) || query(b) || returning(b)) && a.role == b.role => {
                Ok(())
            }
            [send, receive] => self.exchange(send, receive),
            [prefix, send, receive] if local(prefix) && prefix.role == send.role => {
                self.exchange(send, receive)
            }
            _ => Err(BundleError::Shape),
        }
    }
    fn exchange(&self, send: &Step, receive: &Step) -> Result<(), BundleError> {
        match (self.action(send), self.action(receive)) {
            (
                Some(ProgramAction::Send {
                    site,
                    schema,
                    peer,
                    ty,
                }),
                Some(ProgramAction::Receive {
                    site: rs,
                    schema: sc,
                    peer: rp,
                    ty: rt,
                }),
            ) if send.role != receive.role
                && site == rs
                && schema == sc
                && ty == rt
                && peer == &self.roles[receive.role].entry.role
                && rp == &self.roles[send.role].entry.role
                && self.roles[send.role].entry.instance
                    == self.roles[receive.role].entry.instance =>
            {
                Ok(())
            }
            _ => Err(BundleError::Exchange),
        }
    }
}

/// The executed tree must cover exactly the validated coordinate list. Check
/// this independently of decoder construction and role/action scope checks.
fn validate_preorder(segments: &[Segment], count: usize) -> Result<(), BundleError> {
    fn index(actual: usize, next: &mut usize, count: usize) -> Result<(), BundleError> {
        if actual != *next || *next >= count {
            return Err(BundleError::Coverage);
        }
        *next += 1;
        Ok(())
    }
    fn walk(
        nodes: &[Segment],
        next: &mut usize,
        count: usize,
        depth: usize,
    ) -> Result<(), BundleError> {
        if depth >= zkc_runtime::interactive::Limits::STACK_DEPTH {
            return Err(BundleError::Limit);
        }
        for node in nodes {
            match node {
                Segment::Action(i) => index(*i, next, count)?,
                Segment::Loop {
                    entries,
                    body,
                    exits,
                } => {
                    for i in entries {
                        index(*i, next, count)?;
                    }
                    walk(body, next, count, depth + 1)?;
                    for i in exits {
                        index(*i, next, count)?;
                    }
                }
            }
        }
        Ok(())
    }
    let mut next = 0;
    walk(segments, &mut next, count, 0)?;
    if next != count {
        return Err(BundleError::Coverage);
    }
    Ok(())
}

#[cfg(test)]
mod coverage_tests {
    use super::*;
    #[test]
    fn schedule_tree_covers_each_coordinate_once_in_preorder() {
        let nested = || {
            vec![
                Segment::Loop {
                    entries: vec![0, 1],
                    body: vec![
                        Segment::Action(2),
                        Segment::Loop {
                            entries: vec![3],
                            body: vec![Segment::Action(4)],
                            exits: vec![5],
                        },
                    ],
                    exits: vec![6, 7],
                },
                Segment::Action(8),
            ]
        };
        assert_eq!(validate_preorder(&nested(), 9), Ok(()));
        for bad in [
            vec![],
            vec![Segment::Action(0), Segment::Action(0)],
            vec![Segment::Action(1)],
        ] {
            assert_eq!(validate_preorder(&bad, 1), Err(BundleError::Coverage));
        }
        for (bad_index, expected_count) in [(3, 9), (2, 8), (2, 10)] {
            let mut bad = nested();
            let Segment::Loop { body, .. } = &mut bad[0] else {
                unreachable!()
            };
            body[0] = Segment::Action(bad_index);
            assert_eq!(
                validate_preorder(&bad, expected_count),
                Err(BundleError::Coverage)
            );
        }
    }
}
