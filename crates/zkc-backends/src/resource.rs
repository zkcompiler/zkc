use crate::{Policy, Result, Value, ark, exhausted, refused};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    sync::Arc,
};
use zkc_arkworks::{RandomSource, Scalar};
use zkc_runtime::interactive::{
    Frame, FrameExit, FrameKind, Identity, Type, Value as RuntimeValue,
};

/// Host-selected service authority scope. An instance restriction is exact:
/// a differently named child must receive a separately scoped resource or an
/// explicitly instance-unrestricted resource from the host.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Domain {
    pub owner: String,
    pub session: String,
    pub entry: String,
    pub instance: Option<String>,
}
impl Domain {
    pub fn new(owner: &str, session: &str, entry: &str, instance: Option<&str>) -> Self {
        Self {
            owner: owner.into(),
            session: session.into(),
            entry: entry.into(),
            instance: instance.map(Into::into),
        }
    }
    pub(crate) fn matches(&self, f: &Frame) -> bool {
        self.owner == f.role()
            && self.session == f.origin().session
            && self.entry == f.origin().entry
            && self
                .instance
                .as_ref()
                .is_none_or(|s| *s == f.origin().instance)
    }
    fn valid(&self) -> bool {
        [&self.owner, &self.session, &self.entry]
            .into_iter()
            .chain(self.instance.iter())
            .all(|s| {
                !s.is_empty()
                    && s.len() <= 128
                    && s.bytes()
                        .all(|b| b.is_ascii_alphanumeric() || b"_.-".contains(&b))
            })
    }
}
/// Nominal logical unit with an authenticated owner, but no semantic payload.
/// Construction is private to the logical issuance operation.
#[derive(Clone, Debug)]
pub struct LogicalUnit {
    token: Capability,
}
impl LogicalUnit {
    pub fn capability(&self) -> &Capability {
        &self.token
    }
    pub fn domain(&self) -> zkc_runtime::interactive::ResourceDomain {
        self.token.resource_domain.expect("issued logical unit")
    }
}
struct Authority;
struct Seal;
/// Opaque authenticated in-process handle. Cloning copies the handle only.
/// Safe Rust cannot construct an authority or alter an issued generation.
/// ```compile_fail
/// use zkc_backends::Capability;
/// let forged = Capability { id: 0, generation: 0 };
/// ```
#[derive(Clone)]
pub struct Capability {
    resource_domain: Option<zkc_runtime::interactive::ResourceDomain>,
    identity: Identity,
    authority: Arc<Authority>,
    seal: Arc<Seal>,
    id: u64,
    generation: u64,
}
impl Capability {
    pub fn resource_domain(&self) -> Option<zkc_runtime::interactive::ResourceDomain> {
        self.resource_domain
    }
    pub fn identity(&self) -> Identity {
        self.identity
    }
    /// Identifier within this backend's issuance authority. It is not a global
    /// identity or a credential and cannot reconstruct an authenticated handle.
    pub fn issued_id(&self) -> u64 {
        self.id
    }
    /// Generation stored in this handle, which can be stale. `observe` returns
    /// the authoritative generation after completed or failed consumption.
    pub fn generation(&self) -> u64 {
        self.generation
    }
}
impl fmt::Debug for Capability {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Capability")
            .field("id", &self.id)
            .field("generation", &self.generation)
            .finish_non_exhaustive()
    }
}
/// Secret-free authoritative state, including failed consuming attempts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapabilityObservation {
    pub issued_id: u64,
    pub generation: u64,
    /// Logical draw debit: vector length, or one for scalar/nonce/transcript
    /// consumes (including their exhausted-budget attempts). This is not raw
    /// CSPRNG block usage; refused vector preflight contributes zero.
    pub draw_count: u64,
    pub budget: u64,
    pub stage: &'static str,
}
enum Source {
    Os(Box<RandomSource>),
    #[cfg(feature = "test-utils")]
    Tape(std::collections::VecDeque<Scalar>),
}
impl Source {
    fn scalar(&mut self) -> Result<Scalar> {
        match self {
            Self::Os(r) => Ok(r.scalar()),
            #[cfg(feature = "test-utils")]
            Self::Tape(t) => t.pop_front().ok_or_else(|| exhausted("test-tape")),
        }
    }
}
enum State {
    ResourceUnit(zkc_runtime::interactive::ResourceDomain),
    Bn254Rng(Box<RandomSource>),
    #[cfg(feature = "test-utils")]
    Bn254Tape(std::collections::VecDeque<crate::Bn254Scalar>),
    ExtensionRng(Box<rand::rngs::StdRng>),
    RistrettoRng(Box<rand::rngs::StdRng>),
    #[cfg(feature = "test-utils")]
    RistrettoTape(std::collections::VecDeque<crate::RistrettoScalar>),
    RistrettoIssuedNonce(crate::RistrettoScalar),
    RistrettoReadyNonce(crate::RistrettoScalar),
    RistrettoSpentNonce,
    Rng(Source),
    Transcript(Box<crate::transcript::Transcript>, Identity),
    IssuedNonce(Scalar),
    ReadyNonce(Scalar),
    SpentNonce,
}
impl State {
    fn identity(&self) -> Identity {
        match self {
            Self::ResourceUnit(_) => Identity::None,
            Self::Bn254Rng(_) => Identity::Bn254Fr,
            #[cfg(feature = "test-utils")]
            Self::Bn254Tape(_) => Identity::Bn254Fr,
            Self::Transcript(_, suite) => *suite,
            Self::ExtensionRng(_) => Identity::KoalaBearExt8,
            Self::RistrettoRng(_)
            | Self::RistrettoIssuedNonce(_)
            | Self::RistrettoReadyNonce(_)
            | Self::RistrettoSpentNonce => Identity::Ristretto255Scalar,
            #[cfg(feature = "test-utils")]
            Self::RistrettoTape(_) => Identity::Ristretto255Scalar,
            _ => Identity::Bls12381Fr,
        }
    }
    fn ty(&self) -> Type {
        match self {
            Self::ResourceUnit(_) => Type::ResourceUnit,
            Self::Bn254Rng(_) | Self::Rng(_) | Self::RistrettoRng(_) | Self::ExtensionRng(_) => {
                Type::Rng
            }
            #[cfg(feature = "test-utils")]
            Self::Bn254Tape(_) | Self::RistrettoTape(_) => Type::Rng,
            Self::Transcript(_, _) => Type::Transcript,
            _ => Type::Nonce,
        }
    }
    fn stage(&self) -> &'static str {
        match self {
            Self::ResourceUnit(_) => "resource_unit",
            Self::Bn254Rng(_) | Self::Rng(_) | Self::RistrettoRng(_) | Self::ExtensionRng(_) => {
                "rng"
            }
            #[cfg(feature = "test-utils")]
            Self::Bn254Tape(_) | Self::RistrettoTape(_) => "rng",
            Self::Transcript(_, _) => "transcript",
            Self::IssuedNonce(_) | Self::RistrettoIssuedNonce(_) => "issued",
            Self::ReadyNonce(_) | Self::RistrettoReadyNonce(_) => "committed",
            Self::SpentNonce | Self::RistrettoSpentNonce => "spent",
        }
    }
}
struct Slot {
    seal: Arc<Seal>,
    domain: Domain,
    generation: u64,
    draws: u64,
    budget: u64,
    state: State,
}
struct View {
    frame: Frame,
    slots: BTreeSet<u64>,
}
pub(crate) struct Resources {
    authority: Arc<Authority>,
    slots: BTreeMap<u64, Slot>,
    frames: Vec<View>,
    next: u64,
    limit: usize,
}
impl Resources {
    pub fn new(policy: Policy) -> Self {
        Self {
            authority: Arc::new(Authority),
            slots: BTreeMap::new(),
            frames: Vec::new(),
            next: 0,
            limit: policy.max_capabilities,
        }
    }
    fn issue(&mut self, domain: Domain, budget: u64, state: State) -> Result<Capability> {
        if !domain.valid() {
            return Err(refused("capability-domain"));
        }
        if !self.frames.is_empty() {
            return Err(refused("issue-during-frame"));
        }
        self.allocate(domain, budget, state)
    }
    fn allocate(&mut self, domain: Domain, budget: u64, state: State) -> Result<Capability> {
        if self.slots.len() >= self.limit {
            return Err(exhausted("capability-slots"));
        }
        let id = self.next;
        self.next = id
            .checked_add(1)
            .ok_or_else(|| exhausted("capability-id"))?;
        let resource_domain = match &state {
            State::ResourceUnit(domain) => Some(*domain),
            _ => None,
        };
        let identity = state.identity();
        let seal = Arc::new(Seal);
        self.slots.insert(
            id,
            Slot {
                seal: seal.clone(),
                domain,
                generation: 0,
                draws: 0,
                budget,
                state,
            },
        );
        Ok(Capability {
            resource_domain,
            identity,
            authority: self.authority.clone(),
            seal,
            id,
            generation: 0,
        })
    }
    /// No payload or provider state: only affine issuance and role ownership.
    pub fn create_unit(
        &mut self,
        frame: &Frame,
        domain: zkc_runtime::interactive::ResourceDomain,
    ) -> Result<Value> {
        self.active(frame)?;
        let owner = Domain::new(
            frame.role(),
            &frame.origin().session,
            &frame.origin().entry,
            None,
        );
        let token = self.allocate(owner, 0, State::ResourceUnit(domain))?;
        self.frames
            .last_mut()
            .expect("active")
            .slots
            .insert(token.id);
        Ok(Value::ResourceUnit(LogicalUnit { token }))
    }
    pub fn pass_unit(&mut self, frame: &Frame, token: &Capability) -> Result<Value> {
        let slot = self.transition(frame, token, Type::ResourceUnit, 0)?;
        let mut next = token.clone();
        next.generation = slot.generation;
        Ok(Value::ResourceUnit(LogicalUnit { token: next }))
    }
    pub fn consume_unit(&mut self, frame: &Frame, token: &Capability) -> Result<()> {
        self.active_slot(frame, token, Type::ResourceUnit)?;
        self.slots.remove(&token.id);
        self.frames
            .last_mut()
            .expect("active")
            .slots
            .remove(&token.id);
        Ok(())
    }
    pub fn issue_transcript(&mut self, domain: Domain, budget: u64, root: &[u8]) -> Result<Value> {
        self.issue_transcript_for(Identity::Merlin3Fr64Be, domain, budget, root)
    }
    pub fn issue_transcript_for(
        &mut self,
        suite: Identity,
        domain: Domain,
        budget: u64,
        root: &[u8],
    ) -> Result<Value> {
        if !matches!(
            suite,
            Identity::Merlin3Fr64Be
                | Identity::Merlin3KoalaBearExt8
                | Identity::Merlin3Ristretto64Le
                | Identity::Spongefish074KeccakFr64Be
        ) {
            return Err(refused("transcript-suite"));
        }
        // No source/descriptor correspondence is inferred from this decoder.
        zkc_runtime::logical::decode_tree(root).map_err(|_| refused("transcript-root"))?;
        let transcript = crate::transcript::Transcript::new(suite, root);
        Ok(Value::Transcript(self.issue(
            domain,
            budget,
            State::Transcript(Box::new(transcript), suite),
        )?))
    }
    pub fn transcript_observe(
        &mut self,
        f: &Frame,
        t: &Capability,
        origin: &[u8],
        value: &[u8],
    ) -> Result<Capability> {
        let slot = self.consume(f, t, Type::Transcript)?;
        let State::Transcript(transcript, _) = &mut slot.state else {
            unreachable!("validated kind")
        };
        transcript.append_message(b"origin", origin);
        transcript.append_message(b"value", value);
        let mut next = t.clone();
        next.generation = slot.generation;
        Ok(next)
    }
    pub fn transcript_challenge_value(
        &mut self,
        f: &Frame,
        t: &Capability,
        origin: &[u8],
    ) -> Result<(Value, Capability)> {
        let slot = self.consume(f, t, Type::Transcript)?;
        let State::Transcript(transcript, suite) = &mut slot.state else {
            unreachable!("validated kind")
        };
        transcript.append_message(b"origin", origin);
        let mut bytes = [0; 64];
        if *suite != Identity::Merlin3KoalaBearExt8 {
            transcript.challenge_bytes(b"challenge", &mut bytes);
        }
        let value = match suite {
            Identity::Merlin3KoalaBearExt8 => {
                Value::KoalaBearExt8Field(crate::sampling::extension(|| {
                    let mut bytes = [0; 64];
                    transcript.challenge_bytes(b"challenge", &mut bytes);
                    bytes
                })?)
            }
            Identity::Merlin3Fr64Be | Identity::Spongefish074KeccakFr64Be => {
                Value::Field(zkc_arkworks::scalar_from_wide_be(&bytes))
            }
            Identity::Merlin3Ristretto64Le => {
                Value::RistrettoField(crate::RistrettoScalar::from_bytes_mod_order_wide(&bytes))
            }
            _ => unreachable!("issued suite"),
        };
        let mut next = t.clone();
        next.generation = slot.generation;
        Ok((value, next))
    }
    pub fn transcript_index(
        &mut self,
        f: &Frame,
        t: &Capability,
        origin: &[u8],
        bound: u64,
    ) -> Result<(Value, Capability)> {
        if t.identity != Identity::Merlin3KoalaBearExt8 {
            return Err(refused("query-suite"));
        }
        crate::sampling::index_bound(bound)?;
        let slot = self.consume(f, t, Type::Transcript)?;
        let State::Transcript(transcript, _) = &mut slot.state else {
            unreachable!("validated kind")
        };
        transcript.append_message(b"origin", origin);
        transcript.append_message(b"query-bound", &bound.to_le_bytes());
        let mut bytes = [0; 64];
        transcript.challenge_bytes(b"query-index", &mut bytes);
        let mut next = t.clone();
        next.generation = slot.generation;
        Ok((Value::Index(crate::sampling::index(&bytes, bound)?), next))
    }
    pub fn draw_index(
        &mut self,
        f: &Frame,
        t: &Capability,
        bound: u64,
    ) -> Result<(Value, Capability)> {
        use rand::RngCore;
        if t.identity != Identity::KoalaBearExt8 {
            return Err(refused("query-rng"));
        }
        crate::sampling::index_bound(bound)?;
        let slot = self.consume(f, t, Type::Rng)?;
        let State::ExtensionRng(rng) = &mut slot.state else {
            unreachable!("validated RNG")
        };
        let mut bytes = [0; 64];
        rng.fill_bytes(&mut bytes);
        let mut next = t.clone();
        next.generation = slot.generation;
        Ok((Value::Index(crate::sampling::index(&bytes, bound)?), next))
    }
    pub fn issue_rng_for(&mut self, field: Identity, domain: Domain, budget: u64) -> Result<Value> {
        use rand::SeedableRng;
        match field {
            Identity::Bn254Fr => Ok(Value::Rng(self.issue(
                domain,
                budget,
                State::Bn254Rng(Box::new(RandomSource::from_os().map_err(crate::ark)?)),
            )?)),
            Identity::Bls12381Fr => self.issue_rng(domain, budget),
            Identity::KoalaBearExt8 => {
                let rng = rand::rngs::StdRng::from_rng(rand::rngs::OsRng)
                    .map_err(|_| exhausted("entropy-unavailable"))?;
                Ok(Value::Rng(self.issue(
                    domain,
                    budget,
                    State::ExtensionRng(Box::new(rng)),
                )?))
            }
            Identity::Ristretto255Scalar => {
                let rng = rand::rngs::StdRng::from_rng(rand::rngs::OsRng)
                    .map_err(|_| exhausted("entropy-unavailable"))?;
                Ok(Value::Rng(self.issue(
                    domain,
                    budget,
                    State::RistrettoRng(Box::new(rng)),
                )?))
            }
            _ => Err(refused("rng-field")),
        }
    }
    pub fn issue_nonce_for(
        &mut self,
        field: Identity,
        domain: Domain,
        budget: u64,
    ) -> Result<Value> {
        match field {
            Identity::Bls12381Fr => self.issue_nonce(domain, budget),
            Identity::Ristretto255Scalar => {
                use rand::SeedableRng;
                let mut rng = rand::rngs::StdRng::from_rng(rand::rngs::OsRng)
                    .map_err(|_| exhausted("entropy-unavailable"))?;
                let k = crate::RistrettoScalar::random(&mut rng);
                Ok(Value::Nonce(self.issue(
                    domain,
                    budget,
                    State::RistrettoIssuedNonce(k),
                )?))
            }
            _ => Err(refused("nonce-field")),
        }
    }
    #[cfg(feature = "test-utils")]
    pub fn test_ristretto_rng(
        &mut self,
        domain: Domain,
        budget: u64,
        seed: [u8; 32],
    ) -> Result<Value> {
        use rand::SeedableRng;
        Ok(Value::Rng(self.issue(
            domain,
            budget,
            State::RistrettoRng(Box::new(rand::rngs::StdRng::from_seed(seed))),
        )?))
    }
    #[cfg(feature = "test-utils")]
    pub fn test_ristretto_tape(
        &mut self,
        domain: Domain,
        budget: u64,
        tape: Vec<crate::RistrettoScalar>,
    ) -> Result<Value> {
        Ok(Value::Rng(self.issue(
            domain,
            budget,
            State::RistrettoTape(tape.into()),
        )?))
    }
    #[cfg(feature = "test-utils")]
    pub fn test_ristretto_nonce(
        &mut self,
        domain: Domain,
        budget: u64,
        k: crate::RistrettoScalar,
    ) -> Result<Value> {
        Ok(Value::Nonce(self.issue(
            domain,
            budget,
            State::RistrettoIssuedNonce(k),
        )?))
    }
    #[cfg(feature = "test-utils")]
    pub fn test_bn254_tape(
        &mut self,
        domain: Domain,
        budget: u64,
        tape: Vec<crate::Bn254Scalar>,
    ) -> Result<Value> {
        Ok(Value::Rng(self.issue(
            domain,
            budget,
            State::Bn254Tape(tape.into()),
        )?))
    }
    pub fn draw_vector(
        &mut self,
        f: &Frame,
        t: &Capability,
        n: usize,
    ) -> Result<(Value, Capability)> {
        let draws = u64::try_from(n).map_err(|_| exhausted("draw-counter"))?;
        let (value, generation) = match t.identity {
            Identity::Bn254Fr => {
                let mut values = crate::kernels::arithmetic::reserve(n)?;
                let slot = self.transition(f, t, Type::Rng, draws)?;
                for _ in 0..n {
                    values.push(match &mut slot.state {
                        State::Bn254Rng(rng) => rng.bn254_scalar(),
                        #[cfg(feature = "test-utils")]
                        State::Bn254Tape(tape) => {
                            tape.pop_front().ok_or_else(|| exhausted("test-tape"))?
                        }
                        _ => unreachable!("validated RNG domain"),
                    });
                }
                (Value::Bn254Vector(values.into()), slot.generation)
            }
            Identity::KoalaBearExt8 => {
                use rand::RngCore;
                let mut values = crate::kernels::arithmetic::reserve(n)?;
                let slot = self.transition(f, t, Type::Rng, draws)?;
                let State::ExtensionRng(rng) = &mut slot.state else {
                    unreachable!("validated RNG")
                };
                for _ in 0..n {
                    values.push(crate::sampling::extension(|| {
                        let mut bytes = [0; 64];
                        rng.fill_bytes(&mut bytes);
                        bytes
                    })?);
                }
                (Value::KoalaBearExt8Vector(values.into()), slot.generation)
            }
            Identity::Bls12381Fr => {
                let mut values = crate::kernels::arithmetic::reserve(n)?;
                let slot = self.transition(f, t, Type::Rng, draws)?;
                let State::Rng(source) = &mut slot.state else {
                    unreachable!("validated RNG domain")
                };
                for _ in 0..n {
                    values.push(source.scalar()?);
                }
                (Value::Vector(values.into()), slot.generation)
            }
            Identity::Ristretto255Scalar => {
                let mut values = crate::kernels::arithmetic::reserve(n)?;
                let slot = self.transition(f, t, Type::Rng, draws)?;
                for _ in 0..n {
                    values.push(match &mut slot.state {
                        State::RistrettoRng(rng) => crate::RistrettoScalar::random(rng.as_mut()),
                        #[cfg(feature = "test-utils")]
                        State::RistrettoTape(tape) => {
                            tape.pop_front().ok_or_else(|| exhausted("test-tape"))?
                        }
                        _ => unreachable!("validated RNG domain"),
                    });
                }
                (Value::RistrettoVector(values.into()), slot.generation)
            }
            _ => return Err(refused("capability-identity")),
        };
        let mut next = t.clone();
        next.generation = generation;
        Ok((value, next))
    }
    pub fn draw_value(&mut self, f: &Frame, t: &Capability) -> Result<(Value, Capability)> {
        if t.identity == Identity::Bls12381Fr {
            return self.draw(f, t).map(|(v, t)| (Value::Field(v), t));
        }
        let slot = self.consume(f, t, Type::Rng)?;
        let value = match &mut slot.state {
            State::Bn254Rng(rng) => Value::Bn254Field(rng.bn254_scalar()),
            #[cfg(feature = "test-utils")]
            State::Bn254Tape(tape) => {
                Value::Bn254Field(tape.pop_front().ok_or_else(|| exhausted("test-tape"))?)
            }
            State::ExtensionRng(rng) => {
                use rand::RngCore;
                Value::KoalaBearExt8Field(crate::sampling::extension(|| {
                    let mut bytes = [0; 64];
                    rng.fill_bytes(&mut bytes);
                    bytes
                })?)
            }
            State::RistrettoRng(rng) => {
                Value::RistrettoField(crate::RistrettoScalar::random(rng.as_mut()))
            }
            #[cfg(feature = "test-utils")]
            State::RistrettoTape(tape) => {
                Value::RistrettoField(tape.pop_front().ok_or_else(|| exhausted("test-tape"))?)
            }
            _ => return Err(refused("capability-identity")),
        };
        let mut next = t.clone();
        next.generation = slot.generation;
        Ok((value, next))
    }
    pub fn commit_ristretto_nonce(
        &mut self,
        f: &Frame,
        t: &Capability,
    ) -> Result<(crate::RistrettoScalar, Capability)> {
        if t.identity != Identity::Ristretto255Scalar {
            return Err(refused("capability-identity"));
        }
        let s = self.consume(f, t, Type::Nonce)?;
        let State::RistrettoIssuedNonce(k) =
            std::mem::replace(&mut s.state, State::RistrettoSpentNonce)
        else {
            return Err(refused("nonce-stage"));
        };
        s.state = State::RistrettoReadyNonce(k);
        let mut next = t.clone();
        next.generation = s.generation;
        Ok((k, next))
    }
    pub fn respond_ristretto(
        &mut self,
        f: &Frame,
        t: &Capability,
        x: crate::RistrettoScalar,
        c: crate::RistrettoScalar,
    ) -> Result<crate::RistrettoScalar> {
        if t.identity != Identity::Ristretto255Scalar {
            return Err(refused("capability-identity"));
        }
        let s = self.consume(f, t, Type::Nonce)?;
        let State::RistrettoReadyNonce(k) =
            std::mem::replace(&mut s.state, State::RistrettoSpentNonce)
        else {
            return Err(refused("nonce-stage"));
        };
        Ok(k + c * x)
    }
    pub fn issue_rng(&mut self, domain: Domain, budget: u64) -> Result<Value> {
        let source = Source::Os(Box::new(RandomSource::from_os().map_err(ark)?));
        Ok(Value::Rng(self.issue(
            domain,
            budget,
            State::Rng(source),
        )?))
    }
    pub fn issue_nonce(&mut self, domain: Domain, budget: u64) -> Result<Value> {
        let k = RandomSource::from_os().map_err(ark)?.scalar();
        Ok(Value::Nonce(self.issue(
            domain,
            budget,
            State::IssuedNonce(k),
        )?))
    }
    #[cfg(feature = "test-utils")]
    pub fn test_rng(&mut self, domain: Domain, budget: u64, seed: [u8; 32]) -> Result<Value> {
        Ok(Value::Rng(self.issue(
            domain,
            budget,
            State::Rng(Source::Os(Box::new(RandomSource::for_testing(seed)))),
        )?))
    }
    #[cfg(feature = "test-utils")]
    pub fn test_tape(&mut self, domain: Domain, budget: u64, tape: Vec<Scalar>) -> Result<Value> {
        Ok(Value::Rng(self.issue(
            domain,
            budget,
            State::Rng(Source::Tape(tape.into())),
        )?))
    }
    #[cfg(feature = "test-utils")]
    pub fn test_nonce(&mut self, domain: Domain, budget: u64, k: Scalar) -> Result<Value> {
        Ok(Value::Nonce(self.issue(
            domain,
            budget,
            State::IssuedNonce(k),
        )?))
    }
    fn slot(&self, token: &Capability) -> Result<&Slot> {
        if !Arc::ptr_eq(&token.authority, &self.authority) {
            return Err(refused("capability-authority"));
        }
        let slot = self
            .slots
            .get(&token.id)
            .ok_or_else(|| refused("capability-unissued"))?;
        if !Arc::ptr_eq(&token.seal, &slot.seal) {
            return Err(refused("capability-forged"));
        }
        Ok(slot)
    }
    pub fn validate(&self, token: &Capability, ty: Type) -> Result<()> {
        let slot = self.slot(token)?;
        if slot.generation != token.generation {
            return Err(refused("capability-stale"));
        }
        if slot.state.identity() != token.identity {
            return Err(refused("capability-identity"));
        }
        if slot.state.ty() != ty {
            return Err(refused("capability-kind"));
        }
        Ok(())
    }
    pub fn observe(&self, token: &Capability) -> Result<CapabilityObservation> {
        // An old authentic handle may observe its own current public counters.
        let s = self.slot(token)?;
        Ok(CapabilityObservation {
            issued_id: token.id,
            generation: s.generation,
            draw_count: s.draws,
            budget: s.budget,
            stage: s.state.stage(),
        })
    }
    pub fn frame_count(&self) -> usize {
        self.frames.len()
    }
    /// Logical resource units still held, for residual-state comparison with
    /// an independent reference.
    pub fn live_resource_units(&self) -> usize {
        self.slots
            .values()
            .filter(|s| s.state.ty() == Type::ResourceUnit)
            .count()
    }
    /// Host revocation, never an operation available inside a protocol frame.
    /// An authentic old generation may retire its own slot after a failed
    /// consuming call. This grants no successor consume authority. IDs are
    /// never reused and unrelated resources are untouched.
    pub fn retire(&mut self, token: &Capability) -> Result<CapabilityObservation> {
        if !self.frames.is_empty() {
            return Err(refused("retire-during-frame"));
        }
        let observation = self.observe(token)?;
        self.slots.remove(&token.id);
        Ok(observation)
    }
    pub fn active(&self, f: &Frame) -> Result<()> {
        if !self.frames.last().is_some_and(|v| same_frame(&v.frame, f)) {
            return Err(refused("inactive-frame"));
        }
        Ok(())
    }
    fn tokens(
        &self,
        f: &Frame,
        values: &[Value],
        allowed: Option<&BTreeSet<u64>>,
    ) -> Result<BTreeSet<u64>> {
        let mut ids = BTreeSet::new();
        for v in values.iter().flat_map(Value::active_leaves) {
            if let Some(t) = v.capability() {
                self.validate(t, v.ty())?;
                if !self.slot(t)?.domain.matches(f) {
                    return Err(refused("capability-domain"));
                }
                if !ids.insert(t.id) {
                    return Err(refused("capability-alias"));
                }
                if allowed.is_some_and(|a| !a.contains(&t.id)) {
                    return Err(refused("capability-out-of-view"));
                }
            }
        }
        Ok(ids)
    }
    pub fn enter(&mut self, f: &Frame, args: &[Value]) -> Result<()> {
        if self.frames.len() >= 64 {
            return Err(exhausted("frame-depth"));
        }
        if f.inputs().len() != args.len()
            || f.inputs()
                .iter()
                .zip(args)
                .any(|((_, t), v)| *t != v.physical_type())
        {
            return Err(refused("frame-arguments"));
        }
        let allowed = match self.frames.last() {
            None if f.parent().is_none() && matches!(f.kind(), FrameKind::Entry) => None,
            Some(parent)
                if f.parent() == Some(parent.frame.id())
                    && !matches!(f.kind(), FrameKind::Entry) =>
            {
                if f.role() != parent.frame.role()
                    || f.origin().session != parent.frame.origin().session
                    || f.origin().entry != parent.frame.origin().entry
                    || f.origin().format != parent.frame.origin().format
                {
                    return Err(refused("frame-domain"));
                }
                Some(&parent.slots)
            }
            _ => return Err(refused("frame-parent")),
        };
        if self.frames.iter().any(|v| v.frame.id() == f.id()) {
            return Err(refused("frame-duplicate"));
        }
        let slots = self.tokens(f, args, allowed)?;
        self.frames.push(View {
            frame: f.clone(),
            slots,
        });
        Ok(())
    }
    pub fn leave(&mut self, f: &Frame, exit: FrameExit, outputs: &[Value]) -> Result<()> {
        let Some(index) = self.frames.iter().position(|v| same_frame(&v.frame, f)) else {
            return Err(refused("frame-missing"));
        };
        if index + 1 != self.frames.len() {
            return Err(refused("frame-exit-order"));
        }
        let result = if exit == FrameExit::Returned {
            self.tokens(f, outputs, Some(&self.frames[index].slots))
                .map(|_| ())
        } else if !outputs.is_empty() {
            Err(refused("stopped-frame-outputs"))
        } else {
            Ok(())
        };
        let view = self.frames.pop().expect("top frame"); // Cleanup even on refusal.
        // A locally created logical permission can leave only through an explicit
        // affine result. Dropped units are retired; returned units enter the parent view.
        let returned: BTreeSet<_> = if result.is_ok() && exit == FrameExit::Returned {
            outputs
                .iter()
                .flat_map(Value::active_leaves)
                .filter_map(|v| match v {
                    Value::ResourceUnit(t) => Some(t.token.id),
                    _ => None,
                })
                .collect()
        } else {
            BTreeSet::new()
        };
        for id in view.slots {
            if self
                .slots
                .get(&id)
                .is_some_and(|s| s.state.ty() == Type::ResourceUnit)
                && !returned.contains(&id)
            {
                self.slots.remove(&id);
            }
        }
        if let Some(parent) = self.frames.last_mut() {
            parent.slots.extend(returned);
        }
        result
    }
    fn active_slot(&mut self, f: &Frame, t: &Capability, ty: Type) -> Result<&mut Slot> {
        self.active(f)?;
        self.validate(t, ty)?;
        if !self.frames.last().expect("active").slots.contains(&t.id) {
            return Err(refused("capability-out-of-view"));
        }
        if !self.slot(t)?.domain.matches(f) {
            return Err(refused("capability-domain"));
        }
        Ok(self.slots.get_mut(&t.id).expect("authenticated slot"))
    }
    /// Preflight the entire debit, then commit one capability generation.
    /// Entropy acquisition after this transition cannot restore the old handle.
    fn transition(&mut self, f: &Frame, t: &Capability, ty: Type, draws: u64) -> Result<&mut Slot> {
        let s = self.active_slot(f, t, ty)?;
        let budget = s
            .budget
            .checked_sub(draws)
            .ok_or_else(|| exhausted("resource-budget"))?;
        let generation = s
            .generation
            .checked_add(1)
            .filter(|g| *g != u64::MAX)
            .ok_or_else(|| exhausted("generation"))?;
        let draw_count = s
            .draws
            .checked_add(draws)
            .ok_or_else(|| exhausted("draw-counter"))?;
        s.generation = generation;
        s.draws = draw_count;
        s.budget = budget;
        Ok(s)
    }
    fn consume(&mut self, f: &Frame, t: &Capability, ty: Type) -> Result<&mut Slot> {
        let s = self.active_slot(f, t, ty)?;
        // No wrapping or reset. Never return a successor at max generation.
        s.generation = s
            .generation
            .checked_add(1)
            .ok_or_else(|| exhausted("generation"))?;
        s.draws = s
            .draws
            .checked_add(1)
            .ok_or_else(|| exhausted("draw-counter"))?;
        if s.generation == u64::MAX {
            return Err(exhausted("generation"));
        }
        if s.budget == 0 {
            return Err(exhausted("resource-budget"));
        }
        s.budget -= 1;
        Ok(s)
    }
    pub fn draw(&mut self, f: &Frame, t: &Capability) -> Result<(Scalar, Capability)> {
        if t.identity != Identity::Bls12381Fr {
            return Err(refused("capability-identity"));
        }
        let slot = self.consume(f, t, Type::Rng)?;
        let generation = slot.generation;
        let State::Rng(source) = &mut slot.state else {
            unreachable!("validated kind")
        };
        let value = source.scalar()?;
        let mut next = t.clone();
        next.generation = generation;
        Ok((value, next))
    }
    pub fn commit_nonce(&mut self, f: &Frame, t: &Capability) -> Result<(Scalar, Capability)> {
        if t.identity != Identity::Bls12381Fr {
            return Err(refused("capability-identity"));
        }
        let s = self.consume(f, t, Type::Nonce)?;
        let previous = std::mem::replace(&mut s.state, State::SpentNonce);
        let State::IssuedNonce(k) = previous else {
            return Err(refused("nonce-stage"));
        };
        s.state = State::ReadyNonce(k);
        let mut next = t.clone();
        next.generation = s.generation;
        Ok((k, next))
    }
    pub fn respond(&mut self, f: &Frame, t: &Capability, x: Scalar, c: Scalar) -> Result<Scalar> {
        if t.identity != Identity::Bls12381Fr {
            return Err(refused("capability-identity"));
        }
        let s = self.consume(f, t, Type::Nonce)?;
        let previous = std::mem::replace(&mut s.state, State::SpentNonce);
        let State::ReadyNonce(k) = previous else {
            return Err(refused("nonce-stage"));
        };
        Ok(k + c * x)
    }
}
fn same_frame(a: &Frame, b: &Frame) -> bool {
    a.id() == b.id()
        && a.parent() == b.parent()
        && a.role() == b.role()
        && a.origin() == b.origin()
        && a.kind() == b.kind()
        && a.inputs() == b.inputs()
        && a.parameters() == b.parameters()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn retirement_releases_capacity_without_rewinding_issuance() {
        let mut store = Resources::new(Policy {
            max_capabilities: 1,
            ..Policy::default()
        });
        let domain = Domain::new("P", "session", "main", None);
        let first = store.issue_rng(domain.clone(), 1).unwrap();
        assert_eq!(
            store.issue_rng(domain.clone(), 1).unwrap_err().code,
            "exhausted:capability-slots"
        );
        let token = first.capability().unwrap();
        let mut forged = token.clone();
        forged.seal = Arc::new(Seal);
        assert_eq!(
            store.retire(&forged).unwrap_err().code,
            "refused:capability-forged"
        );
        store.retire(token).unwrap();
        let second = store.issue_rng(domain, 1).unwrap();
        assert!(second.capability().unwrap().id > token.id);
        assert_eq!(
            store.validate(token, Type::Rng).unwrap_err().code,
            "refused:capability-unissued"
        );
    }
    #[test]
    fn forged_numeric_ids_and_per_slot_seals_do_not_authenticate() {
        let mut store = Resources::new(Policy::default());
        let domain = Domain::new("P", "s", "entry", None);
        let a = store.issue_rng(domain.clone(), 2).unwrap();
        let b = store.issue_rng(domain, 2).unwrap();
        let mut forged = a.capability().unwrap().clone();
        forged.id = b.capability().unwrap().id;
        assert_eq!(
            store.validate(&forged, Type::Rng).unwrap_err().code,
            "refused:capability-forged"
        );
        forged.id = 1000;
        assert_eq!(
            store.validate(&forged, Type::Rng).unwrap_err().code,
            "refused:capability-unissued"
        );
        forged = a.capability().unwrap().clone();
        forged.seal = Arc::new(Seal);
        assert_eq!(
            store.validate(&forged, Type::Rng).unwrap_err().code,
            "refused:capability-forged"
        );
        forged = a.capability().unwrap().clone();
        forged.authority = Arc::new(Authority);
        assert_eq!(
            store.validate(&forged, Type::Rng).unwrap_err().code,
            "refused:capability-authority"
        );
        forged = a.capability().unwrap().clone();
        forged.generation = 1;
        assert_eq!(
            store.validate(&forged, Type::Rng).unwrap_err().code,
            "refused:capability-stale"
        );
        assert_eq!(
            store
                .validate(a.capability().unwrap(), Type::Nonce)
                .unwrap_err()
                .code,
            "refused:capability-kind"
        );
        assert_eq!(
            store.observe(a.capability().unwrap()).unwrap().generation,
            0
        );
        assert_eq!(
            store.observe(b.capability().unwrap()).unwrap().generation,
            0
        );
    }
}
