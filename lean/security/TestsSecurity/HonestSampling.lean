import ZkcSecurity.FiatShamir.SampledCompiled
import ZkcSecurity.Domains.PrimeField

/-! Controls for the actual joint ideal handler. The finite field is an ideal
interpretation of the matching nominal `f7` contract, not native entropy.
These runtime controls do not claim source admission for a new protocol. -/

set_option autoImplicit false
namespace TestsSecurity.HonestSampling
open Zkc.Source Zkc.Construction ZkcSecurity.FiatShamir OracleComp OracleSpec

abbrev model := ZkcSecurity.Domains.PrimeField.model 7
abbrev carriers := model.toCarriers
abbrev F := ZMod 7

noncomputable instance : SampleableType F := SampleableType.ofFintype F
noncomputable instance samples : (event : Domain.Event carriers) → SampleableType (Domain.Raw event) :=
  ZkcSecurity.Domains.PrimeField.rawSampleable 7
noncomputable instance : DecidableEq (Domain.Event carriers) := Classical.decEq _

def context : Context :=
  ⟨"sampling-control", ["prover", "verifier"], 0, 1, 4,
    "random.f7/0", some (.draw "f7"), "ideal", []⟩
def port : ServicePort := ⟨"service_3", "prover", 3, 3, "random.f7/0"⟩
def origin : Origin := .query context.entry "draw" "input_3" port.contract port.owner (.draw "f7")

theorem installed : SampledCompiled.allowed context [port] [] .producer port origin = true := by
  decide +kernel

def twoDraws : PIR.Process (Domain.effects carriers) (F × F) :=
  .call (.localService port origin) fun first =>
  .call (.localService port origin) fun second => .done (first, second)

noncomputable def independent : ProbComp (F × F) := do
  let first ← $ᵗ F
  let second ← $ᵗ F
  pure (first, second)

/-- The fixed installed service forwards two fresh uniforms at exactly the
same port and origin. It preserves environment, proof, state, and empty trace. -/
theorem two_draw_execution (initial : Domain.RuntimeState carriers Unit) :
    Domain.run .producer SampledCompiled.oracle twoDraws initial
      (SampledCompiled.services context [port] []) =
      liftM ((fun values => PIR.Execution.mk (.returned values) initial []) <$> independent) := by
  simp [twoDraws, independent, Domain.run, PIR.Process.runM, Domain.handler,
    SampledCompiled.services, SampledCompiled.privateServices, installed,
    PIR.Execution.followM]
  rfl

/-- Full joint law, including the actual pre-existing ROM cache. No public
event is emitted and the outer cache is neither replaced nor extended. -/
theorem two_draw_cache (initial : Domain.RuntimeState carriers Unit)
    (cache : (TranscriptOracle.DomainSpec carriers).QueryCache) :
    (simulateQ (TranscriptOracle.DomainSpec carriers).romImpl
      (Domain.run .producer SampledCompiled.oracle twoDraws initial
        (SampledCompiled.services context [port] []))).run cache =
      (fun values => (PIR.Execution.mk (.returned values) initial [], cache)) <$> independent := by
  classical
  rw [two_draw_execution, HonestSampling.private_preserves_cache]
  simp only [Functor.map_map]

theorem independent_uniform : independent = $ᵗ (F × F) := by
  exact (SampleableType.uniformSample_prod_eq_bind F F).symm

theorem independent_agreement : Pr{let values ← independent}[values.1 = values.2] =
    1 / (Fintype.card F : ENNReal) := by
  rw [independent_uniform, SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun values : F × F => values.1 = values.2).card = 7 := by
    decide +kernel
  rw [count, Fintype.card_prod, ZMod.card]
  norm_num only [Nat.cast_ofNat, Nat.cast_mul]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mpr
  norm_num

/-- Agreement is 1/card in the actual handler experiment, not just in an
isolated sampler. Cache and trace remain part of the observed execution. -/
theorem repeated_draw_agreement (initial : Domain.RuntimeState carriers Unit) :
    Pr{let observed ← (HonestSampling.run
      (Domain.run .producer SampledCompiled.oracle twoDraws initial
        (SampledCompiled.services context [port] [])))}[∃ first second,
          observed.1.outcome = .returned (first, second) ∧ first = second] =
      1 / (Fintype.card F : ENNReal) := by
  classical
  unfold HonestSampling.run
  rw [two_draw_cache, prEvent_map]
  have eventEq (values : F × F) :
      (∃ first second, values = (first, second) ∧ first = second) ↔ values.1 = values.2 := by
    constructor
    · rintro ⟨first, second, rfl, same⟩
      exact same
    · intro same
      exact ⟨values.1, values.2, rfl, same⟩
  simpa only [PIR.Outcome.returned.injEq, eventEq] using independent_agreement

/-- Caching one reply changes the law even though both marginals are uniform. -/
theorem cached_draw_agreement :
    Pr{let values ← ((fun value : F => (value, value)) <$> ($ᵗ F))}[values.1 = values.2] = 1 := by
  simp

theorem fresh_not_cached (initial : Domain.RuntimeState carriers Unit) :
    Pr{let observed ← (HonestSampling.run
      (Domain.run .producer SampledCompiled.oracle twoDraws initial
        (SampledCompiled.services context [port] [])))}[∃ first second,
          observed.1.outcome = .returned (first, second) ∧ first = second] ≠ 1 := by
  classical
  rw [repeated_draw_agreement, ZMod.card]
  norm_num

def publicTemplate : Template := ⟨context.entry, [],
  ["query", context.entry, "challenge", "input_4", context.contract, "draw", "verifier"]⟩

/-- A compact runtime fixture. Its two actual participant executions query
the same typed public history; no source-root receipt is asserted here. -/
def publicParticipant : Participant where
  source := "sampling-runtime-control"
  candidate := "sampling-runtime-control"
  policy := ⟨context.entry, "prover", "verifier", 0, context.suite, [4], [], [], "", ""⟩
  symbol := "public-query"
  inputs := [.transcript context.suite, .indices]
  outputs := [.data (.field "f7")]
  instructions := [⟨.challenge context.suite "f7" publicTemplate, [0, 1],
    [.data (.field "f7"), .transcript context.suite], []⟩]
  returned := [2]

def publicInputs : Domain.Environment carriers := [.transcript context.suite [], .indices []]

def PairRepliesAgree (execution : Domain.PairExecution carriers Unit) : Prop :=
  ∃ produced validated, execution.producer.outcome = .returned produced ∧
    execution.validator = some validated ∧
    validated.outcome = .returned produced

/-- This quantifies the actual executePair computation. One outer ROM cache
serves production and validation; clearing it at the phase boundary would
instead give the independent agreement law above. -/
theorem public_pair_shares_cache (program : Structured.Program) :
    Pr{let observed ← (HonestSampling.run (SampledCompiled.computation model program context
      publicParticipant publicParticipant publicInputs publicInputs))}[PairRepliesAgree observed.1] = 1 := by
  apply (HonestSampling.success_probability_one_iff _ _).mpr
  intro answers
  rw [SampledCompiled.simulate_computation]
  simp [Domain.executePair, Domain.produce, Domain.validate, Domain.run,
    publicParticipant, publicInputs, Domain.participant, Domain.evaluate, Domain.step,
    Domain.queryOrigin, Domain.templateOrigin, Template.origin, Template.repeats,
    Template.qualify, Template.applicationPrefix, context, publicTemplate,
    Domain.atCoordinates, Domain.sortsMatch, Domain.Value.sort, Domain.read,
    Context.query, Context.role, Origin.query, Domain.drawRequest, Request.draw,
    PIR.Process.bind, PIR.Process.runM, PIR.Execution.followM, Domain.handler,
    SampledCompiled.tableOracle, HonestCompiled.tableOracle, PairRepliesAgree]

def wrongOwner : ServicePort := { port with owner := "verifier" }
def wrongOwnerOrigin : Origin :=
  .query context.entry "draw" "input_3" wrongOwner.contract wrongOwner.owner (.draw "f7")
def wrongDomain : Origin := { origin with request := some (.draw "other-field") }
def uninstalled : ServicePort := { port with name := "uninstalled" }

theorem refuses_wrong_owner (initial : Domain.RuntimeState carriers Unit) :
    Domain.handler .producer SampledCompiled.oracle (SampledCompiled.services context [wrongOwner] [])
      (.localService wrongOwner wrongOwnerOrigin) initial = pure ⟨.stopped .refused, initial, []⟩ := by
  simp [Domain.handler, SampledCompiled.services, SampledCompiled.privateServices,
    show SampledCompiled.allowed context [wrongOwner] [] .producer wrongOwner wrongOwnerOrigin = false by decide +kernel]

theorem refuses_wrong_domain (initial : Domain.RuntimeState carriers Unit) :
    Domain.handler .producer SampledCompiled.oracle (SampledCompiled.services context [port] [])
      (.localService port wrongDomain) initial = pure ⟨.stopped .refused, initial, []⟩ := by
  simp [Domain.handler, SampledCompiled.services, SampledCompiled.privateServices,
    show SampledCompiled.allowed context [port] [] .producer port wrongDomain = false by decide +kernel]

theorem refuses_uninstalled (initial : Domain.RuntimeState carriers Unit) :
    Domain.handler .producer SampledCompiled.oracle (SampledCompiled.services context [port] [])
      (.localService uninstalled origin) initial = pure ⟨.stopped .refused, initial, []⟩ := by
  simp [Domain.handler, SampledCompiled.services, SampledCompiled.privateServices,
    show SampledCompiled.allowed context [port] [] .producer uninstalled origin = false by decide +kernel]

/-- Distinct local names borrow the same admitted root. A stateful policy
records every call in explicit runtime state; it is intentionally separate
from the fixed stateless ideal field sampler above. -/
def aliasPort : ServicePort := { port with name := "borrowed_service" }
def counter : Domain.LocalServices ProbComp carriers Nat := fun _ actualPort actualOrigin state =>
  if actualPort.root = port.root ∧ actualPort.owner = port.owner then
    if same : actualOrigin = origin then
      pure (.returned (by simpa only [same, origin, Origin.query, Domain.Raw, Request.draw] using
        (state : F)), state + 1)
    else pure (.stopped .refused, state)
  else pure (.stopped .refused, state)

def noPublic : Domain.Oracle ProbComp carriers Nat := fun _ _ state => pure (.stopped .refused, state)
def aliasedCalls : PIR.Process (Domain.effects carriers) (F × F) :=
  .call (.localService port origin) fun first =>
  .call (.localService aliasPort origin) fun second => .done (first, second)

theorem alias_state_preserved (initial : Nat) (env : Domain.Environment carriers)
    (proof : Domain.Proof carriers) :
    Domain.run .producer noPublic aliasedCalls ⟨env, proof, initial⟩ counter =
      pure ⟨.returned ((initial : F), ((initial + 1 : Nat) : F)), ⟨env, proof, initial + 2⟩, []⟩ := by
  simp [Domain.run, aliasedCalls, PIR.Process.runM, Domain.handler, counter,
    port, aliasPort, PIR.Execution.followM, origin, Origin.query, Domain.Raw,
    Request.draw, Nat.add_assoc]

theorem alias_does_not_reset :
    Domain.run .producer noPublic aliasedCalls ⟨[], [], 0⟩ counter =
      pure ⟨.returned (0, 1), ⟨[], [], 2⟩, []⟩ := by
  simpa using alias_state_preserved 0 [] []

#print axioms two_draw_execution
#print axioms two_draw_cache
#print axioms repeated_draw_agreement
#print axioms fresh_not_cached
#print axioms public_pair_shares_cache
#print axioms refuses_wrong_owner
#print axioms refuses_wrong_domain
#print axioms refuses_uninstalled
#print axioms alias_state_preserved
end TestsSecurity.HonestSampling
