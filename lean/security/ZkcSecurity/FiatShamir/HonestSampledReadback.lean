module

public import ZkcSecurity.FiatShamir.HonestReadback
public import ZkcSecurity.FiatShamir.HonestReadbackTransport
public import ZkcSecurity.FiatShamir.HonestSamplingTransport

@[expose] public section

/-! Producer-private sampling prefixes followed by existing exact readback.

The prefix contains only local requests and checkpoints. Each private reply
selects its own frame and tail; replies are never coupled to validator samples.
The deterministic tail retains the existing send/receive and public-query
semantics. All execution theorems use the single Domain handler and runner.
-/

set_option autoImplicit false
namespace ZkcSecurity.FiatShamir
open Zkc.Source Zkc.Construction OracleComp OracleSpec

variable {carriers : Structured.Carriers} {A B C : Type}
  {Allowed : ServicePort → Origin → Prop}

/-- A returning producer prefix, for every private reply. Pure computation and
frame construction are represented by the actual continuation and its return. -/
inductive SamplingPrefix (Allowed : ServicePort → Origin → Prop) (Post : A → Prop) : PIR.Process (Domain.effects carriers) A → Prop
  | done {value} : Post value → SamplingPrefix Allowed Post (.done value)
  | checkpoint {next} (environment : Domain.Environment carriers) :
      SamplingPrefix Allowed Post next →
      SamplingPrefix Allowed Post (.call (.checkpoint environment) (fun _ => next))
  | localService (port : ServicePort) (origin : Origin)
      {next : Domain.Raw (.challenge origin : Domain.Event carriers) →
        PIR.Process (Domain.effects carriers) A} :
      Allowed port origin →
      (∀ reply, SamplingPrefix Allowed Post (next reply)) →
      SamplingPrefix Allowed Post (.call (.localService port origin) next)

/-- Only producer-private prefixes extend Readback. Messages and public
queries remain governed by the original relation, including exact keys. -/
inductive SampledReadback (Allowed : ServicePort → Origin → Prop) (Post : A → B → Prop) :
    PIR.Process (Domain.effects carriers) A → PIR.Process (Domain.effects carriers) B → Prop
  | deterministic {left right} : Readback Post left right → SampledReadback Allowed Post left right
  | checkpointLeft {left right} (environment : Domain.Environment carriers) :
      SampledReadback Allowed Post left right →
      SampledReadback Allowed Post (.call (.checkpoint environment) (fun _ => left)) right
  | localServiceLeft (port : ServicePort) (origin : Origin)
      {left : Domain.Raw (.challenge origin : Domain.Event carriers) →
        PIR.Process (Domain.effects carriers) A} {right} :
      Allowed port origin →
      (∀ reply, SampledReadback Allowed Post (left reply) right) →
      SampledReadback Allowed Post (.call (.localService port origin) left) right

namespace SamplingPrefix

/-- Compose actual returned prefix frames with the existing deterministic
readback method. This accepts any number of draws, including repeated roots. -/
theorem readback {Ready : A → Prop} {Post : B → C → Prop}
    {process : PIR.Process (Domain.effects carriers) A}
    {next : A → PIR.Process (Domain.effects carriers) B}
    {validator : PIR.Process (Domain.effects carriers) C}
    (derivation : SamplingPrefix Allowed Ready process)
    (tail : ∀ frame, Ready frame → Readback Post (next frame) validator) :
    SampledReadback Allowed Post (process.bind next) validator := by
  induction derivation with
  | done ready => exact .deterministic (tail _ ready)
  | checkpoint environment _ ih => exact .checkpointLeft environment ih
  | localService port origin admitted _ ih => exact .localServiceLeft port origin admitted ih

theorem bind {Ready : A → Prop} {Post : B → Prop}
    {process : PIR.Process (Domain.effects carriers) A}
    (derivation : SamplingPrefix Allowed Ready process)
    (next : A → PIR.Process (Domain.effects carriers) B)
    (tail : ∀ frame, Ready frame → SamplingPrefix Allowed Post (next frame)) :
    SamplingPrefix Allowed Post (process.bind next) := by
  induction derivation with
  | done ready => exact tail _ ready
  | checkpoint environment _ ih => exact .checkpoint environment ih
  | localService port origin admitted _ ih => exact .localService port origin admitted ih

end SamplingPrefix

namespace Readback

/-- Reuse the existing deterministic readback witnesses under any private
interpreter and state. Successful tails cannot reach refused local requests. -/
theorem runM_table {Post : A → B → Prop}
    {left : PIR.Process (Domain.effects carriers) A}
    {right : PIR.Process (Domain.effects carriers) B}
    (aligned : Readback Post left right)
    {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id)
    (services : Domain.LocalServices m carriers S) (privateState : S)
    (leftEnvironment rightEnvironment : Domain.Environment carriers)
    (preceding suffix : Domain.Proof carriers) :
    ∃ leftValue rightValue leftFinal rightFinal leftEvents rightEvents emitted,
      Domain.run .producer (ReadbackTransport.tableOracle answers) left
        ⟨leftEnvironment, preceding, privateState⟩ services =
          pure ⟨.returned leftValue, ⟨leftFinal, preceding ++ emitted, privateState⟩, leftEvents⟩ ∧
      Domain.run .validator (ReadbackTransport.tableOracle answers) right
        ⟨rightEnvironment, emitted ++ suffix, privateState⟩ services =
          pure ⟨.returned rightValue, ⟨rightFinal, suffix, privateState⟩, rightEvents⟩ ∧
      Post leftValue rightValue := by
  obtain ⟨a, b, l, r, le, re, emitted, lp, rp, post⟩ :=
    aligned.run answers leftEnvironment rightEnvironment preceding suffix
  exact ⟨a, b, l, r, le, re, emitted,
    ReadbackTransport.run_table_of_returned answers services .producer privateState left
      ⟨leftEnvironment, preceding, ()⟩ a ⟨l, preceding ++ emitted, ()⟩ le lp,
    ReadbackTransport.run_table_of_returned answers services .validator privateState right
      ⟨rightEnvironment, emitted ++ suffix, ()⟩ b ⟨r, suffix, ()⟩ re rp, post⟩

end Readback

namespace SampledReadback

/-- Installed private services return on every supported outcome. This is a
handler law, independent of the relation, source inputs and sampled values. -/
def Returns (Allowed : ServicePort → Origin → Prop) {S : Type} (services : Domain.LocalServices ProbComp carriers S) : Prop :=
  ∀ port origin, Allowed port origin → ∀ state outcome final,
    (outcome, final) ∈ support (services .producer port origin state) →
    ∃ reply, outcome = .returned reply

/-- An equation for the existing runner at a local call, retaining the actual
service post-state and every stop. No public event is emitted by the draw. -/
theorem run_localService {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (oracle : Domain.Oracle m carriers S) (services : Domain.LocalServices m carriers S)
    (mode : Domain.Mode) (port : ServicePort) (origin : Origin)
    (next : Domain.Raw (.challenge origin : Domain.Event carriers) →
      PIR.Process (Domain.effects carriers) A) (state : Domain.RuntimeState carriers S) :
    Domain.run mode oracle (.call (.localService port origin) next) state services =
      (services mode port origin state.oracle >>= fun sampled =>
        match sampled.1 with
        | .returned reply => Domain.run mode oracle (next reply)
            { state with oracle := sampled.2 } services
        | .stopped reason => pure ⟨.stopped reason, { state with oracle := sampled.2 }, []⟩) := by
  simp only [Domain.run, PIR.Process.runM, Domain.handler, bind_assoc, pure_bind]
  congr 1
  funext sampled
  rcases sampled with ⟨outcome, final⟩
  cases outcome <;> simp [PIR.Execution.followM]

/-- Every actual producer outcome is a successful exact readback, using its
actual proof and private post-state for the validator. Arbitrary suffixes are
retained; producer frames and observations remain in the returned execution. -/
theorem run {Post : A → B → Prop}
    {left : PIR.Process (Domain.effects carriers) A}
    {right : PIR.Process (Domain.effects carriers) B}
    (aligned : SampledReadback Allowed Post left right) {S : Type}
    (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id)
    (services : Domain.LocalServices ProbComp carriers S) (total : Returns Allowed services)
    (privateState : S) (leftEnvironment rightEnvironment : Domain.Environment carriers)
    (preceding suffix : Domain.Proof carriers)
    (produced : PIR.Execution (Domain.RuntimeState carriers S) (Domain.Event carriers) A)
    (reached : produced ∈ support (Domain.run .producer (ReadbackTransport.tableOracle answers)
      left ⟨leftEnvironment, preceding, privateState⟩ services)) :
    ∃ leftValue rightValue rightFinal rightEvents emitted,
      produced.outcome = .returned leftValue ∧ produced.state.proof = preceding ++ emitted ∧
      Domain.run .validator (ReadbackTransport.tableOracle answers) right
        ⟨rightEnvironment, emitted ++ suffix, produced.state.oracle⟩ services =
          pure ⟨.returned rightValue, ⟨rightFinal, suffix, produced.state.oracle⟩, rightEvents⟩ ∧
      Post leftValue rightValue := by
  induction aligned generalizing privateState leftEnvironment produced with
  | deterministic aligned =>
      obtain ⟨a, b, l, r, le, re, emitted, lp, rp, post⟩ :=
        aligned.runM_table answers services privateState leftEnvironment rightEnvironment preceding suffix
      rw [lp] at reached
      have same := eq_of_mem_support_pure _ reached
      subst produced
      exact ⟨a, b, r, re, emitted, rfl, rfl, rp, post⟩
  | checkpointLeft environment aligned ih =>
      apply ih privateState environment produced
      simpa [Domain.run, PIR.Process.runM, Domain.handler, PIR.Execution.followM] using reached
  | localServiceLeft port origin admitted aligned ih =>
      rw [run_localService] at reached
      obtain ⟨⟨outcome, final⟩, sampled, continued⟩ := mem_support_bind_peel _ _ reached
      obtain ⟨reply, rfl⟩ := total port origin admitted privateState outcome final sampled
      exact ih reply final leftEnvironment produced continued

/-- The actual sequential compiled pair succeeds with probability one under a
fixed public table. Remaining private draws are still a ProbComp computation. -/
theorem pair_success (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (producer validator : Participant)
    (producerInputs validatorInputs : Domain.Environment model.toCarriers)
    (position : Nat)
    {Allowed : ServicePort → Origin → Prop}
    (aligned : SampledReadback Allowed
      (fun _ result => Domain.acceptanceAt position result.values = some true)
      (Domain.participant model program context producer producerInputs)
      (Domain.participant model program context validator validatorInputs))
    {S : Type} (answers : QueryImpl (TranscriptOracle.DomainSpec model.toCarriers) Id)
    (services : Domain.LocalServices ProbComp model.toCarriers S)
    (total : Returns Allowed services) (initial : S) :
    Pr{let observed ← (Domain.executePair model program context producer validator
      producerInputs validatorInputs (ReadbackTransport.tableOracle answers) initial services)}[
        Domain.PairExecution.Success position observed] = 1 := by
  apply (prEvent_eq_one_iff _ _).mpr
  intro observed reached
  unfold Domain.executePair at reached
  obtain ⟨produced, producedReached, continued⟩ := mem_support_bind_peel _ _ reached
  obtain ⟨a, b, r, re, emitted, returned, proof, validated, accepted⟩ :=
    aligned.run answers services total initial producerInputs validatorInputs [] [] produced producedReached
  simp only [List.nil_append, List.append_nil] at proof validated
  simp only [returned] at continued
  have validation : Domain.validate model program context validator validatorInputs
      produced.state.proof (ReadbackTransport.tableOracle answers) produced.state.oracle services =
      pure ⟨.returned b, ⟨r, [], produced.state.oracle⟩, re⟩ := by
    simpa only [Domain.validate, proof] using validated
  rw [validation] at continued
  simp only [pure_bind] at continued
  have same := eq_of_mem_support_pure _ continued
  subst observed
  exact ⟨a, _, b, returned, rfl, rfl, rfl, accepted⟩

/-- Lift the actual pair theorem through the single outer ROM cache. The
public-oracle equation is supplied by the installed model; private services
are simulated with `unifFwdAnswerImpl`, retaining their fresh uniforms. -/
theorem failure_zero (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (producer validator : Participant)
    (producerInputs validatorInputs : Domain.Environment model.toCarriers)
    (position : Nat)
    {Allowed : ServicePort → Origin → Prop}
    (aligned : SampledReadback Allowed
      (fun _ result => Domain.acceptanceAt position result.values = some true)
      (Domain.participant model program context producer producerInputs)
      (Domain.participant model program context validator validatorInputs))
    [DecidableEq (Domain.Event model.toCarriers)]
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    {S : Type}
    (oracle : Domain.Oracle (OracleComp (HonestSampling.Spec (@Domain.Raw model.toCarriers)))
      model.toCarriers S)
    (services : Domain.LocalServices
      (OracleComp (HonestSampling.Spec (@Domain.Raw model.toCarriers))) model.toCarriers S)
    (publicLaw : ∀ answers : QueryImpl (TranscriptOracle.DomainSpec model.toCarriers) Id,
      (fun history event state => simulateQ (unifFwdAnswerImpl answers)
        (oracle history event state)) = ReadbackTransport.tableOracle answers)
    (total : ∀ answers : QueryImpl (TranscriptOracle.DomainSpec model.toCarriers) Id,
      Returns Allowed (fun mode port origin state => simulateQ (unifFwdAnswerImpl answers)
        (services mode port origin state)))
    (initial : S) :
    HonestSampling.failure
      (Domain.executePair model program context producer validator producerInputs validatorInputs
        oracle initial services) (Domain.PairExecution.Success position) = 0 := by
  apply HonestSampling.failure_zero_of_all_tables
  intro answers
  rw [HonestSampling.simulate_executePair, publicLaw answers]
  exact pair_success model program context producer validator producerInputs validatorInputs
    position aligned answers _ (total answers) initial

end SampledReadback
end ZkcSecurity.FiatShamir
