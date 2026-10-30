module

public import ZkcSecurity.Bindings.Transcript.DomainReading
public import ZkcSecurity.Bindings.Transcript.DomainCoherence
public import ZkcSecurity.ProgramLogic.Transcript.Reduction

@[expose] public section

/-! Exact-key transport to the existing typed charged endpoint. No new
probability semantics is defined: the experiment is the actual Domain handler
and the adversary is any computation on the same history oracle. -/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.DomainReduction
open Zkc.Source Zkc.Construction OracleComp OracleSpec
variable {carriers : Structured.Carriers} {I : PIR.Signature} {A : Type}

/-- Both the selected endpoint reading and actual-observation coherence are
required. Neither field asserts a source binding: that is an independent
whole-Process equation to the admitted artifact. -/
structure Bridge
    (absorb : Typed.Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw)
    (Post : Domain.History carriers → A → Prop) (history : Domain.History carriers)
    (actual : PIR.Process (Domain.effects carriers) A) (presented : PIR.Process I A) : Prop where
  reading : ReadingTo absorb Post history actual presented
  coherent : CoherentTo Post history actual

namespace Bridge
variable {absorb : Typed.Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw}
variable {Post : Domain.History carriers → A → Prop} {history : Domain.History carriers}
variable {actual : PIR.Process (Domain.effects carriers) A} {presented : PIR.Process I A}

/-- Terminal representation facts may be forgotten independently of the
reduction certificate's rejection postcondition. -/
theorem weaken (bridge : Bridge absorb Post history actual presented)
    {Next : Domain.History carriers → A → Prop}
    (implies : ∀ reached value, Post reached value → Next reached value) :
    Bridge absorb Next history actual presented :=
  ⟨bridge.reading.weaken implies, bridge.coherent.weaken implies⟩

/-- Compose once over the reached history and complete returned value. Both
readings carry the same postcondition, so callers need one continuation proof. -/
theorem bind {B : Type} (bridge : Bridge absorb Post history actual presented)
    {PostNext : Domain.History carriers → B → Prop}
    (nextActual : A → PIR.Process (Domain.effects carriers) B)
    (nextPresented : A → PIR.Process I B)
    (next : ∀ reached value, Post reached value →
      Bridge absorb PostNext reached (nextActual value) (nextPresented value)) :
    Bridge absorb PostNext history (actual.bind nextActual) (presented.bind nextPresented) :=
  ⟨bridge.reading.bind nextActual nextPresented (fun reached value holds =>
      (next reached value holds).reading),
    bridge.coherent.bind nextActual (fun reached value holds =>
      (next reached value holds).coherent)⟩

theorem done (history : Domain.History carriers) (value : A) (holds : Post history value) :
    Bridge absorb Post history (.done value) (.done value) :=
  ⟨.done history value holds, .done history value holds⟩

theorem halt (history : Domain.History carriers) (reason : PIR.Stop) :
    Bridge (A := A) absorb Post history (.halt reason) (.halt reason) :=
  ⟨.halt history reason, .halt history reason⟩

theorem checkpoint (environment : Domain.Environment carriers)
    (bridge : Bridge absorb Post history actual presented) :
    Bridge absorb Post history (.call (.checkpoint environment) (fun _ => actual)) presented :=
  ⟨.checkpoint environment bridge.reading, .checkpoint environment bridge.coherent⟩

/-- Equality of oracle computations retains the exact keys and dependent
answers, not only a marginal acceptance probability. Consequently the same
cache and every repeated/adversarial query are retained. -/
theorem computation (bridge : Bridge absorb Post history actual presented)
    (environment : Domain.Environment carriers)
    (prover : OracleComp (OracleSpec.ofFn (Typed.ByLast (@Domain.Raw carriers)))
      (Domain.Proof carriers)) :
    (prover >>= fun proof => (fun result => (result.outcome, result.state.proof)) <$>
      Domain.run .validator (ZkcSecurity.Endpoint.Domain.Compiled.oracle
        (Typed.ask (R := Typed.ByLast Domain.Raw))) actual ⟨environment, proof, ()⟩) =
      Typed.fixedExperiment absorb presented history prover := by
  apply congrArg (Bind.bind prover)
  funext proof
  exact bridge.reading.handler _ _

/-- Ordered logs agree entry for entry, including repeated keys. This
strengthens a mere final-distribution equality and makes cost retention explicit. -/
theorem queryLog (bridge : Bridge absorb Post history actual presented)
    (environment : Domain.Environment carriers)
    (prover : OracleComp (OracleSpec.ofFn (Typed.ByLast (@Domain.Raw carriers)))
      (Domain.Proof carriers))
    (table : (key : Domain.History carriers) → Typed.ByLast Domain.Raw key) :
    tableQueryLog
      (prover >>= fun proof => (fun result => (result.outcome, result.state.proof)) <$>
        Domain.run .validator (ZkcSecurity.Endpoint.Domain.Compiled.oracle
          (Typed.ask (R := Typed.ByLast Domain.Raw))) actual ⟨environment, proof, ()⟩) table =
      tableQueryLog (Typed.fixedExperiment absorb presented history prover) table := by
  rw [bridge.computation]

variable [DecidableEq (Domain.Event carriers)] [∀ event, SampleableType (@Domain.Raw carriers event)]

/-- A reduction's charge and pathwise budget transfer unchanged to the actual
handler. In particular histories, per-key prices, and cache hits are retained. -/
theorem soundness_charged (bridge : Bridge absorb Post history actual presented)
    {accepts : A → Prop} {charge : Domain.History carriers → Domain.Event carriers → ENNReal}
    {ReductionPost : Domain.History carriers → A → Prop}
    (reduction : Typed.Reduction absorb ReductionPost charge)
    (rejects : ∀ reached value, ReductionPost reached value → ¬ accepts value)
    (member : reduction.doomed history presented)
    (validatorCost : ENNReal)
    (validatorBound : Typed.ChargedCostBound absorb charge presented history validatorCost)
    (environment : Domain.Environment carriers)
    (prover : OracleComp (OracleSpec.ofFn (Typed.ByLast (@Domain.Raw carriers)))
      (Domain.Proof carriers)) (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover ⟨Typed.keyCharge charge⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle
      (prover >>= fun proof => (fun result => (result.outcome, result.state.proof)) <$>
        Domain.run .validator (ZkcSecurity.Endpoint.Domain.Compiled.oracle
          (Typed.ask (R := Typed.ByLast Domain.Raw))) actual ⟨environment, proof, ()⟩)).run' ∅}[Accepted accepts result.1] ≤ proverCost + validatorCost := by
  rw [bridge.computation]
  exact Typed.soundness_charged (reduction.toCertificate absorb rejects) presented history member
    validatorCost validatorBound prover proverCost proverBound

end Bridge

namespace Compiled
variable {model : Structured.DomainModel} {art : ZkcSecurity.Endpoint.Domain.Artifacts}
variable (compiled : ZkcSecurity.Endpoint.Domain.Compiled art)
variable {absorb : Typed.Interface I (Domain.Event model.toCarriers)
  (Domain.Payload model.toCarriers) Domain.Raw}
variable {Post : Domain.History model.toCarriers → Domain.Result model.toCarriers → Prop}
variable {statement : art.Statement model} {initial : Domain.History model.toCarriers}
variable {inputs : Domain.Environment model.toCarriers}
variable {presented : PIR.Process I (Domain.Result model.toCarriers)}

/-- The actual compiled endpoint, including its acceptance-position map and
unread proof, is an exact image of the existing typed experiment. -/
theorem computation (encoded : Domain.encodeValues statement = some inputs)
    (bridge : Bridge absorb Post initial
      (Domain.participant model compiled.imported.program compiled.selection.context art.participant
        (Domain.inputFrame compiled.selection.context inputs initial)) presented)
    (prover : OracleComp (OracleSpec.ofFn (Typed.ByLast (@Domain.Raw model.toCarriers)))
      (Domain.Proof model.toCarriers)) :
    (prover >>= compiled.verifier model (Typed.ask (R := Typed.ByLast Domain.Raw)) statement initial) =
      (fun result => (Zkc.Transcript.mapOutcome compiled.acceptance result.1, result.2)) <$>
        Typed.fixedExperiment absorb presented initial prover := by
  simp only [Typed.fixedExperiment, map_bind]
  apply congrArg (Bind.bind prover)
  funext proof
  rw [ZkcSecurity.Endpoint.Domain.Compiled.verifier_readExecution, encoded]
  simp only
  rw [bridge.reading.run]

variable [DecidableEq (Domain.Event model.toCarriers)]
variable [∀ event, SampleableType (@Domain.Raw model.toCarriers event)]

/-- This is the actual Domain verifier's complete-acceptance event. The
adversary is unrestricted except for its stated resource budget; shape and
honesty are not premises of its meaning. -/
theorem soundness_charged (encoded : Domain.encodeValues statement = some inputs)
    (bridge : Bridge absorb Post initial
      (Domain.participant model compiled.imported.program compiled.selection.context art.participant
        (Domain.inputFrame compiled.selection.context inputs initial)) presented)
    {charge : Domain.History model.toCarriers → Domain.Event model.toCarriers → ENNReal}
    {ReductionPost : Domain.History model.toCarriers → Domain.Result model.toCarriers → Prop}
    (reduction : Typed.Reduction absorb ReductionPost charge)
    (rejects : ∀ reached value, ReductionPost reached value → compiled.acceptance value ≠ some true)
    (member : reduction.doomed initial presented)
    (validatorCost : ENNReal)
    (validatorBound : Typed.ChargedCostBound absorb charge presented initial validatorCost)
    (prover : OracleComp (OracleSpec.ofFn (Typed.ByLast (@Domain.Raw model.toCarriers)))
      (Domain.Proof model.toCarriers)) (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover ⟨Typed.keyCharge charge⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle
      (prover >>= compiled.verifier model (Typed.ask (R := Typed.ByLast Domain.Raw)) statement initial)).run' ∅}[ZkcSecurity.Endpoint.Domain.CompleteAccepted result] ≤ proverCost + validatorCost := by
  rw [computation compiled encoded bridge]
  simp only [simulateQ_map, StateT.run'_map', prEvent_map]
  apply (prEvent_mono _ _ _ (fun result accepted => ?_)).trans
    (Typed.soundness_charged (reduction.toCertificate absorb rejects) presented initial member
      validatorCost validatorBound prover proverCost proverBound)
  exact (Zkc.Transcript.accepted_mapOutcome compiled.acceptance (· = some true) result.1).mp accepted.1

end Compiled
end ZkcSecurity.FiatShamir.DomainReduction
