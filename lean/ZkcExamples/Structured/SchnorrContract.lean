module

public import ZkcExamples.Structured.SchnorrBinding
public import Zkc.Source.Structured.ContractExecution
public import Zkc.Source.Structured.ContractObligations
public import ZkcExamples.Structured.SchnorrExecution

@[expose] public section

/-! The retained target at actual returned verifier boundaries. Both accepted
transcripts read the selected V output of the admitted participant execution.
Extraction supplies a new logical witness; it fabricates no prover input or
verifier output. The source formula and exact clause inventory remain explicit. -/
namespace ZkcExamples.Structured.SchnorrContract
open Zkc.Source Zkc.Source.Structured SchnorrBinding

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option smartUnfolding false

theorem only_clause (index : Fin owner.contract.clauses.length) : index = clauseIndex := by
  apply Fin.ext
  have bound : index.val < 1 := index.isLt
  change index.val = 0
  omega

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

def interpretation : ContractInterpretation owner F G environment where
  subjects index := by
    have same := only_clause index
    subst index
    exact target
  residuals index residual selected := by
    have same := only_clause index
    subst index
    change none = some residual at selected
    cases selected
  decisions index selector selected := by
    have same := only_clause index
    subst index
    change some decisionSelector.erase = some selector at selected
    cases Option.some.inj selected
    exact ⟨decisionSelector, rfl⟩

/-- Only the actual verifier's local inputs and actual returned tuple are
projected. The adversarial transcript does not imply an honest prover execution. -/
def observedBoundary (base key : G) (service : Nat)
    (prover : Zkc.Protocols.Schnorr.Common.Strategy F G) (challenge : F) :
    ContractBoundaryValues owner F G :=
  BoundaryValuation.ofOutcome 1 (SchnorrInteractive.verifierInputs base key service)
    (SchnorrExecution.execute base key service prover challenge).outcome

/-- The interpretation's selected decision resolves to this exact V port. -/
theorem selected_accepts_iff (values : ContractBoundaryValues owner F G) :
    (interpretation (F := F) (G := G)).Accepts {} clauseIndex values ↔
      decisionSelector.read {} values = some true := by
  constructor
  · rintro ⟨selector, selected, accepts⟩
    change some decisionSelector.erase = some selector at selected
    cases Option.some.inj selected
    exact accepts
  · intro accepts
    exact ⟨decisionSelector.erase, rfl, accepts⟩

/-- The selected decision is load-bearing: no stop or absent output can accept. -/
theorem observed_accepts_iff (base key : G) (service : Nat)
    (prover : Zkc.Protocols.Schnorr.Common.Strategy F G) (challenge : F) :
    decisionSelector.read {} (observedBoundary base key service prover challenge) = some true ↔
      (SchnorrInteractive.run base key service prover challenge).outcome = .returned (some true) := by
  apply Iff.trans (decisionSelector.returnedSatisfies_decision
    (Value := assignment F G) rfl {} 1 (SchnorrInteractive.verifierInputs base key service)
    (SchnorrExecution.execute base key service prover challenge).outcome .here rfl rfl)
  apply Iff.trans ?_ (SchnorrExecution.accepted_iff base key service prover challenge)
  generalize (SchnorrExecution.execute base key service prover challenge).outcome = outcome
  cases outcome with
  | stopped reason => exact ⟨False.elim, (by intro impossible; cases impossible)⟩
  | returned results =>
    cases results with
    | cons decision rest =>
      cases rest
      constructor
      · intro same
        change decision = some true at same
        cases same
        rfl
      · intro same
        exact congrArg (fun values => values.get .here) (PIR.Outcome.returned.inj same)

theorem observed_read (base key : G) (witness : F) (service : Nat)
    (prover : Zkc.Protocols.Schnorr.Common.Strategy F G) (challenge : F) :
    application.read {} (observedBoundary base key service prover challenge)
      (assignments base witness) = some (arguments base key witness) := by
  rfl

theorem observed_target_iff (base key : G) (witness : F) (service : Nat)
    (prover : Zkc.Protocols.Schnorr.Common.Strategy F G) (challenge : F) :
    (target (F := F) (G := G)).Holds {} (observedBoundary base key service prover challenge)
      (assignments base witness) ↔ Relation base key witness := by
  change (∃ args, application.read {} _ _ = some args ∧
    formulaBinding.invokeRelation args = .done (.cons true .nil)) ↔ _
  constructor
  · rintro ⟨args, read, truth⟩
    rw [observed_read] at read
    cases Option.some.inj read
    exact truth
  · intro truth
    exact ⟨_, observed_read .., truth⟩

def selected : SelectedApplication owner F G environment :=
  interpretation.select (.subject clauseIndex)

theorem every_clause_selected (index : Fin owner.contract.clauses.length) :
    (selected (F := F) (G := G)).selection = .subject index := by
  cases only_clause index
  rfl

def targetUse (base key : G) (witness : F) (service : Nat)
    (prover : Zkc.Protocols.Schnorr.Common.Strategy F G) (challenge : F) :
    ApplicationUse selected {} (observedBoundary base key service prover challenge)
      (assignments base witness) :=
  ⟨arguments base key witness, observed_read ..⟩

theorem target_translation (base key : G) (witness : F) (service : Nat)
    (prover : Zkc.Protocols.Schnorr.Common.Strategy F G) (challenge : F) :
    (targetUse base key witness service prover challenge).Translation :=
  ⟨target_formula_law, trivial⟩

def extractionRequests (base key : G) (service : Nat)
    (prover : Zkc.Protocols.Schnorr.Common.Strategy F G) (first second : F) :
    ContractRequests owner F G environment rootInvocation {}
      (observedBoundary base key service prover first)
      (assignments base ((prover.response first - prover.response second) / (first - second))) :=
  .one (.relation selected (targetUse base key
    ((prover.response first - prover.response second) / (first - second)) service prover first)
    .assertion)

theorem no_protocol_calls : callInventory owner.protocol.body = [] := rfl

/-- The only retained clause is requested; every lexical protocol call is also
covered. There are none in this admitted body. The local proof supplies the
actual formula law/domain and an algebraic consequence of actual acceptances. -/
def all_obligations (base key : G) (service : Nat)
    (prover : Zkc.Protocols.Schnorr.Common.Strategy F G) (first second : F)
    (distinct : first ≠ second)
    (acceptFirst : decisionSelector.read {}
      (observedBoundary base key service prover first) = some true)
    (acceptSecond : decisionSelector.read {}
      (observedBoundary base key service prover second) = some true) :
    SelectedObligations (extractionRequests base key service prover first second) (fun _ => False) where
  localRequests := ⟨target_translation ..,
    (SchnorrInteractive.special_soundness base key service prover first second distinct
      ((observed_accepts_iff ..).mp acceptFirst) ((observed_accepts_iff ..).mp acceptSecond)).symm⟩
  calls call := by
    rcases call with ⟨occurrence, impossible⟩
    rw [no_protocol_calls] at impossible
    cases impossible

/-- Both actual selected outputs are load-bearing. Generic request resolution
uses the formula law at the extracted arguments to prove the actual target. -/
theorem extracted_target (base key : G) (service : Nat)
    (prover : Zkc.Protocols.Schnorr.Common.Strategy F G) (first second : F)
    (distinct : first ≠ second)
    (acceptFirst : decisionSelector.read {}
      (observedBoundary base key service prover first) = some true)
    (acceptSecond : decisionSelector.read {}
      (observedBoundary base key service prover second) = some true) :
    (target (F := F) (G := G)).Holds {} (observedBoundary base key service prover first)
      (assignments base ((prover.response first - prover.response second) / (first - second))) :=
  (extractionRequests base key service prover first second).resolve
    (all_obligations base key service prover first second distinct acceptFirst acceptSecond).localRequests

theorem selected_extraction (base key : G) (service : Nat)
    (prover : Zkc.Protocols.Schnorr.Common.Strategy F G) (first second : F)
    (distinct : first ≠ second)
    (acceptFirst : (interpretation (F := F) (G := G)).Accepts {} clauseIndex
      (observedBoundary base key service prover first))
    (acceptSecond : (interpretation (F := F) (G := G)).Accepts {} clauseIndex
      (observedBoundary base key service prover second)) :
    (interpretation (F := F) (G := G)).Subject {} clauseIndex
      (observedBoundary base key service prover first)
      (assignments base ((prover.response first - prover.response second) / (first - second))) :=
  extracted_target base key service prover first second distinct
    ((selected_accepts_iff _).mp acceptFirst) ((selected_accepts_iff _).mp acceptSecond)

/-- Honest completeness uses the source witness in both the admitted prover and
actual formula. The prover's separate key copy remains unconstrained. -/
theorem honest_accepts (proverBase proverKey base key : G) (witness nonce challenge : F)
    (nonceService service : Nat) (sameBase : proverBase = base)
    (valid : Relation base key witness) :
    decisionSelector.read {} (observedBoundary base key service
      (SchnorrHonestProver.strategy proverBase proverKey witness nonce nonceService) challenge) =
        some true :=
  (observed_accepts_iff ..).mpr (target_complete proverBase proverKey base key witness nonce
    challenge nonceService service sameBase valid)

end ZkcExamples.Structured.SchnorrContract
