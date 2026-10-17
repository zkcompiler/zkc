module

public import ZkcExamples.Structured.ChaumPedersen
public import Zkc.Source.Structured.ContractExecution
public import Zkc.Source.Structured.ContractElaboration
public import Zkc.Source.Structured.ContractObligations
public import Zkc.Protocols.Schnorr

@[expose] public section

/-! The authored `knowledge` target of `sigma::ChaumPedersen`: the retained
`DLogEquality` formula with one witness port used at both bases. The single
witness selector keys one logical slot, so both equations read the same value. -/
namespace ZkcExamples.Structured.ChaumPedersenBinding
open Zkc.Source Zkc.Source.Structured ChaumPedersenViews ChaumPedersen

set_option smartUnfolding false

def owner : ContractBinding imported := by bind_contract

def clauseIndex : Fin owner.contract.clauses.length := owner.namedClause "knowledge"

def clause : ContractClause := owner.clause clauseIndex

theorem owner_is_entry : owner.protocol = program.payload.entry := rfl

def application : ApplicationBinding owner clause.subject := by bind_contract

def firstBaseSelector : BoundarySelector owner.protocol.signature (.group groupDomain) :=
  application.selectors.get .here

def firstKeySelector : BoundarySelector owner.protocol.signature (.group groupDomain) :=
  application.selectors.get (.there .here)

def secondBaseSelector : BoundarySelector owner.protocol.signature (.group groupDomain) :=
  application.selectors.get (.there (.there .here))

def secondKeySelector : BoundarySelector owner.protocol.signature (.group groupDomain) :=
  application.selectors.get (.there (.there (.there .here)))

def witnessSelector : BoundarySelector owner.protocol.signature (.field scalarDomain) :=
  application.selectors.get (.there (.there (.there (.there .here))))

def decisionSelector : BoundarySelector owner.protocol.signature .boolean :=
  ⟨.output .here, ⟨1, by decide +kernel⟩, by decide +kernel⟩

theorem exact_clause : clause.kind = .target ∧ clause.name = "knowledge" ∧
    clause.residual = none ∧ clause.decision = some decisionSelector.erase := by
  decide +kernel

theorem all_clauses : owner.contract.clauses = [clause] := rfl

def formulaBinding : FormulaBinding imported application.relation := by bind_contract

theorem no_formula_preconditions : formulaBinding.preconditions = [] := rfl

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def arguments (firstBase firstKey secondBase secondKey : G) (witness : F) :
    Values (assignment F G) formulaBinding.definition.inputs :=
  .cons firstBase (.cons firstKey (.cons secondBase (.cons secondKey (.cons witness .nil))))

/-- The target denotes the actual retained formula process. -/
def Relation (firstBase firstKey secondBase secondKey : G) (witness : F) : Prop :=
  formulaBinding.process (arguments firstBase firstKey secondBase secondKey witness) =
    .done (.cons true .nil)

theorem formula_process (firstBase firstKey secondBase secondKey : G) (witness : F) :
    formulaBinding.process (arguments firstBase firstKey secondBase secondKey witness) =
      .done (.cons (decide (firstKey = witness • firstBase) &&
        decide (secondKey = witness • secondBase)) .nil) := by
  rfl

theorem relation_iff (firstBase firstKey secondBase secondKey : G) (witness : F) :
    Relation firstBase firstKey secondBase secondKey witness ↔
      firstKey = witness • firstBase ∧ secondKey = witness • secondBase := by
  unfold Relation
  rw [formula_process]
  change (PIR.Proc.done (I := closedInterface)
    (.cons (decide (firstKey = witness • firstBase) &&
      decide (secondKey = witness • secondBase)) .nil : Values (assignment F G) [.boolean]) =
        .done (.cons true .nil)) ↔ _
  simp

/-- The subject's only relation is this formula. -/
def environment : RelationEnvironment imported F G where
  meanings index args := by
    have same : index = application.relation.index := by
      apply Fin.ext
      have bound : index.val < 1 := index.isLt
      change index.val = 0
      omega
    subst index
    exact Relation (args.get .here) (args.get (.there .here)) (args.get (.there (.there .here)))
      (args.get (.there (.there (.there .here)))) (args.get (.there (.there (.there (.there .here)))))

def target : InterpretedApplication owner clause.subject F G environment where
  binding := application
  interpretation := .formula formulaBinding rfl (fun _ => True)
    (fun args => args.get (.there .here) =
        args.get (.there (.there (.there (.there .here)))) • args.get .here ∧
      args.get (.there (.there (.there .here))) =
        args.get (.there (.there (.there (.there .here)))) • args.get (.there (.there .here)))
    inferInstance

theorem target_formula_law : (target (F := F) (G := G)).interpretation.FormulaLaw := by
  intro args _
  cases args with | cons firstBase args =>
  cases args with | cons firstKey args =>
  cases args with | cons secondBase args =>
  cases args with | cons secondKey args =>
  cases args with | cons witness args =>
  cases args
  simp only [Bool.decide_and]
  rfl

def rootInvocation : InvocationCoordinate := ⟨0, []⟩

/-- Parameter values and the one witness, keyed by the actual typed selectors. -/
def assignments (firstBase secondBase : G) (witness : F) :
    LogicalAssignments (assignment F G) owner rootInvocation where
  parameters type selector := match type with
    | .group _ => if selector.erase = firstBaseSelector.erase then some firstBase
        else if selector.erase = secondBaseSelector.erase then some secondBase else none
    | _ => none
  witnesses type selector := match type with
    | .field _ => if selector.erase = witnessSelector.erase then some witness else none
    | _ => none

/-- Only the verifier's own inputs and its actual returned tuple are projected. -/
def observedBoundary (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (challenge response : F) : ContractBoundaryValues owner F G :=
  BoundaryValuation.ofOutcome 1 (verifierInputs firstBase firstKey secondBase secondKey service)
    (execute firstBase firstKey secondBase secondKey service commitments challenge response).outcome

/-- The selected decision is the actual verifier's: one response, both bases. -/
theorem observed_accepts_iff (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (challenge response : F) :
    decisionSelector.read {} (observedBoundary firstBase firstKey secondBase secondKey service
        commitments challenge response) = some true ↔
      response • firstBase = commitments.1 + challenge • firstKey ∧
        response • secondBase = commitments.2 + challenge • secondKey := by
  change (some (decide (response • firstBase = commitments.1 + challenge • firstKey) &&
      decide (response • secondBase = commitments.2 + challenge • secondKey)) = some true) ↔ _
  simp

theorem observed_read (firstBase firstKey secondBase secondKey : G) (witness : F) (service : Nat)
    (commitments : G × G) (challenge response : F) :
    application.read {} (observedBoundary firstBase firstKey secondBase secondKey service
        commitments challenge response) (assignments firstBase secondBase witness) =
      some (arguments firstBase firstKey secondBase secondKey witness) := by
  rfl

theorem observed_target_iff (firstBase firstKey secondBase secondKey : G) (witness : F) (service : Nat)
    (commitments : G × G) (challenge response : F) :
    (target (F := F) (G := G)).Holds {} (observedBoundary firstBase firstKey secondBase secondKey service
        commitments challenge response) (assignments firstBase secondBase witness) ↔
      Relation firstBase firstKey secondBase secondKey witness := by
  change (∃ args, application.read {} _ _ = some args ∧
    formulaBinding.invokeRelation args = .done (.cons true .nil)) ↔ _
  constructor
  · rintro ⟨args, read, truth⟩
    rw [observed_read] at read
    cases Option.some.inj read
    exact truth
  · intro truth
    exact ⟨_, observed_read .., truth⟩

/-- Two transcripts with one pair of commitments and distinct challenges, both
accepted by the actual verifier, give one witness for both bases. -/
theorem extracted_target (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (first second firstResponse secondResponse : F) (distinct : first ≠ second)
    (acceptFirst : decisionSelector.read {} (observedBoundary firstBase firstKey secondBase secondKey
      service commitments first firstResponse) = some true)
    (acceptSecond : decisionSelector.read {} (observedBoundary firstBase firstKey secondBase secondKey
      service commitments second secondResponse) = some true) :
    (target (F := F) (G := G)).Holds {} (observedBoundary firstBase firstKey secondBase secondKey service
        commitments first firstResponse)
      (assignments firstBase secondBase ((firstResponse - secondResponse) / (first - second))) := by
  rw [observed_accepts_iff] at acceptFirst acceptSecond
  apply (observed_target_iff ..).mpr
  apply (relation_iff ..).mpr
  exact ⟨(Zkc.Protocols.Schnorr.extract_public_key firstBase firstKey commitments.1 first second
      firstResponse secondResponse distinct acceptFirst.1 acceptSecond.1).symm,
    (Zkc.Protocols.Schnorr.extract_public_key secondBase secondKey commitments.2 first second
      firstResponse secondResponse distinct acceptFirst.2 acceptSecond.2).symm⟩

/-- The actual prover's sends are accepted when both keys use its witness. -/
theorem honest_accepts (firstBase firstKey secondBase secondKey : G) (witness nonce challenge : F)
    (service : Nat) (valid : Relation firstBase firstKey secondBase secondKey witness) :
    decisionSelector.read {} (observedBoundary firstBase firstKey secondBase secondKey service
      (nonce • firstBase, nonce • secondBase) challenge (nonce + challenge * witness)) = some true := by
  obtain ⟨firstValid, secondValid⟩ := (relation_iff ..).mp valid
  apply (observed_accepts_iff ..).mpr
  subst firstValid secondValid
  exact ⟨Zkc.Protocols.Schnorr.response_equation .., Zkc.Protocols.Schnorr.response_equation ..⟩

end ZkcExamples.Structured.ChaumPedersenBinding
