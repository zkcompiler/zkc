module

public import ZkcExamples.Structured.SchnorrHonestProver
public import Zkc.Source.Structured.ContractExecution
public import Zkc.Source.Structured.ContractElaboration

@[expose] public section

/-! The authored Schnorr target, including its role-local ports and retained
DLog formula. Honest execution uses the source witness; two-transcript extraction
assigns a new witness to the same logical target without identifying private inputs.
-/
namespace ZkcExamples.Structured.SchnorrBinding
open Zkc.Source Zkc.Source.Structured
open SchnorrInteractive

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option smartUnfolding false

def owner : ContractBinding imported := by bind_contract

def clauseIndex : Fin owner.contract.clauses.length := owner.namedClause "knowledge"

def clause : ContractClause := owner.clause clauseIndex

theorem owner_is_entry : owner.protocol = program.payload.entry := rfl

def application : ApplicationBinding owner clause.subject := by bind_contract

def baseSelector : BoundarySelector owner.protocol.signature (.group groupDomain) :=
  application.selectors.get .here

def keySelector : BoundarySelector owner.protocol.signature (.group groupDomain) :=
  application.selectors.get (.there .here)

def witnessSelector : BoundarySelector owner.protocol.signature (.field scalarDomain) :=
  application.selectors.get (.there (.there .here))

def decisionSelector : BoundarySelector owner.protocol.signature .boolean :=
  ⟨.output .here, ⟨1, by decide +kernel⟩, by decide +kernel⟩

theorem exact_clause : clause.kind = .target ∧ clause.name = "knowledge" ∧
    clause.residual = none ∧ clause.decision = some decisionSelector.erase := by
  decide +kernel

theorem all_clauses : owner.contract.clauses = [clause] := rfl

def formulaBinding : FormulaBinding imported application.relation := by bind_contract

/-- The original source formula recovered by the checked binding. -/
def originalFormula : Function := formulaBinding.original

theorem no_formula_preconditions : formulaBinding.preconditions = [] := rfl

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

def arguments (base key : G) (witness : F) :
    Values (assignment F G) formulaBinding.definition.inputs :=
  .cons base (.cons key (.cons witness .nil))

/-- This target denotes the actual retained formula process, not a predicate
attached to the relation's name or digest. -/
def Relation (base key : G) (witness : F) : Prop :=
  formulaBinding.process (arguments base key witness) = .done (.cons true .nil)

theorem formula_process (base key : G) (witness : F) :
    formulaBinding.process (arguments base key witness) =
      .done (.cons (decide (key = witness • base)) .nil) := by
  rfl

theorem relation_iff (base key : G) (witness : F) :
    Relation base key witness ↔ key = witness • base := by
  unfold Relation
  rw [formula_process]
  change (PIR.Proc.done (I := closedInterface)
    (.cons (decide (key = witness • base)) .nil : Values (assignment F G) [.boolean]) =
      .done (.cons true .nil)) ↔ _
  simp

/-- This subject has one formula declaration. Even the experiment environment's
entry uses that formula; the formula interpretation below ignores opaque slots. -/
def environment : RelationEnvironment imported F G where
  meanings index args := by
    have same : index = application.relation.index := by
      apply Fin.ext
      have bound : index.val < 1 := index.isLt
      change index.val = 0
      omega
    subst index
    exact Relation (args.get .here) (args.get (.there .here))
      (args.get (.there (.there .here)))

def target : InterpretedApplication owner clause.subject F G environment where
  binding := application
  interpretation := .formula formulaBinding rfl (fun _ => True)
    (fun args => args.get (.there .here) =
      (args.get (.there (.there .here))) • args.get .here) inferInstance

theorem target_formula_law : (target (F := F) (G := G)).interpretation.FormulaLaw := by
  intro args _
  cases args with
  | cons base rest =>
    cases rest with
    | cons key rest =>
      cases rest with
      | cons witness rest =>
        cases rest
        rfl

/-- A local valuation for input-agreement controls. Role copies are independent;
execution theorems use SchnorrContract.observedBoundary instead. -/
def boundary (proverBase proverKey verifierBase verifierKey : G) (sourceWitness : F)
    (nonceService challengeService : Nat) (decision : Option Bool) :
    BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs where
  inputs self := if self = 0 then proverInputs proverBase proverKey sourceWitness nonceService
    else if self = 1 then verifierInputs verifierBase verifierKey challengeService
    else Values.absent (assignment F G) _
  outputs self := .cons (if self = 1 then decision else none) .nil

/-- Parameter/witness values are keyed by the actual typed selectors. A new
extracted witness need not equal the prover's input in `boundary`. -/
def rootInvocation : InvocationCoordinate := ⟨0, []⟩

def assignments (base : G) (witness : F) :
    LogicalAssignments (assignment F G) owner rootInvocation where
  parameters type selector := match type with
    | .group _ => if selector.erase = baseSelector.erase then some base else none
    | _ => none
  witnesses type selector := match type with
    | .field _ => if selector.erase = witnessSelector.erase then some witness else none
    | _ => none

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem read_application (proverBase proverKey verifierBase verifierKey : G)
    (sourceWitness witness : F) (nonceService challengeService : Nat) (decision : Option Bool) :
    application.read {}
      (boundary proverBase proverKey verifierBase verifierKey sourceWitness
        nonceService challengeService decision)
      (assignments verifierBase witness) = some (arguments verifierBase verifierKey witness) := by
  rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem honest_assignments_agree (proverBase proverKey verifierBase verifierKey : G)
    (sourceWitness : F) (nonceService challengeService : Nat) (decision : Option Bool) :
    application.Agrees {}
      (boundary proverBase proverKey verifierBase verifierKey sourceWitness
        nonceService challengeService decision)
      (assignments verifierBase sourceWitness) := by
  rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem read_decision (proverBase proverKey verifierBase verifierKey : G)
    (sourceWitness : F) (nonceService challengeService : Nat) (decision : Option Bool) :
    decisionSelector.read {}
      (boundary proverBase proverKey verifierBase verifierKey sourceWitness
        nonceService challengeService decision) = decision := rfl

/-- The selected role and output port observe exactly the participant process
used by the verifier theorems; no external acceptance predicate is substituted. -/
theorem selected_process (base key : G) (service : Nat) :
    ((program.participant F G decisionSelector.role.val (verifierInputs base key service)).bind
      fun outputs => .done (decisionSelector.read {}
        (BoundaryValuation.ofReturned decisionSelector.role.val
          (verifierInputs base key service) outputs))) = process (F := F) base key service := by
  rfl

theorem target_holds_iff (proverBase proverKey verifierBase verifierKey : G)
    (sourceWitness witness : F) (nonceService challengeService : Nat) (decision : Option Bool) :
    (target (F := F) (G := G)).Holds {}
      (boundary proverBase proverKey verifierBase verifierKey sourceWitness
        nonceService challengeService decision) (assignments verifierBase witness) ↔
      Relation verifierBase verifierKey witness := by
  change (∃ args, application.read {} _ _ = some args ∧
    formulaBinding.invokeRelation args = .done (.cons true .nil)) ↔ _
  constructor
  · rintro ⟨args, read, truth⟩
    rw [read_application] at read
    cases Option.some.inj read
    exact truth
  · intro truth
    exact ⟨_, read_application .., truth⟩

/-- Honest completeness uses the source witness and explicit base agreement.
The prover's local public-key copy remains unconstrained. -/
theorem target_complete (proverBase proverKey verifierBase verifierKey : G)
    (sourceWitness nonce challenge : F) (nonceService challengeService : Nat)
    (sameBase : proverBase = verifierBase)
    (valid : Relation verifierBase verifierKey sourceWitness) :
    (Zkc.Protocols.Schnorr.Common.run SchnorrInteractive.verifier verifierBase verifierKey
      challengeService (SchnorrHonestProver.strategy proverBase proverKey sourceWitness nonce
        nonceService) challenge).outcome = .returned (some true) :=
  SchnorrHonestProver.accepts proverBase proverKey verifierBase verifierKey sourceWitness
    nonce challenge nonceService challengeService sameBase
    ((relation_iff verifierBase verifierKey sourceWitness).mp valid)

/-- The conclusion evaluates DLog's retained formula at the new extracted
witness. No honest secret, equality of role copies, or rewinding algorithm occurs. -/
theorem target_special_soundness (base key : G) (service : Nat)
    (prover : Zkc.Protocols.Schnorr.Common.Strategy F G) (first second : F)
    (distinct : first ≠ second)
    (acceptFirst : (run base key service prover first).outcome = .returned (some true))
    (acceptSecond : (run base key service prover second).outcome = .returned (some true)) :
    Relation base key ((prover.response first - prover.response second) / (first - second)) :=
  (relation_iff ..).mpr
    (SchnorrInteractive.special_soundness base key service prover first second
      distinct acceptFirst acceptSecond).symm

end ZkcExamples.Structured.SchnorrBinding
