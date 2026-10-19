module

public import ZkcExamples.Structured.SchnorrHonestProver
public import ZkcExamples.Structured.SchnorrInteractiveNormalForms

@[expose] public section

/-! The authored Schnorr target, including its role-local ports and retained
DLog formula. The binding, selectors, formula process and target are the
generated ones of `SchnorrInteractiveNormalForms`, kept here under the names the
Schnorr consumers use. Honest execution uses the source witness; two-transcript
extraction assigns a new witness to the same logical target without identifying
private inputs. -/
namespace ZkcExamples.Structured.SchnorrBinding
open Zkc.Source Zkc.Source.Structured
open SchnorrInteractive

set_option smartUnfolding false

abbrev owner : ContractBinding imported := SchnorrInteractiveNormalForms.owner

abbrev clauseIndex : Fin owner.contract.clauses.length := SchnorrInteractiveNormalForms.clauseIndex

abbrev clause : ContractClause := SchnorrInteractiveNormalForms.clause

theorem owner_is_entry : owner.protocol = program.payload.entry := rfl

abbrev application : ApplicationBinding owner clause.subject := SchnorrInteractiveNormalForms.application

abbrev baseSelector : BoundarySelector owner.protocol.signature (.group groupDomain) :=
  SchnorrInteractiveNormalForms.baseSelector

abbrev keySelector : BoundarySelector owner.protocol.signature (.group groupDomain) :=
  SchnorrInteractiveNormalForms.keySelector

abbrev witnessSelector : BoundarySelector owner.protocol.signature (.field scalarDomain) :=
  SchnorrInteractiveNormalForms.witnessSelector

abbrev decisionSelector : BoundarySelector owner.protocol.signature .boolean :=
  SchnorrInteractiveNormalForms.decisionSelector

theorem exact_clause : clause.kind = .target ∧ clause.name = "knowledge" ∧
    clause.residual = none ∧ clause.decision = some decisionSelector.erase :=
  SchnorrInteractiveNormalForms.exact_clause

theorem all_clauses : owner.contract.clauses = [clause] := rfl

abbrev formulaBinding : FormulaBinding imported application.relation :=
  SchnorrInteractiveNormalForms.formulaBinding

/-- The original source formula recovered by the checked binding. -/
def originalFormula : Function := formulaBinding.original

theorem no_formula_preconditions : formulaBinding.preconditions = [] := rfl

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev arguments (base key : G) (witness : F) :
    Values (assignment F G) formulaBinding.definition.inputs :=
  SchnorrInteractiveNormalForms.arguments base key witness

/-- This target denotes the actual retained formula process, not a predicate
attached to the relation's name or digest. -/
abbrev Relation (base key : G) (witness : F) : Prop :=
  SchnorrInteractiveNormalForms.Relation base key witness

theorem formula_process (base key : G) (witness : F) :
    formulaBinding.process (arguments base key witness) =
      .done (.cons (decide (key = witness • base)) .nil) :=
  SchnorrInteractiveNormalForms.formula_process base key witness

theorem relation_iff (base key : G) (witness : F) :
    Relation base key witness ↔ key = witness • base :=
  SchnorrInteractiveNormalForms.relation_iff base key witness

/-- This subject has one formula declaration. Even the experiment environment's
entry uses that formula; the formula interpretation below ignores opaque slots. -/
abbrev environment : RelationEnvironment imported F G := SchnorrInteractiveNormalForms.environment

abbrev target : InterpretedApplication owner clause.subject F G environment :=
  SchnorrInteractiveNormalForms.target

theorem target_formula_law : (target (F := F) (G := G)).interpretation.FormulaLaw :=
  SchnorrInteractiveNormalForms.target_formula_law

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
abbrev rootInvocation : InvocationCoordinate := SchnorrInteractiveNormalForms.rootInvocation

abbrev assignments (base : G) (witness : F) : LogicalAssignments (assignment F G) owner rootInvocation :=
  SchnorrInteractiveNormalForms.assignments base witness

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
