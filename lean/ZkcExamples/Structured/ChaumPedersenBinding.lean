module

public import ZkcExamples.Structured.ChaumPedersen
public import Zkc.Source.Structured.ContractExecution
public import Zkc.Source.Structured.ContractElaboration
public import Zkc.Source.Structured.ContractObligations
public import Zkc.Protocols.Schnorr

@[expose] public section

/-! The authored `knowledge` target of `sigma::ChaumPedersen`: the retained
`DLogEquality` formula with one witness port used at both bases. The single
witness selector keys one logical slot, so both equations read the same value.
The binding, the formula's process and the observed decision are the generated
ones of `ChaumPedersenNormalForms`; the extraction and honest acceptance below
are this protocol's mathematics. -/
namespace ZkcExamples.Structured.ChaumPedersenBinding
open Zkc.Source Zkc.Source.Structured ChaumPedersenViews ChaumPedersen

set_option smartUnfolding false

abbrev owner : ContractBinding imported := ChaumPedersenNormalForms.owner

abbrev clauseIndex : Fin owner.contract.clauses.length := ChaumPedersenNormalForms.clauseIndex

abbrev clause : ContractClause := ChaumPedersenNormalForms.clause

theorem owner_is_entry : owner.protocol = program.payload.entry := rfl

abbrev application : ApplicationBinding owner clause.subject := ChaumPedersenNormalForms.application

abbrev firstBaseSelector : BoundarySelector owner.protocol.signature (.group groupDomain) :=
  ChaumPedersenNormalForms.firstBaseSelector

abbrev firstKeySelector : BoundarySelector owner.protocol.signature (.group groupDomain) :=
  ChaumPedersenNormalForms.firstKeySelector

abbrev secondBaseSelector : BoundarySelector owner.protocol.signature (.group groupDomain) :=
  ChaumPedersenNormalForms.secondBaseSelector

abbrev secondKeySelector : BoundarySelector owner.protocol.signature (.group groupDomain) :=
  ChaumPedersenNormalForms.secondKeySelector

abbrev witnessSelector : BoundarySelector owner.protocol.signature (.field scalarDomain) :=
  ChaumPedersenNormalForms.witnessSelector

abbrev decisionSelector : BoundarySelector owner.protocol.signature .boolean :=
  ChaumPedersenNormalForms.decisionSelector

theorem exact_clause : clause.kind = .target ∧ clause.name = "knowledge" ∧
    clause.residual = none ∧ clause.decision = some decisionSelector.erase :=
  ChaumPedersenNormalForms.exact_clause

theorem all_clauses : owner.contract.clauses = [clause] := rfl

abbrev formulaBinding : FormulaBinding imported application.relation :=
  ChaumPedersenNormalForms.formulaBinding

theorem no_formula_preconditions : formulaBinding.preconditions = [] := rfl

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev arguments (firstBase firstKey secondBase secondKey : G) (witness : F) :
    Values (assignment F G) formulaBinding.definition.inputs :=
  ChaumPedersenNormalForms.arguments firstBase firstKey secondBase secondKey witness

/-- The target denotes the actual retained formula process. -/
abbrev Relation (firstBase firstKey secondBase secondKey : G) (witness : F) : Prop :=
  ChaumPedersenNormalForms.Relation firstBase firstKey secondBase secondKey witness

theorem formula_process (firstBase firstKey secondBase secondKey : G) (witness : F) :
    formulaBinding.process (arguments firstBase firstKey secondBase secondKey witness) =
      .done (.cons (decide (firstKey = witness • firstBase) &&
        decide (secondKey = witness • secondBase)) .nil) :=
  ChaumPedersenNormalForms.formula_process firstBase firstKey secondBase secondKey witness

theorem relation_iff (firstBase firstKey secondBase secondKey : G) (witness : F) :
    Relation firstBase firstKey secondBase secondKey witness ↔
      firstKey = witness • firstBase ∧ secondKey = witness • secondBase :=
  ChaumPedersenNormalForms.relation_iff firstBase firstKey secondBase secondKey witness

/-- The subject's only relation is this formula. -/
abbrev environment : RelationEnvironment imported F G := ChaumPedersenNormalForms.environment

abbrev target : InterpretedApplication owner clause.subject F G environment :=
  ChaumPedersenNormalForms.target

theorem target_formula_law : (target (F := F) (G := G)).interpretation.FormulaLaw :=
  ChaumPedersenNormalForms.target_formula_law

abbrev rootInvocation : InvocationCoordinate := ChaumPedersenNormalForms.rootInvocation

/-- Parameter values and the one witness, keyed by the actual typed selectors. -/
abbrev assignments (firstBase secondBase : G) (witness : F) :
    LogicalAssignments (assignment F G) owner rootInvocation :=
  ChaumPedersenNormalForms.assignments firstBase secondBase witness

/-- Only the verifier's own inputs and its actual returned tuple are projected. -/
abbrev observedBoundary (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (challenge response : F) : ContractBoundaryValues owner F G :=
  ChaumPedersenNormalForms.observedBoundary firstBase firstKey secondBase secondKey service
    commitments.1 commitments.2 challenge response

/-- The selected decision is the actual verifier's: one response, both bases. -/
theorem observed_accepts_iff (firstBase firstKey secondBase secondKey : G) (service : Nat)
    (commitments : G × G) (challenge response : F) :
    decisionSelector.read {} (observedBoundary firstBase firstKey secondBase secondKey service
        commitments challenge response) = some true ↔
      response • firstBase = commitments.1 + challenge • firstKey ∧
        response • secondBase = commitments.2 + challenge • secondKey :=
  ChaumPedersenNormalForms.observed_accepts_iff firstBase firstKey secondBase secondKey service
    commitments.1 commitments.2 challenge response

theorem observed_read (firstBase firstKey secondBase secondKey : G) (witness : F) (service : Nat)
    (commitments : G × G) (challenge response : F) :
    application.read {} (observedBoundary firstBase firstKey secondBase secondKey service
        commitments challenge response) (assignments firstBase secondBase witness) =
      some (arguments firstBase firstKey secondBase secondKey witness) :=
  ChaumPedersenNormalForms.observed_read firstBase firstKey secondBase secondKey service witness
    commitments.1 commitments.2 challenge response

theorem observed_target_iff (firstBase firstKey secondBase secondKey : G) (witness : F) (service : Nat)
    (commitments : G × G) (challenge response : F) :
    (target (F := F) (G := G)).Holds {} (observedBoundary firstBase firstKey secondBase secondKey service
        commitments challenge response) (assignments firstBase secondBase witness) ↔
      Relation firstBase firstKey secondBase secondKey witness :=
  ChaumPedersenNormalForms.observed_target_iff firstBase firstKey secondBase secondKey service witness
    commitments.1 commitments.2 challenge response

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

/-- The values the admitted prover sends (`ChaumPedersen.prover_run`) for a
nonce and a challenge, delivered with that challenge, are accepted by the actual
verifier when both keys use the witness at the verifier's bases. This states the
values, not a joint run of the two participants. -/
theorem honest_accepts (firstBase firstKey secondBase secondKey : G) (witness nonce challenge : F)
    (service : Nat) (valid : Relation firstBase firstKey secondBase secondKey witness) :
    decisionSelector.read {} (observedBoundary firstBase firstKey secondBase secondKey service
      (nonce • firstBase, nonce • secondBase) challenge (nonce + challenge * witness)) = some true := by
  obtain ⟨firstValid, secondValid⟩ := (relation_iff ..).mp valid
  apply (observed_accepts_iff ..).mpr
  subst firstValid secondValid
  exact ⟨Zkc.Protocols.Schnorr.response_equation .., Zkc.Protocols.Schnorr.response_equation ..⟩

end ZkcExamples.Structured.ChaumPedersenBinding
