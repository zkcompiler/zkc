module

public import Zkc.Construction.DomainPublicBinding
public import Zkc.Construction.AuthoredPair
public import Zkc.Construction.RetainedTarget
public import Zkc.Source.Structured.DomainContract
public import Zkc.Construction.SourceOccurrences
public import ZkcSecurity.Claims.HonestInput
public import ZkcSecurity.FiatShamir.HonestCompiled

@[expose] public section

/-! Source-owned honest inputs and retained formula truth. Neither a predicate
nor a producer is a field of completeness evidence. Unsupported opaque input
relations require a future registered interpretation and are not admitted here. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims.HonestPair
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure FormulaClause {snapshot : Snapshot} (imported : Imported snapshot)
    (owner : ContractBinding imported) (application : RelationApplication) where
  binding : ApplicationBinding owner application
  formula : FormulaBinding imported binding.relation
  booleanOutput : binding.relation.declaration.outputs = [.boolean]

/-- All selections precede evidence. Exact artifacts, input clauses and target
come from core pair admission; the retained target supplies checked selectors
and the source formula body. The original export fixes the initial namespace. -/
structure Subject (model : DomainModel) (original : Snapshot) (imported : Imported original)
    (selected : Zkc.Construction.AuthoredPair.Selection original) where
  /-- Physical export identities selected by the request. Pipeline read-back
  checks these against bytes; source/candidate identities stay in the artifacts. -/
  originalExport : String
  producerExport : String
  validatorExport : String
  admitted : Zkc.Construction.AuthoredPair.Admitted imported selected selected.artifacts
  selection : Zkc.Construction.Selection imported.program.payload.entry.outputs
  selectionExact : select imported selected.artifacts.validator = some selection
  selectionChecked : selection.check imported selected.artifacts.validator = true
  producerOccurrences : SourceOccurrences.check original selection.context selected.artifacts.producer = .ok ()
  validatorOccurrences : SourceOccurrences.check original selection.context selected.artifacts.validator = .ok ()
  target : RetainedTarget imported selected.policy selection.publics
  targetExact : target.owner.clause target.clauseIndex = selected.target
  inputContractExact : Zkc.Construction.AuthoredPair.inputContract original = some selected.inputs
  inputClausesExact : selected.inputs.clauses = target.owner.contract.clauses.filter (·.kind == .input)
  /-- Protocol entries currently have no index-bound preconditions. Refuse a
  future unsupported contract rather than silently dropping it. -/
  preconditionsEmpty : selected.inputs.preconditions = []
  inputFormulas : (index : Fin target.owner.contract.clauses.length) →
    (target.owner.clause index).kind = .input →
      FormulaClause imported target.owner (target.owner.clause index).subject
  inputPolicy : InputPolicy target.owner.protocol.inputs

namespace Subject
variable {model : DomainModel} {original : Snapshot} {imported : Imported original}
  {selected : Zkc.Construction.AuthoredPair.Selection original}

/-- Public source-coordinate arity comes from the checked admitted selection. -/
theorem publicBindingArity (subject : Subject model original imported selected) :
    selected.policy.publicInputs.length = subject.selection.publics.length := by
  rw [← Zkc.Construction.AuthoredPair.admitted_validator_policy subject.admitted]
  exact Domain.PublicBinding.selectionArity imported selected.artifacts.validator
    subject.selection subject.selectionChecked

abbrev Inputs (subject : Subject model original imported selected) :=
  Values (Component model.Value) subject.target.owner.protocol.inputs

def boundary (subject : Subject model original imported selected) (inputs : subject.Inputs) :
    BoundaryValuation model.Value subject.target.owner.protocol.inputs subject.target.owner.protocol.outputs :=
  ⟨fun self => maskValues self subject.target.owner.protocol.inputScopes inputs,
    fun _ => Values.absent model.Value _⟩

def assignments (subject : Subject model original imported selected) (inputs : subject.Inputs) :
    LogicalAssignments model.Value subject.target.owner ⟨subject.target.owner.protocolIndex.val, []⟩ :=
  ⟨fun _ selector => selector.read {} (subject.boundary inputs),
    fun _ selector => selector.read {} (subject.boundary inputs)⟩

/-- The retained formula, on selectors reading the same inputs used by the
compiled producer and verifier. A stopped formula is never true. -/
def Relation (subject : Subject model original imported selected) (inputs : subject.Inputs) : Prop :=
  ∃ arguments, subject.target.application.read {} (subject.boundary inputs)
      (subject.assignments inputs) = some arguments ∧
    subject.target.formula.invokeRelationOn model arguments =
      .done (subject.target.booleanOutput.symm ▸ Values.cons true .nil)

def inputClause (subject : Subject model original imported selected) (inputs : subject.Inputs)
    (index : Fin subject.target.owner.contract.clauses.length)
    (isInput : (subject.target.owner.clause index).kind = .input) : Prop :=
  let clause := subject.inputFormulas index isInput
  ∃ arguments, clause.binding.read {} (subject.boundary inputs) (subject.assignments inputs) =
      some arguments ∧ clause.formula.invokeRelationOn model arguments =
        .done (clause.booleanOutput.symm ▸ Values.cons true .nil)

/-- Source positions are retained even for absent values and service handles.
Dropping an absent input must not shift later public or witness coordinates. -/
def encodeInputs {carriers : Carriers} : {types : List Ty} →
    Values (Component carriers.Value) types → List (Option (Domain.Value carriers))
  | [], .nil => []
  | type :: _, .cons value rest => (value >>= Domain.Value.encode type) :: encodeInputs rest

def project {carriers : Carriers} (encoded : List (Option (Domain.Value carriers)))
    (positions : List Nat) : Option (Domain.Environment carriers) :=
  positions.mapM fun index => encoded[index]? >>= id

/-- The source ABI fixes both projections. A public binding contains the
actual nominal payloads and source positions, before either phase queries. -/
def runtimeInputs (subject : Subject model original imported selected) (inputs : subject.Inputs) :
    Option (Domain.Environment model.toCarriers × Domain.Environment model.toCarriers) := do
  let (types, interface) ← entryInterface original
  let encoded := encodeInputs inputs
  let producer ← project encoded (dataInputs types interface.inputScopes selected.policy.producer)
  let validator ← project encoded selected.policy.publicInputs
  let history ← Domain.PublicBinding.fromEnvironment subject.originalExport
    selected.policy.publicInputs subject.publicBindingArity validator
  return (producer ++ [.transcript selected.policy.suite history],
    validator ++ [.transcript selected.policy.suite history])

/-- The request's closed shape/bound policy and every retained input clause
must hold. Exact source projections must encode and match the selected compiled
ABIs. Resource failure inside this domain remains an experiment failure. -/
def HonestInput (subject : Subject model original imported selected) (inputs : subject.Inputs) : Prop :=
  subject.inputPolicy.Holds inputs ∧
    (∀ index isInput, subject.inputClause inputs index isInput) ∧
    ∃ producer validator, subject.runtimeInputs inputs = some (producer, validator) ∧
      Domain.sortsMatch selected.artifacts.producer.inputs producer = true ∧
      Domain.sortsMatch selected.artifacts.validator.inputs validator = true

end Subject
end ZkcSecurity.Claims.HonestPair
