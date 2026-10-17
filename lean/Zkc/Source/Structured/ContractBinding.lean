module

public import Zkc.Source.Structured.Import
public import Zkc.Source.Structured.Association

@[expose] public section

/-! Typed associations select data from one admitted snapshot. They contain no
externally supplied relation assertion or whole-protocol correctness theorem. -/
set_option autoImplicit false
namespace Zkc.Source.Structured

structure ContractBinding {snapshot : Snapshot} (imported : Imported snapshot) where
  ownerIndex : Fin snapshot.contracts.length
  protocolIndex : Fin imported.program.payload.protocols.length
  owner_eq : (snapshot.contracts.get ownerIndex).owner =
    (imported.program.payload.protocols.get protocolIndex).name

namespace ContractBinding
variable {snapshot : Snapshot} {imported : Imported snapshot}

def contract (binding : ContractBinding imported) : ProtocolContract :=
  snapshot.contracts.get binding.ownerIndex

def protocol (binding : ContractBinding imported) : CheckedProtocol :=
  imported.program.payload.protocols.get binding.protocolIndex

def clause (binding : ContractBinding imported) (index : Fin binding.contract.clauses.length) :
    ContractClause := binding.contract.clauses.get index

theorem retained (binding : ContractBinding imported) :
    binding.contract ∈ snapshot.contracts ∧
    binding.protocol ∈ imported.program.payload.protocols ∧
    binding.contract.owner = binding.protocol.name :=
  ⟨List.get_mem .., List.get_mem .., binding.owner_eq⟩

end ContractBinding

/-- The declaration itself is recovered by position, never supplied as an
unrelated external proposition bearing the same diagnostic name. -/
structure RelationBinding (snapshot : Snapshot) (application : RelationApplication) where
  index : Fin snapshot.relations.length
  name_eq : (snapshot.relations.get index).name = application.relation

def RelationBinding.declaration {snapshot : Snapshot} {application : RelationApplication}
    (binding : RelationBinding snapshot application) : Relation := snapshot.relations.get binding.index

/-- Both the original formula and the admitted helper are selected from their
actual tables. Full signatures, including helper kind, must agree. -/
structure FormulaBinding {snapshot : Snapshot} (imported : Imported snapshot)
    {application : RelationApplication} (relation : RelationBinding snapshot application) where
  original : Function
  original_mem : Definition.function original ∈ snapshot.definitions
  formula_kind : relation.declaration.kind = "zkc.language.formula/0"
  formula_eq : relation.declaration.formula = some original.name
  math_kind : original.kind = .math
  inputs_eq : original.inputs = relation.declaration.inputs
  outputs_eq : original.outputs = relation.declaration.outputs
  helperIndex : Fin imported.program.payload.definitions.length
  signature_eq : (imported.program.payload.definitions.get helperIndex).helper =
    ⟨original.name, .math, relation.declaration.inputs, relation.declaration.outputs⟩

namespace FormulaBinding
variable {snapshot : Snapshot} {imported : Imported snapshot}
variable {application : RelationApplication} {relation : RelationBinding snapshot application}

def definition (binding : FormulaBinding imported relation) : CheckedDefinition :=
  imported.program.payload.definitions.get binding.helperIndex

/-- Preconditions remain inspectable even when the helper has a Boolean result. -/
def preconditions (binding : FormulaBinding imported relation) : List Bound :=
  binding.original.preconditions

theorem bodyIn (binding : FormulaBinding imported relation) :
    BodyIn imported.program.payload.definitions binding.definition.helper binding.definition.body :=
  BodyIn.of_mem (List.get_mem ..) rfl binding.definition.exactBody.symm

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The formula meaning is the actual process, including refusal. It is not a
Boolean obtained by mapping every non-return to false. -/
def process (binding : FormulaBinding imported relation)
    (arguments : Values (assignment F G) binding.definition.inputs) :
    Closed (Values (assignment F G) binding.definition.outputs) :=
  invoke (closedMeanings imported.program.payload.definitions) binding.definition.helper arguments

theorem process_eq_body (binding : FormulaBinding imported relation)
    (arguments : Values (assignment F G) binding.definition.inputs) :
    binding.process arguments = binding.definition.body.denote
      (meaning F G (closedMeanings imported.program.payload.definitions)) arguments.get :=
  binding.bodyIn.invoke imported.program.payload.linked arguments

/-- A separate local proof can establish a decidable predicate only under its
explicit domain. Admission and the formula link do not supply this proof. -/
def Realizes (binding : FormulaBinding imported relation)
    (booleanOutput : binding.definition.outputs = [.boolean])
    (domain predicate : Values (assignment F G) binding.definition.inputs → Prop)
    [DecidablePred predicate] : Prop :=
  ∀ arguments, domain arguments → binding.process arguments =
    .done (booleanOutput.symm ▸ (Values.cons (decide (predicate arguments)) .nil))

end FormulaBinding

end Zkc.Source.Structured
