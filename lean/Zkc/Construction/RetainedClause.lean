module

public import Zkc.Source.Structured.RelationMeaning

@[expose] public section

set_option autoImplicit false
namespace Zkc.Construction
open Zkc.Source Zkc.Source.Structured

/-- The same exact ordered application read is used for targets and every
honest input clause. Argument existence never chooses a new witness. -/
structure RetainedClause {snapshot : Snapshot} (imported : Imported snapshot)
    (owner : ContractBinding imported) (application : RelationApplication)
    (Value : Ty → Type) (registry : OpaqueRegistry Value) where
  binding : ApplicationBinding owner application
  booleanOutput : binding.relation.declaration.outputs = [.boolean]
  meaning : RelationMeaning imported binding.relation Value registry

namespace RetainedClause
variable {snapshot : Snapshot} {imported : Imported snapshot} {owner : ContractBinding imported}
  {application : RelationApplication} {model : DomainModel} {registry : OpaqueRegistry model.Value}
  {invocation : InvocationCoordinate}

def Holds (clause : RetainedClause imported owner application model.Value registry)
    (context : ProtocolContext)
    (boundary : BoundaryValuation model.Value owner.protocol.inputs owner.protocol.outputs)
    (assignments : LogicalAssignments model.Value owner invocation) : Prop :=
  ∃ arguments, clause.binding.read context boundary assignments = some arguments ∧
    clause.meaning.HoldsOn clause.booleanOutput arguments

/-- A successful read has one ordered result, shared by every consumer. -/
theorem holds_iff_of_read (clause : RetainedClause imported owner application model.Value registry)
    (context : ProtocolContext)
    (boundary : BoundaryValuation model.Value owner.protocol.inputs owner.protocol.outputs)
    (assignments : LogicalAssignments model.Value owner invocation)
    (arguments : Values model.Value clause.binding.relation.declaration.inputs)
    (read : clause.binding.read context boundary assignments = some arguments) :
    clause.Holds context boundary assignments ↔ clause.meaning.HoldsOn clause.booleanOutput arguments := by
  constructor
  · rintro ⟨actual, actualRead, truth⟩
    cases Option.some.inj (read.symm.trans actualRead)
    exact truth
  · exact fun truth => ⟨arguments, read, truth⟩

end RetainedClause
end Zkc.Construction
