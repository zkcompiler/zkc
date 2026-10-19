module

public import Zkc.Source.Structured.ContractBinding

@[expose] public section

set_option autoImplicit false
namespace Zkc.Source.Structured

/-- Only explicitly named target projections contribute to selected Entry
identity. Generic protocol statements remain legal outside this profile. -/
def Instruction.isNamedStatement : Instruction → Bool
  | .instruction (.statement _ _ _ (some _)) _ _ _ _ => true
  | _ => false

/-- Entry selection requires the actual root and an explicit retained target
reference in its statement. Component bindings do not imply Entry selection.
No target is inferred from a matching Boolean port or from list order. -/
structure EntryContractBinding {snapshot : Snapshot} (imported : Imported snapshot) where
  owner : ContractBinding imported
  root : owner.protocolIndex = imported.program.payload.entryIndex
  original : Function
  original_mem : Definition.function original ∈ snapshot.definitions
  original_name : original.name = owner.protocol.name
  original_kind : original.kind = .protocol
  clauseIndex : Fin owner.contract.clauses.length
  target : (owner.clause clauseIndex).kind = .target
  selectors : List String
  acceptance : Nat
  operands : List Nat
  site : String
  uniqueStatement : original.body.topLevelInstructions.filter Instruction.isNamedStatement = [Instruction.instruction
      (.statement (owner.clause clauseIndex).subject.relation selectors acceptance
        (some (owner.clause clauseIndex).name)) operands [] [] site]
  decision : ContractSelector
  decision_eq : (owner.clause clauseIndex).decision = some decision
  decision_output : decision.direction = .output
  decision_port : decision.port = acceptance

namespace EntryContractBinding
variable {snapshot : Snapshot} {imported : Imported snapshot}

theorem statement (binding : EntryContractBinding imported) : Instruction.instruction
    (.statement (binding.owner.clause binding.clauseIndex).subject.relation binding.selectors binding.acceptance
      (some (binding.owner.clause binding.clauseIndex).name)) binding.operands [] [] binding.site ∈
      binding.original.body.topLevelInstructions := by
  apply (List.mem_filter.mp (show _ ∈ binding.original.body.topLevelInstructions.filter
    Instruction.isNamedStatement from by rw [binding.uniqueStatement]; exact List.mem_cons_self)).1

theorem unique_named_statement (binding : EntryContractBinding imported) (instruction : Instruction)
    (member : instruction ∈ binding.original.body.topLevelInstructions)
    (named : instruction.isNamedStatement = true) :
    instruction = Instruction.instruction
      (.statement (binding.owner.clause binding.clauseIndex).subject.relation binding.selectors binding.acceptance
        (some (binding.owner.clause binding.clauseIndex).name)) binding.operands [] [] binding.site := by
  have selected := List.mem_filter.mpr ⟨member, named⟩
  rw [binding.uniqueStatement] at selected
  exact List.mem_singleton.mp selected

theorem named_statement_count (binding : EntryContractBinding imported) :
    (binding.original.body.topLevelInstructions.filter Instruction.isNamedStatement).length = 1 := by
  rw [binding.uniqueStatement]
  rfl

theorem selected_root (binding : EntryContractBinding imported) :
    binding.owner.protocol = imported.program.payload.entry := by
  simp only [ContractBinding.protocol, UnitPayload.entry, binding.root]

theorem selected_name (binding : EntryContractBinding imported) :
    binding.owner.contract.owner = snapshot.entry := by
  exact binding.owner.owner_eq.trans
    ((congrArg (fun protocol : CheckedProtocol => protocol.name) binding.selected_root).trans imported.protocolSelection)

end EntryContractBinding
end Zkc.Source.Structured
