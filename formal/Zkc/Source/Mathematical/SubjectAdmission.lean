import Zkc.Source.Mathematical.ClosedProvenance

/-! Complete mathematical source formation under explicit installed contracts.

All declarations, relations and symbolic definitions are checked, including
unused syntax. Closed admission then follows syntactic reachability from the
entry and rechecks actual instantiated bodies. The result retains the authored
source, typed bodies, call identities and the header's actual root table.
Operational package interpretations and byte-reader adequacy are separate.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.SubjectAdmission

inductive Error where
  | declaration (reason : DeclarationAdmission.Error)
  | relation (reason : RelationAdmission.Error)
  | template (reason : DefinitionCalls.Error)
  | discovery (reason : ClosedInstances.Error)
  | assembly (reason : ClosedAssembly.Error)
  deriving Repr

structure Admitted {Payload : ManifestAdmission.Category → Type}
    (contracts : RegistryAdmission.Contracts Payload) (source : Raw.Subject) where
  header : DeclarationAdmission.Header contracts source
  relations : Values (fun declaration => RelationAdmission.Instance header declaration
    (DeclarationAdmission.parameters declaration.statics)) source.module.relations
  templates : Values (DefinitionCalls.Template header) (List.range source.module.definitions.length)
  assembly : ClosedAssembly.Result header

/-- Resolution passes share an allowance. Intrinsic formation still uses
an independent nesting limit; complete work accounting and native/Lean capacity equivalence
remain separate obligations. Resource refusal does not prove ill-formedness. -/
def admit {Payload : ManifestAdmission.Category → Type} (contracts : RegistryAdmission.Contracts Payload)
    (source : Raw.Subject) : StateT Nat (Except Error) (Admitted contracts source) := do
  let header ← fun remaining => (DeclarationAdmission.admit contracts source remaining).mapError Error.declaration
  let relations ← fun remaining => (RelationAdmission.all header source.module.relations remaining).mapError Error.relation
  let templates ← fun remaining => (DefinitionCalls.declarations header remaining).mapError Error.template
  let graph ← fun remaining => (ClosedInstances.discover source remaining).mapError Error.discovery
  let assembly ← fun remaining => (ClosedAssembly.assemble header graph remaining).mapError Error.assembly
  return ⟨header, relations, templates, assembly⟩

end Zkc.Source.Mathematical.SubjectAdmission
