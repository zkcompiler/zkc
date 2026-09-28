import Zkc.Source.Mathematical.ClosedAssembly

/-! Computational views of the bodies actually stored by closed admission.

Every view comes from the intrinsic program in assembly history. Operation and
wire keys retain their checked declaration identities; the source and intrinsic
erasure theorems on Prepared certify the two admission boundaries. This view
does not parse or elaborate a second body.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.PlacementView

variable {Payload : ManifestAdmission.Category → Type} {contracts : RegistryAdmission.Contracts Payload}
  {source : Raw.Subject} (header : DeclarationAdmission.Header contracts source)

structure Body where
  key : ClosedInstances.Key
  parties : List Nat
  capabilities : List (Protocol.Capability Nat (RegisteredVocabulary.vocabulary header 0).Service)
  arguments : List (Port Nat (RegisteredVocabulary.vocabulary header 0).Ty)
  results : List (Port Nat (RegisteredVocabulary.vocabulary header 0).Ty)
  program : Protocol.Raw Nat (RegisteredVocabulary.vocabulary header 0)

def ofPrepared {records key node} (prepared : ClosedAssembly.Prepared header records key node) : Body header :=
  ⟨key, prepared.target.parties, prepared.bound.selected.bound,
    prepared.bound.signature.value.arguments, prepared.bound.signature.value.results,
    prepared.bound.body.checked.program.erase⟩

def history : {records : List (ClosedAssembly.Record header)} →
    ClosedAssembly.History header records → List (Body header)
  | _, .nil => []
  | _, .snoc previous prepared => history previous ++ [ofPrepared header prepared]

end Zkc.Source.Mathematical.PlacementView
