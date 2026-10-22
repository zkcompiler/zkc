module

public import Zkc.Claims.Registry
public import Zkc.Source.RegionDerivation

@[expose] public section

/-! All proof routes end at the same evaluated request type. The root method and
its audited declaration closure are different records. Audit strings cannot
establish a premise or a required implementation link. -/

set_option autoImplicit false
namespace Zkc.Claims
universe u

inductive Route where
  | endpoint | theorem | derivation
  deriving DecidableEq, Repr

inductive PremiseCategory where
  | model | hardness | sourceCorrespondence | implementation
  deriving DecidableEq, Repr

structure PremiseRecord where
  identifier : Identifier
  category : PremiseCategory
  responsibility : Responsibility
  deriving DecidableEq, Repr

structure Provenance where
  root : Route
  discharger : String
  method : Identifier
  dependencies : List String := []
  premises : List PremiseRecord := []
  deriving DecidableEq, Repr

/-- The proposition is computed by the registered function and equality is
checked by the kernel. There is no proposition supplied by a proof method. -/
structure Evaluated {Subject : Type u} {registry : Registry (PropertyExport Subject)}
    {reference : Subject → SubjectRef} {subject : Subject} {request : Wire.Request}
    (resolved : Resolved registry reference subject request) where
  proposition : Prop
  evaluated : resolved.meaning = .ok proposition

def sourcePremise : PremiseRecord := ⟨⟨"source.correspondence", 0⟩, .sourceCorrespondence, .infrastructure⟩

def Provenance.withSource (provenance : Provenance) : Provenance :=
  { provenance with premises := sourcePremise :: provenance.premises }

structure Receipt {Subject : Type u} {registry : Registry (PropertyExport Subject)}
    {reference : Subject → SubjectRef} {subject : Subject} {request : Wire.Request}
    {resolved : Resolved registry reference subject request} (meaning : Evaluated resolved) where
  proof : meaning.proposition
  provenance : Provenance
  /-- Annotation consistency only: membership does not prove source correspondence.
  The assurance report independently retains that external boundary. -/
  sourceRecorded : sourcePremise ∈ provenance.premises
  /-- Required links come from the registered request, never from a route. -/
  linkProofs : (index : Fin resolved.requiredLinks.length) →
    Option (PLift (resolved.requiredLinks.get index).goal) := fun _ => none

namespace Receipt
variable {Subject : Type u} {registry : Registry (PropertyExport Subject)}
  {reference : Subject → SubjectRef} {subject : Subject} {request : Wire.Request}
  {resolved : Resolved registry reference subject request} {meaning : Evaluated resolved}

/-- Every product here is a verifier product. Authored-pair completeness and
native/source correspondence require their own later links. -/
def product (_receipt : Receipt meaning) : String := "certified_verifier"

/-- Completeness of this receipt's registered link proofs, not final assurance
report certification. Reporting also checks subject/model admission, canonical
meaning, the remaining statement binders, axioms, and independently required
stage links. A generic receipt does not perform those security-layer audits. -/
def status (receipt : Receipt meaning) : Status :=
  if (List.finRange resolved.requiredLinks.length).all (fun index => (receipt.linkProofs index).isSome)
  then .certified else .open

def scope (_receipt : Receipt meaning) : String := "ir-relative"

def ofTheorem (proof : meaning.proposition) (provenance : Provenance)
    (links : (index : Fin resolved.requiredLinks.length) →
      Option (PLift (resolved.requiredLinks.get index).goal) := fun _ => none) : Receipt meaning :=
  ⟨proof, { provenance.withSource with root := .theorem }, List.mem_cons_self, links⟩

def ofEndpoint (proof : meaning.proposition) (provenance : Provenance)
    (links : (index : Fin resolved.requiredLinks.length) →
      Option (PLift (resolved.requiredLinks.get index).goal) := fun _ => none) : Receipt meaning :=
  ⟨proof, { provenance.withSource with root := .endpoint }, List.mem_cons_self, links⟩

/-- Thin consumer of the existing occurrence-local derivation. Its semantic
soundness theorem is applied, and the registered consumer must prove an actual
implication to exactly the same evaluated meaning as every other route. -/
def ofDerivation {dialect : Zkc.Source.Dialect} {I J : PIR.Signature}
    {semantics : Zkc.Source.RegionMeaning dialect I}
    {operations : PIR.OperationInterpretation I J} {Γ out : List dialect.Ty}
    {region : Zkc.Source.Region dialect Γ out}
    {environment : Zkc.Source.Environment semantics.Value Γ}
    {process : PIR.Process J (Zkc.Source.Values semantics.Value out)}
    (derivation : Zkc.Source.Region.Derivation semantics operations region environment process)
    (consume : (region.denote semantics environment).interpret operations = process → meaning.proposition)
    (provenance : Provenance)
    (links : (index : Fin resolved.requiredLinks.length) →
      Option (PLift (resolved.requiredLinks.get index).goal) := fun _ => none) : Receipt meaning :=
  ⟨consume derivation.sound, { provenance.withSource with root := .derivation }, List.mem_cons_self, links⟩

end Receipt
end Zkc.Claims
