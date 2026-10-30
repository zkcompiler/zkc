module

public import ZkcSecurity.Bindings.Sumcheck.SourceFamilyRoots
public import ZkcSecurity.Bindings.Sumcheck.SourceFamilyProperties
public import ZkcSecurity.Bindings.Sumcheck.SourceFamilyPair
public import Zkc.Source.Structured.ComponentClosure
public import ZkcSecurity.Bindings.Source.HelperComponents
public import ZkcSecurity.Bindings.Source.PropertyAssembly
public meta import ZkcSecurityTools.SourceProperties
public meta import ZkcTools.StructuredSource.Composition
public meta import ZkcSecurityTools.SourceProperties.Builder

@[expose] public section

/-! Contracts selected by the common source composition proposer. A successful
Boolean carries only the implication to its represented claim. This supports
arbitrary Boolean conjunction trees without choosing a false leaf in advance.
All helper laws retain their optional inputs and complete returned tuples. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourceFamily
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured ReferenceLibrary Zkc.Transcript Zkc.Obligations
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent SourceIteration
open ZkcSecurity.FiatShamir
variable {program : Zkc.Source.Structured.Program} (model : DomainModel)
  [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {E P : Type} {Raw : E → Type}

/-- The contract is unconditional on public input shape and scalar truth. The
implication is established outside the same reached-history collision escape
set used for rejection; a false returned leaf does not stop its siblings. -/
def one_summary (installation : Installation program) (site : String)
    (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (escape : EscapeJudgment E Raw) (empty : ∀ reached event, escape reached event (fun _ => False))
    (steps : RepeatedComponent.NoContract
      (component model program.payload.definitions (Occurrence.table model program.payload)
        (context site) handle) absorb escape (no model original ()))
    (history : List E) :
    Derivation absorb escape (fun _ out => ∃ accepted : Bool, out = some accepted ∧
      (accepted = true → count ≤ installation.maximum ∧ original.length = 2^count ∧ scalar = original.sum))
      history (one installation model {} site (some original) (some scalar) (some count) (some handle)) := by
  classical
  by_cases valid : count ≤ installation.maximum ∧ original.length = 2^count ∧ scalar = original.sum
  · exact (Derivation.ofYields empty (one_present model installation site original count handle scalar) history).consequence
      (fun _ _ present => by obtain ⟨accepted, rfl⟩ := present; exact ⟨accepted, rfl, fun _ => valid⟩)
  · exact (one_no model installation site original count handle scalar absorb escape empty steps valid history).consequence
      (fun _ _ rejected => ⟨false, rejected, by simp⟩)

/-- The installed Pair law with the source bound supplying its machine-index
capability. Applicability remains a kernel-checked local obligation. -/
theorem pair_contract (installation : Installation program) (scope : ZkcSecurity.Source.PairScope)
    (roles : scope.producer = 0 ∧ scope.validator = 1)
    (site : String) (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (delivery : (SumcheckRoundNormalForms.challengeSite (context site),
      SumcheckRoundNormalForms.deliverySite (context site)) ∈ scope.deliveries)
    (shape : original.length = 2^count) (bounded : count ≤ installation.maximum)
    (finite : original.length < indexLimit) (honest : scalar = original.sum) :
    ZkcSecurity.Source.Pair scope (fun _ v => v = some true)
      (producerOne installation model site original count)
      (one installation model {} site (some original) (some scalar) (some count) (some handle)) :=
  pair model installation site scope roles delivery original count handle scalar () shape bounded
    (lt_of_le_of_lt bounded installation.maximum_small) finite honest

abbrev conjunctionHelper : Helper :=
  ⟨"s3h7a6b637h626f6f6c65616e4h626f7468", .math, [.boolean, .boolean], [.boolean]⟩

def optionalAnd (a b : Option Bool) : Option Bool := a.bind fun left => b.map fun right => left && right

omit fieldLaw in
theorem conjunction_equation
    (body : BodyIn program.payload.definitions conjunctionHelper (Sum.both model).body)
    (a b : Option Bool) :
    invoke (Occurrence.helpers model program.payload).components conjunctionHelper (.cons a (.cons b .nil)) =
      .done (.cons (optionalAnd a b) .nil) := by
  change invoke (tables model program.payload.definitions).components conjunctionHelper _ = _
  apply ZkcSecurity.Source.HelperComponents.invoke model program.payload.definitions
    program.payload.linked conjunctionHelper (Sum.both model).body body
  intro tables
  cases a <;> cases b <;> rfl

end ZkcSecurity.Realizations.Sumcheck.SourceFamily
