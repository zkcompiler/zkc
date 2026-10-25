module

public import ZkcSecurity.Claims.DomainModel
public import Zkc.Source.Structured.CatalogueJustification
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! A closed prime-field installation for protocols using one scalar domain.
The mathematical specialization uses the additive scalar carrier for unused
group names; it makes no claim about native curve groups or codecs. Catalogue
admission and the characteristic check remain required for every selected source.
-/
set_option autoImplicit false

namespace ZkcSecurity.Domains.PrimeField
open Zkc.Source Zkc.Source.Structured

abbrev model (modulus : Nat) : DomainModel := ringModel (ZMod modulus) (ZMod modulus)

/-- A finite metadata check; field cardinality is still taken from the carrier. -/
def compatible (catalogue : Catalogue) (modulus : Nat) : Bool :=
  catalogue.nominals.all fun row => row.sort != .field || row.modulus == some modulus

theorem expected_field {catalogue : Catalogue} {identity : String} {row : Nominal}
    (found : catalogue.expect identity .field = .ok row) :
    row ∈ catalogue.nominals ∧ row.sort = .field := by
  unfold Catalogue.expect Catalogue.find at found
  cases lookup : catalogue.nominals.find? (·.identity == identity) with
  | none => simp [lookup] at found
  | some selected =>
    simp only [lookup] at found
    change (if selected.sort != .field then Except.error "structured-domain-sort"
      else .ok selected) = .ok row at found
    split at found
    · cases found
    · rename_i same
      cases found
      exact ⟨List.mem_of_find?_eq_some lookup, by simpa using same⟩

theorem characteristic (catalogue : Catalogue) (modulus : Nat)
    (checked : compatible catalogue modulus = true) :
    CharacteristicLaws catalogue (model modulus).toFieldModel := by
  intro identity row found p selected
  obtain ⟨member, field⟩ := expected_field found
  have rowChecked := List.all_eq_true.mp checked row member
  simp only [field, bne_self_eq_false, Bool.false_or, beq_iff_eq] at rowChecked
  have same : p = modulus := Option.some.inj (selected.symm.trans rowChecked)
  subst p
  exact inferInstanceAs (CharP (ZMod modulus) modulus)

noncomputable abbrev rawSampleable (modulus : Nat) [NeZero modulus] :
    (event : Zkc.Construction.Domain.Event (model modulus).toCarriers) →
      SampleableType (Zkc.Construction.Domain.Raw event)
  | .challenge origin => by
      cases origin with
      | mk entry event request =>
        cases request with
        | none => exact inferInstanceAs (SampleableType Unit)
        | some request =>
          cases request with
          | mk method parameters sort =>
            cases sort
            case field identity => exact SampleableType.ofFintype (ZMod modulus)
            all_goals exact inferInstanceAs (SampleableType Unit)
  | .message .. | .publicBinding .. => inferInstanceAs (SampleableType Unit)

noncomputable def capabilities (snapshot : Snapshot) (modulus : Nat)
    [Fact modulus.Prime] (checked : compatible snapshot.catalogue modulus = true) :
    Claims.Domain.Capabilities (model modulus) snapshot where
  algebra := ringModel_laws (ZMod modulus) (ZMod modulus) snapshot.catalogue
  characteristic := characteristic snapshot.catalogue modulus checked
  finite _ _ := inferInstanceAs (Fintype (ZMod modulus))
  samples := rawSampleable modulus

instance blsPrime : Fact blsModulus.Prime := ⟨blsModulus_prime⟩

abbrev blsScalarModel := model blsModulus

noncomputable def blsCapabilities (snapshot : Snapshot)
    (checked : compatible snapshot.catalogue blsModulus = true) :
    Claims.Domain.Capabilities blsScalarModel snapshot :=
  capabilities snapshot blsModulus checked

end ZkcSecurity.Domains.PrimeField
