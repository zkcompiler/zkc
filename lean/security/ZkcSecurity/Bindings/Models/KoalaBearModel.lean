module

public import ZkcSecurity.Mathematics.Fields.KoalaBear
public import Zkc.Source.Structured.DomainLaws
public import Mathlib.Algebra.Group.PUnit

/-!
# A nominal model of the KoalaBear base and octic fields

The selected catalogue is the core's installed KoalaBear catalogue, whose rows
follow `compiler/lib/Contracts/Domains.cpp`. The random service's identity, sampled
field and methods follow `crates/zkc-runtime/src/vm/services.rs`. This is a
restricted catalogue, not the entire native installation. Its capability
strings record native admission facts; the law records prove the field,
embedding and characteristic obligations consumed here. They do not certify
two-adic operations, native arithmetic, codecs or sampling distributions.
The index-block capability and method are catalogue metadata only; this model
does not interpret index-block requests or gates.

Unknown names have a default carrier because `DomainModel` is total, but are
never admitted. There are no group rows. Only local standard algebra instances
are used to construct the stored structures; consumers select laws explicitly.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

namespace ZkcSecurity.Domains.KoalaBearModel

open Zkc.Source.Structured
open _root_.ZkcSecurity.Domains.KoalaBear (Base Octic q)

def baseIdentity : String := "koala-bear"
def octicIdentity : String := "koala-bear.ext8-binomial3"
def randomService : String := "random.koala-bear.ext8-binomial3/0"

def baseNominal : Nominal where
  identity := baseIdentity
  sort := .field
  members := []
  capabilities := ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"]
  modulus := some q

def octicNominal : Nominal where
  identity := octicIdentity
  sort := .field
  members := [("BaseField", baseIdentity)]
  capabilities := ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo",
    "ExtensionField", "IndexRandomness", "IndexBlockRandomness"]
  modulus := some q

/-- Only these two field rows and the octic random service are selected. -/
def catalogue : Catalogue := koalaBearCatalogue

theorem catalogue_eq_installed : catalogue = koalaBearCatalogue := rfl

theorem catalogue_check : catalogue.check = .ok () := by decide

/-- Resolve each nominal identity once, retaining an explicit unsupported case. -/
inductive FieldKind where
  | base | octic | unknown
  deriving DecidableEq

def resolve (identity : String) : FieldKind :=
  if identity = baseIdentity then .base
  else if identity = octicIdentity then .octic
  else .unknown

def carrier : FieldKind → Type
  | .base => Base
  | .octic => Octic
  | .unknown => Base

local instance carrierField (kind : FieldKind) : Field (carrier kind) := by
  cases kind <;> unfold carrier <;> infer_instance

local instance carrierDecidableEq (kind : FieldKind) : DecidableEq (carrier kind) := by
  cases kind <;> unfold carrier <;> infer_instance

/-- Only supported identities have an operational inverse. -/
def inverse : (kind : FieldKind) → Option (carrier kind → carrier kind)
  | .base => some (fun x : Base => x⁻¹)
  | .octic => some (fun x : Octic => x⁻¹)
  | .unknown => none

/-- The one admitted pair uses the actual constant-coefficient embedding.
Other total-function values carry no admission or homomorphism claim. -/
def embedding : (target source : FieldKind) → carrier source → carrier target
  | .octic, .base => KoalaBear.embed
  | _, _ => fun _ => 0

def model : DomainModel where
  Field identity := carrier (resolve identity)
  Group _ := PUnit
  fieldRing identity := inferInstanceAs (CommRing (carrier (resolve identity)))
  fieldDecEq identity := inferInstanceAs (DecidableEq (carrier (resolve identity)))
  inverse identity := inverse (resolve identity)
  embed extension base := embedding (resolve extension) (resolve base)
  groupAdd _ := inferInstanceAs (AddCommGroup PUnit)
  groupDecEq _ := inferInstanceAs (DecidableEq PUnit)
  smul _ _ _ point := point

theorem base_carrier : model.Field baseIdentity = Base := rfl
theorem octic_carrier : model.Field octicIdentity = Octic := rfl

theorem base_ring : model.fieldRing baseIdentity = (inferInstance : CommRing Base) := rfl
theorem octic_ring : model.fieldRing octicIdentity = (inferInstance : CommRing Octic) := rfl

@[simp] theorem inverse_base : model.inverse baseIdentity = some (fun x : Base => x⁻¹) := rfl
@[simp] theorem inverse_octic : model.inverse octicIdentity = some (fun x : Octic => x⁻¹) := rfl

/-- Equality of functions fixes the operation, not merely an isomorphic map. -/
theorem embed_eq : model.embed octicIdentity baseIdentity = KoalaBear.embed := rfl

theorem embedding_law : EmbeddingLaw (model.embed octicIdentity baseIdentity) :=
  ⟨KoalaBear.embed.map_one, KoalaBear.embed.map_mul,
    KoalaBear.embed.map_zero, KoalaBear.embed.map_add⟩

theorem embed_injective : Function.Injective (model.embed octicIdentity baseIdentity) :=
  KoalaBear.embed_injective

theorem find_eq (identity : String) : catalogue.find identity =
    if identity = baseIdentity then .ok baseNominal
    else if identity = octicIdentity then .ok octicNominal
    else .error "structured-domain-unknown" := by
  change (match [baseNominal, octicNominal].find? (fun row => row.identity == identity) with
    | some row => Except.ok row
    | none => Except.error "structured-domain-unknown") = _
  by_cases hb : identity = baseIdentity
  · subst identity
    rfl
  · by_cases he : identity = octicIdentity
    · subst identity
      rfl
    · have hb' : (baseIdentity == identity) = false := beq_eq_false_iff_ne.mpr (Ne.symm hb)
      have he' : (octicIdentity == identity) = false := beq_eq_false_iff_ne.mpr (Ne.symm he)
      simp only [List.find?_cons, baseNominal, octicNominal, hb', he',
        ↓reduceIte, List.find?_nil, hb, he]

attribute [local simp] bind pure Except.bind Except.pure throw throwThe MonadExceptOf.throw

theorem expect_field_iff (identity : String) (row : Nominal) :
    catalogue.expect identity .field = .ok row ↔
      (identity = baseIdentity ∧ row = baseNominal) ∨
      (identity = octicIdentity ∧ row = octicNominal) := by
  by_cases hb : identity = baseIdentity
  · subst identity
    simp [Catalogue.expect, find_eq, baseNominal, baseIdentity, octicIdentity, eq_comm]
  · by_cases he : identity = octicIdentity
    · subst identity
      simp [Catalogue.expect, find_eq, octicNominal, show octicIdentity ≠ baseIdentity from by decide, eq_comm]
    · simp [Catalogue.expect, find_eq, hb, he]

theorem require_field_iff (identity : String) :
    catalogue.require identity .field "Field" = .ok () ↔
      identity = baseIdentity ∨ identity = octicIdentity := by
  by_cases hb : identity = baseIdentity
  · subst identity
    simp [Catalogue.require, Catalogue.expect, find_eq, baseNominal, Nominal.holds]
  · by_cases he : identity = octicIdentity
    · subst identity
      simp [Catalogue.require, Catalogue.expect, find_eq, octicNominal, Nominal.holds,
        baseIdentity, octicIdentity]
    · simp [Catalogue.require, Catalogue.expect, find_eq, hb, he]

theorem require_embedding_iff (extension base : String) :
    catalogue.requireEmbedding extension base = .ok () ↔
      extension = octicIdentity ∧ base = baseIdentity := by
  by_cases eb : extension = baseIdentity
  · subst extension
    by_cases bb : base = baseIdentity
    · subst base
      decide
    · by_cases be : base = octicIdentity
      · subst base
        decide
      · simp [Catalogue.requireEmbedding, Catalogue.expect, find_eq, bb, be,
          baseNominal]
  · by_cases ee : extension = octicIdentity
    · subst extension
      by_cases bb : base = baseIdentity
      · subst base
        decide
      · by_cases be : base = octicIdentity
        · subst base
          decide
        · simp [Catalogue.requireEmbedding, Catalogue.expect, find_eq, bb, be,
            octicNominal, show octicIdentity ≠ baseIdentity from by decide]
    · simp [Catalogue.requireEmbedding, Catalogue.expect, find_eq, eb, ee]

theorem unknown_refused (identity : String) (hb : identity ≠ baseIdentity)
    (he : identity ≠ octicIdentity) :
    catalogue.find identity = .error "structured-domain-unknown" := by
  simp [find_eq, hb, he]

theorem scale_refused (group field : String) :
    catalogue.requireScale group field ≠ .ok () := by
  by_cases hb : group = baseIdentity
  · subst group
    simp [Catalogue.requireScale, Catalogue.expect, find_eq, baseNominal]
  · by_cases he : group = octicIdentity
    · subst group
      simp [Catalogue.requireScale, Catalogue.expect, find_eq, octicNominal,
        baseIdentity, octicIdentity]
    · simp [Catalogue.requireScale, Catalogue.expect, find_eq, hb, he]

theorem inverse_law (kind : FieldKind) (inv : carrier kind → carrier kind)
    (supplied : inverse kind = some inv) : ∀ x, x ≠ 0 → x * inv x = 1 := by
  cases kind with
  | base =>
    cases Option.some.inj supplied
    exact fun x hx => mul_inv_cancel₀ hx
  | octic =>
    cases Option.some.inj supplied
    exact fun x hx => mul_inv_cancel₀ hx
  | unknown => cases supplied

/-- The supplied inverse also agrees at zero, beyond the nonzero law record. -/
theorem inverse_zero_law (kind : FieldKind) (inv : carrier kind → carrier kind)
    (supplied : inverse kind = some inv) : inv 0 = 0 := by
  cases kind with
  | base =>
    cases Option.some.inj supplied
    exact inv_zero
  | octic =>
    cases Option.some.inj supplied
    exact inv_zero
  | unknown => cases supplied

theorem laws : DomainLaws catalogue model where
  field identity admitted := by
    rcases (require_field_iff identity).mp admitted with rfl | rfl
    · exact Field.toIsField Base
    · exact Field.toIsField Octic
  inverse identity inv supplied := inverse_law (resolve identity) inv supplied
  embedding extension base admitted := by
    obtain ⟨rfl, rfl⟩ := (require_embedding_iff extension base).mp admitted
    exact embedding_law
  action group field admitted := False.elim (scale_refused group field admitted)

/-- Recovering a field from the stored ring preserves the actual inverse too. -/
theorem field_inverse (identity : String)
    (admitted : catalogue.require identity .field "Field" = .ok ()) :
    model.inverse identity = some (laws.fieldInstance identity admitted).inv := by
  obtain ⟨inv, supplied⟩ : ∃ inv, model.inverse identity = some inv := by
    rcases (require_field_iff identity).mp admitted with rfl | rfl
    · exact ⟨_, inverse_base⟩
    · exact ⟨_, inverse_octic⟩
  rw [supplied]
  congr 1
  funext x
  let := laws.fieldInstance identity admitted
  by_cases hx : x = 0
  · subst x
    exact (inverse_zero_law (resolve identity) inv supplied).trans (inv_zero (G₀ := model.Field identity)).symm
  · exact (inv_eq_of_mul_eq_one_right (laws.inverse identity inv supplied x hx)).symm

theorem base_characteristic : CharP (model.Field baseIdentity) q :=
  inferInstanceAs (CharP Base q)

theorem octic_characteristic : CharP (model.Field octicIdentity) q := by
  let : CharP (model.Field baseIdentity) q := base_characteristic
  exact embedding_law.charP embed_injective q

theorem characteristic_laws : CharacteristicLaws catalogue model.toFieldModel := by
  intro identity row admitted p modulus
  rcases (expect_field_iff identity row).mp admitted with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases Option.some.inj modulus
    exact base_characteristic
  · cases Option.some.inj modulus
    exact octic_characteristic

/-- Finiteness is supplied explicitly for each consumed, admitted field. -/
abbrev fintype (identity : String)
    (admitted : catalogue.require identity .field "Field" = .ok ()) :
    Fintype (model.Field identity) :=
  if hb : identity = baseIdentity then by
    subst identity
    exact inferInstanceAs (Fintype Base)
  else by
    have he := ((require_field_iff identity).mp admitted).resolve_left hb
    subst identity
    exact inferInstanceAs (Fintype Octic)

theorem card_base : @Fintype.card (model.Field baseIdentity)
    (fintype baseIdentity (by decide)) = q := KoalaBear.card_base

theorem card_octic : @Fintype.card (model.Field octicIdentity)
    (fintype octicIdentity (by decide)) = q ^ 8 := KoalaBear.card_octic

/-- Cardinality selection is nominal and requires admission. -/
theorem card_admitted (identity : String)
    (admitted : catalogue.require identity .field "Field" = .ok ()) :
    @Fintype.card (model.Field identity) (fintype identity admitted) =
      if identity = baseIdentity then q else q ^ 8 := by
  rcases (require_field_iff identity).mp admitted with rfl | rfl
  · simpa using card_base
  · simpa [baseIdentity, octicIdentity] using card_octic

theorem carriers_ne : model.Field baseIdentity ≠ model.Field octicIdentity := by
  intro same
  have cards := congrArg Nat.card same
  change Nat.card Base = Nat.card Octic at cards
  rw [KoalaBear.nat_card_base, KoalaBear.nat_card_octic] at cards
  norm_num at cards

end ZkcSecurity.Domains.KoalaBearModel
