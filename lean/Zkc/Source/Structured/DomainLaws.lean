module

public import Zkc.Source.Structured.DomainModels
public import Zkc.Source.Structured.Catalogue
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Algebra.Defs

@[expose] public section

/-! Algebraic laws for the operations of an admitted domain interpretation.

The model owns operations and carriers. These propositions justify only the
capabilities and pairs selected by the catalogue. Field and module instances
are installed locally by consumers; typeclass search never chooses a model or
an admitted pair. Characteristic is separate from carrier cardinality.
-/

set_option autoImplicit false
namespace Zkc.Source.Structured

/-- Homomorphism laws for the actual embedding operation. -/
structure EmbeddingLaw {B E : Type} [CommRing B] [CommRing E] (embed : B → E) : Prop where
  map_one : embed 1 = 1
  map_mul : ∀ x y, embed (x * y) = embed x * embed y
  map_zero : embed 0 = 0
  map_add : ∀ x y, embed (x + y) = embed x + embed y

namespace EmbeddingLaw
variable {B E : Type} [CommRing B] [CommRing E] {embed : B → E}

def toRingHom (law : EmbeddingLaw embed) : B →+* E where
  toFun := embed
  map_one' := law.map_one
  map_mul' := law.map_mul
  map_zero' := law.map_zero
  map_add' := law.map_add

theorem coe_toRingHom (law : EmbeddingLaw embed) : ⇑law.toRingHom = embed := rfl

theorem not_zero [Nontrivial E] : ¬ EmbeddingLaw (fun _ : B => (0 : E)) :=
  fun law => zero_ne_one law.map_one

theorem charP (law : EmbeddingLaw embed) (injective : Function.Injective embed) (p : Nat)
    [CharP B p] : CharP E p where
  cast_eq_zero_iff x := by
    rw [← CharP.cast_eq_zero_iff B p x, ← map_natCast law.toRingHom x]
    exact ⟨fun zero => injective (zero.trans law.map_zero.symm),
      fun zero => by rw [zero, _root_.map_zero law.toRingHom]⟩

end EmbeddingLaw

theorem EmbeddingLaw.injective {B E : Type} [Field B] [CommRing E] [Nontrivial E]
    {embed : B → E} (law : EmbeddingLaw embed) : Function.Injective embed := by
  intro x y same
  by_contra different
  have unit : (x - y) * (x - y)⁻¹ = 1 := mul_inv_cancel₀ (sub_ne_zero.mpr different)
  have mapped := congrArg law.toRingHom unit
  rw [_root_.map_mul law.toRingHom, _root_.map_one law.toRingHom,
    _root_.map_sub law.toRingHom] at mapped
  have equal : law.toRingHom x = law.toRingHom y := same
  rw [equal, sub_self, zero_mul] at mapped
  exact zero_ne_one mapped

/-- Module laws for the model's stored action, without replacing its operations. -/
structure ActionLaw {K M : Type} [CommRing K] [AddCommGroup M]
    (smul : K → M → M) : Prop where
  one_smul : ∀ m, smul 1 m = m
  mul_smul : ∀ a b m, smul (a * b) m = smul a (smul b m)
  smul_zero : ∀ a, smul a 0 = 0
  smul_add : ∀ a m n, smul a (m + n) = smul a m + smul a n
  add_smul : ∀ a b m, smul (a + b) m = smul a m + smul b m
  zero_smul : ∀ m, smul 0 m = 0

abbrev ActionLaw.toModule {K M : Type} [CommRing K] [AddCommGroup M]
    {smul : K → M → M} (law : ActionLaw smul) : Module K M where
  smul := smul
  one_smul := law.one_smul
  mul_smul := law.mul_smul
  smul_zero := law.smul_zero
  smul_add := law.smul_add
  add_smul := law.add_smul
  zero_smul := law.zero_smul

/-- Laws are required only for admitted capabilities. Ring-only domains need
no field or finite-carrier structure. Unsupported pairs remain inadmissible. -/
structure DomainLaws (catalogue : Catalogue) (model : DomainModel) : Prop where
  field : ∀ d, catalogue.require d .field "Field" = .ok () → IsField (model.Field d)
  inverse : ∀ d (inv : model.Field d → model.Field d), model.inverse d = some inv →
    ∀ x, x ≠ 0 → x * inv x = 1
  embedding : ∀ extension base, catalogue.requireEmbedding extension base = .ok () →
    EmbeddingLaw (model.embed extension base)
  action : ∀ group field, catalogue.requireScale group field = .ok () →
    ActionLaw (model.smul group field)

/-- Modulus describes the characteristic, not the size of an extension field. -/
def CharacteristicLaws (catalogue : Catalogue) (model : FieldModel) : Prop :=
  ∀ d row, catalogue.expect d .field = .ok row →
    ∀ p, row.modulus = some p → CharP (model.Field d) p

namespace DomainLaws
variable {catalogue : Catalogue} {model : DomainModel}

/-- This field retains the model's existing ring operations. Use it locally. -/
noncomputable abbrev fieldInstance (laws : DomainLaws catalogue model) (d : String)
    (admitted : catalogue.require d .field "Field" = .ok ()) : Field (model.Field d) :=
  (laws.field d admitted).toField

theorem field_ring (laws : DomainLaws catalogue model) (d : String)
    (admitted : catalogue.require d .field "Field" = .ok ()) :
    (laws.fieldInstance d admitted).toCommRing = model.fieldRing d := by
  with_reducible_and_instances rfl

theorem embedding_injective (laws : DomainLaws catalogue model) (extension base : String)
    (baseField : catalogue.require base .field "Field" = .ok ())
    (extensionField : catalogue.require extension .field "Field" = .ok ())
    (admitted : catalogue.requireEmbedding extension base = .ok ()) :
    Function.Injective (model.embed extension base) := by
  let := laws.fieldInstance base baseField
  let := laws.fieldInstance extension extensionField
  exact (laws.embedding extension base admitted).injective

end DomainLaws

/-- The uniform interpretation is a mathematical specialization. This does not
identify different nominal cardinalities, characteristics or native codecs. -/
theorem ringModel_laws (F G : Type) [Field F] [DecidableEq F] [AddCommGroup G]
    [Module F G] [DecidableEq G] (catalogue : Catalogue) :
    DomainLaws catalogue (ringModel F G) where
  field _ _ := Field.toIsField F
  inverse _ _ supplied := by cases supplied
  embedding _ _ _ := ⟨rfl, fun _ _ => rfl, rfl, fun _ _ => rfl⟩
  action _ _ _ := ⟨one_smul F, mul_smul, smul_zero, smul_add, add_smul, zero_smul F⟩

end Zkc.Source.Structured
