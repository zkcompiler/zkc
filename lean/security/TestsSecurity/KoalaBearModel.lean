module

public import ZkcSecurity.Bindings.Models.KoalaBearModel
public import Zkc.Source.Structured.DomainEvaluation

/-! Nominal admission, operation coherence and characteristic controls for the
actual KoalaBear base/octic model. These are independent mathematical checks;
they do not construct an endpoint or identify a native arithmetic provider. -/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

namespace TestsSecurity.KoalaBearModel

open Zkc.Source.Structured
open ZkcSecurity.Domains.KoalaBearModel
open ZkcSecurity.Domains.KoalaBear (Base Octic q)

example : q = 2130706433 := rfl
example : catalogue.check = .ok () := catalogue_check
example : model.Field "koala-bear" = Base := rfl
example : model.Field "koala-bear.ext8-binomial3" = Octic := rfl
example : model.Field baseIdentity ≠ model.Field octicIdentity := carriers_ne

example : catalogue.expect baseIdentity .field = .ok baseNominal := by decide
example : catalogue.expect octicIdentity .field = .ok octicNominal := by decide
example : catalogue.require baseIdentity .field "Field" = .ok () := by decide
example : catalogue.require octicIdentity .field "ExtensionField" = .ok () := by decide
example : octicNominal.member "BaseField" = some baseIdentity := by decide
example : baseNominal.modulus = some 2130706433 := rfl
example : octicNominal.modulus = some 2130706433 := rfl

example : catalogue.requireEmbedding octicIdentity baseIdentity = .ok () := by decide
example : catalogue.requireEmbedding baseIdentity octicIdentity =
    .error "structured-domain-capability" := by decide
example : catalogue.requireEmbedding octicIdentity octicIdentity =
    .error "structured-domain-member" := by decide
example : catalogue.requireEmbedding baseIdentity baseIdentity =
    .error "structured-domain-capability" := by decide
example : catalogue.requireEmbedding "koala-bear.ext4-binomial3" baseIdentity =
    .error "structured-domain-unknown" := by decide
example : catalogue.requireEmbedding octicIdentity "missing" =
    .error "structured-domain-unknown" := by decide

-- An unknown carrier's total interpretation never earns catalogue admission.
example : model.Field "missing" = Base := rfl
example : model.inverse "missing" = none := rfl
example : catalogue.require "missing" .field "Field" =
    .error "structured-domain-unknown" := by decide
example (identity : String) (hb : identity ≠ baseIdentity) (he : identity ≠ octicIdentity) :
    catalogue.find identity = .error "structured-domain-unknown" := unknown_refused identity hb he
example (identity : String) (admitted : catalogue.require identity .field "Field" = .ok ()) :
    identity = baseIdentity ∨ identity = octicIdentity := (require_field_iff identity).mp admitted
example (extension base : String)
    (admitted : catalogue.requireEmbedding extension base = .ok ()) :
    extension = octicIdentity ∧ base = baseIdentity := (require_embedding_iff extension base).mp admitted

example : catalogue.requireDraw "random.koala-bear.ext8-binomial3/0" octicIdentity = .ok () := by decide
example : catalogue.requireDraw randomService baseIdentity = .error "structured-service-contract" := by decide
example : catalogue.findService "random.koala-bear/0" = .error "structured-service-contract" := by decide
example : (catalogue.findService randomService).map Service.methods = .ok ["draw", "index"] := by decide
example : catalogue.require baseIdentity .field "IndexRandomness" =
    .error "structured-domain-capability" := by decide
example : catalogue.require octicIdentity .field "PrimeField" =
    .error "structured-domain-capability" := by decide
example (group field : String) : catalogue.requireScale group field ≠ .ok () := scale_refused group field
example : model.Group "missing" = PUnit := rfl

example : DomainLaws catalogue model := laws
example : CharacteristicLaws catalogue model.toFieldModel := characteristic_laws
example : model.fieldRing baseIdentity = (inferInstance : CommRing Base) := base_ring
example : model.fieldRing octicIdentity = (inferInstance : CommRing Octic) := octic_ring
example (identity : String) (admitted : catalogue.require identity .field "Field" = .ok ()) :
    (laws.fieldInstance identity admitted).toCommRing = model.fieldRing identity :=
  laws.field_ring identity admitted
example (identity : String) (admitted : catalogue.require identity .field "Field" = .ok ()) :
    model.inverse identity = some (laws.fieldInstance identity admitted).inv := field_inverse identity admitted

example : model.inverse baseIdentity = some (fun x : Base => x⁻¹) := inverse_base
example : model.inverse octicIdentity = some (fun x : Octic => x⁻¹) := inverse_octic
example (x : Base) (hx : x ≠ 0) : x * x⁻¹ = 1 :=
  laws.inverse baseIdentity (Inv.inv (α := Base)) inverse_base x hx
example (x : Octic) (hx : x ≠ 0) : x * x⁻¹ = 1 :=
  laws.inverse octicIdentity (Inv.inv (α := Octic)) inverse_octic x hx
example : ((laws.fieldInstance baseIdentity (by decide)).inv : Base → Base) =
    Inv.inv (α := Base) := (Option.some.inj (inverse_base.symm.trans (field_inverse _ _))).symm
example : ((laws.fieldInstance octicIdentity (by decide)).inv : Octic → Octic) =
    Inv.inv (α := Octic) := (Option.some.inj (inverse_octic.symm.trans (field_inverse _ _))).symm

example : model.embed octicIdentity baseIdentity = ZkcSecurity.Domains.KoalaBear.embed := embed_eq
example : EmbeddingLaw (model.embed octicIdentity baseIdentity) := embedding_law
example : Function.Injective (model.embed octicIdentity baseIdentity) := embed_injective
example : embedding_law.toRingHom = ZkcSecurity.Domains.KoalaBear.embed := by ext x; rfl
example (a b : Base) : model.embed octicIdentity baseIdentity (a + b) =
    model.embed octicIdentity baseIdentity a + model.embed octicIdentity baseIdentity b :=
  embedding_law.map_add a b
example (a b : Base) : model.embed octicIdentity baseIdentity (a * b) =
    model.embed octicIdentity baseIdentity a * model.embed octicIdentity baseIdentity b :=
  embedding_law.map_mul a b
example : model.embed octicIdentity baseIdentity (1 : Base) = (1 : Octic) := embedding_law.map_one
example (a : Base) : Evaluation.operationOn model SiteObservations.closed []
    (.fieldEmbed octicIdentity baseIdentity) (.cons a .nil) .nil =
    .done (.cons (ZkcSecurity.Domains.KoalaBear.embed a) .nil) := rfl
example (x y : Octic) : Evaluation.operationOn model SiteObservations.closed []
    (.fieldMultiply octicIdentity) (.cons x (.cons y .nil)) .nil =
    .done (.cons (x * y) .nil) := rfl

theorem zero_embedding_rejected : ¬ EmbeddingLaw (fun _ : Base => (0 : Octic)) :=
  EmbeddingLaw.not_zero

example (identity : String) (admitted : catalogue.require identity .field "Field" = .ok ()) :
    Fintype (model.Field identity) := fintype identity admitted
example : @Fintype.card (model.Field baseIdentity) (fintype baseIdentity (by decide)) = q := card_base
example : @Fintype.card (model.Field octicIdentity) (fintype octicIdentity (by decide)) = q ^ 8 := card_octic
example (identity : String) (admitted : catalogue.require identity .field "Field" = .ok ()) :
    @Fintype.card (model.Field identity) (fintype identity admitted) =
      if identity = baseIdentity then q else q ^ 8 := card_admitted identity admitted
example : CharP (model.Field baseIdentity) q := base_characteristic
example : CharP (model.Field octicIdentity) q := octic_characteristic

theorem characteristic_not_octic_cardinality : ¬ CharP (model.Field octicIdentity) (q ^ 8) := by
  intro wrong
  have same := CharP.eq (model.Field octicIdentity) octic_characteristic wrong
  norm_num at same

theorem characteristic_not_two : ¬ CharP (model.Field baseIdentity) 2 := by
  intro wrong
  have same := CharP.eq (model.Field baseIdentity) base_characteristic wrong
  norm_num at same

def wrongCharacteristic : Catalogue :=
  { catalogue with nominals := [baseNominal, { octicNominal with modulus := some (q ^ 8) }] }

example : wrongCharacteristic.check = .ok () := by decide
example : wrongCharacteristic.requireEmbedding octicIdentity baseIdentity =
    .error "structured-domain-modulus" := by decide

theorem wrong_characteristic_laws_rejected :
    ¬ CharacteristicLaws wrongCharacteristic model.toFieldModel := by
  intro wrong
  apply characteristic_not_octic_cardinality
  exact wrong octicIdentity { octicNominal with modulus := some (q ^ 8) } (by rfl) (q ^ 8) rfl

end TestsSecurity.KoalaBearModel
