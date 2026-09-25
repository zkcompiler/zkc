import Tools.Interactive.Bindings

/-! Independent finite full-type contracts. These tests do not enable portable
source correspondence; they exercise its nominal/representation foundation. -/
set_option autoImplicit false
namespace Tests.ExplicitBindings
open Tools.Interactive Tools.Interactive.Bindings

private def succeeds {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false
private def ports (binding : Declaration) (physical : Bool) : List String :=
  match resolve physical binding with
  | .ok signature => (signature.inputs ++ signature.outputs).map ValueType.spelling
  | .error _ => []

example : ports ⟨"fold", "poly.fold", ["bls12-381.fr"], "arkworks-msb/poly.fold"⟩ true =
    ["table:bls12-381.fr@arkworks.mle-msb/1", "field:bls12-381.fr@arkworks.fr/1",
     "table:bls12-381.fr@arkworks.mle-msb/1"] := by native_decide
example : ports ⟨"fold", "poly.fold", ["bls12-381.fr"], "arkworks-msb/poly.fold"⟩ false =
    ["table:bls12-381.fr", "field:bls12-381.fr", "table:bls12-381.fr"] := by native_decide
example : ports ⟨"open", "pcs.open", ["multilinear.kzg.bls12-381/1"], "arkworks/pcs.open"⟩ false =
    ["opening_state:multilinear.kzg.bls12-381/1", "point:bls12-381.fr",
     "field:bls12-381.fr", "proof:multilinear.kzg.bls12-381/1"] := by native_decide
example : ports ⟨"empty", "poly.empty_point", ["bls12-381.fr"], "arkworks/poly.empty_point"⟩ true =
    ["point:bls12-381.fr@arkworks.point/1"] := by native_decide
example : succeeds (resolve true ⟨"empty", "poly.empty_point", [], "arkworks/poly.empty_point"⟩) = false := by native_decide
example : succeeds (resolve true ⟨"fold", "poly.fold", ["bls12-381.g1"], "arkworks/poly.fold"⟩) = false := by native_decide
example : succeeds (resolve true ⟨"fold", "poly.fold", ["bls12-381.fr"], "arkworks/curve.scale"⟩) = false := by native_decide
example : succeeds (resolve true ⟨"old", "group.public", ["bls12-381.g1"], "reference/group.public"⟩) = false := by native_decide
example : succeeds (resolve false ⟨"observe", "transcript.observe.group",
    ["merlin3.bls12-381.fr64be/1", "bls12-381.g1", "zkcv.group.bls12-381.g1/1"], ""⟩) = true := by native_decide
example : succeeds (resolve false ⟨"observe", "transcript.observe.group",
    ["merlin3.bls12-381.fr64be/1", "bls12-381.g1", "zkcv.field.bls12-381.fr/1"], ""⟩) = false := by native_decide
example : succeeds (resolve false ⟨"challenge", "transcript.challenge",
    ["sha256.fiat-shamir.bls12-381/1"], ""⟩) = false := by native_decide
example : succeeds (resolve true ⟨"convert", "table.relayout",
    ["bls12-381.fr", "arkworks.mle-lsb/1", "arkworks.mle-msb/1"], "arkworks/table.relayout"⟩) = true := by native_decide
example : succeeds (resolve true ⟨"convert", "table.relayout",
    ["bls12-381.fr", "arkworks.mle-lsb/1", "arkworks.mle-lsb/1"], "arkworks/table.relayout"⟩) = false := by native_decide
example : succeeds (valueType true "table:bls12-381.fr@arkworks.mle-msb/1") = true := by native_decide
example : succeeds (valueType true "table:bls12-381.g1@arkworks.mle-msb/1") = false := by native_decide
example : succeeds (valueType true "field:bls12-381.fr@arkworks.g1/1") = false := by native_decide
example : succeeds (valueType false "table:bls12-381.fr@arkworks.mle-msb/1") = false := by native_decide
example : succeeds (valueType true "bool:@native.bool/1") = false := by native_decide
example : succeeds (valueType true "bool@native.bool/1") = true := by native_decide
example : (match associatedSort .commitment "EvaluationField" with | .ok .field => true | _ => false) = true := by native_decide
example : succeeds (associatedSort .field "Scalar") = false := by native_decide
end Tests.ExplicitBindings
