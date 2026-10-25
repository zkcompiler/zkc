import Zkc.Source.Structured.Import
import Zkc.Source.Structured.NormalForm.Soundness
import Zkc.Construction.Semantics
import Mathlib.Algebra.Ring.Prod

/-! Nominal embedding admission and operational interpretation controls.
These fixtures test operation selection; algebraic domain laws and the concrete
extension-field endpoint are separate consumers. -/

set_option autoImplicit false
namespace Tests.FieldEmbedding
open Lean Zkc.Source Zkc.Source.Structured

private def catalogue : Catalogue where
  nominals := [
    ⟨"base", .field, [], ["CommRing", "Field"], some 3⟩,
    ⟨"other", .field, [], ["CommRing", "Field"], some 3⟩,
    ⟨"extension", .field, [("BaseField", "base")],
      ["CommRing", "Field", "ExtensionField"], some 3⟩,
    ⟨"missing-extension-capability", .field, [("BaseField", "base")],
      ["CommRing", "Field"], some 3⟩,
    ⟨"missing-field-capability", .field, [("BaseField", "base")],
      ["CommRing", "ExtensionField"], some 3⟩,
    ⟨"ring", .field, [], ["CommRing"], some 3⟩,
    ⟨"ring-extension", .field, [("BaseField", "ring")],
      ["CommRing", "Field", "ExtensionField"], some 3⟩,
    ⟨"wrong-characteristic", .field, [("BaseField", "base")],
      ["CommRing", "Field", "ExtensionField"], some 5⟩,
    ⟨"missing-characteristic", .field, [("BaseField", "base")],
      ["CommRing", "Field", "ExtensionField"], none⟩]
  services := []

private def snapshot : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '0')
  entry := "main"
  domains := []
  relations := []
  bindings := [⟨"embed", "field.embed", ["extension"], ""⟩]
  definitions := []
  catalogue := catalogue

private def helper (extension base : String) (kind : Kind := .math)
    (descriptor : Descriptor := .fieldEmbed extension base)
    (input : String := base) (output : String := extension) : Definition :=
  .function ⟨"embed_helper", kind, .privateDef, [.field input], [.field output], none, [],
    if kind == .local then some (.local "embed_helper" []) else none,
    .block [.instruction descriptor [0] [.field output] []
      (if kind == .local then "embed_site" else "")] (.ret [0])⟩

private def admit (extension base : String) : Except String CheckedDefinition :=
  checkDefinition snapshot [] [] (helper extension base)

example : catalogue.check = .ok () := by decide
example : (admit "extension" "base").isOk = true := by decide
example : (admit "extension" "other").map (fun _ => ()) =
    .error "structured-domain-member" := by decide
example : (admit "base" "extension").map (fun _ => ()) =
    .error "structured-domain-capability" := by decide
example : (admit "missing-extension-capability" "base").map (fun _ => ()) =
    .error "structured-domain-capability" := by decide
example : (admit "missing-field-capability" "base").map (fun _ => ()) =
    .error "structured-domain-capability" := by decide
example : (admit "ring-extension" "ring").map (fun _ => ()) =
    .error "structured-domain-capability" := by decide
example : (admit "wrong-characteristic" "base").map (fun _ => ()) =
    .error "structured-domain-modulus" := by decide
example : (admit "missing-characteristic" "base").map (fun _ => ()) =
    .error "structured-domain-modulus" := by decide

-- Exact native binding, with no new exec descriptor shape.
example : (checkDefinition snapshot [] [] (helper "extension" "base" .local
    (.exec "algebra.exec.field_embed" "embed" []))).isOk = true := by decide
example : (checkDefinition snapshot [] [] (helper "extension" "base" .local
    (.exec "algebra.exec.field_embed" "embed" []))).map (fun checked => checked.raw.operations) =
    .ok [.mark "embed_site", .fieldEmbed "extension" "base"] := rfl
example : (checkDefinition snapshot [] [] (helper "extension" "base" .local
    (.exec "algebra.exec.field_embed" "embed" ["unexpected"]))).map (fun _ => ()) =
    .error "structured-primitive-parameters" := by decide
example : (checkDefinition snapshot [] [] (helper "extension" "base" .local
    (.exec "algebra.exec.field_equal" "embed" []))).map (fun _ => ()) =
    .error "structured-binding-contract" := by decide
example : (checkDefinition snapshot [] [] (helper "extension" "base" .math
    (.fieldEmbed "extension" "base") "other")).map (fun _ => ()) =
    .error "structured-formation" := by decide
example : (checkDefinition snapshot [] [] (helper "extension" "base" .math
    (.fieldEmbed "extension" "base") "base" "base")).map (fun _ => ()) =
    .error "structured-formation" := by decide

example : Format.descriptor (.arr #[.str "field.embed", .str "extension", .str "base"]) =
    .ok (.fieldEmbed "extension" "base") := by decide
example : Format.descriptor (.arr #[.str "field.embed", .str "extension"]) =
    .error "structured-operation-unsupported" := by decide
example : Format.descriptor (.arr #[.str "field.embed", .str "extension", .str "base", .str "extra"]) =
    .error "structured-operation-unsupported" := by decide
example : (Op.fieldEmbed "extension" "base").arguments = [.field "base"] := rfl
example : (Op.fieldEmbed "extension" "base").results = [.field "extension"] := rfl

-- A ring-valued operational fixture with distinct carriers. It deliberately
-- makes no assertion that this product ring realizes a declared field.
private abbrev carriers : Carriers where
  Field := fun domain => if domain = "base" then Int else Int × Int
  Group := fun _ => Int

private def model : DomainModel where
  toCarriers := carriers
  fieldRing := fun domain => by dsimp [carriers]; split <;> infer_instance
  fieldDecEq := fun domain => by dsimp [carriers]; split <;> infer_instance
  inverse := fun _ => none
  embed := fun extension base value => by
    change carriers.Field extension
    change carriers.Field base at value
    dsimp [carriers] at value ⊢
    split at value
    · split
      · exact value
      · exact (value, value)
    · split
      · exact value.1
      · exact value
  groupAdd := fun _ => inferInstance
  groupDecEq := fun _ => inferInstance
  smul := fun _ _ _ point => point

example : Evaluation.operationOn model SiteObservations.closed [] (.fieldEmbed "extension" "base")
    (.cons 2 .nil) .nil = .done (.cons (2, 2) .nil) := by rfl

example (selected : DomainModel) (extension base : String) (value : selected.Field base) :
    Evaluation.operationOn selected SiteObservations.closed [] (.fieldEmbed extension base)
      (.cons value .nil) .nil = .done (.cons (selected.embed extension base value) .nil) := rfl

example : (Op.fieldEmbed "extension" "base").evalTotal model rfl (.cons 2 .nil) =
    .cons (2, 2) .nil := by rfl

-- Constant folding must retain an embedding even when its input is literal.
example : NormalForm.constantResults (laws := []) (Δ := []) (.fieldEmbed "extension" "base") = none := rfl
example : NormalForm.folded (laws := []) (Δ := []) (.fieldEmbed "extension" "base")
    (.cons (.field "base" 2) .nil) = none := rfl

private def protocolBody : Region protocolDialect [.field "base"] [.field "extension"] :=
  .letOp (.calculate (.fieldEmbed "extension" "base") rfl) (.cons .here .nil) .nil
    (.ret (.cons .here .nil))

example : NormalForm.normalize {} protocolBody 0 1 (.cons .present .nil) =
    .ok (.done (.cons (.present (.calc (.fieldEmbed "extension" "base") rfl
      (.cons (.var .here) .nil) .here)) .nil)) := rfl
example : NormalForm.normalize {} protocolBody 0 1 (.cons (.field "base" 2) .nil) =
    .ok (.done (.cons (.present (.calc (.fieldEmbed "extension" "base") rfl
      (.cons (.field "base" 2) .nil) .here)) .nil)) := rfl
example : NormalForm.normalize {} protocolBody 0 1 (.cons .absent .nil) =
    .ok (.done (.cons .absent .nil)) := rfl

example : NormalForm.Comps.eval
    (model := model) (⟨fun entry => entry.elim0⟩ : NormalForm.LawResults model [])
    (NormalForm.calculation (.fieldEmbed "extension" "base") rfl
      (.cons (.field "base" 2) .nil)) (.nil : NormalForm.Binders model []) =
      .cons (some (2, 2)) .nil := rfl

example : Zkc.Construction.Calculation.ofOp? (.fieldEmbed "extension" "base") =
    some (.fieldEmbed "extension" "base") := rfl
example : (Zkc.Construction.Calculation.fieldEmbed "extension" "base").op =
    .fieldEmbed "extension" "base" := rfl
example {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] (value : F) :
    (Zkc.Construction.Calculation.fieldEmbed "extension" "base").evaluate (G := G) (.cons value .nil) =
      .returned (.cons value .nil) := rfl

end Tests.FieldEmbedding
