import Zkc.Source.Structured.Inlining
import Mathlib.Algebra.Ring.Int.Defs

/-! Controls for complete stopping behavior, empty results, argument renaming,
ordered multiple results and the retained caller context. -/
set_option autoImplicit false
namespace Tests.StructuredInlining
open Zkc.Source Zkc.Source.Structured

private def guardBody : Region dialect [.boolean] [] :=
  .letOp .guard (.cons .here .nil) .nil (.ret .nil)

private abbrev guardHelper : Helper := ⟨"guard", .local, [.boolean], []⟩

private def guardTable : Meanings Int Int :=
  [⟨guardHelper, fun actual => guardBody.denote (meaning Int Int []) actual.get⟩]

private theorem guard_lookup (actual : Values (assignment Int Int) [.boolean]) :
    invoke guardTable guardHelper actual = guardBody.denote (meaning Int Int guardTable) actual.get := by
  cases actual with | cons enabled rest => cases rest; rfl

/-- A zero-result helper's guard is preserved for every suffix, even a suffix
that stops for a different reason. The caller supplies its second input. -/
theorem guard_inlined (next : Region dialect [.boolean, .boolean] [.boolean]) :
    Region.Equivalent (meaning Int Int guardTable)
      (.letOp (.invoke guardHelper) (.cons (.there .here) .nil) .nil next)
      (.bind (guardBody.rename (Values.cons (.there .here) .nil).get) next) :=
  inline_invoke guardTable guardHelper guardBody guard_lookup _ next

theorem stopped_body_bypasses_suffix :
    (Region.letOp (dialect := dialect) (.invoke guardHelper) (.cons (.there .here) .nil) .nil
      (.stop .abort : Region dialect [.boolean, .boolean] [.boolean])).denote
      (meaning Int Int guardTable) (Values.cons true (.cons false .nil)).get = .halt .reject :=
  (guard_inlined (.stop .abort) (Values.cons true (.cons false .nil)).get).trans (by rfl)

theorem empty_result_preserves_suffix_stop :
    (Region.letOp (dialect := dialect) (.invoke guardHelper) (.cons (.there .here) .nil) .nil
      (.stop .abort : Region dialect [.boolean, .boolean] [.boolean])).denote
      (meaning Int Int guardTable) (Values.cons false (.cons true .nil)).get = .halt .abort :=
  (guard_inlined (.stop .abort) (Values.cons false (.cons true .nil)).get).trans (by rfl)

theorem empty_result_preserves_caller :
    (Region.letOp (dialect := dialect) (.invoke guardHelper) (.cons (.there .here) .nil) .nil
      (.ret (.cons .here .nil) : Region dialect [.boolean, .boolean] [.boolean])).denote
      (meaning Int Int guardTable) (Values.cons false (.cons true .nil)).get =
        .done (.cons false .nil) :=
  (guard_inlined (.ret (.cons .here .nil))
    (Values.cons false (.cons true .nil)).get).trans (by rfl)

private abbrev scalar : Ty := .field "bls12-381.fr"
private def pairBody : Region dialect [scalar, scalar] [scalar, scalar] :=
  .ret (.cons (.there .here) (.cons .here .nil))

private def pairDefinition : CheckedDefinition :=
  ⟨"pair", .math, [scalar, scalar], [scalar, scalar], pairBody.erase, pairBody,
    pairBody.elaborate_erase⟩

private def pairPayload : Payload :=
  (linkPayload "pair" [pairDefinition]).toOption.get (by decide +kernel)

/-- Repeated actuals remain distinct ordered bindings, and the suffix still
sees the original second caller value below the two returned results. -/
theorem repeated_arguments_and_ordered_results (x y : Int) :
    (Region.letOp (dialect := dialect) (.invoke pairDefinition.helper)
      (.cons .here (.cons .here .nil)) .nil
      (.ret (.cons (.there .here) (.cons .here
        (.cons (.there (.there (.there .here))) .nil)))) :
      Region dialect [scalar, scalar] [scalar, scalar, scalar]).denote
      (meaning Int Int (pairPayload.meanings Int Int))
      (Values.cons x (.cons y (.nil : Values (assignment Int Int) []))).get =
        .done (.cons x (.cons x (.cons y .nil))) :=
  (pairPayload.inline_body_view pairDefinition List.mem_cons_self pairBody (by rfl)
    (Γ := [scalar, scalar]) (out := [scalar, scalar, scalar])
    (.cons .here (.cons .here .nil))
    (.ret (.cons (.there .here) (.cons .here
      (.cons (.there (.there (.there .here))) .nil))))
    (Values.cons x (.cons y .nil)).get).trans (by rfl)

/-- Distinct arguments make a result permutation observable. -/
theorem distinct_ordered_results (x y : Int) :
    (Region.letOp (dialect := dialect) (.invoke pairDefinition.helper)
      (.cons .here (.cons (.there .here) .nil)) .nil
      (.ret (.cons .here (.cons (.there .here) .nil))) :
      Region dialect [scalar, scalar] [scalar, scalar]).denote
      (meaning Int Int (pairPayload.meanings Int Int))
      (Values.cons x (.cons y (.nil : Values (assignment Int Int) []))).get =
        .done (.cons y (.cons x .nil)) :=
  (pairPayload.inline_body_view pairDefinition List.mem_cons_self pairBody (by rfl)
    (.cons .here (.cons (.there .here) .nil)) _
    (Values.cons x (.cons y .nil)).get).trans (by rfl)

/-- Same name and ports do not authorize replacing a Local helper with Math. -/
theorem wrong_kind_refused (enabled : Bool) :
    invoke guardTable { guardHelper with kind := .math } (.cons enabled .nil) =
      .halt .refused := rfl

private abbrev group : Ty := .group "bls12-381.g1"
private def sites : PIR.Signature := ⟨String, fun _ => Unit⟩
private def observations : SiteObservations sites := ⟨fun site => .call site .done⟩

private abbrev scaleHelper : Helper := ⟨"scale", .local, [group, scalar], [group, group]⟩

private def scaleBody : Region dialect [group, scalar] [group, group] :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.groupScale "bls12-381.g1" "bls12-381.fr")
    (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here (.cons (.there .here) .nil)))

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

private def scaleTable : Evaluation.Meanings F G sites :=
  [⟨scaleHelper, fun actual =>
    scaleBody.denote (Evaluation.meaning observations []) actual.get⟩]

private theorem scale_lookup (actual : Values (assignment F G) scaleHelper.inputs) :
    invoke scaleTable scaleHelper actual =
      scaleBody.denote (Evaluation.meaning observations scaleTable) actual.get := by
  cases actual with | cons point rest => cases rest with
    | cons scalar rest => cases rest; rfl

/-- Uniform group interpretation retains body/suffix observation order and the
caller value beneath both ordered returned groups. -/
theorem group_sites_and_suffix (point : G) (scalar : F) :
    (Region.letOp (dialect := dialect) (.invoke scaleHelper) (Operands.identity _) .nil
      (.letOp (.mark "suffix") .nil .nil
        (.ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))))) :
      Region dialect [group, .field "bls12-381.fr"] [group, group, group]).denote
      (Evaluation.meaning observations scaleTable)
      (Values.cons point (.cons scalar (.nil : Values (assignment F G) []))).get =
        .call "body" (fun _ => .call "suffix" (fun _ =>
          .done (.cons (scalar • point) (.cons point (.cons point .nil))))) :=
  (Evaluation.inline_invoke observations scaleTable scaleHelper scaleBody scale_lookup
    (Operands.identity _)
    (.letOp (.mark "suffix") .nil .nil
      (.ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))))
    (Values.cons point (.cons scalar .nil)).get).trans (by rfl)

end Tests.StructuredInlining
