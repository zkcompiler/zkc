import Zkc.Source.Structured.Inlining
import Mathlib.Algebra.Ring.Int.Defs

/-! Controls for complete stopping behavior, empty results, argument renaming,
ordered multiple results and the retained caller context. -/
set_option autoImplicit false
namespace Tests.StructuredInlining
open Zkc.Source Zkc.Source.Structured

private def guardBody : Region dialect [.boolean] [] :=
  .letOp .guard (.cons .here .nil) .nil (.ret .nil)

private abbrev guardHelper : Helper := ⟨"guard", [.boolean], []⟩

private def guardTable : Meanings Int :=
  [⟨guardHelper, fun actual => guardBody.denote (meaning Int []) actual.get⟩]

private theorem guard_lookup (actual : Values (scalarAssignment Int) [.boolean]) :
    invoke guardTable guardHelper actual = guardBody.denote (meaning Int guardTable) actual.get := by
  cases actual with | cons enabled rest => cases rest; rfl

/-- A zero-result helper's guard is preserved for every suffix, even a suffix
that stops for a different reason. The caller supplies its second input. -/
theorem guard_inlined (next : Region dialect [.boolean, .boolean] [.boolean]) :
    Region.Equivalent (meaning Int guardTable)
      (.letOp (.invoke guardHelper) (.cons (.there .here) .nil) .nil next)
      (.bind (guardBody.rename (Values.cons (.there .here) .nil).get) next) :=
  inline_invoke guardTable guardHelper guardBody guard_lookup _ next

theorem stopped_body_bypasses_suffix :
    (Region.letOp (dialect := dialect) (.invoke guardHelper) (.cons (.there .here) .nil) .nil
      (.stop .abort : Region dialect [.boolean, .boolean] [.boolean])).denote
      (meaning Int guardTable) (Values.cons true (.cons false .nil)).get = .halt .reject :=
  (guard_inlined (.stop .abort) (Values.cons true (.cons false .nil)).get).trans (by rfl)

theorem empty_result_preserves_suffix_stop :
    (Region.letOp (dialect := dialect) (.invoke guardHelper) (.cons (.there .here) .nil) .nil
      (.stop .abort : Region dialect [.boolean, .boolean] [.boolean])).denote
      (meaning Int guardTable) (Values.cons false (.cons true .nil)).get = .halt .abort :=
  (guard_inlined (.stop .abort) (Values.cons false (.cons true .nil)).get).trans (by rfl)

theorem empty_result_preserves_caller :
    (Region.letOp (dialect := dialect) (.invoke guardHelper) (.cons (.there .here) .nil) .nil
      (.ret (.cons .here .nil) : Region dialect [.boolean, .boolean] [.boolean])).denote
      (meaning Int guardTable) (Values.cons false (.cons true .nil)).get =
        .done (.cons false .nil) :=
  (guard_inlined (.ret (.cons .here .nil))
    (Values.cons false (.cons true .nil)).get).trans (by rfl)

private abbrev scalar : Ty := .field "bls12-381.fr"
private def pairBody : Region dialect [scalar, scalar] [scalar, scalar] :=
  .ret (.cons (.there .here) (.cons .here .nil))

private def pairDefinition : CheckedDefinition :=
  ⟨"pair", [scalar, scalar], [scalar, scalar], pairBody.erase, pairBody,
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
      (meaning Int (pairPayload.meanings Int))
      (Values.cons x (.cons y (.nil : Values (scalarAssignment Int) []))).get =
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
      (meaning Int (pairPayload.meanings Int))
      (Values.cons x (.cons y (.nil : Values (scalarAssignment Int) []))).get =
        .done (.cons y (.cons x .nil)) :=
  (pairPayload.inline_body_view pairDefinition List.mem_cons_self pairBody (by rfl)
    (.cons .here (.cons (.there .here) .nil)) _
    (Values.cons x (.cons y .nil)).get).trans (by rfl)

end Tests.StructuredInlining
