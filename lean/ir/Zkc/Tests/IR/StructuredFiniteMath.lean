import Zkc.IR.Source.Structured.AvailabilityLaws
import Zkc.IR.Source.Structured.NormalForm.Soundness

/-! Complete outcomes for strict finite Math and exact named calls. Out-of-word
indices and arbitrary stopping callback tables are semantic controls, not native
admitted-input counterexamples. No callback evaluator is defined here. -/
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
open Zkc.Source Zkc.Source.Structured
namespace Tests.StructuredFiniteMath

def model : DomainModel := ringModel Int Int
def sites : SiteObservations closedInterface := SiteObservations.closed

def rangeDomain : DomainSpec :=
  ⟨"range", [.index, .index], [.index],
    .letNode (.range .here (.there .here)) (.ret .here)⟩

def foldSpec : FoldSpec := ⟨rangeDomain, [.index], [.boolean], "step", "", .math⟩

def closedTable : Evaluation.MeaningsOn model.toCarriers closedInterface :=
  [⟨foldSpec.stepHelper, fun args => .done (.cons (args.get .here + 1) .nil)⟩]

def tables : Evaluation.ComponentTablesOn model.toCarriers closedInterface := ⟨closedTable, []⟩

/-- A reusable strict-fold law over every current model, table and interface.
This is an equation for the existing operation, not an evaluator parameter. -/
theorem component_fold_strict (domainModel : DomainModel) {I : PIR.Signature}
    (observations : SiteObservations I)
    (meanings : Evaluation.ComponentTablesOn domainModel.toCarriers I)
    (spec : FoldSpec) (args : Values (Component domainModel.Value) spec.arguments) :
    Evaluation.componentOperationOn domainModel observations meanings (.fold spec) args .nil =
      strictComponent (Evaluation.meaningOn domainModel observations meanings.closed)
        (.fold spec) args .nil := rfl

def foldArgs (lo hi state : Nat) (capture : Bool) : Values model.Value foldSpec.arguments :=
  .cons lo (.cons hi (.cons state (.cons capture .nil)))

def optionalFoldArgs (lo hi state : Option Nat) (capture : Option Bool) :
    Values (Component model.Value) foldSpec.arguments :=
  .cons lo (.cons hi (.cons state (.cons capture .nil)))

theorem empty_fold_returns :
    Evaluation.denoteFoldOn closedTable foldSpec (foldArgs 0 0 7 true) =
      .done (.cons 7 .nil) := rfl

theorem nonempty_fold_returns :
    Evaluation.denoteFoldOn closedTable foldSpec (foldArgs 0 2 7 true) =
      .done (.cons 9 .nil) := rfl

theorem empty_fold_still_needs_capture :
    Evaluation.componentOperationOn model sites tables (.fold foldSpec)
      (optionalFoldArgs (some 0) (some 0) (some 7) none) .nil =
      .done (.cons none .nil) := rfl

theorem ignored_capture_still_needed :
    Evaluation.componentOperationOn model sites tables (.fold foldSpec)
      (optionalFoldArgs (some 0) (some 2) (some 7) none) .nil =
      .done (.cons none .nil) := rfl

theorem invalid_zero_trip_domain_refuses :
    Evaluation.componentOperationOn model sites tables (.fold foldSpec)
      (foldArgs indexLimit indexLimit 7 true).present .nil = .halt .refused := rfl

theorem invalid_domain_absent_capture_skips :
    Evaluation.componentOperationOn model sites tables (.fold foldSpec)
      (optionalFoldArgs (some indexLimit) (some indexLimit) (some 7) none) .nil =
      .done (.cons none .nil) := rfl

def zeroSpec : FoldSpec := ⟨rangeDomain, [], [], "zeroStep", "", .math⟩

theorem zero_result_domain_failure :
    Evaluation.componentOperationOn model sites ⟨[], []⟩ (.fold zeroSpec)
      (Values.cons indexLimit (.cons indexLimit .nil)).present .nil = .halt .refused := rfl

theorem zero_result_missing_operand_skips :
    Evaluation.componentOperationOn model sites ⟨[], []⟩ (.fold zeroSpec)
      (.cons (some 0) (.cons none .nil)) .nil = .done .nil := rfl

def failingStepTable : Evaluation.MeaningsOn model.toCarriers closedInterface :=
  [⟨foldSpec.stepHelper, fun _ => .halt .exhausted⟩]

theorem reached_callback_stop :
    Evaluation.componentOperationOn model sites ⟨failingStepTable, []⟩ (.fold foldSpec)
      (foldArgs 0 1 7 true).present .nil = .halt .exhausted := rfl

theorem unreached_callback_stop :
    Evaluation.componentOperationOn model sites ⟨failingStepTable, []⟩ (.fold foldSpec)
      (foldArgs 0 0 7 true).present .nil = .done (.cons (some 7) .nil) := rfl

def stepSummary : DependencySummary :=
  ⟨foldSpec.stepHelper, [[0]], [], false, 0⟩

theorem fold_summary_is_joint :
    (((Availability.calculation [stepSummary] (.fold foldSpec)
      [[0], [1], [2], [3]]).run {}).run {}).map
        (fun (result, _) => (result.1, result.2.requirements, result.2.partial)) =
      .ok ([[0, 1, 2, 3]], [[0, 1, 2, 3]], true) := by
  decide

def zeroStepSummary : DependencySummary :=
  ⟨zeroSpec.stepHelper, [], [], false, 0⟩

theorem zero_result_summary_keeps_requirement :
    (((Availability.calculation [zeroStepSummary] (.fold zeroSpec)
      [[0], [1]]).run {}).run {}).map
        (fun (result, _) => (result.1, result.2.requirements, result.2.partial)) =
      .ok ([], [[0, 1]], true) := by
  decide

theorem disjoint_requirement_has_no_owner :
    ((Availability.available 2 [[0], [1]] [0, 1]).run {}).map Prod.fst = .ok [] := by
  decide

theorem independent_requirements_have_distinct_owners :
    (((Availability.available 2 [[0], [1]] [0]).run {}).map Prod.fst,
      ((Availability.available 2 [[0], [1]] [1]).run {}).map Prod.fst) =
      (.ok [0], .ok [1]) := by
  decide

def directFoldBody : Region protocolDialect foldSpec.arguments [.index] :=
  .letOp (.calculate (.fold foldSpec) rfl) (Operands.identity _) .nil
    (.ret (.cons .here .nil))

def presentPattern : NormalForm.InputPattern foldSpec.arguments :=
  .cons .present (.cons .present (.cons .present (.cons .present .nil)))

def directForm : NormalForm.Form [] [] presentPattern.scope [.index] :=
  .compute (.fold foldSpec) rfl
    (.cons (.var .here) (.cons (.var (.there .here))
      (.cons (.var (.there (.there .here))) (.cons (.var (.there (.there (.there .here)))) .nil))))
    (.done (.cons (.present (.result .here .here)) .nil))

theorem direct_fold_normalizes :
    NormalForm.normalize {} directFoldBody 0 2 presentPattern = .ok directForm := rfl

theorem direct_absent_fold_normalizes :
    NormalForm.normalize {} directFoldBody 0 2
      (.cons .present (.cons .present (.cons .present (.cons .absent .nil)))) =
      .ok (.done (.cons .absent .nil)) := rfl

theorem optional_fold_normalizes :
    (NormalForm.normalize {} directFoldBody 0 2
      (.cons .optional (.cons .optional (.cons .optional
        (.cons .optional .nil))))).isOk = true := rfl

/-- Apply the existing normalizer theorem to this actual retained fold operation,
with arbitrary domain model, helper meanings and represented inputs. -/
def noResults (domainModel : DomainModel) : NormalForm.LawResults domainModel [] where
  result entry := entry.elim0

theorem direct_fold_process (domainModel : DomainModel) (meanings : NormalForm.Tables domainModel)
    (binders : NormalForm.Binders domainModel presentPattern.scope) :
    directFoldBody.denote (NormalForm.meaningAt domainModel meanings [] {} 0)
      (presentPattern.environment domainModel binders).get =
      directForm.denote domainModel meanings (noResults domainModel) {}
        (NormalForm.runsAt domainModel meanings [] {} 0)
        (NormalForm.noCallees domainModel) binders :=
  NormalForm.normalize_sound {} directFoldBody 0 2 presentPattern directForm
    direct_fold_normalizes (by rfl) (by intro other _ different; exact different)
    (noResults domainModel) (NormalForm.noCallees domainModel) binders
    (fun entry => entry.elim0) (NormalForm.noCallees_hold _ _)

def helper : Helper := ⟨"foldHelper", .math, foldSpec.arguments, [.index]⟩
def helperBody : Region dialect foldSpec.arguments [.index] :=
  .letOp (.fold foldSpec) (Operands.identity _) .nil (.ret (.cons .here .nil))

def helperTables : Evaluation.ComponentTablesOn model.toCarriers closedInterface :=
  ⟨closedTable,
    [⟨helper, fun args => helperBody.component (Evaluation.meaningOn model sites closedTable)
      (Evaluation.componentOperationOn model sites tables) args.get⟩]⟩

def nestedBody : Region protocolDialect foldSpec.arguments [.index] :=
  .letOp (.calculate (.invoke helper) rfl) (Operands.identity _) .nil
    (.ret (.cons .here .nil))

theorem nested_helper_preserves_present_stop :
    invoke helperTables.components helper (foldArgs indexLimit indexLimit 7 true).present =
      .halt .refused := rfl

theorem nested_fold_normalizer_keeps_exact_math :
    NormalForm.normalize {} nestedBody 0 2
      (.cons .present (.cons .present (.cons .present (.cons .absent .nil)))) =
      .ok (.math helper
        (.cons (.present (.var .here))
          (.cons (.present (.var (.there .here)))
            (.cons (.present (.var (.there (.there .here)))) (.cons .absent .nil))))
        (.done (.cons (.read .here .here) .nil))) := rfl

def unusedBody : Region dialect foldSpec.arguments [.index] :=
  .letOp (.fold foldSpec) (Operands.identity _) .nil
    (.ret (.cons (.there (.there (.there .here))) .nil))

theorem unused_fold_is_not_erasable :
    unusedBody.component (Evaluation.meaningOn model sites closedTable)
      (Evaluation.componentOperationOn model sites tables)
      (foldArgs indexLimit indexLimit 7 true).present.get = .halt .refused := rfl

def zeroHelper : Helper := ⟨"zeroHelper", .math, zeroSpec.arguments, []⟩
def zeroHelperBody : Region dialect zeroSpec.arguments [] :=
  .letOp (.fold zeroSpec) (Operands.identity _) .nil (.ret .nil)

theorem zero_result_helper_still_fails :
    zeroHelperBody.component (Evaluation.meaningOn model sites [])
      (Evaluation.componentOperationOn model sites ⟨[], []⟩)
      (Values.cons (some indexLimit) (.cons (some indexLimit) .nil)).get =
      .halt .refused := rfl

def unusedProtocolBody : Region protocolDialect foldSpec.arguments [] :=
  .letOp (.calculate (.invoke helper) rfl) (Operands.identity _) .nil (.ret .nil)

theorem normalizer_keeps_unused_math_call :
    NormalForm.normalize {} unusedProtocolBody 0 2
      (.cons .present (.cons .present (.cons .present (.cons .present .nil)))) =
      .ok (.math helper
        (.cons (.present (.var .here))
          (.cons (.present (.var (.there .here)))
            (.cons (.present (.var (.there (.there .here))))
              (.cons (.present (.var (.there (.there (.there .here))))) .nil))))
        (.done .nil)) := rfl

theorem bounded_read_present_failure :
    Evaluation.componentOperationOn model sites ⟨[], []⟩ (.boundedAt "test")
      (Values.cons ([] : List Int) (.cons 0 .nil)).present .nil = .halt .refused := rfl

theorem bounded_read_absent_skips :
    Evaluation.componentOperationOn model sites ⟨[], []⟩ (.boundedAt "test")
      (.cons none (.cons (some 0) .nil)) .nil = .done (.cons none .nil) := rfl

def forwardBody : Region dialect [.index, .boolean] [.index] := .ret (.cons .here .nil)

theorem math_forward_ignores_absent_input :
    forwardBody.component (Evaluation.meaningOn model sites [])
      (Evaluation.componentOperationOn model sites ⟨[], []⟩)
      (Values.cons (some 7) (.cons none .nil)).get = .done (.cons (some 7) .nil) := rfl

def mixedBody : Region dialect [.index, .index] [.boolean, .boolean] :=
  .letOp .indexEqual (.cons .here (.cons .here .nil)) .nil
    (.letOp .indexEqual (.cons (.there (.there .here))
      (.cons (.there (.there .here)) .nil)) .nil
      (.ret (.cons (.there .here) (.cons .here .nil))))

theorem mixed_owner_first_component :
    mixedBody.component (Evaluation.meaningOn model sites [])
      (Evaluation.componentOperationOn model sites ⟨[], []⟩)
      (Values.cons (some 7) (.cons none .nil)).get =
      .done (.cons (some true) (.cons none .nil)) := rfl

theorem mixed_owner_second_component :
    mixedBody.component (Evaluation.meaningOn model sites [])
      (Evaluation.componentOperationOn model sites ⟨[], []⟩)
      (Values.cons none (.cons (some 9) .nil)).get =
      .done (.cons none (.cons (some true) .nil)) := rfl

theorem available_does_not_imply_returns :
    ¬ ∃ values, Evaluation.componentOperationOn model sites tables (.fold foldSpec)
      (foldArgs indexLimit indexLimit 7 true).present .nil = .done values := by
  intro ⟨values, h⟩
  rw [invalid_zero_trip_domain_refuses] at h
  cases h


/-- A false predicate leaves state unchanged and never reaches the stopping step. -/
theorem false_predicate_skips_step :
    let spec := { foldSpec with predicate := "disabled" }
    let meanings : Evaluation.MeaningsOn model.toCarriers closedInterface :=
      [⟨spec.predicateHelper, fun _ => .done (.cons false .nil)⟩,
       ⟨spec.stepHelper, fun _ => .halt .exhausted⟩]
    Evaluation.componentOperationOn model sites ⟨meanings, []⟩ (.fold spec)
      (.cons (some 0) (.cons (some 2) (.cons (some 7) (.cons (some true) .nil)))) .nil =
        .done (.cons (some 7) .nil) := rfl

def zeroBody : Region protocolDialect zeroSpec.arguments [] :=
  .letOp (.calculate (.fold zeroSpec) rfl) (Operands.identity _) .nil (.ret .nil)

theorem zero_result_normalizer_retains_operation :
    NormalForm.normalize {} zeroBody 0 2 (.cons .present (.cons .present .nil)) =
      .ok (.compute (.fold zeroSpec) rfl
        (.cons (.var .here) (.cons (.var (.there .here)) .nil)) (.done .nil)) := rfl

def unusedDirectBody : Region protocolDialect foldSpec.arguments [] :=
  .letOp (.calculate (.fold foldSpec) rfl) (Operands.identity _) .nil (.ret .nil)

theorem unused_direct_normalizer_retains_operation :
    NormalForm.normalize {} unusedDirectBody 0 2 presentPattern =
      .ok (.compute (.fold foldSpec) rfl
        (.cons (.var .here) (.cons (.var (.there .here))
          (.cons (.var (.there (.there .here)))
            (.cons (.var (.there (.there (.there .here)))) .nil)))) (.done .nil)) := rfl

def formed {inputs outputs : List Ty} (name : String)
    (body : Region dialect inputs outputs) : CheckedDefinition :=
  ⟨name, .math, inputs, outputs, body.erase, body, body.elaborate_erase⟩

def emptyStep : CheckedDefinition := formed zeroSpec.step
  (.ret .nil : Region dialect zeroSpec.stepHelper.inputs [])

def emptyHelper : CheckedDefinition := formed "empty-fold" zeroHelperBody

def emptyNested : CheckedDefinition := formed "empty-nested"
  (.letOp (.invoke emptyHelper.helper) (Operands.identity _) .nil (.ret .nil))

def zeroRoot (scopes : List (List Nat)) (body : Region protocolDialect zeroSpec.arguments []) :
    CheckedProtocol :=
  ⟨⟨"main", ["P", "V"], zeroSpec.arguments, [], scopes, []⟩,
    body.erase, body, body.elaborate_erase⟩

theorem zero_result_disjoint_refused :
    checkUnitAvailability [emptyStep] [zeroRoot [[0], [1]] zeroBody] =
      .error "structured-availability-requirement" := by decide +kernel

theorem zero_result_shared_accepted :
    checkUnitAvailability [emptyStep] [zeroRoot [[0], [0]] zeroBody] = .ok () := by decide +kernel

def nestedZeroBody : Region protocolDialect zeroSpec.arguments [] :=
  .letOp (.calculate (.invoke emptyNested.helper) rfl) (Operands.identity _) .nil (.ret .nil)

theorem nested_zero_result_disjoint_refused :
    checkUnitAvailability [emptyStep, emptyHelper, emptyNested]
      [zeroRoot [[0], [1]] nestedZeroBody] =
      .error "structured-availability-requirement" := by decide +kernel

theorem nested_zero_result_shared_accepted :
    checkUnitAvailability [emptyStep, emptyHelper, emptyNested]
      [zeroRoot [[0], [0]] nestedZeroBody] = .ok () := by decide +kernel

end Tests.StructuredFiniteMath
