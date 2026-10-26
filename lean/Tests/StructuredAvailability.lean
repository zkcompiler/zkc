import Zkc.Source.Structured.Availability
import Zkc.Source.Structured.Component

/-! Hand-built formed-tree controls for computational availability admission.
These checks do not assert general presence soundness or native correspondence. -/

set_option autoImplicit false
namespace Tests.StructuredAvailability
open Zkc.Source Zkc.Source.Structured

private instance {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α) := fun left right => match left, right with
  | .ok a, .ok b => if h : a = b then isTrue (congrArg Except.ok h)
      else isFalse (fun hEq => h (Except.ok.inj hEq))
  | .error a, .error b => if h : a = b then isTrue (congrArg Except.error h)
      else isFalse (fun hEq => h (Except.error.inj hEq))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private abbrev scalar : Ty := .field "bls12-381.fr"
private abbrev group : Ty := .group "bls12-381.g1"
private abbrev vector : Ty := .vector "bls12-381.fr"
private abbrev service : Ty := .service "random.bls12-381.fr/0"

private def formed {inputs outputs : List Ty} (name : String) (kind : HelperKind)
    (body : Region dialect inputs outputs) : CheckedDefinition :=
  ⟨name, kind, inputs, outputs, body.erase, body, body.elaborate_erase⟩

private def root {inputs outputs : List Ty} (inputScopes outputScopes : List (List Nat))
    (body : Region protocolDialect inputs outputs) (roles : List String := ["P", "V"]) :
    CheckedProtocol where
  toProtocolSignature := ⟨"main", roles, inputs, outputs, inputScopes, outputScopes⟩
  raw := body.erase
  body := body
  formed := body.elaborate_erase

private def first : CheckedDefinition := formed "first" .math
  (.ret (.cons .here .nil) : Region dialect [scalar, scalar] [scalar])

private def relay (name : String) (target : Helper) : CheckedDefinition :=
  formed name .math (.letOp (.invoke target) (Operands.identity _) .nil
    (.ret ((Values.split target.outputs (Operands.identity (target.outputs ++ target.inputs))).1)))

private def nestedFirst : CheckedDefinition := relay "nested-first" first.helper

private def mathCall {outputs : List Ty} (helper : Helper)
    (kind : helper.kind = .math) (args : Operands helper.inputs helper.inputs)
    (next : Region protocolDialect (helper.outputs ++ helper.inputs) outputs) :
    Region protocolDialect helper.inputs outputs :=
  .letOp (.calculate (.invoke helper) (by simp [Op.isCalculation, kind])) args .nil next

private def splitFirst : CheckedProtocol := root [[0], [1]] [[0]]
  (mathCall nestedFirst.helper rfl (.cons .here (.cons (.there .here) .nil))
    (.ret (.cons .here .nil)))

theorem nested_first_accepted :
    checkUnitAvailability [first, nestedFirst] [splitFirst] = .ok () := by decide +kernel

theorem nested_first_exact_dependencies :
    (summarizeHelpers [first, nestedFirst]).map
      (fun summaries => summaries.map fun summary => (summary.results, summary.requirements)) =
        .ok [([[0]], []), ([[0]], [])] := by decide +kernel

theorem actual_argument_permutation_preserved :
    checkUnitAvailability [first]
      [root [[0], [1]] [[1]]
        (mathCall first.helper rfl (.cons (.there .here) (.cons .here .nil))
          (.ret (.cons .here .nil)))] = .ok () := by decide +kernel

private def nonadjacentRequirement : CheckedDefinition := formed "nonadjacent" .math
  (.letOp (.fieldAdd "bls12-381.fr")
    (.cons .here (.cons (.there (.there .here)) .nil)) .nil
    (.ret (.cons (.there (.there .here)) .nil)) :
    Region dialect [scalar, scalar, scalar] [scalar])

private def aliasedCaller : CheckedDefinition := formed "aliased-caller" .math
  (.letOp (.invoke nonadjacentRequirement.helper)
    (.cons .here (.cons .here (.cons (.there .here) .nil))) .nil
    (.ret (.cons .here .nil)) : Region dialect [scalar, scalar] [scalar])

theorem actual_argument_aliases_substitute_intermediate_requirements :
    checkUnitAvailability [nonadjacentRequirement, aliasedCaller]
      [root [[0], [1]] [[0]]
        (mathCall aliasedCaller.helper rfl (.cons .here (.cons (.there .here) .nil))
          (.ret (.cons .here .nil)))] = .error "structured-availability-requirement" := by
  decide +kernel

private def unusedSum : CheckedDefinition := formed "unused-sum" .math
  (.letOp (.fieldAdd "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons (.there .here) .nil)) : Region dialect [scalar, scalar] [scalar])

private def nestedUnused : CheckedDefinition := relay "nested-unused" unusedSum.helper

theorem unused_intermediate_refused :
    checkUnitAvailability [unusedSum, nestedUnused]
      [root [[0], [1]] [[0]]
        (mathCall nestedUnused.helper rfl (.cons .here (.cons (.there .here) .nil))
          (.ret (.cons .here .nil)))] = .error "structured-availability-requirement" := by
  decide +kernel

private def separate : CheckedDefinition := formed "separate" .math
  (.letOp (.fieldAdd "bls12-381.fr") (.cons .here (.cons .here .nil)) .nil
    (.letOp (.fieldMultiply "bls12-381.fr")
      (.cons (.there (.there .here)) (.cons (.there (.there .here)) .nil)) .nil
      (.ret (.cons (.there .here) (.cons .here .nil)))) :
    Region dialect [scalar, scalar] [scalar, scalar])

theorem separate_outputs_and_requirements_accepted :
    checkUnitAvailability [separate]
      [root [[0], [1]] [[0], [1]]
        (mathCall separate.helper rfl (.cons .here (.cons (.there .here) .nil))
          (.ret (.cons .here (.cons (.there .here) .nil))))] = .ok () := by decide +kernel

theorem separate_requirements_are_not_unioned :
    (summarizeHelpers [separate]).map
      (fun summaries => summaries.map fun summary => (summary.results, summary.requirements)) =
        .ok [([[0], [1]], [[0], [1]])] := by decide +kernel

private def zeroResult : CheckedDefinition := formed "zero-result" .math
  (.letOp (.fieldAdd "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret .nil) : Region dialect [scalar, scalar] [])

private def nestedZero : CheckedDefinition := relay "nested-zero" zeroResult.helper

theorem zero_result_unmet_requirement_refused :
    checkUnitAvailability [zeroResult, nestedZero]
      [root [[0], [1]] []
        (mathCall nestedZero.helper rfl (.cons .here (.cons (.there .here) .nil))
          (.ret .nil))] = .error "structured-availability-requirement" := by decide +kernel

private def strictSelect : CheckedDefinition := formed "select" .math
  (.letOp (.select scalar)
    (.cons .here (.cons (.there .here) (.cons (.there .here) .nil))) .nil
    (.ret (.cons .here .nil)) : Region dialect [.boolean, scalar] [scalar])

theorem equal_select_arms_keep_condition :
    (summarizeHelpers [strictSelect]).map
      (fun summaries => summaries.map (·.results)) = .ok [[[0, 1]]] := by decide +kernel

theorem unavailable_select_condition_refused :
    checkUnitAvailability [strictSelect]
      [root [[1], [0]] [[0]]
        (mathCall strictSelect.helper rfl (.cons .here (.cons (.there .here) .nil))
          (.ret (.cons .here .nil)))] = .error "structured-availability-requirement" := by
  decide +kernel

private def constant : CheckedDefinition := formed "constant" .math
  (.letOp (.fieldConstant "bls12-381.fr" 7) .nil .nil (.ret (.cons .here .nil)) :
    Region dialect [scalar, scalar] [scalar])

theorem constant_has_empty_dependencies :
    (summarizeHelpers [constant]).map
      (fun summaries => summaries.map (·.results)) = .ok [[[]]] := by decide +kernel

theorem constant_available_at_every_role :
    checkUnitAvailability [constant]
      [root [[0], [1]] [[0, 1]]
        (mathCall constant.helper rfl (.cons .here (.cons (.there .here) .nil))
          (.ret (.cons .here .nil)))] = .ok () := by decide +kernel

private def groupFormula : CheckedDefinition := formed "unused-group" .math
  (.letOp (.groupScale "bls12-381.g1" "bls12-381.fr")
    (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)) :
    Region dialect [group, scalar] [group])

theorem unused_group_helper_analyzed :
    (summarizeHelpers [groupFormula]).map
      (fun summaries => summaries.map fun summary => (summary.results, summary.requirements)) =
        .ok [([[0, 1]], [[0, 1]])] := by decide +kernel

theorem unused_group_helper_unit_accepted :
    checkUnitAvailability [groupFormula] [] = .ok () := by decide +kernel

private def readHelper : CheckedDefinition := formed "read" .math
  (.letOp (.boundedAt "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here .nil)) : Region dialect [vector, .index] [scalar])

private def nestedRead : CheckedDefinition := relay "nested-read" readHelper.helper

theorem transitive_read_flag :
    (summarizeHelpers [readHelper, nestedRead]).map
      (fun summaries => summaries.map (·.partial)) = .ok [true, true] := by decide +kernel

theorem reachable_read_refused_even_when_colocated :
    checkUnitAvailability [readHelper, nestedRead]
      [root [[0], [0]] [[0]]
        (mathCall nestedRead.helper rfl (.cons .here (.cons (.there .here) .nil))
          (.ret (.cons .here .nil)))] = .error "structured-availability-partial-math" := by
  decide +kernel

theorem singleton_read_profile_preserved :
    checkUnitAvailability [readHelper, nestedRead]
      [root [[0], [0]] [[0]]
        (mathCall nestedRead.helper rfl (.cons .here (.cons (.there .here) .nil))
          (.ret (.cons .here .nil))) ["P"]] = .ok () := by decide +kernel

private def localFirst : CheckedDefinition := formed "local-first" .local first.body

theorem owned_local_requires_unused_argument :
    checkUnitAvailability [localFirst]
      [root (inputs := [scalar, scalar]) [[0], [1]] [[0]]
        (.letOp (.localCall localFirst.helper rfl 0 "local")
          (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)))] =
        .error "structured-availability-owned-operand" := by decide +kernel

theorem owned_local_result_has_owner_scope :
    checkUnitAvailability [localFirst]
      [root (inputs := [scalar, scalar]) [[0], [0]] [[1]]
        (.letOp (.localCall localFirst.helper rfl 0 "local")
          (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)))] =
        .error "structured-availability-output" := by decide +kernel

theorem owned_local_available :
    checkUnitAvailability [localFirst]
      [root (inputs := [scalar, scalar]) [[0], [0]] [[0]]
        (.letOp (.localCall localFirst.helper rfl 0 "local")
          (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)))] =
        .ok () := by decide +kernel

theorem exchange_then_restriction :
    checkUnitAvailability [] [root (inputs := [scalar]) [[0]] [[1]]
      (.letOp (.exchange scalar 0 1 "send") (.cons .here .nil) .nil
        (.letOp (.restrict scalar [1]) (.cons .here .nil) .nil
          (.ret (.cons .here .nil))))] = .ok () := by decide +kernel

theorem exchange_output_excludes_uninvolved_participants :
    checkUnitAvailability [] [root (inputs := [scalar]) [[0, 2]] [[2]]
      (.letOp (.exchange scalar 0 1 "send") (.cons .here .nil) .nil
        (.ret (.cons .here .nil))) ["P", "V", "Other"]] =
          .error "structured-availability-output" := by decide +kernel

theorem restriction_must_be_subset :
    checkUnitAvailability [] [root (inputs := [scalar]) [[0]] [[1]]
      (.letOp (.restrict scalar [1]) (.cons .here .nil) .nil
        (.ret (.cons .here .nil)))] = .error "structured-availability-restriction" := by
  decide +kernel

theorem empty_restriction_refused :
    checkUnitAvailability [] [root (inputs := [scalar]) [[0]] []
      (.letOp (.restrict scalar []) (.cons .here .nil) .nil (.ret .nil))] =
        .error "structured-availability-scope" := by decide +kernel

theorem wrong_guard_owner_refused :
    checkUnitAvailability [] [root (inputs := [.boolean]) [[1]] []
      (.letOp (.guard 0 "guard") (.cons .here .nil) .nil (.ret .nil))] =
        .error "structured-availability-owned-operand" := by decide +kernel

theorem actual_service_operand_owner_checked :
    checkUnitAvailability [] [root (inputs := [service]) [[1]] [[0]]
      (.letOp (.draw 0 "bls12-381.fr" "draw") (.cons .here .nil) .nil
        (.ret (.cons .here .nil)))] = .error "structured-availability-owned-operand" := by
  decide +kernel

theorem service_calculation_refused :
    checkUnitAvailability [] [root (inputs := [.boolean, service]) [[0], [0]] []
      (.letOp (.calculate (.select service) rfl)
        (.cons .here (.cons (.there .here) (.cons (.there .here) .nil))) .nil
        (.ret .nil))] = .error "structured-availability-service" := by decide +kernel

theorem service_helper_refused_even_unused :
    checkUnitAvailability [formed "service" .math
      (.ret (.cons .here .nil) : Region dialect [service] [service])] [] =
        .error "structured-availability-service" := by decide +kernel

theorem statement_selector_availability_checked :
    checkUnitAvailability [] [root (inputs := [scalar]) [[0]] []
      (.letOp (.statement "relation" [scalar] ["V"] 0)
        (.cons .here .nil) .nil (.ret .nil))] =
        .error "structured-availability-owned-operand" := by decide +kernel

theorem forward_reference_not_sorted_here :
    (summarizeHelpers [nestedFirst, first]).map (fun _ => ()) =
      .error "structured-availability-helper-order" := by decide +kernel

theorem duplicate_helper_refused :
    (summarizeHelpers [first, first]).map (fun _ => ()) =
      .error "structured-availability-helper-duplicate" := by decide +kernel

theorem declaration_kind_part_of_reference :
    (summarizeHelpers [localFirst,
      relay "wrong-kind" { localFirst.helper with kind := .math }]).map (fun _ => ()) =
        .error "structured-availability-helper-signature" := by decide +kernel

/-- Bind intermediates use the same environment extension as operation results. -/
theorem lexical_bind_dependencies :
    (summarizeHelpers [formed "bind" .math
      (.bind first.body (.ret (.cons .here .nil)))]).map
        (fun summaries => summaries.map (·.results)) = .ok [[[0]]] := by decide +kernel

private def boundPair : Region dialect [scalar, scalar] [scalar, scalar] :=
  .bind
    (.letOp (.fieldConstant "bls12-381.fr" 7) .nil .nil
      (.ret (.cons (.there (.there .here)) (.cons (.there .here) .nil))))
    (.ret (.cons .here (.cons (.there (.there .here)) .nil)))

theorem lexical_bind_drops_intermediates_and_preserves_result_order :
    (summarizeHelpers [formed "bound-pair" .math boundPair]).map
      (fun summaries => summaries.map (·.results)) = .ok [[[1], [0]]] := by decide +kernel

theorem protocol_bind_drops_intermediates_and_preserves_result_order :
    checkUnitAvailability [] [root (inputs := [scalar, scalar]) [[0], [1]] [[1], [0]]
      (.bind
        (.letOp (.calculate (.fieldConstant "bls12-381.fr" 7) rfl) .nil .nil
          (.ret (.cons (.there (.there .here)) (.cons (.there .here) .nil))))
        (.ret (.cons .here (.cons (.there (.there .here)) .nil))))] = .ok () := by
  decide +kernel

theorem zero_result_bind_preserves_outer_context :
    (summarizeHelpers [formed "bound-zero" .math
      (.bind
        (.letOp (.fieldConstant "bls12-381.fr" 7) .nil .nil (.ret .nil))
        (.ret (.cons .here .nil)) : Region dialect [scalar] [scalar])]).map
      (fun summaries => summaries.map (·.results)) = .ok [[[0]]] := by decide +kernel

theorem environment_tuple_order :
    (do
      let environment := Availability.extendEnvironment #[[2], [1]] [[3], [4]]
      [0, 1, 2, 3].mapM (Availability.lookup environment)).run' {} =
        .ok [[3], [4], [1], [2]] := by decide +kernel

theorem environment_lookup_refuses_out_of_bounds_before_subtraction :
    (Availability.lookup #[[0]] 1).run' {} =
      .error "structured-availability-operand" := by decide +kernel

theorem empty_environment_lookup_refused :
    (Availability.lookup #[] 0).run' {} =
      .error "structured-availability-operand" := by decide +kernel

private def markedFirst : CheckedDefinition := formed "marked-first" .math
  (.letOp (.mark "") .nil .nil first.body)

theorem source_marks_preserve_dependencies :
    (summarizeHelpers [markedFirst]).map
      (fun summaries => summaries.map fun summary =>
        (summary.results, summary.requirements, summary.partial)) =
          .ok [([[0]], [], false)] := by decide +kernel

theorem marked_first_accepted :
    checkUnitAvailability [markedFirst]
      [root [[0], [1]] [[0]]
        (mathCall markedFirst.helper rfl (.cons .here (.cons (.there .here) .nil))
          (.ret (.cons .here .nil)))] = .ok () := by decide +kernel

theorem marks_do_not_consume_operation_budget :
    ((Availability.analyzeHelpers [markedFirst]).run' { operations := 1 }).map (fun _ => ()) =
      .ok () := by decide +kernel

theorem return_consumes_operation_budget :
    ((Availability.analyzeHelpers [markedFirst]).run' { operations := 0 }).map (fun _ => ()) =
      .error "structured-availability-operation-limit" := by decide +kernel

private def emptyRoot : CheckedProtocol := root (inputs := []) [] [] (.ret .nil)

theorem operation_budget_shared_across_roots :
    (do
      Availability.checkRoot [] emptyRoot
      Availability.checkRoot [] emptyRoot).run' { operations := 1 } =
        .error "structured-availability-operation-limit" := by decide +kernel

theorem dependency_budget_charged_before_substitution_union :
    (Availability.substitute [[0, 1], [2, 3]] [0, 1]).run' { dependencies := 3 } =
      .error "structured-availability-dependency-limit" := by decide +kernel

theorem replay_budget_checked_before_role_intersection :
    (Availability.available 2 [[0], [1]] [0, 1]).run' { replay := 3 } =
      .error "structured-availability-replay-limit" := by decide +kernel

private def foldStep : CheckedDefinition := formed "fold-step" .math
  (.ret (.cons .here .nil) : Region dialect [scalar, scalar, vector] [scalar])

private def foldSpec : FoldSpec :=
  ⟨DomainSpec.elements "elements" [vector] (.vector "bls12-381.fr") .here,
    [scalar], [], "fold-step", "", .math⟩

private def foldHelper : CheckedDefinition := formed "fold" .math
  (.letOp (.fold foldSpec) (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here .nil)) : Region dialect [vector, scalar] [scalar])

private def nestedFold : CheckedDefinition := relay "nested-fold" foldHelper.helper

theorem transitive_fold_flag_and_conservative_result :
    (summarizeHelpers [foldStep, foldHelper, nestedFold]).map
      (fun summaries => summaries.map fun summary => (summary.results, summary.partial)) =
        .ok [([[0]], false), ([[0, 1]], true), ([[0, 1]], true)] := by decide +kernel

theorem singleton_fold_profile_preserved :
    checkUnitAvailability [foldStep, foldHelper, nestedFold]
      [root [[0], [0]] [[0]]
        (mathCall nestedFold.helper rfl (.cons .here (.cons (.there .here) .nil))
          (.ret (.cons .here .nil))) ["P"]] = .ok () := by decide +kernel

theorem transitive_fold_multirole_refused :
    checkUnitAvailability [foldStep, foldHelper, nestedFold]
      [root [[0], [0]] [[0]]
        (mathCall nestedFold.helper rfl (.cons .here (.cons (.there .here) .nil))
          (.ret (.cons .here .nil)))] = .error "structured-availability-partial-math" := by
  decide +kernel

theorem direct_fold_multirole_refused :
    checkUnitAvailability [foldStep]
      [root (inputs := [vector, scalar]) [[0], [0]] [[0]]
        (.letOp (.calculate (.fold foldSpec) rfl)
          (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)))] =
        .error "structured-availability-partial-math" := by decide +kernel

private def localFoldStep : CheckedDefinition := formed "local-step" .local foldStep.body
private def localFold : CheckedDefinition := formed "local-fold" .local
  (.letOp (.fold { foldSpec with step := "local-step", kind := .local })
    (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)) :
    Region dialect [vector, scalar] [scalar])

theorem owned_finite_local_multirole_preserved :
    checkUnitAvailability [localFoldStep, localFold]
      [root (inputs := [vector, scalar]) [[0], [0]] [[0]]
        (.letOp (.localCall localFold.helper rfl 0 "finite")
          (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)))] =
        .ok () := by decide +kernel

theorem local_dormant_callback_link_checked :
    (summarizeHelpers [formed "local-branch" .local
      (.letOp (.branch [] []) (.cons .here .nil)
        (.cons (.ret .nil)
          (.cons (.letOp (.invoke ⟨"missing", .local, [], []⟩) .nil .nil (.ret .nil)) .nil))
        (.ret .nil) : Region dialect [.boolean] [])]).map (fun _ => ()) =
          .error "structured-availability-helper-order" := by decide +kernel

theorem math_stop_refused :
    (summarizeHelpers [formed "bad-stop" .math (.stop .abort : Region dialect [] [])]).map
      (fun _ => ()) = .error "structured-availability-math-stop" := by decide +kernel

theorem math_control_refused :
    (summarizeHelpers [formed "bad-control" .math
      (.letOp .guard (.cons .here .nil) .nil (.ret .nil) : Region dialect [.boolean] [])]).map
        (fun _ => ()) = .error "structured-availability-math-operation" := by decide +kernel

theorem malformed_scope_count_refused :
    checkAvailability [] (root (inputs := [scalar]) [] [] (.ret .nil)) =
      .error "structured-availability-port-scopes" := by decide +kernel

theorem repeated_scope_role_refused :
    checkAvailability [] (root (inputs := [scalar]) [[0, 0]] [] (.ret .nil)) =
      .error "structured-availability-scope" := by decide +kernel

theorem unknown_owner_refused :
    checkAvailability [] (root (inputs := [.boolean]) [[0]] []
      (.letOp (.guard 2 "guard") (.cons .here .nil) .nil (.ret .nil))) =
        .error "structured-availability-owner" := by decide +kernel

theorem exchange_must_have_distinct_roles :
    checkAvailability [] (root (inputs := [scalar]) [[0]] [[0]]
      (.letOp (.exchange scalar 0 0 "send") (.cons .here .nil) .nil
        (.ret (.cons .here .nil)))) = .error "structured-availability-exchange" := by
  decide +kernel

theorem protocol_stop_refused :
    checkAvailability [] (root (inputs := []) (outputs := []) [] [] (.stop .abort)) =
      .error "structured-availability-protocol-stop" := by decide +kernel

theorem malformed_statement_selector_count_refused :
    checkAvailability [] (root (inputs := [scalar]) [[0]] []
      (.letOp (.statement "relation" [scalar] [] 0) (.cons .here .nil) .nil (.ret .nil))) =
        .error "structured-availability-statement" := by decide +kernel

private def duplicated (name : String) (target : Helper) : CheckedDefinition := formed name target.kind
  (.letOp (.invoke target) (Operands.identity target.inputs) .nil
    (.letOp (.invoke target)
      ((Operands.identity target.inputs).rename (fun ref => ref.weakenPrefix target.outputs)) .nil
      (.ret (Values.split target.outputs
        (Operands.identity (target.outputs ++ (target.outputs ++ target.inputs)))).1)))

private def doublingDeclarations : Nat → CheckedDefinition × List CheckedDefinition
  | 0 => (unusedSum, [unusedSum])
  | n + 1 =>
    let (last, previous) := doublingDeclarations n
    let next := duplicated ("double-" ++ toString n) last.helper
    (next, previous ++ [next])

private def linearDeclarations : Nat → CheckedDefinition × List CheckedDefinition
  | 0 => (first, [first])
  | n + 1 =>
    let (last, previous) := linearDeclarations n
    let next := relay ("relay-" ++ toString n) last.helper
    (next, previous ++ [next])

private def sharedDeclarations (kind : HelperKind) : Nat → CheckedDefinition × List CheckedDefinition
  | 0 =>
    let base := formed "shared-first" kind first.body
    (base, [base])
  | n + 1 =>
    let (last, previous) := sharedDeclarations kind n
    let next := duplicated ("shared-" ++ toString n) last.helper
    (next, previous ++ [next])

/-- Every operation references the second original input through a growing
de Bruijn index. The final tuple distinguishes its result from the first input. -/
private def longMath : RawRegion Ty Op :=
  (List.range 4096).foldr (fun index next =>
    .letOp (.fieldAdd "bls12-381.fr") [index + 1, index + 1] [scalar] .nil next)
    (.ret [0, 4096])

private def longProtocol : RawRegion Ty ProtocolOp :=
  (List.range 4096).foldr (fun index next =>
    .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl)
      [index + 1, index + 1] [scalar] .nil next)
    (.ret [0, 4096])

/-- Actual transitive requirements exhaust incremental dependency work, while
shared Math/Local DAGs with bounded summaries remain admitted. Runtime controls
complement the kernel examples; they do not establish asymptotic bounds. -/
def run : IO Unit := do
  let expanded := (summarizeHelpers (doublingDeclarations 20).2).map (fun _ => ())
  match expanded with
  | .error "structured-availability-dependency-limit" => pure ()
  | _ => throw (IO.userError "transitive summary expansion did not refuse")
  let dependencyLimited := (Availability.analyzeHelpers (doublingDeclarations 8).2).run'
    { dependencies := 1024 }
  match dependencyLimited with
  | .error "structured-availability-dependency-limit" => pure ()
  | _ => throw (IO.userError "transitive dependency budget did not refuse")
  match (Availability.analyzeHelpers (doublingDeclarations 8).2).run' { operations := 26 } with
  | .ok _ => pure ()
  | .error error => throw (IO.userError ("26 stored operations refused: " ++ error))
  let operationLimited := (Availability.analyzeHelpers (doublingDeclarations 8).2).run'
    { operations := 25 }
  match operationLimited with
  | .error "structured-availability-operation-limit" => pure ()
  | _ => throw (IO.userError "stored operation budget did not refuse")
  for kind in [HelperKind.math, HelperKind.local] do
    match (Availability.analyzeHelpers (sharedDeclarations kind 40).2).run' { operations := 121 } with
    | .ok summaries =>
      let expected := if kind == .math then ([[0]], []) else ([[0, 1]], [[0, 1]])
      unless summaries.getLast?.map (fun summary => (summary.results, summary.requirements)) ==
          some expected do
        throw (IO.userError "shared DAG summary changed")
      let helper : Helper := ⟨"shared-39", kind, [scalar, scalar], [scalar]⟩
      let body : Region protocolDialect [scalar, scalar] [scalar] := match h : kind with
        | .math => .letOp
            (.calculate (.invoke helper) (by simp [Op.isCalculation, helper, h]))
            (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))
        | .local => .letOp (.localCall helper (by simp [helper, h]) 0 "shared")
            (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))
      let checkedRoot := root (inputs := [scalar, scalar]) [[0], [0]] [[0]]
        body
      match (Availability.checkRoot summaries checkedRoot).run' { operations := 2 } with
      | .ok () => pure ()
      | .error error => throw (IO.userError ("shared DAG root refused: " ++ error))
    | .error error => throw (IO.userError ("shared DAG refused: " ++ error))
  match longMath.elaborate (dialect := dialect) [scalar, scalar] [scalar, scalar] with
  | .error _ => throw (IO.userError "long SSA Math formation failed")
  | .ok body =>
    match summarizeHelpers [formed "long-ssa" .math body] with
    | .ok [summary] =>
      unless summary.results == [[1], [0]] &&
          summary.requirements == List.replicate 4096 [1] do
        throw (IO.userError "long SSA Math dependencies changed")
    | _ => throw (IO.userError "4096 high-reference Math operations refused")
  match longProtocol.elaborate (dialect := protocolDialect) [scalar, scalar] [scalar, scalar] with
  | .error _ => throw (IO.userError "long SSA protocol formation failed")
  | .ok body =>
    match checkUnitAvailability [] [root [[0], [1]] [[1], [0]] body] with
    | .ok () => pure ()
    | .error error => throw (IO.userError ("4096 high-reference protocol operations refused: " ++ error))
  match summarizeHelpers (linearDeclarations 64).2 with
  | .ok _ => pure ()
  | .error error => throw (IO.userError ("depth 64 refused: " ++ error))
  match summarizeHelpers (linearDeclarations 65).2 with
  | .error "structured-availability-depth-limit" => pure ()
  | _ => throw (IO.userError "depth 65 did not refuse")
  IO.println "structured-availability: expansion, sharing, SSA and depth controls passed"

private def componentTables (F G : Type) [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G]
    (definitions : List CheckedDefinition) : ComponentTables F G :=
  definitions.foldl (Evaluation.ComponentTables.extend SiteObservations.closed) ⟨[], []⟩

/-- The same nested-first body returns x with an absent irrelevant operand. -/
theorem nested_first_component (F G : Type) [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (x : F) :
    invoke (componentTables F G [first, nestedFirst]).components nestedFirst.helper
      (.cons (some x) (.cons none .nil)) = .done (.cons (some x) .nil) := rfl

/-- Counterexample to validating only returned values: the missing strict sum
is skipped by optional meaning, but admission above refuses its requirement. -/
theorem unused_sum_component_still_returns (F G : Type) [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (x : F) :
    invoke (componentTables F G [unusedSum, nestedUnused]).components nestedUnused.helper
      (.cons (some x) (.cons none .nil)) = .done (.cons (some x) .nil) := rfl

theorem separate_results_component (F G : Type) [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (x : F) :
    invoke (componentTables F G [separate]).components separate.helper
      (.cons (some x) (.cons none .nil)) = .done (.cons (some (x + x)) (.cons none .nil)) := rfl

/-- Empty optional outputs do not establish the intermediate was available. -/
theorem zero_result_component_hides_missing_requirement
    (F G : Type) [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (x : F) :
    invoke (componentTables F G [zeroResult, nestedZero]).components nestedZero.helper
      (.cons (some x) (.cons none .nil)) = .done .nil := rfl

theorem equal_select_arms_component_needs_condition
    (F G : Type) [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (x : F) :
    invoke (componentTables F G [strictSelect]).components strictSelect.helper
      (.cons none (.cons (some x) .nil)) = .done (.cons none .nil) := rfl

#eval run

end Tests.StructuredAvailability
