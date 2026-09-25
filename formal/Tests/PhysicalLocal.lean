import Tools.Interactive.PhysicalLocal

set_option autoImplicit false

namespace Tests.PhysicalLocal
open Tools.Interactive
open Lean (Json)

-- Handwritten, independently related source and candidate. These tests exercise
-- the public entry point without requiring the native compiler or Rust runner.
private def parse (text : String) : Json := (Json.parse text).toOption.getD .null

private def source : Json := parse r#"["zkc.protocol/1",
  [["and","bool.and",[],""]],
  [["function","B",[["x","bool"],["y","bool"]],["bool"],
    [["op","combine","and",[],["x","y"],["z"]],["return",["z"]]],["B",[]]]],
  [["protocol","Main",["P"],[],[["x","P","bool"],["y","P","bool"]],
    [["P","bool"]],[],[["local","step","P","B",["x","y"],["z"]],["return",["z"]]]]],
  [["instance","root","Main",[],[],[["P","P"]]]],[["entry","main","root"]]]"#

private def candidate : Json := parse r#"["zkc.participants/1",
  [["and","bool.and",[],"arkworks/bool.and"]],"physical",
  [["function","B",[["a","bool@native.bool/1"],["b","bool@native.bool/1"]],
    ["bool@native.bool/1"],[["op","combine","and",[],["a","b"],["c"]],["return",["c"]]],["B",[]]]],
  [["participant","p","root","P",[],[["x","bool@native.bool/1"],["y","bool@native.bool/1"]],
    ["bool@native.bool/1"],[["local","step","B",["x","y"],["z"]],["return",["z"]]]]],
  [["entry","main",[["P","p"]]]]]"#

private def inputs : Json := parse r#"["zkc.reference-inputs/1","main","test",
  [["P",[["x",["bool","true"]],["y",["bool","false"]]]]],[],[],[]]"#
private def storage : Json := parse r#"["zkc.local-resources/1","67108864",[]]"#

private def replace : Json → List Nat → Json → Json
  | _, [], value => value
  | .arr items, index :: rest, value =>
      .arr (items.modify index fun current => replace current rest value)
  | original, _, _ => original

private def run (s := source) (c := candidate) (i := inputs) (m := storage) : Result Json :=
  PhysicalLocal.reference s c i m

private def code (result : Result Json) : Option String :=
  match result with | .error error => some error | .ok _ => none

private def field (result : Result Json) (index : Nat) : Option Json := do
  (← result.toOption).getArr?.toOption >>= (·[index]?)

example : (field (run) 1 == some (parse r#"["returned",[["bool","false"]]]"#)) = true := by native_decide
-- Root args, local args, kernel output, root binding and final retained result.
example : (field (run) 4 == some (parse r#"["4","1","512","3584","0"]"#)) = true := by native_decide
example : code (run (m := .arr #[])) = some "physical-storage-input" := by native_decide
example : code (run (m := replace storage [1] (.str "67108865"))) =
    some "physical-output-ceiling" := by native_decide
example : code (run (m := replace storage [2] (parse r#"[["x","1"]]"#))) =
    some "physical-table-capacities" := by native_decide
example : code (run (m := replace storage [2] (parse r#"[["x","1"],["x","1"]]"#))) =
    some "physical-table-capacities" := by native_decide
example : code (run (i := replace inputs [5] (parse r#"[[[],["ok",[]]]]"#))) =
    some "physical-external-inputs-not-supported" := by native_decide
example : code (run (i := replace inputs [6] (parse r#"[[[],["bool","true"]]]"#))) =
    some "physical-external-inputs-not-supported" := by native_decide
example : code (run (c := replace candidate [3, 0, 4, 0, 3] (parse r#"["wrong"]"#))) =
    some "interactive-kernel-parameters" := by native_decide

private def logicalTypes : Json → Json
  | .str text => .str (text.splitOn "@").head!
  | .arr values => .arr (values.map logicalTypes)
  | value => value
example : code (run (c := replace (logicalTypes candidate) [2] (.str "logical"))) =
    some "physical-stage-required" := by native_decide

private def twoRoleSource :=
  replace (replace source [3, 0, 2] (parse r#"["P","V"]"#))
    [4, 0, 5] (parse r#"[["P","P"],["V","V"]]"#)
private def twoRoleCandidate :=
  replace (replace candidate [4] (parse r#"[
    ["participant","p","root","P",[],[["x","bool@native.bool/1"],["y","bool@native.bool/1"]],
      ["bool@native.bool/1"],[["local","step","B",["x","y"],["z"]],["return",["z"]]]],
    ["participant","v","root","V",[],[],[],[["return",[]]]]]"#))
    [5, 0, 2] (parse r#"[["P","p"],["V","v"]]"#)
private def twoRoleInputs := replace inputs [3] (parse r#"[
  ["P",[["x",["bool","true"]],["y",["bool","false"]]]],["V",[]]]"#)
example : code (run (s := twoRoleSource) (c := twoRoleCandidate) (i := twoRoleInputs)) =
    some "physical-single-role" := by native_decide

private def reorderedSource := replace source [3, 0, 7, 0, 4] (parse r#"["y","x"]"#)
private def reorderedCandidate := replace candidate [4, 0, 7, 0, 3] (parse r#"["y","x"]"#)
-- Valid source/candidate correspondence, outside this interpreter's wrapper.
example : code (run (s := reorderedSource) (c := reorderedCandidate)) =
    some "physical-local-wrapper" := by native_decide

private def noLocalSource := replace source [3, 0, 7] (parse r#"[["return",["x"]]]"#)
private def noLocalCandidate := replace candidate [4, 0, 7] (parse r#"[["return",["x"]]]"#)
example : code (run (s := noLocalSource) (c := noLocalCandidate)) =
    some "physical-single-local" := by native_decide

-- Physical helpers use exactly the logical reference's observation weights.
private def observationCost : Nat :=
  let location : Reference.Location := Reference.Location.plain "test" "root" "op" "P"
  let action := do
    Reference.observeRequest location (.str "request") [.boolean true, .boolean false]
    Reference.observeResponse location (.str "request") [.boolean false]
  (action.run {}).2.spent
example : observationCost = 5 := by native_decide

-- Safe release is admitted before erasure for exact source correspondence.
private def released := replace candidate [3, 0, 4] (parse r#"[
  ["op","combine","and",[],["a","b"],["c"]],
  ["release",["a","b"]],["return",["c"]]]"#)
example : code (run (c := released)) = none := by native_decide
example : ((run (c := released)).toOption == (run).toOption) = true := by native_decide

private def releaseBody (body : String) := replace candidate [3, 0, 4] (parse body)
example : code (run (c := releaseBody r#"[
  ["release",["a"]],["op","combine","and",[],["a","b"],["c"]],
  ["return",["c"]]]"#)) = some "interactive-resource-reuse" := by native_decide
example : code (run (c := releaseBody r#"[
  ["op","combine","and",[],["a","b"],["c"]],["release",["c"]],
  ["return",["c"]]]"#)) = some "interactive-resource-reuse" := by native_decide
example : code (run (c := releaseBody r#"[
  ["op","combine","and",[],["a","b"],["c"]],["release",["a","a"]],
  ["return",["c"]]]"#)) = some "release-unavailable" := by native_decide
example : code (run (c := releaseBody r#"[
  ["op","combine","and",[],["a","b"],["c"]],["release",["a"]],
  ["release",["a"]],["return",["c"]]]"#)) = some "release-unavailable" := by native_decide
example : code (run (c := releaseBody r#"[
  ["op","combine","and",[],["a","b"],["c"]],["release",[]],
  ["return",["c"]]]"#)) = some "release-empty" := by native_decide
example : (run (c := releaseBody r#"[
  ["release",["missing"]],["op","combine","and",[],["a","b"],["c"]],
  ["return",["c"]]]"#)).toOption.isNone = true := by native_decide
example : code (run (c := replace (logicalTypes released) [2] (.str "logical"))) =
  some "release-context" := by native_decide
example : code (run (s := replace source [2, 0, 4] (parse r#"[
  ["op","combine","and",[],["x","y"],["z"]],["release",["x","y"]],
  ["return",["z"]]]"#))) = some "release-context" := by native_decide

-- Positive custody is required: unknown values do not gain release rights.
example : (["rng", "nonce", "transcript", "capability:opaque", "opaque:value"].all fun ty =>
  (admitFunctionWith (fun _ _ => .error "unused-signature")
    ⟨"F", [("x", ty)], [], some [.release ["x"], .ret []]⟩ true true) ==
    .error "release-resource") = true := by native_decide

example : (["prover_key", "verifier_key", "opening_state", "opening_states"].all fun ty =>
  (admitFunctionWith (fun _ _ => .error "unused-signature")
    ⟨"F", [("x", ty)], [], some [.release ["x"], .ret []]⟩ true true).isOk) = true := by native_decide

example : duplicable "opaque:value" = false := by native_decide
example : discardable "opening_states:scheme" = true := by native_decide

end Tests.PhysicalLocal
