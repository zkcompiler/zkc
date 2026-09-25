import Tools.Interactive.GenericReference

set_option autoImplicit false

namespace Tests.GenericReference
open Tools.Interactive
open Reference (Value State)
open Lean (Json)

private def bindings : List OperationBinding :=
  [⟨"draw", "random.draw", ["bls12-381.fr"], ""⟩,
   ⟨"guard", "control.require", [], ""⟩]

private def source : Explicit.Function :=
  ⟨⟨"Checked", [("rng", "rng:bls12-381.fr"), ("allowed", "bool")],
    ["field:bls12-381.fr", "rng:bls12-381.fr"], some [
      .op "draw" "draw" [] ["rng"] ["r", "next"],
      .op "guard" "guard" [] ["allowed"] [], .ret ["r", "next"]]⟩,
    some ⟨"Step", [("F", "bls12-381.fr")]⟩⟩

private def location : Reference.Location :=
  ⟨"session", "main", ⟨"child", [.call "nested", .localCall "step" "Checked"], "step", "P"⟩, none, #[]⟩

private def execute (state : State) (generation : Nat) (allowed : Bool) : Result Json := do
  let function ← TypedLocal.elaborate bindings source
  let (outcome, after) := (Reference.executeFunction location function
    [.rng "draws" generation, .boolean allowed]).run state
  let outcome := match outcome with
    | .ok values => Json.arr #[.str "returned", Reference.valuesJson values]
    | .error error => .arr #[.str error.reason, .str error.detail,
        .str error.location.scope.site, error.location.json]
  return .arr #[outcome, after.resourcesJson, .arr after.events]

private def initial (budget : Nat) (tape : List Math.Fr)
    (boundInstance : Option Name := none) : State :=
  { resources := [⟨"draws", "P", boundInstance, budget, .rng tape, 0, 0⟩,
                  ⟨"untouched", "P", none, 3, .rng [7], 0, 0⟩] }

private def terminal (result : Result Json) : Option (List Json) := do
  let j ← result.toOption
  (j.getArr?.toOption >>= (·[0]?)) >>= (·.getArr?.toOption.map Array.toList)

private def stopped (result : Result Json) : Option (String × String × String) := do
  let [.str reason, .str detail, .str site, _] ← terminal result | none
  return (reason, detail, site)

private def resources (result : Result Json) : Option String :=
  (result.toOption >>= (·.getArr?.toOption) >>= (·[1]?)).map Json.compress

example : stopped (execute (initial 2 [3]) 0 false) = some ("reject", "require", "guard") := by native_decide
example : stopped (execute (initial 0 [3]) 0 true) = some ("exhausted", "resource-budget", "draw") := by native_decide
example : stopped (execute (initial 2 []) 0 true) = some ("exhausted", "test-tape", "draw") := by native_decide
example : stopped (execute (initial 2 [3]) 1 true) = some ("refused", "capability-stale", "step") := by native_decide
example : stopped (execute (initial 2 [3] (some "other")) 0 true) = some ("refused", "capability-domain", "step") := by native_decide

-- Resource authenticity is now checked at local-frame entry, before draw.
-- Guard failure is after consumption. Domain/generation refusal is before it.
example : resources (execute (initial 2 [3]) 0 false) = resources (execute (initial 2 [3]) 0 true) := by native_decide
example : resources (execute (initial 2 [3]) 1 true) = some (initial 2 [3]).resourcesJson.compress := by native_decide
example : resources (execute (initial 2 [3] (some "other")) 0 true) =
    some (initial 2 [3] (some "other")).resourcesJson.compress := by native_decide

private def key : Json := Reference.requestJson location "curve.generator" ["bls12-381.g1"] [] []
private def external (answers : List (String × Json)) : String × Nat × Nat :=
  let (result, state) := (Reference.external location "curve.generator" ["bls12-381.g1"] [] []).run
    { answers := Std.HashMap.ofList answers }
  (match result with | .ok _ => "returned" | .error fault => fault.reason ++ ":" ++ fault.detail,
    state.events.size, state.usedAnswers.size)

example : external [] = ("pending-primitive:exact-request-missing", 1, 0) := by native_decide
example : external [("different-site", .arr #[.str "ok", .arr #[]])] =
    ("pending-primitive:exact-request-missing", 1, 0) := by native_decide
example : external [(key.compress, .arr #[.str "error", .str "refused", .str "invalid-subgroup"])] =
    ("refused:invalid-subgroup", 1, 1) := by native_decide
example : external [(key.compress, .arr #[.str "error", .str "success", .str "ignored"])] =
    ("refused:primitive-error-reason", 1, 1) := by native_decide

private def decodeCode (value : Json) : Option String :=
  match Reference.decodeValue value with | .error code => some code | .ok _ => none
example : decodeCode (.arr #[.str "field:bls12-381.fr", .str (toString fieldModulus)]) =
    some "noncanonical-field" := by native_decide
example : decodeCode (.arr #[.str "field:bls12-381.fr@arkworks.fr/1", .str "1"]) =
    some "binding-type" := by native_decide
example : decodeCode (.arr #[.str "group:bls12-381.fr", .str "1"]) =
    some "binding-type" := by native_decide
example : decodeCode (.arr #[.str "bool", .str "1"]) =
    some "reference-bool" := by native_decide

example : Reference.decodeSession (.str "2026-09-15") = .ok "2026-09-15" := by native_decide
example : Reference.decodeSession (.str ".session") = .ok ".session" := by native_decide
example : Reference.decodeSession (.str "-session") = .ok "-session" := by native_decide
example : Reference.decodeSession (.str "") = .error "invalid-session" := by native_decide
example : Reference.decodeSession (.str "bad/session") = .error "invalid-session" := by native_decide
example : Reference.decodeSession (.str "é") = .error "invalid-session" := by native_decide
example : Reference.decodeSession (.str (String.ofList (List.replicate 128 '0'))) =
    .ok (String.ofList (List.replicate 128 '0')) := by native_decide
example : Reference.decodeSession (.str (String.ofList (List.replicate 129 '0'))) =
    .error "invalid-session" := by native_decide

example : (Reference.Value.nonce "n" 0).public = false := by native_decide

end Tests.GenericReference
