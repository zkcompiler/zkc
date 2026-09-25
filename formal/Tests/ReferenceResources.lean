import Tools.Interactive.GenericReference

set_option autoImplicit false

namespace Tests.ReferenceResources
open Tools.Interactive
open Reference (State NonceState ResourcePayload)
open Lean (Json)

private def location : Reference.Location :=
  Reference.Location.plain "session" "root" "response" "P"

private def initial (payload : ResourcePayload) (budget : Nat) : State :=
  { resources := [⟨"nonce", "P", none, budget, payload, 0, 0⟩,
                  ⟨"untouched", "P", none, 3, .rng [7], 0, 0⟩] }

private def response (payload : ResourcePayload) (budget : Nat) : String × String :=
  let (result, state) := (Reference.nonceResponse location 3 7 "nonce" 0).run (initial payload budget)
  let outcome := match result with
    | .ok values => (Reference.valuesJson values).compress
    | .error fault => fault.reason ++ ":" ++ fault.detail
  (outcome, state.resourcesJson.compress)

private def expected (generation budget : Nat) (stage : String) : String :=
  (Json.arr #[.arr #[.str "nonce", .str "P", .arr #[], .str (toString generation),
    .str (toString generation), .str (toString budget), .str stage],
    .arr #[.str "untouched", .str "P", .arr #[], .str "0", .str "0", .str "3", .str "rng"]]).compress

-- A response before commitment spends the nonce, even though it returns no value.
example : response (.nonce (.issued 5)) 2 =
    ("refused:nonce-stage", expected 1 1 "spent") := by native_decide
example : response (.nonce (.committed 5)) 2 =
    ("[[\"field:bls12-381.fr\",\"26\"]]", expected 1 1 "spent") := by native_decide
example : response (.nonce .spent) 2 =
    ("refused:nonce-stage", expected 1 1 "spent") := by native_decide

-- Exhausted budget advances counters but does not reach the stage transition.
example : response (.nonce (.issued 5)) 0 =
    ("exhausted:resource-budget", expected 1 0 "issued") := by native_decide
example : response (.nonce (.committed 5)) 0 =
    ("exhausted:resource-budget", expected 1 0 "committed") := by native_decide
example : response (.nonce .spent) 0 =
    ("exhausted:resource-budget", expected 1 0 "spent") := by native_decide
example : response (.rng [5]) 2 =
    ("refused:capability-kind", expected 0 2 "rng") := by native_decide

private def emptyGroups : ByteArray :=
  (Tools.Artifact.magic.push 10) ++ Tools.Artifact.little 4 0

private def commit (payload : ResourcePayload) (budget : Nat) : String × String :=
  let (result, state) := (Reference.nonceCommit location emptyGroups "nonce" 0).run (initial payload budget)
  (match result with
    | .ok _ => "returned"
    | .error fault => fault.reason ++ ":" ++ fault.detail,
   state.resourcesJson.compress)

example : commit (.nonce (.issued 5)) 2 =
    ("pending-primitive:exact-request-missing", expected 1 1 "committed") := by native_decide
example : commit (.nonce (.committed 5)) 2 =
    ("refused:nonce-stage", expected 1 1 "spent") := by native_decide
example : commit (.nonce .spent) 2 =
    ("refused:nonce-stage", expected 1 1 "spent") := by native_decide
example : commit (.nonce (.issued 5)) 0 =
    ("exhausted:resource-budget", expected 1 0 "issued") := by native_decide
example : commit (.nonce (.committed 5)) 0 =
    ("exhausted:resource-budget", expected 1 0 "committed") := by native_decide

end Tests.ReferenceResources
