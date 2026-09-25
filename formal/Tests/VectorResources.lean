import Tools.Interactive.GenericReference

set_option autoImplicit false

namespace Tests.VectorResources
open Tools.Interactive Reference
open Lean (Json)

private def location : Location :=
  Location.plain "session" "root" "mask" "P"

private def payload (domain : RandomDomain) (tape : List Nat) : ResourcePayload :=
  match domain with
  | .bls => .rng (tape.map Nat.cast)
  | .ristretto => .rrng (tape.map Nat.cast)
  | .bn254 => .brng (tape.map Nat.cast)

private def initial (domain : RandomDomain) (budget : Nat) (tape : List Nat) : State :=
  { resources := [⟨"rng", "P", some "root", budget, payload domain tape, 3, 7⟩,
      ⟨"untouched", "V", none, 11, .rng [19], 2, 5⟩]
    events := #[.str "existing-event"]
    spent := 9 }

-- Include the whole observable resource record, payload tape, prior events,
-- fault origin and work counter. These expectations do not erase generation,
-- draw budget or unaffected resources to obtain parity.
private def snapshot (result : Except Fault (List Value)) (state : State) : Json :=
  .arr #[
    match result with
    | .ok values => .arr #[.str "returned", valuesJson values]
    | .error f => .arr #[.str f.reason, .str f.detail, f.location.json],
    state.resourcesJson,
    .arr (state.resources.map fun r => match r.payload with
      | .rng tape => .arr (tape.map fun x => .str (toString x.val)).toArray
      | .brng tape => .arr (tape.map fun x => .str (toString x.val)).toArray
      | .rrng tape => .arr (tape.map fun x => .str (toString x.val)).toArray
      | _ => .null).toArray,
    .arr state.events, .str (toString state.spent)]

private def expected (domain : RandomDomain) (budget : Nat) (tape : List Nat)
    (generation draws : Nat) (result : Except Fault (List Value)) : Json :=
  let state := initial domain budget tape
  snapshot result { state with resources := state.resources.map fun r =>
    if r.identity == "rng" then { r with generation, draws } else r }

private def success (domain : RandomDomain) (xs : List Nat) : Except Fault (List Value) :=
  .ok [Value.fromArithmetic domain.scalar (.vector (xs.map Nat.cast)), rngValue domain "rng" 4]

private def failure (reason detail : String) : Except Fault (List Value) :=
  .error ⟨reason, detail, location⟩

private def run (domain : RandomDomain) (count budget : Nat) (tape : List Nat)
    (generation := 3) : Json :=
  let (result, state) := (randomVector location domain "rng" generation count).run (initial domain budget tape)
  snapshot result state

private def checks (domain : RandomDomain) : List Bool := [
  run domain 0 4 [2, 3, 4, 5] == expected domain 4 [2, 3, 4, 5] 4 7 (success domain []),
  run domain 1 4 [2, 3, 4, 5] == expected domain 3 [3, 4, 5] 4 8 (success domain [2]),
  run domain 3 4 [2, 3, 4, 5] == expected domain 1 [5] 4 10 (success domain [2, 3, 4]),
  run domain 0 0 [] == expected domain 0 [] 4 7 (success domain []),
  run domain 3 2 [2, 3, 4] == expected domain 2 [2, 3, 4] 3 7 (failure "exhausted" "resource-budget"),
  run domain 1 0 [2] == expected domain 0 [2] 3 7 (failure "exhausted" "resource-budget"),
  run domain 0 0 [] 2 == expected domain 0 [] 3 7 (failure "refused" "capability-stale"),
  run domain 1 4 [2] 2 == expected domain 4 [2] 3 7 (failure "refused" "capability-stale"),
  run domain 3 4 [] == expected domain 1 [] 4 10 (failure "exhausted" "test-tape"),
  run domain 3 4 [2] == expected domain 1 [] 4 10 (failure "exhausted" "test-tape")]

example : (checks .bls).all id = true := by native_decide
example : (checks .ristretto).all id = true := by native_decide
example : (checks .bn254).all id = true := by native_decide

private def staleAfterFailure (domain : RandomDomain) : Json :=
  let action : RunM (List Value) := do
    try let _ ← randomVector location domain "rng" 3 3; pure () catch _ => pure ()
    randomVector location domain "rng" 3 0
  let (result, state) := action.run (initial domain 4 [2])
  snapshot result state
example : staleAfterFailure .bls == expected .bls 1 [] 4 10 (failure "refused" "capability-stale") := by native_decide
example : staleAfterFailure .bn254 == expected .bn254 1 [] 4 10 (failure "refused" "capability-stale") := by native_decide
example : staleAfterFailure .ristretto == expected .ristretto 1 [] 4 10 (failure "refused" "capability-stale") := by native_decide

private def scalar (domain : RandomDomain) (budget : Nat) (tape : List Nat) : Json :=
  let (result, state) := (randomDraw location "rng" 3 domain).run (initial domain budget tape)
  snapshot result state
-- Scalar consumption still advances before budget/backend-output failure.
example : ([RandomDomain.bls, .ristretto, .bn254].all fun d =>
    scalar d 0 [2] == expected d 0 [2] 4 8 (failure "exhausted" "resource-budget")) = true := by native_decide
example : ([RandomDomain.bls, .ristretto, .bn254].all fun d =>
    scalar d 4 [] == expected d 3 [] 4 8 (failure "exhausted" "test-tape")) = true := by native_decide

private def wrongScope (owner : Name) (binding : Option Name) (count : Nat) : Json :=
  let state := initial .bls 4 [2]
  let state := { state with resources := state.resources.map fun r =>
    if r.identity == "rng" then { r with owner, boundInstance := binding } else r }
  let (result, next) := (randomVector location .bls "rng" 3 count).run state
  .arr #[snapshot result next, snapshot (failure "refused" "capability-domain") state]
example : ([0, 1].all fun count =>
    match wrongScope "V" (some "root") count with
    | .arr pair => pair[0]? == pair[1]?
    | _ => false) = true := by native_decide
example : ([0, 1].all fun count =>
    match wrongScope "P" (some "elsewhere") count with
    | .arr pair => pair[0]? == pair[1]?
    | _ => false) = true := by native_decide

end Tests.VectorResources
