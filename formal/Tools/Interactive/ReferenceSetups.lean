import Tools.Interactive.ReferenceState

/-! Host-selected PCS authority, independent of peer bytes and provider answers.
Keys name already imported external material. Receive policies select an intended
key at an exact source receiving cut; authorizing several keys is not selection.
-/

set_option autoImplicit false

namespace Tools.Interactive.Reference
open Lean (Json)

def setupContext (roles : List Name) (json : Json) : Result
    (List (Name × List CommitmentIdentity) × List (Json × CommitmentIdentity)) := do
  if json == .arr #[] then return ([], [])
  let [.str "zkc.reference-setups/1", keys, receiving] ← Decode.array json
    | throw "reference-setup-context"
  let keys ← Decode.pairs Decode.name (fun j => do
    let identities ← (← Decode.array j 64).mapM CommitmentIdentity.decode
    ensure (identities.length == identities.eraseDups.length) "duplicate-setup"
    return identities) keys
  ensure (unique (keys.map Prod.fst) && keys.all (fun row => roles.contains row.1)) "setup-roles"
  let mut seen : Std.HashSet String := {}
  let receiving ← (← Decode.array receiving).mapM fun j => do
    let [key, identity] ← Decode.array j | throw "reference-receiving-key"
    let [.str "receive", .arr origin, .str _, .str _, .str _] ← Decode.array key
      | throw "reference-receiving-key"
    ensure (origin.size == 8) "reference-receiving-key"
    let role ← Decode.name origin[6]!
    let identity ← CommitmentIdentity.decode identity
    let installed := (keys.find? (fun row => row.1 == role)).map Prod.snd |>.getD []
    ensure (installed.any (· == identity)) "unauthorized-receiving-setup"
    return (key, identity)
  for (key, _) in receiving do
    ensure (!(seen.contains key.compress)) "duplicate-receiving-key"
    seen := seen.insert key.compress
  return (keys, receiving)

def validateReceivingKey (location : Location) (key : Json) (value : Value) : RunM Unit := do
  if let some actual ← checked location value.commitmentIdentity then
    let state ← get
    let some (_, expected) := state.receivingKeys.find? (fun row => row.1 == key)
      | failAt location "refused" "receiving-setup-missing"
    checked location (expected.matches actual)
    checked location (authorized state location.scope.role value)

end Tools.Interactive.Reference
