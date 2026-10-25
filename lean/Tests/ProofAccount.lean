module

public import ZkcTools.ProofAccount

/-! Measurement controls do not introduce a receipt-acceptance rule. -/
public section
namespace Tests.ProofAccount
open Lean Meta Elab Command ZkcTools.ProofAccount

theorem reuse {α : Type} (value : α) (proof : value = value) : value = value := proof

theorem dependent (n : Nat) (value : Fin (n + 1)) : value = value :=
  let first := value
  let second := first
  reuse second rfl

theorem dataLast (proof : True) (_index : Nat) : True := proof
theorem selectsData : True := dataLast True.intro 3
theorem typeOnly (_proof : reuse 3 rfl = rfl) : True := True.intro

namespace auxiliary
theorem proof : 3 = 3 := reuse 3 rfl
end auxiliary
theorem auxiliary : 3 = 3 := auxiliary.proof

meta def expectRefusal {α : Type} {m : Type → Type} [Monad m] [MonadExceptOf Exception m]
    [MonadLiftT BaseIO m] (label reason : String) (action : m α) : m Unit := do
  let refused ← try
    let _ ← action
    pure false
  catch error =>
    let message ← error.toMessageData.toString
    unless message.contains reason do throw error
    pure true
  unless refused do throw (.error Syntax.missing m!"control unexpectedly succeeded: {label}")

meta def selected (owner : Name) : Checkpoint := {
  identifier := "control", phase := "initialization", responsibility := "I"
  owner, callee := ``reuse, route := .generalRule, expectedUses := some 1 }

run_cmd liftTermElabM do
  let graph ← reachable ``dependent
  let record ← account graph (selected ``dependent)
  let applications ← ofExcept <| record.getObjValAs? (Array Json) "applications"
  let uses ← ofExcept <| applications[0]!.getObjValAs? (Array Json) "uses"
  let context ← ofExcept <| uses[0]!.getObjValAs? (Array Json) "context"
  unless context.size == 4 do throwError "dependent/let telescope was truncated"
  for entry in context do
    let _ ← ofExcept <| entry.getObjValAs? String "name"
  let last ← ofExcept <| context[3]!.getObjValAs? String "value"
  unless last == "first" do throwError "let value was lost"
  let closed ← ofExcept <| uses[0]!.getObjValAs? String "closed_type"
  unless closed.contains "Fin" do throwError "dependent type was lost"
  let _ ← account (← reachable ``auxiliary) (selected ``auxiliary)
  expectRefusal "unconnected owner" "declaration is not reached" <|
    account (← reachable ``selectsData) (selected ``dependent)
  expectRefusal "missing application" "missing application" <|
    account graph { selected ``dependent with callee := ``dataLast }
  expectRefusal "ambiguous count" "expected 2 applications, found 1" <|
    account graph { selected ``dependent with expectedUses := some 2 }
  expectRefusal "unknown parameter" "unknown application parameter" <| account graph { selected ``dependent with
    arguments := [⟨`absent, .natural 1⟩] }
  expectRefusal "wrong argument" "missing application" <| account graph { selected ``dependent with
    arguments := [⟨`value, .natural 1⟩] }
  expectRefusal "data selected as proof" "selected argument is data" <| account (← reachable ``selectsData) {
    selected ``selectsData with callee := ``dataLast, selection := .lastArgument }
  expectRefusal "type-only application" "missing application" <| account (← reachable ``typeOnly) (selected ``typeOnly)
  logInfo "PROOF-ACCOUNT-CONTROLS-PASS"

end Tests.ProofAccount
