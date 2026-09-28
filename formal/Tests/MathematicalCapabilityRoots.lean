import Zkc.Source.Mathematical.DefinitionAdmission

set_option autoImplicit false
namespace Tests.MathematicalCapabilityRoots
open Zkc.Source.Mathematical
open Protocol

def table : List (Protocol.Capability Nat Nat) := [⟨⟨5, [0]⟩, 0⟩, ⟨⟨5, [0, 1]⟩, 1⟩]

example : RootTable table := rfl
example : Rooted table table := (show RootTable table from rfl).rooted

example : ¬ Rooted table [⟨⟨6, [0]⟩, 0⟩] := by
  intro rooted
  have invalid := rooted Zkc.Source.Var.here
  simp [RootedIn, table] at invalid

example : ¬ Rooted table [⟨⟨5, [0, 1]⟩, 0⟩] := by
  intro rooted
  have invalid := rooted Zkc.Source.Var.here
  simp [RootedIn, table] at invalid

example : ¬ Rooted table [⟨⟨5, [0]⟩, 2⟩] := by
  intro rooted
  have invalid := rooted Zkc.Source.Var.here
  simp [RootedIn, table] at invalid

-- Empty permissions are a valid weakening of the selected root.
example : Rooted table [⟨⟨5, []⟩, 0⟩] := by
  intro capability reference
  cases reference with
  | here => simp [RootedIn, table]
  | there reference => cases reference

-- Repeated port aliases retain one service identity. Distinctness, when an
-- operation requires it, is an additional obligation rather than a root-table
-- invariant that would reject all aliases.
example : Rooted table [⟨⟨5, [0]⟩, 0⟩, ⟨⟨5, []⟩, 0⟩] := by
  intro capability reference
  cases reference with
  | here => simp [RootedIn, table]
  | there reference =>
      cases reference with
      | here => simp [RootedIn, table]
      | there reference => cases reference

example {Role Service} {table : List (Protocol.Capability Role Service)} {first second}
    (left : RootedIn table first) (right : RootedIn table second) (same : first.root = second.root) :
    first.service = second.service := left.service_functional right same

example {Payload contracts source} (header : DeclarationAdmission.Header (Payload := Payload) contracts source) :
    RootTable header.capabilities := header.rootTable

example {Payload contracts source} (header : DeclarationAdmission.Header (Payload := Payload) contracts source)
    {target declaration parameters binding calls scope available indices}
    (checked : DefinitionAdmission.Bound header (target := target) declaration parameters binding calls scope available indices)
    {table : List (Protocol.Capability Nat (RegisteredVocabulary.vocabulary header target).Service)}
    (rooted : Rooted table available) : Rooted table checked.selected.bound := DefinitionAdmission.Bound.rooted header checked rooted

end Tests.MathematicalCapabilityRoots
