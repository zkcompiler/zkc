module

public import Zkc.Core.Meaning.Program
public import Zkc.Core.Process.Same
public import Std.WP
public import Std.Tactic

@[expose] public section
set_option autoImplicit false
set_option experimental.vcgen true

namespace Zkc.Formal.Written
open Zkc.Core Std.WP

/-- A complete execution of the actual Core process, with the operation and typed reply at
every interaction, through its successful return. Stops have no such derivation. -/
inductive Returns {S : Sig} {H A : Type} : Process S H A → List ((op : S.Op) × S.Reply op) → Prop where
  | done (value : A) : Returns (.done value) []
  | call {op : S.Op} {k : S.Reply op → Process S H A} {rest} (v : S.Reply op) :
      Returns (k v) rest → Returns (.call op k) (⟨op, v⟩ :: rest)

variable {S : Sig} {H A : Type}

@[simp] theorem returns_call {op : S.Op} {k : S.Reply op → Process S H A} {v : S.Reply op} {rest} :
    Returns (.call op k) (⟨op, v⟩ :: rest) ↔ Returns (k v) rest := by
  constructor
  · intro h; cases h with | call _ h => exact h
  · exact .call v

@[simp] theorem returns_done (a : A) : Returns (S := S) (H := H) (.done a) [] := .done a

@[simp] theorem not_returns_halt (why : H) (trace) : ¬ Returns (S := S) (A := A) (.halt why) trace := by
  intro h; cases h

/-- A driver can realize each permitted returning transcript as a returning Core execution. -/
theorem Returns.canReturn {p : Process S H A} {trace} (h : Returns p trace)
    (allowed : ∀ op, S.Reply op → Prop)
    (valid : ∀ x ∈ trace, allowed x.1 x.2) : ∃ a, p.CanReturn allowed a := by
  induction h with
  | done value => exact ⟨value, .done value⟩
  | call v tail ih =>
    obtain ⟨a, h⟩ := ih (fun x hx => valid x (List.mem_cons_of_mem _ hx))
    exact ⟨a, .call _ v (valid _ (List.mem_cons_self ..)) h⟩

/-- An observed input whose operation can be compared with an arbitrary process call.
Only the expected operation needs decidable equality. -/
structure Input (S : Sig) where
  op : S.Op
  reply : S.Reply op
  compareOp : (actual : S.Op) → Decidable (actual = op)

def Input.entry {S : Sig} (x : Input S) : (op : S.Op) × S.Reply op := ⟨x.op, x.reply⟩

def replay {S : Sig} {H A : Type} : List (Input S) → Process S H A → Option Unit
  | [], .done _ => some ()
  | x :: xs, .call op k =>
    match x.compareOp op with
    | .isTrue h => replay xs (k (h ▸ x.reply))
    | .isFalse _ => none
  | _, _ => none

theorem replay_iff {S : Sig} {H A : Type} (inputs : List (Input S)) (p : Process S H A) :
    Returns p (inputs.map Input.entry) ↔ replay inputs p = some () := by
  induction inputs generalizing p with
  | nil =>
    cases p with
    | done value => exact ⟨fun _ => rfl, fun _ => .done value⟩
    | halt | call => constructor <;> intro h <;> cases h
  | cons x xs ih =>
    cases p with
    | done | halt => constructor <;> intro h <;> cases h
    | call op k =>
      simp only [List.map_cons, replay]
      split
      next h =>
        subst op
        exact returns_call.trans (ih _)
      next noMatch _ =>
        constructor
        · intro run
          cases x with | mk expected reply _ =>
            cases run
            exact False.elim (noMatch rfl)
        · intro no; cases no

end Zkc.Formal.Written
