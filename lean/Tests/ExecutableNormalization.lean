import Tests.CanonicalNormalization
import Mathlib.Algebra.Field.ZMod

/-! The refusal controls in `CanonicalNormalization` preserve observable
interaction, not just the eventual stop. These counterexamples execute the
actual Domain Process under a handler that counts challenge queries. -/
namespace Tests.ExecutableNormalization
open Zkc.Construction Zkc.Executable Zkc.Source
open Tests.CanonicalNormalization

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
abbrev F := ZMod 5
abbrev G := ZMod 5

def context : Context :=
  Context.fiatShamir "entry" ["prover", "verifier"] 0 1 2 "random.fr/0" (some (.draw fr)) suite []

/-- A challenge function that counts its queries. -/
def counting (_ : History F G) : StateM Nat F := do
  modify (· + 1)
  pure 0

/-- Run actual canonical instructions; the supplied program is relevant only
when an instruction calls one of its helpers. -/
def actual (program : Structured.Program) (instructions : List Instruction)
    (returned : List Nat) (env : DomainVM.Environment F G) :=
  Uniform.DomainAdapter.run id [] counting
    (DomainVM.observation program context instructions returned env) []

def queries (run : StateM Nat (PIR.Outcome (DomainVM.Environment F G) × Proof F G)) : Nat :=
  (run.run 0).2

def outOfRange : DomainVM.Environment F G :=
  [.transcript suite [], .data (.vector fr []), .data (.index 0)]

/-- Moving a partial calculation past a challenge retains its refusal but
changes the interaction. The same counterexample holds for every helper library. -/
theorem moved_stop_changes_interaction (program : Structured.Program) :
    queries (actual program [coordinates, element 1 2, draw 0 3] [4, 6] outOfRange) = 0 ∧
      queries (actual program [coordinates, draw 0 3, element 1 2] [6, 5] outOfRange) = 1 ∧
      (actual program [coordinates, element 1 2, draw 0 3] [4, 6] outOfRange |>.run 0).1 =
        (actual program [coordinates, draw 0 3, element 1 2] [6, 5] outOfRange |>.run 0).1 := by
  constructor
  · kernel_rfl
  constructor <;> kernel_rfl

def rejecting : DomainVM.Environment F G := [.transcript suite [], .data (.boolean false)]

/-- A rejecting guard is equally observable: moving it past a challenge adds
one oracle query before the same rejection. -/
theorem moved_guard_changes_interaction (program : Structured.Program) :
    queries (actual program [coordinates, guard 1, draw 0 2] [3] rejecting) = 0 ∧
      queries (actual program [coordinates, draw 0 2, guard 1] [3] rejecting) = 1 ∧
      (actual program [coordinates, guard 1, draw 0 2] [3] rejecting |>.run 0).1 =
        (actual program [coordinates, draw 0 2, guard 1] [3] rejecting |>.run 0).1 := by
  constructor
  · kernel_rfl
  constructor <;> kernel_rfl

end Tests.ExecutableNormalization
