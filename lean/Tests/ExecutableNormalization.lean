import Tests.CanonicalNormalization
import Mathlib.Algebra.Field.ZMod
import ZkcExamples.Construction.SchnorrArtifact

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

/-- A missing helper is an anchored refusal, even when dead total work moves. -/
theorem missing_helper_normalizes :
    (Zkc.Executable.CanonicalNormalization.check [field] [field]
      [multiply 0 0, helper 0] [2] [helper 0] [1]).toOption.isSome = true := by
  decide +kernel

theorem missing_helper_stops :
    (actual ZkcExamples.Construction.SchnorrProof.program
      [multiply 0 0, helper 0] [2] [.data (.field fr 1)] |>.run 0) =
      ((.stopped .refused, []), 0) ∧
    (actual ZkcExamples.Construction.SchnorrProof.program
      [helper 0] [1] [.data (.field fr 1)] |>.run 0) =
      ((.stopped .refused, []), 0) := by
  constructor <;> kernel_rfl

/-- Eliminating unused total work before a loop preserves both zero iterations
and refusal above the actual maximum. It does not change that bound. -/
theorem bounded_loop_normalizes :
    (Zkc.Executable.CanonicalNormalization.check [transcript, field, .data .index] [field]
      [multiply 1 1, loop 2 1 [5] []] [4] [loop 2 1 [4] []] [3]).toOption.isSome = true := by
  decide +kernel

def loopInput (count : Nat) : DomainVM.Environment F G :=
  [.transcript suite [], .data (.field fr 1), .data (.index count)]

theorem zero_loop_returns (program : Structured.Program) :
    (actual program [multiply 1 1, loop 2 1 [5] []] [4] (loopInput 0) |>.run 0) =
      ((.returned [.data (.field fr 1)], []), 0) ∧
    (actual program [loop 2 1 [4] []] [3] (loopInput 0) |>.run 0) =
      ((.returned [.data (.field fr 1)], []), 0) := by
  constructor <;> kernel_rfl

theorem oversized_loop_refuses (program : Structured.Program) :
    (actual program [multiply 1 1, loop 2 1 [5] []] [4] (loopInput 3) |>.run 0) =
      ((.stopped .refused, []), 0) ∧
    (actual program [loop 2 1 [4] []] [3] (loopInput 3) |>.run 0) =
      ((.stopped .refused, []), 0) := by
  constructor <;> kernel_rfl

/-- Normalization preserves an unchanged refusal; it is not whole-program
admission. This malformed schema never reaches a receive effect. -/
def refusingReceive : Instruction :=
  ⟨.receive "site" "different-schema" "peer" .boolean, [], [.data .boolean], []⟩

theorem common_refusal_normalizes :
    (Zkc.Executable.CanonicalNormalization.check [] []
      [refusingReceive] [] [refusingReceive] []).toOption.isSome = true := by
  decide +kernel

theorem common_refusal_stops (program : Structured.Program) :
    (actual program [refusingReceive] [] [] |>.run 0) = ((.stopped .refused, []), 0) := by
  kernel_rfl

end Tests.ExecutableNormalization
