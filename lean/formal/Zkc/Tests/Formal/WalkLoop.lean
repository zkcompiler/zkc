import Zkc.Core.Admission.Theorems
import Zkc.Kernel
import Zkc.Vocabulary.Project
import Zkc.Formal.Walk
import Zkc.Formal.ChargedProbability

/-!
A walk through a loop whose body has effects.

The program is the stored form of a protocol of three rounds. In each round the verifier gets a
position from the prover and draws one; it rejects unless the claim holds or some round drew
the position that it got.

```
protocol Guess roles(P, V)(claim: bool @(P, V), guess: index<8> @P):
    mut hit = false
    for i in 0..3:
        g <- send guess from P to V
        r <- draw index<8> from V to P
        hit := hit or (r == g)
    guard @V claim or hit
```

The verifier is walked twice, and each walk takes every kind of step: values that are
constants, variables and computations, an effect and what is left of its instruction, a loop by
an invariant, a guard that waits on a value, a return and a stop.

- Under a judgment that follows every reply and counts the effects, it meets six of them on
  every run, however the run ends (`six_effects`).
- Under the judgment with fees, it is judged within any budget when nothing is asked of how a
  run ends: every effect is met at no fee (`judged_free`).

The second walk also keeps the cost of a walk in check. Each step is an equation about one
instruction, which the kernel checks there. When a step instead left the kernel to find the
goal before it and the goal after it equal, the first step of the second walk did not pass the
kernel within its limit, while the whole of the first walk did, and so did the walks of
programs without a loop of effects under the judgment with fees.
-/

open Zkc.Core Zkc.Formal Zkc.Formal.ProbabilisticProcess
open scoped NNRat

namespace Zkc.Tests.Formal.WalkLoop

abbrev V : Vocabulary := (Zkc.Vocabulary.Project.Bindings.mk [] (by decide +kernel)).vocabulary

/-- The protocol by names: the claim and the hit (`0`, `3`, `13`), the position got and the
position drawn in a round (`6`, `7`), and what the guard reads (`14`). -/
def stored : Definition V :=
  .protocol ⟨0⟩ 2 [⟨.bool, [0, 1]⟩, ⟨.fin 8, [0]⟩] []
    (.mk [0, 1] [
      .op ⟨0⟩ [2] (.compute [0, 1] (.literal .bool [0])) [],
      .op ⟨1⟩ [3] (.narrow [0, 1]) [2],
      .loop ⟨9⟩ [0, 1] (.fixed 3) [3] [13] (.mk [4, 5] [
        .op ⟨2⟩ [6] (.event (.flow .message 0 [1]) (.fin 8)) [1],
        .op ⟨3⟩ [7] (.event (.given (.coin (.uniform (.fin 8))) 1 [0]) (.fin 8)) [],
        .op ⟨4⟩ [8] (.compute [0, 1] (.owned OwnedName.finToNat [.fin 8] [])) [7],
        .op ⟨5⟩ [9] (.compute [0, 1] (.owned OwnedName.finToNat [.fin 8] [])) [6],
        .op ⟨6⟩ [10] (.compute [0, 1] (.owned OwnedName.natEqual [] [])) [8, 9],
        .op ⟨7⟩ [11] (.compute [0, 1] (.owned OwnedName.boolOr [] [])) [5, 10],
        .op ⟨8⟩ [12] (.narrow [0, 1]) [11]] [12]),
      .op ⟨10⟩ [14] (.compute [1] (.owned OwnedName.boolOr [] [])) [0, 13],
      .guard ⟨11⟩ [1] 14 .reject] [])

noncomputable section

kernel_ok elaborated with header names body : Elaborated V Typed.empty.headers :=
  elaborateDefinition Typed.empty.headers stored

def installed : Typed V := Typed.empty.add elaborated

abbrev verifier : Role := 1

-- The program of the verifier, in the kernel's normal form.
kernel_normal verifierProgram :
    Term (roleDialect V Typed.empty.headers verifier) (Ctx.empty.extend names) header.outs :=
  project verifier body

/-- The process of the verifier in a run of the installed program is the denotation of its
program. -/
theorem verifier_meaning (M : Model V) (path : List Frame)
    (inputs : HList (RV M verifier) header.ins) :
    roleMeaning M installed Member.head verifier path inputs =
      (verifierProgram.denote (roleSem M verifier (Defs.fnTable M Typed.empty.defs)
        (Defs.rTable M Typed.empty.defs)) path (Env.empty.extend names inputs)).sealed := by
  kernel_rfl

/-- What the verifier holds when a run starts: the claim, and nothing of the prover's guess. -/
def inputs (M : Model V) (claim : Bool) : HList (RV M verifier) header.ins :=
  .cons claim (.cons () .nil)

/-- A judgment that follows every reply and counts the effects met. -/
def counting (S : Sig) : ProcessJudgment S (Nat → Prop) where
  node _ next count := ∀ reply, next reply (count + 1)

theorem counting_monotone (S : Sig) : (counting S).Monotone :=
  fun _ _ _ implied count all reply => implied reply (count + 1) (all reply)

/-- On every run the verifier meets six effects, a message and a coin in each of the three
rounds, whether it returns or rejects. -/
theorem six_effects (M : Model V) (path : List Frame) (claim : Bool) :
    (roleMeaning M installed Member.head verifier path (inputs M claim)).interpret
      (counting _) (fun _ count => count = 6) (fun _ count => count = 6) 0 := by
  rw [verifier_meaning]
  walk_step
  walk_step
  walk_loop (fun i (_ : Bool) count => count = 2 * i) using counting_monotone _
  case first => rfl
  case step =>
    subst invariant9
    -- the message, and the position that it brings
    walk_step
    intro got
    walk_step
    -- the coin, and the position that it draws
    walk_step
    intro drawn
    walk_step
    -- whether the two are one position, and the hit so far
    walk_step
    walk_step
    walk_step
    guard_hyp h10 :ₛ x10 = Nat.beq drawn got
    walk_step
    walk_step
    walk_step
    show 2 * i9 + 1 + 1 = 2 * (i9 + 1)
    omega
  case after =>
    subst invariant9
    walk_step
    -- the guard waits on whether the claim holds or a round hit
    walk_step
    · rfl
    · walk_step
      rfl

/-- Under the fees of any samplers the verifier is judged within any budget when nothing is asked
of how a run ends: every effect is met at no fee, which pays for no reply. -/
theorem judged_free (M : Model V) (path : List Frame) (claim : Bool)
    (allowed : ∀ op, (RSig M).Reply op → Prop) (samplers : Samplers (RSig M)) (budget : ℚ≥0) :
    (roleMeaning M installed Member.head verifier path (inputs M claim)).interpret
      (.charged allowed (paysBy samplers)) (fun _ _ => True) (fun _ _ => True) budget := by
  rw [verifier_meaning]
  walk_step
  walk_step
  walk_loop fun _ (_ : Bool) _ => True
  case first => trivial
  case step =>
    walk_step
    refine ⟨0, fun _ => False, zero_le, Or.inl ⟨rfl, fun _ excluded => excluded⟩,
      fun got _ _ => ?_⟩
    walk_step
    walk_step
    refine ⟨0, fun _ => False, zero_le, Or.inl ⟨rfl, fun _ excluded => excluded⟩,
      fun drawn _ _ => ?_⟩
    walk_step
    walk_step
    walk_step
    walk_step
    walk_step
    walk_step
    walk_step
    trivial
  case after =>
    walk_step
    walk_step
    · trivial
    · walk_step
      trivial

end

/-- info: 'Zkc.Tests.Formal.WalkLoop.six_effects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms six_effects

/--
info: 'Zkc.Tests.Formal.WalkLoop.judged_free' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms judged_free

end Zkc.Tests.Formal.WalkLoop
