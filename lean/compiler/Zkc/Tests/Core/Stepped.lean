import Zkc.Core.Evidence.Stepped
import Zkc.Core.Facts.SteppedLoops
import Zkc.Tests.Core.Subjects

/-!
The term in steps, on the bodies of `Subjects.lean` and on the body of one test of `Facts.lean`
with a choice inside a loop (`N-TY9e`), over the vocabulary with a field of `Facts.lean`.

The concrete bodies are split and reassembled, then compared by erasure. For the
elaborated loop with a nested choice, erasure is also compared to its written source.

A proof from the equations alone: for the sum of two products, in every model, against any
callees, and for all naturals, the process of the term in steps is the return of `a * b + c * d`.
It uses the equation of an exit, the rule of a step whose subject yields a function
(`Term.step_yields`), the subject of an operation (`Instr.subject_op`) and the
law of the operations that the core owns (`product_yields`, `addition_yields`); it unfolds no
meaning. Then the same body as its first two instructions, a prefix, filled with its last one: its
process is the prefix's process, then the last instruction on the environment that the prefix
ends in (`Prefix.denote_fill_run`).

The loops that a run reaches: a loop in steps, as often as two, whose body adds the second input
to the carried value. In every model, against any callees, every loop that a run of it reaches
runs at most twice, by the rule of a step (`Term.everyLoop_step`) at the loop and in its
body. The negative control refutes a bound of one.
-/

namespace Zkc.Core.SteppedTests

open Zkc.Core.Shapes
open Zkc.Core.SubjectsTests
open FactsTests (field verdict bytes natural equal item toNat plus «N-TY9e»)

set_option maxRecDepth 4000

/-! ## The round trip -/

/-- A function of the four naturals, with the key 20, that cannot stop. -/
def callerHeader : FnHeader field := ⟨⟨20⟩, four, [.nat], false, none, Summary.empty⟩

/-- A function of the four naturals, with the key 21, that can stop. -/
def stoppingHeader : FnHeader field := ⟨⟨21⟩, four, [.nat], true, none, Summary.empty⟩

/-- Erasure preserves the instruction sequence and lexical names across a prefix split. -/
def erasesAlike {fns : List (FnHeader field)} (hdr : FnHeader field) (inputs : Names hdr.ins)
    (body : Fn field fns hdr inputs) : Bool :=
  let cut := body.splitPrefix 2
  decide (eraseFn inputs (cut.2.1.fill cut.2.2) = eraseFn inputs body)

private def splitFills {D : Dialect} {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) : Prop :=
  let cut := t.splitPrefix 2
  cut.2.1.fill cut.2.2 = t

example : splitFills sumBody := rfl
example : splitFills sumBodyExchanged := rfl
example : splitFills blockCaller := rfl
example : splitFills blockExchanged := rfl
example : splitFills inlineCaller := rfl
example : splitFills inlineExchanged := rfl
example : splitFills callingCaller := rfl
example : splitFills callingExchanged := rfl
example : splitFills firstBody := rfl
example : splitFills guardedBody := rfl

example : erasesAlike sumHeader (Names.counting 0 _) sumBody = true := by decide +kernel
example : erasesAlike callerHeader (Names.counting 0 _) sumBodyExchanged = true := by
  decide +kernel
example : erasesAlike callerHeader (Names.counting 0 _) blockCaller = true := by decide +kernel
example : erasesAlike callerHeader (Names.counting 0 _) blockExchanged = true := by
  decide +kernel
example : erasesAlike callerHeader (Names.counting 0 _) inlineCaller = true := by decide +kernel
example : erasesAlike callerHeader (Names.counting 0 _) inlineExchanged = true := by
  decide +kernel
example : erasesAlike (fns := [sumHeader]) callerHeader (Names.counting 0 _) callingCaller = true :=
  by decide +kernel
example : erasesAlike (fns := [sumHeader]) callerHeader (Names.counting 0 _) callingExchanged =
    true := by
  decide +kernel
example : erasesAlike firstHeader (Names.counting 0 _) firstBody = true := by decide +kernel
example : erasesAlike stoppingHeader (Names.counting 0 _) guardedBody = true := by decide +kernel

/-- The function of `N-TY9e`, with the key 1: a sequence of four bytes, one natural, it cannot
stop. -/
def tracedHeader : FnHeader field := ⟨⟨1⟩, [bytes 4], [.nat], false, none, Summary.empty⟩

/-- The body of `N-TY9e`: a loop of one iteration whose body has a choice on the index. -/
def tracedRegion : Region (LocalRaw field) Unit := .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .loop ⟨2⟩ () (.fixed 1) [10] [11]
    (.mk [20, 21] [
      .op ⟨3⟩ [22] (natural 1) [],
      .op ⟨4⟩ [23] equal [20, 22],
      .choose ⟨5⟩ () 23 [24]
        (.mk [] [
          .op ⟨6⟩ [30] (natural 5) [],
          .op ⟨7⟩ [31] (item (bytes 4)) [0, 30],
          .op ⟨8⟩ [32] (toNat 256) [31],
          .op ⟨9⟩ [33] plus [21, 32]] [33])
        (.mk [] [] [21])] [24])] [11]

/-- It is the function of the test of `Facts.lean`. -/
example : «N-TY9e» = verdict [] tracedHeader tracedRegion := rfl

/-- The function elaborates, and its body erases to the original written region. -/
def roundTripErases (hdr : FnHeader field) (region : Region (LocalRaw field) Unit) : Bool :=
  match typeFn [] hdr region with
  | .ok f => decide (eraseFn f.inputs f.body = region)
  | .error _ => false

example : roundTripErases tracedHeader tracedRegion = true := by decide +kernel

/-! ## A proof from the equations alone -/

/-- The sum of two products, as a term in steps. -/
def sumStepped : Term (localDialect field []) (Ctx.positional four) [.nat] :=
  .step ⟨1⟩ (.op (.owned .natMul) (.cons (var 0) (.cons (var 1) .nil))) (.cons 4 .nil) <|
  .step ⟨2⟩ (.op (.owned .natMul) (.cons (var 2) (.cons (var 3) .nil))) (.cons 5 .nil) <|
  .step ⟨3⟩ (.op (.owned .natAdd) (.cons (var 4) (.cons (var 5) .nil))) (.cons 6 .nil) <|
  .ret (.cons (var 6) .nil)

/-- The body of `Subjects.lean`, in steps, is the term in steps written here. -/
theorem sumBody_steps : sumBody = sumStepped := rfl

/-- The subject of a product of naturals in steps yields the product of its operands' values,
from every start. -/
theorem stepped_product_yields (M : Model field) (table : FnTable M []) {Γ : Ctx field.Ty}
    (key : Key) (x y : Var Γ .nat) :
    (Instr.subject (localSem M [] table) key
      (.op (LocalOp.owned .natMul) (.cons x (.cons y .nil)))).Yields (localSem M [] table)
      (fun _ _ => True) (fun env => .cons (env.get x * env.get y) .nil) := by
  rw [Instr.subject_op]
  exact product_yields M table key x y

/-- The subject of a sum of naturals in steps yields the sum of its operands' values, from every
start. -/
theorem stepped_addition_yields (M : Model field) (table : FnTable M []) {Γ : Ctx field.Ty}
    (key : Key) (x y : Var Γ .nat) :
    (Instr.subject (localSem M [] table) key
      (.op (LocalOp.owned .natAdd) (.cons x (.cons y .nil)))).Yields (localSem M [] table)
      (fun _ _ => True) (fun env => .cons (env.get x + env.get y) .nil) := by
  rw [Instr.subject_op]
  exact addition_yields M table key x y

/-- **The sum of two products, from the equations alone**: in every model, against any callees,
on any path and for all naturals, the process of the body in steps is the return of
`a * b + c * d`. Each step is the rest on what its operation yields, and the exit gives its value;
what remains is the value of a name in an environment. -/
theorem sumStepped_denote (M : Model field) (table : FnTable M []) (path : List Frame)
    (a b c d : Nat) :
    sumBody.denote (localSem M [] table) path
        (Env.positional (.cons a (.cons b (.cons c (.cons d .nil))))) =
      .done (.cons (a * b + c * d) .nil) := by
  rw [sumBody_steps, sumStepped,
    Term.step_yields _ (stepped_product_yields M table ⟨1⟩ _ _) _ _ path _ trivial,
    Term.step_yields _ (stepped_product_yields M table ⟨2⟩ _ _) _ _ path _ trivial,
    Term.step_yields _ (stepped_addition_yields M table ⟨3⟩ _ _) _ _ path _ trivial,
    Term.denote_ret]
  rfl

/-! ## A prefix -/

/-- The first two instructions of the sum of two products: the two products, a prefix. -/
def productsFirst : Prefix (localDialect field []) (Ctx.positional four) afterProducts :=
  .step ⟨1⟩ (.op (.owned .natMul) (.cons (var 0) (.cons (var 1) .nil))) (.cons 4 .nil) <|
  .step ⟨2⟩ (.op (.owned .natMul) (.cons (var 2) (.cons (var 3) .nil))) (.cons 5 .nil) .nil

/-- What follows them: the sum, then the return. -/
def sumAfter : Term (localDialect field []) afterProducts [.nat] :=
  .step ⟨3⟩ (.op (.owned .natAdd) (.cons (var 4) (.cons (var 5) .nil))) (.cons 6 .nil) <|
  .ret (.cons (var 6) .nil)

/-- The body in steps is the prefix filled with what follows it, and its split after two
instructions is the two. -/
example : productsFirst.fill sumAfter = sumBody := rfl
example : sumBody.splitPrefix 2 = ⟨afterProducts, productsFirst, sumAfter⟩ := rfl

/-- **The body's process is the process of its first two instructions, then the rest** on the
environment that they end in. -/
theorem sumBody_prefix (M : Model field) (table : FnTable M []) (path : List Frame)
    (env : Env M.Val (Ctx.positional four)) :
    sumBody.denote (localSem M [] table) path env =
      (productsFirst.run (localSem M [] table) path env).bind fun env' =>
        sumAfter.denote (localSem M [] table) path env' :=
  Prefix.denote_fill_run (localSem M [] table) productsFirst sumAfter path env

/-- Reading the two products at the prefix exit uses the original invocation path. -/
example (M : Model field) (table : FnTable M []) (path : List Frame)
    (a b c d : Nat) :
    productsFirst.subject (localSem M [] table)
        (.cons (var 4) (.cons (var 5) .nil) : HList (Var afterProducts) [.nat, .nat]) path
        (Env.positional (.cons a (.cons b (.cons c (.cons d .nil))))) =
      .done (.cons (a * b) (.cons (c * d) .nil)) := rfl

/-! ## The loops that a run reaches -/

/-- The names in scope in the body of the loop: the inputs, the iteration number (the name 10)
and the carried value (11). -/
abbrev inLoop : Ctx field.Ty :=
  (Ctx.positional four).extend (.cons 10 (.cons 11 .nil) : Names [(.nat : field.Ty), .nat])

/-- The body of the loop: `c' := c + b`, the carried value plus the second input. -/
def loopBody : Term (localDialect field []) inLoop [.nat] :=
  .step ⟨2⟩ (.op (.owned .natAdd) (.cons (var 11) (.cons (var 1) .nil))) (.cons 12 .nil) <|
  .ret (.cons (var 12) .nil)

/-- A loop in steps, as often as two, whose carried value starts at the first input and adds the
second at each iteration; what the loop gives is returned. -/
def loopStepped : Term (localDialect field []) (Ctx.positional four) [.nat] :=
  .step ⟨1⟩ (.loop (carried := [(.nat : field.Ty)]) (each := []) () (.fixed 2) (fun _ _ => trivial)
      (.cons (var 0) .nil) (.cons 10 (.cons 11 .nil)) loopBody) (.cons 4 .nil) <|
  .ret (.cons (var 4) .nil)

/-- **Every loop that a run of the loop in steps reaches runs at most twice**, in every model,
against any callees, on any path and from any start: by the rule of a step
(`Term.everyLoop_step`), at the loop by its written count, and in its body, a step whose
operation reaches no loop, by the rule of a step again. -/
theorem loopStepped_bounded (M : Model field) (table : FnTable M []) (path : List Frame)
    (env : Env M.Val (Ctx.positional four)) :
    loopStepped.EveryLoop (localSem M [] table) (fun _ _ => True) (fun _ _ count => count ≤ 2)
      path [] env := by
  rw [loopStepped, Term.everyLoop_step]
  dsimp only [Instr.EveryLoop]
  refine ⟨⟨Nat.le_refl 2, fun i _ => every_of_all _ (fun state => ?_) _⟩,
    every_of_all _ (fun _ => trivial) _⟩
  rw [loopBody, Term.everyLoop_step]
  exact ⟨trivial, every_of_all _ (fun _ => trivial) _⟩

/-- The control: the loop that it reaches does not run at most once. -/
example (M : Model field) (table : FnTable M []) (path : List Frame)
    (env : Env M.Val (Ctx.positional four)) :
    ¬ loopStepped.EveryLoop (localSem M [] table) (fun _ _ => True) (fun _ _ count => count ≤ 1)
      path [] env := by
  rw [loopStepped, Term.everyLoop_step]
  dsimp only [Instr.EveryLoop]
  exact fun bounded => (by decide : ¬ 2 ≤ 1) bounded.1.1

end Zkc.Core.SteppedTests
