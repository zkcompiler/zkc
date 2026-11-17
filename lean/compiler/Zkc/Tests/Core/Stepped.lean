import Zkc.Core.Evidence.Stepped
import Zkc.Tests.Core.Subjects

/-!
The term in steps, on the bodies of `Subjects.lean` and on the body of one test of `Facts.lean`
with a choice inside a loop (`N-TY9e`), over the vocabulary with a field of `Facts.lean`.

The round trip: each body of `Subjects.lean` (the sum of two products and the same instructions
reading `c, d` then `a, b`, the caller with a block, the caller with the instructions in line, the
caller of the sum, the callee that returns the first product and the callee with a guard), as a
term in steps and back, is the body, and erases to what the body erases to; the body that
`N-TY9e` elaborates, as a term in steps and back, erases to what it erases to. A term has no
decision of equality (its operations are of any type), so that a body as a term in steps and
back is the body is checked by the kernel's evaluation of a body written as a term, and of an
elaborated body by its erased form, which the kernel compares whole.

A proof from the equations alone: for the sum of two products, in every model, against any
callees, and for all naturals, the process of the term in steps is the return of `a * b + c * d`.
It uses the equation of an exit, the rule of a step whose subject yields a function
(`Stepped.Term.step_yields`), the subject of an operation (`Stepped.Instr.subject_op`) and the
law of the operations that the core owns (`product_yields`, `addition_yields`); it unfolds no
meaning. Then the same body as its first two instructions, a prefix, filled with its last one: its
process is the prefix's process, then the last instruction on the environment that the prefix
ends in (`Prefix.denote_fill_run`).
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

/-- The body as a term in steps and back erases to what the body erases to. -/
def erasesAlike {fns : List (FnHeader field)} (hdr : FnHeader field) (inputs : Names hdr.ins)
    (body : Fn field fns hdr inputs) : Bool :=
  decide (eraseFn inputs body.toStepped.toTerm = eraseFn inputs body)

example : sumBody.toStepped.toTerm = sumBody := rfl
example : sumBodyExchanged.toStepped.toTerm = sumBodyExchanged := rfl
example : blockCaller.toStepped.toTerm = blockCaller := rfl
example : inlineCaller.toStepped.toTerm = inlineCaller := rfl
example : callingCaller.toStepped.toTerm = callingCaller := rfl
example : firstBody.toStepped.toTerm = firstBody := rfl
example : guardedBody.toStepped.toTerm = guardedBody := rfl

example : erasesAlike sumHeader (Names.counting 0 _) sumBody = true := by decide +kernel
example : erasesAlike callerHeader (Names.counting 0 _) sumBodyExchanged = true := by
  decide +kernel
example : erasesAlike callerHeader (Names.counting 0 _) blockCaller = true := by decide +kernel
example : erasesAlike callerHeader (Names.counting 0 _) inlineCaller = true := by decide +kernel
example : erasesAlike (fns := [sumHeader]) callerHeader (Names.counting 0 _) callingCaller = true :=
  by decide +kernel
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

/-- The function elaborates, and its body, as a term in steps and back, erases to what the body
erases to. -/
def roundTripErases (hdr : FnHeader field) (region : Region (LocalRaw field) Unit) : Bool :=
  match typeFn [] hdr region with
  | .ok f => erasesAlike hdr f.inputs f.body
  | .error _ => false

example : roundTripErases tracedHeader tracedRegion = true := by decide +kernel

/-! ## A proof from the equations alone -/

/-- The sum of two products, as a term in steps. -/
def sumStepped : Stepped.Term (localDialect field []) (Ctx.positional four) [.nat] :=
  .step ⟨1⟩ (.op (.owned .natMul) (.cons (var 0) (.cons (var 1) .nil))) (.cons 4 .nil) <|
  .step ⟨2⟩ (.op (.owned .natMul) (.cons (var 2) (.cons (var 3) .nil))) (.cons 5 .nil) <|
  .step ⟨3⟩ (.op (.owned .natAdd) (.cons (var 4) (.cons (var 5) .nil))) (.cons 6 .nil) <|
  .ret (.cons (var 6) .nil)

/-- The body of `Subjects.lean`, in steps, is the term in steps written here. -/
theorem sumBody_toStepped : sumBody.toStepped = sumStepped := rfl

/-- The subject of a product of naturals in steps yields the product of its operands' values,
from every start. -/
theorem stepped_product_yields (M : Model field) (table : FnTable M []) {Γ : Ctx field.Ty}
    (key : Key) (x y : Var Γ .nat) :
    (Stepped.Instr.subject (localSem M [] table) key
      (.op (LocalOp.owned .natMul) (.cons x (.cons y .nil)))).Yields (localSem M [] table)
      (fun _ _ => True) (fun env => .cons (env.get x * env.get y) .nil) := by
  rw [Stepped.Instr.subject_op]
  exact product_yields M table key x y

/-- The subject of a sum of naturals in steps yields the sum of its operands' values, from every
start. -/
theorem stepped_addition_yields (M : Model field) (table : FnTable M []) {Γ : Ctx field.Ty}
    (key : Key) (x y : Var Γ .nat) :
    (Stepped.Instr.subject (localSem M [] table) key
      (.op (LocalOp.owned .natAdd) (.cons x (.cons y .nil)))).Yields (localSem M [] table)
      (fun _ _ => True) (fun env => .cons (env.get x + env.get y) .nil) := by
  rw [Stepped.Instr.subject_op]
  exact addition_yields M table key x y

/-- **The sum of two products, from the equations alone**: in every model, against any callees,
on any path and for all naturals, the process of the body in steps is the return of
`a * b + c * d`. Each step is the rest on what its operation yields, and the exit gives its value;
what remains is the value of a name in an environment. -/
theorem sumStepped_denote (M : Model field) (table : FnTable M []) (path : List Frame)
    (a b c d : Nat) :
    sumBody.toStepped.denote (localSem M [] table) path
        (Env.positional (.cons a (.cons b (.cons c (.cons d .nil))))) =
      .done (.cons (a * b + c * d) .nil) := by
  rw [sumBody_toStepped, sumStepped,
    Stepped.Term.step_yields _ (stepped_product_yields M table ⟨1⟩ _ _) _ _ path _ trivial,
    Stepped.Term.step_yields _ (stepped_product_yields M table ⟨2⟩ _ _) _ _ path _ trivial,
    Stepped.Term.step_yields _ (stepped_addition_yields M table ⟨3⟩ _ _) _ _ path _ trivial,
    Stepped.Term.denote_ret]
  rfl

/-! ## A prefix -/

/-- The first two instructions of the sum of two products: the two products, a prefix. -/
def productsFirst : Prefix (localDialect field []) (Ctx.positional four) afterProducts :=
  .step ⟨1⟩ (.op (.owned .natMul) (.cons (var 0) (.cons (var 1) .nil))) (.cons 4 .nil) <|
  .step ⟨2⟩ (.op (.owned .natMul) (.cons (var 2) (.cons (var 3) .nil))) (.cons 5 .nil) .nil

/-- What follows them: the sum, then the return. -/
def sumAfter : Stepped.Term (localDialect field []) afterProducts [.nat] :=
  .step ⟨3⟩ (.op (.owned .natAdd) (.cons (var 4) (.cons (var 5) .nil))) (.cons 6 .nil) <|
  .ret (.cons (var 6) .nil)

/-- The body in steps is the prefix filled with what follows it, and its split after two
instructions is the two. -/
example : productsFirst.fill sumAfter = sumBody.toStepped := rfl
example : sumBody.toStepped.splitAt 2 = ⟨afterProducts, productsFirst, sumAfter⟩ := rfl

/-- **The body's process is the process of its first two instructions, then the rest** on the
environment that they end in. -/
theorem sumBody_prefix (M : Model field) (table : FnTable M []) (path : List Frame)
    (env : Env M.Val (Ctx.positional four)) :
    sumBody.toStepped.denote (localSem M [] table) path env =
      (productsFirst.run (localSem M [] table) path env).bind fun env' =>
        sumAfter.denote (localSem M [] table) path env' :=
  Prefix.denote_fill_run (localSem M [] table) productsFirst sumAfter path env

end Zkc.Core.SteppedTests
