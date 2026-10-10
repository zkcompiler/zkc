import Zkc.Source.Program

/-! Direct typed execution plans and their whole-execution interpreter.

This first plan uses logical values. Buffer allocation, codecs and native kernel
dispatch refine this representation later; they are not hidden in its evaluator.
This is a reference profile, not a required second IR in every compiler. The
source/plan distinction concerns the subjects of preservation (spec PROG-08).
-/

set_option autoImplicit false

namespace Zkc.Compiler

open Source

inductive Plan (language : Language) : List language.Ty → language.Ty → Type where
  | yield {Γ ty} (value : Var Γ ty) : Plan language Γ ty
  | stop {Γ ty} (reason : PIR.Stop) : Plan language Γ ty
  | execute {Γ ty} (op : language.Op) (arguments : Operands Γ (language.arguments op))
      (next : Plan language (language.result op :: Γ) ty) : Plan language Γ ty
  | select {Γ ty} (condition : Var Γ language.condition)
      (yes no : Plan language Γ ty) : Plan language Γ ty
  | loop {Γ ty acc} (count : Nat) (initial : Var Γ acc)
      (body : Plan language (acc :: Γ) acc)
      (next : Plan language (acc :: Γ) ty) : Plan language Γ ty

variable {S E A : Type}

/-- Iteration retains state and events from a stopped body and skips its suffix. -/
def executeLoop (body : A → S → PIR.Execution S E A) :
    Nat → A → S → PIR.Execution S E A
  | 0, value, state => ⟨.returned value, state, []⟩
  | count + 1, value, state =>
    (body value state).follow fun next => executeLoop body count next

variable {language : Language} {interface : PIR.Signature}

def Plan.run (meaning : Interpretation language interface) (handler : PIR.Handler interface S E)
    {Γ ty} (plan : Plan language Γ ty) (env : Environment meaning.Value Γ)
    (state : S) : PIR.Execution S E (meaning.Value ty) :=
  match plan with
  | .yield value => ⟨.returned (env value), state, []⟩
  | .stop reason => ⟨.stopped reason, state, []⟩
  | .execute op arguments next =>
    ((meaning.operation op (Operands.eval env arguments)).run handler state).follow fun value =>
      next.run meaning handler (env.push value)
  | .select condition yes no =>
    if meaning.condition (env condition) then yes.run meaning handler env state
    else no.run meaning handler env state
  | .loop count initial body next =>
    (executeLoop (fun value => body.run meaning handler (env.push value))
      count (env initial) state).follow fun value => next.run meaning handler (env.push value)

end Zkc.Compiler
