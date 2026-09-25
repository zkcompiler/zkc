import Zkc.Source.Arithmetic
import Zkc.Compiler.Transformation

/-! Checked lowering of quadratic evaluation to a Horner computation.

The target explicitly computes two multiplications and two additions. It keeps
the actual caller, operands, structured control and effectful continuation.
Only semiring laws are used; a field or commutative multiplication is not needed.
-/

set_option autoImplicit false

namespace Zkc.Compiler.Arithmetic.Horner

open Source
open Source.Arithmetic

/-- Four target temporaries replace the one source result. Old input bindings
keep their order behind them; only the final temporary is returned to the caller. -/
def resultRenaming {Γ : List Ty} : Renaming (.scalar :: Γ)
    (.scalar :: .scalar :: .scalar :: .scalar :: Γ)
  | _, .here => .here
  | _, .there ref => .there (.there (.there (.there ref)))

def expand {Γ ty} (args : Operands Γ (arguments .quadratic))
    (next : Program language (.scalar :: Γ) ty) : Program language Γ ty :=
  match args with
  | .cons a (.cons b (.cons c (.cons r .nil))) =>
    .letOp .multiply (.cons c (.cons r .nil))
      (.letOp .add (.cons (.there b) (.cons .here .nil))
        (.letOp .multiply (.cons .here (.cons (.there (.there r)) .nil))
          (.letOp .add (.cons (.there (.there (.there a))) (.cons .here .nil))
            (next.rename resultRenaming))))

theorem denote_expand {F : Type} [Semiring F] {I : PIR.Signature}
    (invoke : F → PIR.Proc I F) {Γ ty}
    (args : Operands Γ (arguments .quadratic)) (next : Program language (.scalar :: Γ) ty)
    (env : Environment (Value F) Γ) :
    (expand args next).denote (interpretation invoke) env =
      (.letOp .quadratic args next : Program language Γ ty).denote (interpretation invoke) env := by
  cases args with
  | cons a args =>
    cases args with
    | cons b args =>
      cases args with
      | cons c args =>
        cases args with
        | cons r args =>
          cases args
          simp only [expand, Program.denote, Operands.eval, interpretation,
            Environment.push, PIR.Proc.bind, Program.denote_rename]
          congr 1
          funext ty ref
          cases ref with
          | here => simp [resultRenaming, Environment.push, add_mul, mul_assoc]
          | there ref => rfl

def rewrite {Γ ty} : Program language Γ ty → Program language Γ ty
  | .ret value => .ret value
  | .stop why => .stop why
  | .letOp .quadratic args next => expand args (rewrite next)
  | .letOp .add args next => .letOp .add args (rewrite next)
  | .letOp .multiply args next => .letOp .multiply args (rewrite next)
  | .letOp .invoke args next => .letOp .invoke args (rewrite next)
  | .branch condition yes no => .branch condition (rewrite yes) (rewrite no)
  | .iterate count initial body next => .iterate count initial (rewrite body) (rewrite next)

/-- The law holds for all inputs and effectful continuations, before choosing
a handler, initial state, observer or success assumption. -/
theorem denote_rewrite {F : Type} [Semiring F] {I : PIR.Signature}
    (invoke : F → PIR.Proc I F) {Γ ty} (source : Program language Γ ty)
    (env : Environment (Value F) Γ) :
    (rewrite source).denote (interpretation invoke) env =
      source.denote (interpretation invoke) env := by
  induction source with
  | ret value => rfl
  | stop why => rfl
  | letOp op args next ih =>
    cases op <;> simp only [rewrite]
    · rw [denote_expand]
      simp only [Program.denote]
      congr 1
      funext value
      exact ih (env.push value)
    all_goals
      simp only [Program.denote]
      congr 1
      funext value
      exact ih (env.push value)
  | branch condition yes no ihYes ihNo => simp [rewrite, Program.denote, ihYes, ihNo]
  | iterate count initial body next ihBody ihNext =>
    simp only [rewrite, Program.denote]
    have bodySame :
        (fun value => (rewrite body).denote (interpretation invoke) (env.push value)) =
        (fun value => body.denote (interpretation invoke) (env.push value)) := by
      funext value
      exact ihBody (env.push value)
    rw [bodySame]
    congr 1
    funext value
    exact ihNext (env.push value)

abbrev model {F : Type} [Semiring F] {I : PIR.Signature} {S E : Type}
    (invoke : F → PIR.Proc I F) (handler : PIR.Handler I S E) : ExecutionModel language where
  interface := I
  meaning := interpretation invoke
  State := S
  Event := E
  handler := handler

/-- This rule implements a fixed algorithm and needs no search certificate.
The candidate still has to match its actual output for the retained source. -/
def rule {F : Type} [Semiring F] {I : PIR.Signature} {S E : Type}
    (invoke : F → PIR.Proc I F) (handler : PIR.Handler I S E) (Γ : List Ty) (ty : Ty) :
    TransformationRule (Refinement.exact (model invoke handler) Γ ty) where
  Certificate := Unit
  apply source _ := some (lower (rewrite source))
  sound source _ plan accepted := by
    cases Option.some.inj accepted
    apply Refinement.exact_of_execution
    intro env state
    simp only [ExecutionModel.runSource, ExecutionModel.runPlan, model]
    rw [lower_correct, denote_rewrite]

end Zkc.Compiler.Arithmetic.Horner
