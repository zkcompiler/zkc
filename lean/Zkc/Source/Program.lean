import Zkc.Source.Context
import Zkc.Semantics.Interaction

/-! A finite, intrinsically typed source language.

Operations supply signatures and meanings. Binding and structured control are
independent of protocol names, field choices and native storage representations.
An interpretation is trusted mathematical input here; external admission must
resolve operation references to the interpretation selected by the consumer.
-/

set_option autoImplicit false

namespace Zkc.Source

/-- The finite source's type and operation vocabulary. -/
structure Language where
  Ty : Type
  Op : Type
  arguments : Op → List Ty
  result : Op → Ty
  condition : Ty

/-- Control syntax has no host-language continuations. A portable vocabulary
uses type/operation descriptors, with values supplied by the environment.
Loop bodies receive an accumulator followed by the enclosing context. -/
inductive Program (language : Language) : List language.Ty → language.Ty → Type where
  | ret {Γ ty} (value : Var Γ ty) : Program language Γ ty
  | stop {Γ ty} (reason : PIR.Stop) : Program language Γ ty
  | letOp {Γ ty} (op : language.Op) (arguments : Operands Γ (language.arguments op))
      (next : Program language (language.result op :: Γ) ty) : Program language Γ ty
  | branch {Γ ty} (condition : Var Γ language.condition)
      (yes no : Program language Γ ty) : Program language Γ ty
  | iterate {Γ ty acc} (count : Nat) (initial : Var Γ acc)
      (body : Program language (acc :: Γ) acc)
      (next : Program language (acc :: Γ) ty) : Program language Γ ty

/-- Meaning is separate from formation, handlers, state and observation policy. -/
structure Interpretation (language : Language) (interface : PIR.Signature) where
  Value : language.Ty → Type
  condition : Value language.condition → Bool
  operation : (op : language.Op) → Values Value (language.arguments op) →
    PIR.Proc interface (Value (language.result op))

variable {language : Language} {interface : PIR.Signature}

def Program.denote (meaning : Interpretation language interface) {Γ ty}
    (program : Program language Γ ty) (env : Environment meaning.Value Γ) :
    PIR.Proc interface (meaning.Value ty) :=
  match program with
  | .ret v => .done (env v)
  | .stop reason => .halt reason
  | .letOp op arguments next =>
    (meaning.operation op (Operands.eval env arguments)).bind fun value =>
      next.denote meaning (env.push value)
  | .branch condition yes no =>
    if meaning.condition (env condition) then yes.denote meaning env else no.denote meaning env
  | .iterate count initial body next =>
    (PIR.repeatN count (fun value => body.denote meaning (env.push value)) (env initial)).bind
      fun value => next.denote meaning (env.push value)

/-- Capture maps are applied structurally, including both branches and loop regions. -/
def Program.rename {Γ Δ ty} (rename : Renaming Γ Δ) :
    Program language Γ ty → Program language Δ ty
  | .ret value => .ret (rename value)
  | .stop reason => .stop reason
  | .letOp op arguments next =>
    .letOp op (Operands.rename rename arguments) (next.rename (Renaming.lift rename))
  | .branch condition yes no => .branch (rename condition) (yes.rename rename) (no.rename rename)
  | .iterate count initial body next =>
    .iterate count (rename initial) (body.rename (Renaming.lift rename))
      (next.rename (Renaming.lift rename))

theorem Program.denote_rename (meaning : Interpretation language interface)
    {Γ Δ ty} (program : Program language Γ ty) (rename : Renaming Γ Δ)
    (env : Environment meaning.Value Δ) :
    (program.rename rename).denote meaning env =
      program.denote meaning (fun v => env (rename v)) := by
  induction program generalizing Δ with
  | ret value => rfl
  | stop reason => rfl
  | letOp op arguments next ih =>
    simp only [Program.rename, denote, Operands.eval_rename]
    congr 1
    funext value
    rw [ih, Environment.push_rename]
  | branch condition yes no yesIH noIH =>
    simp only [Program.rename, denote, yesIH, noIH]
  | iterate count initial body next bodyIH nextIH =>
    simp only [Program.rename, denote]
    have bodySame :
        (fun value => (body.rename (Renaming.lift rename)).denote meaning (env.push value)) =
        (fun value => body.denote meaning (Environment.push (fun v => env (rename v)) value)) := by
      funext value
      rw [bodyIH, Environment.push_rename]
    rw [bodySame]
    congr 1
    funext value
    rw [nextIH, Environment.push_rename]

end Zkc.Source
