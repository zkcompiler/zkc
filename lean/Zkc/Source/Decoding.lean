import Zkc.Source.Program

/-! Untyped finite source data, typed elaboration and exact erasure laws.

Every branch and declared operand is elaborated before runtime values are
supplied. Missing or mistyped operands are errors, including in dormant code.
-/

set_option autoImplicit false

namespace Zkc.Source

inductive RawProgram (Ty Op : Type) where
  | ret (index : Nat)
  | stop (reason : PIR.Stop)
  | letOp (op : Op) (arguments : List Nat) (next : RawProgram Ty Op)
  | branch (condition : Nat) (yes no : RawProgram Ty Op)
  | iterate (count : Nat) (accumulator : Ty) (initial : Nat)
      (body next : RawProgram Ty Op)
  deriving DecidableEq, Repr

inductive FormationError (Ty : Type) where
  | invalidOperand (index : Nat) (expected : Ty)
  | operandCount (expected actual : Nat)
  deriving DecidableEq, Repr

variable {Ty : Type} [DecidableEq Ty]

def decodeVariable (Γ : List Ty) (ty : Ty) (index : Nat) :
    Except (FormationError Ty) (Var Γ ty) :=
  match Var.decode Γ ty index with
  | some value => .ok value
  | none => .error (.invalidOperand index ty)

def Operands.indices {Γ args : List Ty} : Operands Γ args → List Nat
  | .nil => []
  | .cons v tail => v.index :: Operands.indices tail

def decodeOperands (Γ : List Ty) : (args : List Ty) → List Nat →
    Except (FormationError Ty) (Operands Γ args)
  | [], [] => .ok .nil
  | ty :: args, index :: indices => do
    let value ← decodeVariable Γ ty index
    let tail ← decodeOperands Γ args indices
    pure (.cons value tail)
  | args, indices => .error (.operandCount args.length indices.length)

@[simp] theorem decodeVariable_index {Γ : List Ty} {ty : Ty} (v : Var Γ ty) :
    decodeVariable Γ ty v.index = .ok v := by
  simp [decodeVariable]

@[simp] theorem decodeOperands_indices {Γ args : List Ty} (operands : Operands Γ args) :
    decodeOperands Γ args (Operands.indices operands) = .ok operands := by
  induction operands with
  | nil => rfl
  | cons v tail ih => simp [Operands.indices, decodeOperands, ih]; rfl

variable {language : Language} [DecidableEq language.Ty]

def RawProgram.elaborate (Γ : List language.Ty) (ty : language.Ty) :
    RawProgram language.Ty language.Op →
      Except (FormationError language.Ty) (Program language Γ ty)
  | .ret index => return .ret (← decodeVariable Γ ty index)
  | .stop reason => .ok (.stop reason)
  | .letOp op indices next => do
    let arguments ← decodeOperands Γ (language.arguments op) indices
    let next ← next.elaborate (language.result op :: Γ) ty
    pure (.letOp op arguments next)
  | .branch index yes no => do
    let condition ← decodeVariable Γ language.condition index
    let yes ← yes.elaborate Γ ty
    let no ← no.elaborate Γ ty
    pure (.branch condition yes no)
  | .iterate count acc index body next => do
    let initial ← decodeVariable Γ acc index
    let body ← body.elaborate (acc :: Γ) acc
    let next ← next.elaborate (acc :: Γ) ty
    pure (.iterate count initial body next)

def Program.erase {Γ ty} : Program language Γ ty → RawProgram language.Ty language.Op
  | .ret value => .ret value.index
  | .stop reason => .stop reason
  | .letOp op arguments next => .letOp op (Operands.indices arguments) next.erase
  | .branch condition yes no => .branch condition.index yes.erase no.erase
  | .iterate (acc := acc) count initial body next =>
    .iterate count acc initial.index body.erase next.erase

@[simp] theorem Program.elaborate_erase {Γ ty} (program : Program language Γ ty) :
    program.erase.elaborate Γ ty = .ok program := by
  induction program with
  | ret value => simp [erase, RawProgram.elaborate]; rfl
  | stop reason => rfl
  | letOp op arguments next ih => simp [erase, RawProgram.elaborate, ih]; rfl
  | branch condition yes no yesIH noIH => simp [erase, RawProgram.elaborate, yesIH, noIH]; rfl
  | iterate count initial body next bodyIH nextIH =>
    simp [erase, RawProgram.elaborate, bodyIH, nextIH]; rfl

end Zkc.Source
