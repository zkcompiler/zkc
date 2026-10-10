import Zkc.Source.Expressions
import Mathlib.Logic.Function.Basic

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Zkc.Protocols.Sumcheck.LocalProver

/-- Only explicitly supplied input slots and four local registers are readable. -/
abbrev Expr := Zkc.Source.Expressions.Expr (Sum Nat (Fin 4))
inductive Event (F : Type) where
  | write : Fin 4 → F → Event F
  | coin : Nat → Nat → Event F
  | branch : Bool → Event F
  deriving DecidableEq
structure State (F : Type) where
  inputs : List F
  regs : Fin 4 → F
  history : List (Event F)

def initial {F : Type} [Zero F] (inputs : List F) : State F :=
  ⟨inputs, fun _ => 0, []⟩
def eval {F : Type} [Ring F] [DecidableEq F] (st : State F) (e : Expr) : F :=
  e.eval (fun | .inl i => st.inputs[i]?.getD 0 | .inr i => st.regs i)
def write {F : Type} (st : State F) (i : Fin 4) (v : F) : State F :=
  {st with regs := Function.update st.regs i v, history := st.history ++ [.write i v]}
def coin {F : Type} [NatCast F] (st : State F) (n : Nat) (i : Fin 4)
    (x : Fin (n+1)) : State F :=
  let st' := write st i (x.val : F)
  {st' with history := st'.history ++ [.coin (n+1) x.val]}
def branch {F : Type} (st : State F) (b : Bool) : State F :=
  {st with history := st.history ++ [.branch b]}

/-- Finite first-order quadratic-message syntax: no host continuations or oracle reads.
    Commit is terminal: the three wire messages become immutable before the challenge. -/
inductive Code where
  | abort
  | assign : Fin 4 → Expr → Code → Code
  | random : Nat → Fin 4 → Code → Code
  | ifz : Expr → Code → Code → Code
  | commit : Expr → Expr → Expr → Expr → Code
  deriving DecidableEq
structure Boundary (F : Type) where
  state : State F
  claim : F
  message : F × F × F
inductive Cut (F : Type) where
  | stopped : State F → Cut F
  | committed : Boundary F → Cut F

/-- The retained input vector is available at either local exit. -/
def Cut.inputs {F : Type} : Cut F → List F
  | .stopped state => state.inputs
  | .committed message => message.state.inputs

def boundary {F : Type} [Ring F] [DecidableEq F] (st : State F)
    (s a b c : Expr) : Boundary F :=
  ⟨st, eval st s, eval st a, eval st b, eval st c⟩

/-- Explicit finite operational reachability, including every local coin result. -/
inductive Reaches {F : Type} [Ring F] [DecidableEq F] : Code → State F → Cut F → Prop where
  | abort (st) : Reaches .abort st (.stopped st)
  | assign (i e p st out) : Reaches p (write st i (eval st e)) out →
      Reaches (.assign i e p) st out
  | random (n i p st out) (x : Fin (n+1)) : Reaches p (coin st n i x) out →
      Reaches (.random n i p) st out
  | yes (e p q st out) : eval st e = 0 → Reaches p (branch st true) out →
      Reaches (.ifz e p q) st out
  | no (e p q st out) : eval st e ≠ 0 → Reaches q (branch st false) out →
      Reaches (.ifz e p q) st out
  | commit (s a b c st) : Reaches (.commit s a b c) st (.committed (boundary st s a b c))

/-- Every input occurrence, including guards and syntactically dead branches. -/
def exprInputs (e : Zkc.Protocols.Sumcheck.LocalProver.Expr) : List Nat :=
  e.deps.filterMap (fun | .inl i => some i | .inr _ => none)

def codeInputs : Zkc.Protocols.Sumcheck.LocalProver.Code → List Nat
  | .abort => []
  | .assign _ e p => exprInputs e ++ codeInputs p
  | .random _ _ p => codeInputs p
  | .ifz e p q => exprInputs e ++ codeInputs p ++ codeInputs q
  | .commit s a b c => exprInputs s ++ exprInputs a ++ exprInputs b ++ exprInputs c


end Zkc.Protocols.Sumcheck.LocalProver
