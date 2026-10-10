import Zkc.Modules.Preparation

set_option autoImplicit false

namespace Zkc.Source.TablePreparation
open Zkc.Modules.Preparation

/-- Register expressions over immutable captured integers. Missing registers have
    specified zero semantics, so all syntax is total; adapters use valid indices. -/
inductive Expr where
  | lit : Nat → Expr
  | reg : Nat → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | mod : Expr → Nat → Expr
  deriving DecidableEq, Repr

def Expr.eval (env : List Nat) : Expr → Nat × Nat
  | .lit n => (n,0)
  | .reg i => (env[i]?.getD 0,0)
  | .add a b => let x := a.eval env; let y := b.eval env; (x.1+y.1,x.2+y.2+1)
  | .mul a b => let x := a.eval env; let y := b.eval env; (x.1*y.1,x.2+y.2+1)
  | .mod a q => let x := a.eval env; (x.1 % q,x.2+1)

/-- Straight-line immutable table preparation: each instruction appends a cell.
    One interpreter evaluates both arithmetic residual tables and group tables. -/
def exec : List Expr → List Nat → List Nat × Nat
  | [],env => (env,0)
  | e :: rest,env => let x := e.eval env; let r := exec rest (env ++ [x.1]); (r.1,x.2+r.2)
structure Key where
  version : Nat
  origin : Nat
  captures : List Nat
  code : List Expr
  deriving DecidableEq, Repr

def provider : Provider Key (List Nat) := fun k => exec k.code k.captures
def prices : Prices Key (List Nat) := ⟨fun _ _ => 1,fun _ _ => 1⟩

end Zkc.Source.TablePreparation
