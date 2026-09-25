import Std

set_option autoImplicit false

namespace Zkc.Compiler.Readback
inductive Term (L Op : Type) where
  | input (i : Nat)
  | literal (v : L)
  | apply (op : Op) (left right : Term L Op)
  | choose (condition yes no : Term L Op)
  deriving DecidableEq, Repr


variable {L NativeOp : Type}

def readTerm (resolve : NativeOp → Option String) : Term L NativeOp → Option (Term L String)
  | .input i => some (.input i)
  | .literal v => some (.literal v)
  | .apply op a b => do pure (.apply (← resolve op) (← readTerm resolve a) (← readTerm resolve b))
  | .choose c a b => do pure (.choose (← readTerm resolve c) (← readTerm resolve a) (← readTerm resolve b))

abbrev Block (L Op : Type) := List (Nat × Term L Op)

def readBlock (resolve : NativeOp → Option String) : Block L NativeOp → Option (Block L String)
  | [] => some []
  | (i,e)::rest => do pure ((i,← readTerm resolve e)::(← readBlock resolve rest))

end Zkc.Compiler.Readback
