module

public import Zkc.Construction.Participant

@[expose] public section

/-! Why the executable lowering rule refuses a validator. -/

set_option autoImplicit false

namespace Zkc.Executable

/-- Why the rule refuses. -/
inductive Refusal where
  | unsupported (name : String)
  | binding (symbol : String)
  | operand (name : String)
  | operation (site : String)
  | representation
  | frames
  | entry
  | duplicate (kind : String)
  | different (part : String)
  | helper (symbol : String)
  | loop (site : String)
  /-- Normalization: the anchors at this ordinal of a scope differ. -/
  | anchor (index : Nat)
  /-- Normalization: an operand of the anchor at this ordinal denotes another
  term. -/
  | anchorOperand (index operand : Nat)
  /-- Normalization: a pure calculation before the anchor at this ordinal is
  ill-sorted. -/
  | sort (index : Nat)
  /-- Normalization: the loop at this ordinal yields other terms or sorts. -/
  | yielded (index : Nat)
  /-- Normalization: a returned reference denotes another term. -/
  | returned (position : Nat)
  deriving DecidableEq, Repr

end Zkc.Executable
