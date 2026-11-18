module

public import Zkc.Core.Program.Identity
public import Zkc.Core.Program.Vocabulary

@[expose] public section

/-! The written operations available in local expressions and function bodies. -/

namespace Zkc.Core

/-- An operation that the core owns, by name. -/
inductive OwnedName where
  | natAdd | natSub | natMul | natDiv | natRem | natPow | natEqual | natLess
  | boolAnd | boolOr | boolNot | boolEqual
  | seqLength | seqAt | seqSlice | seqConcat | seqFill
  | seqSized | natBelow
  | seqUnsized | finToNat | finWiden
  | make | get | take | variant
deriving DecidableEq, Repr

/-- The operations of a function. An owned operation carries its types and its numbers (a
position of `get` and of `variant`). -/
inductive LocalRaw (V : Vocabulary) where
  | row (key : V.RowKey)
  | owned (name : OwnedName) (at_ : List V.Ty) (numbers : List Nat)
  | literal (τ : V.Ty) (data : List Nat)
  | call (callee : Key)
deriving DecidableEq

end Zkc.Core
