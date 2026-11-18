module

/-! Accepted generated code, loaded back from `.olean.private` by the audit. One-constructor
and proposition types also exercise the cases where no native constructor index is needed. -/

@[expose] public section
namespace Zkc.Tools.Audit.Controls.Generated

inductive Tag where
  | left | right

private inductive PrivateTag where
  | left | right

inductive Indexed : Nat → Type where
  | zero : Indexed 0
  | next {n : Nat} : Indexed n → Indexed (n + 1)

mutual
inductive Even where
  | zero : Even
  | next : Odd → Even
inductive Odd where
  | one : Odd
  | next : Even → Odd
end

universe u

inductive Tree (α : Type u) where
  | leaf : α → Tree α
  | branch : Tree α → Tree α → Tree α

inductive EmptyType : Type where

inductive Nested (α : Type u) where
  | leaf : α → Nested α
  | node : List (Nested α) → Nested α

structure Single where
  number : Nat

inductive Proposition : Prop where
  | first | second

end Zkc.Tools.Audit.Controls.Generated
