module

public import Zkc.Core.Program.Annotations
public import Zkc.Core.Program.LocalRaw
public import Zkc.Core.Program.Requirement

@[expose] public section

namespace Zkc.Core

open BodyAnalysis (Expr Exprs ContractClause Contract)

/-- A producer can write a Boolean expression directly. A positional clause from the earlier
format retains its original syntax for diagnostics and is decoded under its argument types. -/
inductive HeaderClause (V : Vocabulary) where
  | positional (requirement : Requirement Empty)
  | assertion (clause : ContractClause (LocalRaw V))
  deriving DecidableEq

/-- Inputs precede returned values in the contexts of guarantees. -/
structure HeaderSummary (V : Vocabulary) where
  requires : List (HeaderClause V)
  ensures : List (HeaderClause V)
  deriving DecidableEq

variable {V : Vocabulary}

instance : Summary.EmptyOf (HeaderSummary V) Empty := ⟨⟨[], []⟩⟩

def HeaderSummary.ofPositional (s : Summary Empty) : HeaderSummary V :=
  ⟨s.requires.map .positional, s.ensures.map .positional⟩

instance : Coe (Summary Empty) (HeaderSummary V) := ⟨HeaderSummary.ofPositional⟩
instance : Coe (List (Requirement Empty)) (List (HeaderClause V)) := ⟨List.map .positional⟩
instance : Coe (Requirement Empty) (HeaderClause V) := ⟨.positional⟩

def HeaderSummary.ofContract (s : Contract (LocalRaw V)) : HeaderSummary V :=
  ⟨s.preconditions.map .assertion, s.postconditions.map .assertion⟩

namespace HeaderClause

abbrev le (x y : Operand Empty) : HeaderClause V := .positional (.le x y)
abbrev lt (x y : Operand Empty) : HeaderClause V := .positional (.lt x y)
abbrev atLeast (x : Operand Empty) (n : Nat) : HeaderClause V := .positional (.atLeast x n)
abbrev below (x : Operand Empty) (n : Nat) : HeaderClause V := .positional (.below x n)
abbrev exactly (x : Operand Empty) (n : Nat) : HeaderClause V := .positional (.exactly x n)
abbrev difference (x y : Operand Empty) (n : Nat) : HeaderClause V := .positional (.difference x y n)
abbrev holds (x : Operand Empty) : HeaderClause V := .positional (.holds x)
abbrev bounded (x : Operand Empty) : HeaderClause V := .positional (.bounded x)

end HeaderClause

mutual
  def BodyAnalysis.Expr.inRange {Raw : Type} (size : Nat) : Expr Raw → Bool
    | .arg i => decide (i < size)
    | .apply _ operands _ => BodyAnalysis.Exprs.inRange size operands
  def BodyAnalysis.Exprs.inRange {Raw : Type} (size : Nat) : Exprs Raw → Bool
    | .nil => true
    | .cons e es => BodyAnalysis.Expr.inRange size e && BodyAnalysis.Exprs.inRange size es
end

def HeaderClause.within (size : Nat) : HeaderClause V → Bool
  | .positional q => q.within size
  | .assertion c => c.assertion.inRange size && c.staticBound.all (·.inRange size)

def HeaderSummary.misplaced (ins outs : Nat) (s : HeaderSummary V) : Option (HeaderClause V) :=
  (s.requires.find? (fun q => !q.within ins)).orElse fun _ =>
    s.ensures.find? (fun q => !q.within (ins + outs))

def HeaderSummary.InRange (ins outs : Nat) (s : HeaderSummary V) : Prop :=
  s.misplaced ins outs = none

end Zkc.Core
