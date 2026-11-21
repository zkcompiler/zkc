module

public import Zkc.Formal.Interactive.PairReadback

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck

/-- The fragment of field expressions read at the two arguments of the external line. -/
inductive EndpointExpression
  | first | second
  | add (left right : EndpointExpression)
  deriving DecidableEq, Repr

def EndpointExpression.eval {F : Type} [Lean.Grind.Field F] (m : F × F) : EndpointExpression → F
  | .first => m.1
  | .second => m.2
  | .add a b => a.eval m + b.eval m

structure LineExpression where
  zero : EndpointExpression
  one : EndpointExpression
  deriving DecidableEq, Repr

def LineExpression.decode (line : LineExpression) : ScalarRows.PairEncoding :=
  fun _ _ m => (line.zero.eval m, line.one.eval m)

end Zkc.Formal.Interactive.Sumcheck
