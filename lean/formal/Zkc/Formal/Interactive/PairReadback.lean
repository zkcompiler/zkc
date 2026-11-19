module

public import Zkc.Core.Evidence.FunctionReadback
public import Zkc.Formal.Interactive.PairMembers

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.ScalarRows
open Core
variable {V : Vocabulary} (rows : ScalarRows V)

def BoundaryLaw (k : Key) (run : FunctionMeaning (rows.scalarHeader k [rows.pair])) : Prop :=
  ∀ (M : Model V) [Lean.Grind.Field (rows.F M)], rows.Arithmetic M → ∀ a z : rows.F M,
    run M (.cons (a,z,()) .nil) = .done (.cons (a+z) .nil)

def EvaluationLaw (k : Key) (run : FunctionMeaning (rows.scalarHeader k [rows.pair,rows.scalarTy])) : Prop :=
  ∀ (M : Model V) [Lean.Grind.Field (rows.F M)], rows.Arithmetic M → ∀ a z r : rows.F M,
    run M (.cons (a,z,()) (.cons r .nil)) = .done (.cons (line (a,z) r) .nil)

def boundaryReadback (k : Key) : FunctionReadback _ (rows.BoundaryLaw k) where
  inputs := Names.counting 0 _
  body fns := rows.boundaryBody fns k
  armed _ := rfl
  holds _ tables M _ math a z := rows.boundary_value M (tables M) k a z math

def evaluationReadback (k : Key) : FunctionReadback _ (rows.EvaluationLaw k) where
  inputs := Names.counting 0 _
  body fns := rows.evaluateBody fns k
  armed _ := rfl
  holds _ tables M _ math a z r := rows.evaluate_value M (tables M) k a z r math

def affineReadback (k : Key) : FunctionReadback _ (rows.EvaluationLaw k) where
  inputs := Names.counting 0 _
  body fns := rows.affineBody fns k
  armed _ := rfl
  holds _ tables M _ math a z r := rows.affine_value M (tables M) k a z r math

/-- Both certified references belong to this program. The evaluation formula is a
property of its table entry and can be used by a caller independently of its expression. -/
structure Members (p : Typed V) (b e : Key) where
  boundary : Member p.headers.fns (rows.scalarHeader b [rows.pair])
  evaluate : Member p.headers.fns (rows.scalarHeader e [rows.pair, rows.scalarTy])
  boundaryLaw : rows.BoundaryLaw b (fun M => fnMeaning M p boundary)
  evaluateLaw : rows.EvaluationLaw e (fun M => fnMeaning M p evaluate)

def locateMembers (p : Typed V) (b e : Key)
    (implementation : FunctionReadback _ (rows.EvaluationLaw e)) : Option (rows.Members p b e) := do
  let unique := (List.nodup_append.mp p.distinct).1
  let ⟨boundary, boundaryLaw⟩ ← (rows.boundaryReadback b).locate p.defs unique
  let ⟨evaluate, evaluateLaw⟩ ← implementation.locate p.defs unique
  return ⟨boundary, evaluate, boundaryLaw, evaluateLaw⟩

end Zkc.Formal.Interactive.Sumcheck.ScalarRows
