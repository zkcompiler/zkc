module

public import Zkc.Core.Evidence.FunctionReadback
public import Zkc.Formal.Interactive.PairMembers

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.ScalarRows
open Core
variable {V : Vocabulary} (rows : ScalarRows V)

def EncodedBoundaryLaw (k : Key) (shifted : Bool) (run : FunctionMeaning (rows.scalarHeader k [rows.pair])) : Prop :=
  ∀ (M : Model V) [Lean.Grind.Field (rows.F M)], rows.Arithmetic M → ∀ a z : rows.F M,
    run M (.cons (a,z,()) .nil) = .done (.cons (encode shifted (a+z)) .nil)

def EncodedEvaluationLaw (k : Key) (shifted : Bool) (run : FunctionMeaning (rows.scalarHeader k [rows.pair,rows.scalarTy])) : Prop :=
  ∀ (M : Model V) [Lean.Grind.Field (rows.F M)], rows.Arithmetic M → ∀ a z r : rows.F M,
    run M (.cons (a,z,()) (.cons r .nil)) = .done (.cons (encode shifted (line (a,z) r)) .nil)

abbrev BoundaryLaw (k : Key) := rows.EncodedBoundaryLaw k false
abbrev EvaluationLaw (k : Key) := rows.EncodedEvaluationLaw k false

def boundaryReadback (k : Key) (shifted : Bool := false) : FunctionReadback _ (rows.EncodedBoundaryLaw k shifted) where
  inputs := Names.counting 0 _
  body fns := rows.boundaryBody fns k shifted
  armed _ := by cases shifted <;> rfl
  holds _ tables M _ math a z := rows.boundary_value M (tables M) k a z math shifted

def evaluationReadback (k : Key) : FunctionReadback _ (rows.EvaluationLaw k) where
  inputs := Names.counting 0 _
  body fns := rows.evaluateBody fns k
  armed _ := rfl
  holds _ tables M _ math a z r := rows.evaluate_value M (tables M) k a z r math

def encodedAffineReadback (commuted shifted : Bool) (k : Key) : FunctionReadback _ (rows.EncodedEvaluationLaw k shifted) where
  inputs := Names.counting 0 _
  body fns := rows.affineBody fns k commuted shifted
  armed _ := by cases shifted <;> rfl
  holds _ tables M _ math a z r := rows.affine_value M (tables M) k a z r math commuted shifted

abbrev affineReadback := rows.encodedAffineReadback false false

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
