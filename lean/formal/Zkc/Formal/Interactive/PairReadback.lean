module

public import Zkc.Core.Evidence.FunctionReadback
public import Zkc.Formal.Interactive.PairMembers

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.ScalarRows
open Core

-- This file passes between the meaning of a program and its tables by definitional unfolding.
unseal Zkc.Core.fnMeaning Zkc.Core.roleMeaning Zkc.Core.protocolMeaning

variable {V : Vocabulary} (rows : ScalarRows V)

abbrev PairEncoding := (F : Type) → [Lean.Grind.Field F] → F × F → F × F

def endpointEncoding : PairEncoding := fun _ _ m => m

def BoundaryLaw (k : Key) (run : FunctionMeaning (rows.scalarHeader k [rows.pair]))
    (decode : PairEncoding := endpointEncoding) : Prop :=
  ∀ (M : Model V) [Lean.Grind.Field (rows.F M)], rows.Arithmetic M → ∀ a z : rows.F M,
    run M (.cons (a,z,()) .nil) = .done (.cons ((decode _ (a,z)).1 + (decode _ (a,z)).2) .nil)

def EvaluationLaw (k : Key) (run : FunctionMeaning (rows.scalarHeader k [rows.pair,rows.scalarTy]))
    (decode : PairEncoding := endpointEncoding) : Prop :=
  ∀ (M : Model V) [Lean.Grind.Field (rows.F M)], rows.Arithmetic M → ∀ a z r : rows.F M,
    run M (.cons (a,z,()) (.cons r .nil)) = .done (.cons (line (decode _ (a,z)) r) .nil)

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

/-- Evidence for a selected operation can use the definitions of its own dependencies. -/
abbrev OperationCheck (ins : List V.Ty)
    (law : FunctionMeaning (rows.scalarHeader ⟨0⟩ ins) → Prop) :=
  {hs : Headers V} → (defs : Defs V hs) → (hs.fns.map (·.key)).Nodup →
    (op : LocalOp V hs.fns ins [rows.scalarTy]) →
    Option (PLift (law (fun M => localOp M (Defs.fnTable M defs) op)))

/-- Reinstall a key-independent body proof at the call found in this client. -/
def checkReadback {ins : List V.Ty} {law : FunctionMeaning (rows.scalarHeader ⟨0⟩ ins) → Prop}
    (proof : ∀ key, FunctionReadback (rows.scalarHeader key ins) law) : rows.OperationCheck ins law :=
  fun defs unique op => do
    let .call key := op.print | none
    (proof key).atOperation defs unique op

structure Companion (decode : PairEncoding) where
  boundary : rows.OperationCheck [rows.pair] (fun run => rows.BoundaryLaw ⟨0⟩ run decode)
  evaluate : rows.OperationCheck [rows.pair, rows.scalarTy] (fun run => rows.EvaluationLaw ⟨0⟩ run decode)

def endpointCompanion (evaluation : ∀ k, FunctionReadback _ (rows.EvaluationLaw k))
    (alternatives : List (∀ k, FunctionReadback _ (rows.EvaluationLaw k)) := []) :
    rows.Companion endpointEncoding where
  boundary defs unique op := rows.checkReadback (ins := [rows.pair])
    (law := fun run => rows.BoundaryLaw ⟨0⟩ run) rows.boundaryReadback defs unique op
  evaluate defs unique op := (evaluation :: alternatives).findSome? fun rule =>
    rows.checkReadback (law := fun run => rows.EvaluationLaw ⟨0⟩ run) (fun k => rule k) defs unique op

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
