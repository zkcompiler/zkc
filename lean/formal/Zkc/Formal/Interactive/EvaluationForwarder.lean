module

public import Zkc.Formal.Interactive.PairReadback
public import Zkc.Core.Evidence.FunctionEntry

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.ScalarRows
open Core

variable {V : Vocabulary} (rows : ScalarRows V) {decode : PairEncoding}

/-- A two-argument wrapper forwards both inputs and returns the helper's sole result. -/
def forwardedEvaluation {fns : List (FnHeader V)} (wrapper helper site : Key)
    (ref : Member fns (rows.scalarHeader helper [rows.pair,rows.scalarTy])) :
    FunctionReadback.ArmedBody fns (rows.scalarHeader wrapper [rows.pair,rows.scalarTy]) :=
  ⟨Names.counting 0 _, .op site (.call ref) (.cons ⟨0,rfl⟩ (.cons ⟨1,rfl⟩ .nil)) (.cons 2 .nil)
    (.ret (.cons ⟨2,rfl⟩ .nil)), rfl⟩

/-- Transport a helper's installed meaning through a call in the wrapper's own table. -/
def throughEvaluationCall
    (leaf : rows.OperationCheck [rows.pair,rows.scalarTy] (fun run => rows.EvaluationLaw ⟨0⟩ run decode)) :
    rows.OperationCheck [rows.pair,rows.scalarTy] (fun run => rows.EvaluationLaw ⟨0⟩ run decode) :=
  fun defs unique op => do
    let .call key := op.print | none
    let outer ← FunctionEntry.resolve _ (rows.scalarHeader key [rows.pair,rows.scalarTy])
    let ⟨same⟩ ← op.same? (.call outer) unique
    let entry := defs.functionEntry unique outer
    let .mk _ [.op site _ (.call helper) _] _ := eraseFn entry.inputs entry.body | none
    let inner ← FunctionEntry.resolve _ (rows.scalarHeader helper [rows.pair,rows.scalarTy])
    let ⟨holds⟩ ← leaf entry.definitions entry.distinct (.call inner)
    let expected := rows.forwardedEvaluation key helper site inner
    let ⟨wrapped⟩ ← entry.recognize expected (fun run => rows.EvaluationLaw key run decode) (by
      intro M _ math a b r
      change (localOp M (Defs.fnTable M entry.definitions) (.call inner)
        (.cons (a,b,()) (.cons r .nil))).bind _ = _
      have value := holds M math a b r
      dsimp only at value
      rw [value]
      rfl)
    return ⟨same ▸ wrapped⟩

end Zkc.Formal.Interactive.Sumcheck.ScalarRows
