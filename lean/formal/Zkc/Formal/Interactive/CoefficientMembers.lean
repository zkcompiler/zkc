module

public import Zkc.Formal.Interactive.EvaluationForwarder
public import Zkc.Formal.Interactive.EndpointExpression

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.Coefficients
open Core

/-- The source pair contains the constant and slope. Decode it to Boolean endpoints. -/
def expression : LineExpression := ⟨.first, .add .first .second⟩

abbrev decode := expression.decode

variable {V : Vocabulary} (rows : ScalarRows V)
local macro "inputName " n:term:max : term => `(⟨$n, rfl⟩)

def boundaryBody (fns : List (FnHeader V)) (k : Key) :
    Fn V fns (rows.scalarHeader k [rows.pair]) (Names.counting 0 _) :=
  .op ⟨0⟩ (.owned (.getTuple rows.fields .head rows.freelyProjected)) (.cons (inputName 0) .nil) (.cons 1 .nil) <|
  .op ⟨1⟩ (.owned (.getTuple rows.fields .head rows.freelyProjected)) (.cons (inputName 0) .nil) (.cons 2 .nil) <|
  .op ⟨2⟩ (.owned (.getTuple rows.fields (.tail .head) rows.freelyProjected)) (.cons (inputName 0) .nil) (.cons 3 .nil) <|
  .op ⟨3⟩ (.row rows.add rows.signature rows.addType) (.cons (inputName 2) (.cons (inputName 3) .nil)) (.cons 4 .nil) <|
  .op ⟨4⟩ (.row rows.add rows.signature rows.addType) (.cons (inputName 1) (.cons (inputName 4) .nil)) (.cons 5 .nil) <|
  .ret (.cons (inputName 5) .nil)

def evaluateBody (fns : List (FnHeader V)) (k : Key) :
    Fn V fns (rows.scalarHeader k [rows.pair,rows.scalarTy]) (Names.counting 0 _) :=
  .op ⟨0⟩ (.owned (.getTuple rows.fields .head rows.freelyProjected)) (.cons (inputName 0) .nil) (.cons 2 .nil) <|
  .op ⟨1⟩ (.owned (.getTuple rows.fields (.tail .head) rows.freelyProjected)) (.cons (inputName 0) .nil) (.cons 3 .nil) <|
  .op ⟨2⟩ (.row rows.mul rows.signature rows.mulType) (.cons (inputName 1) (.cons (inputName 3) .nil)) (.cons 4 .nil) <|
  .op ⟨3⟩ (.row rows.add rows.signature rows.addType) (.cons (inputName 2) (.cons (inputName 4) .nil)) (.cons 5 .nil) <|
  .ret (.cons (inputName 5) .nil)

def boundaryReadback (k : Key) : FunctionReadback _ (fun run => rows.BoundaryLaw k run decode) where
  inputs := Names.counting 0 _
  body fns := boundaryBody rows fns k
  armed _ := rfl
  holds fns tables M _ math a b := by
    change (localOp M (tables M) (.row rows.add rows.signature rows.addType) (.cons a (.cons b .nil))).bind _ = _
    rw [rows.binary_value M _ _ _ _ math.add]
    change (localOp M (tables M) (.row rows.add rows.signature rows.addType) (.cons a (.cons (a+b) .nil))).bind _ = _
    rw [rows.binary_value M _ _ _ _ math.add]
    rfl

def evaluateReadback (k : Key) : FunctionReadback _ (fun run => rows.EvaluationLaw k run decode) where
  inputs := Names.counting 0 _
  body fns := evaluateBody rows fns k
  armed _ := rfl
  holds fns tables M _ math a b r := by
    change (localOp M (tables M) (.row rows.mul rows.signature rows.mulType) (.cons r (.cons b .nil))).bind _ = _
    rw [rows.binary_value M _ _ _ _ math.mul]
    change (localOp M (tables M) (.row rows.add rows.signature rows.addType) (.cons a (.cons (r*b) .nil))).bind _ = _
    rw [rows.binary_value M _ _ _ _ math.add]
    have formula : line (a,a+b) r = a + r*b := by
      rw [line_normalForm]
      change a + r * (a + b - a) = a + r * b
      rw [Lean.Grind.Semiring.add_comm a b, Lean.Grind.AddCommGroup.add_sub_cancel]
    rw [← formula]
    rfl

def directEvaluation : rows.OperationCheck [rows.pair,rows.scalarTy] (fun run => rows.EvaluationLaw ⟨0⟩ run decode) :=
  fun defs unique op => rows.checkReadback (law := fun run => rows.EvaluationLaw ⟨0⟩ run decode)
    (evaluateReadback rows) defs unique op

def companion : rows.Companion decode where
  boundary defs unique op := rows.checkReadback (ins := [rows.pair])
    (law := fun run => rows.BoundaryLaw ⟨0⟩ run decode) (boundaryReadback rows) defs unique op
  evaluate defs unique op :=
    directEvaluation rows defs unique op <|> rows.throughEvaluationCall (decode := decode) (directEvaluation rows) defs unique op

end Zkc.Formal.Interactive.Sumcheck.Coefficients
