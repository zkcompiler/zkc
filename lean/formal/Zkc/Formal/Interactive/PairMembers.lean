module

public import Zkc.Core.Admission.Elaboration
public import Zkc.Core.Meaning.Program
public import Zkc.Core.World.Layer
public import Zkc.Formal.Interactive.Sumcheck

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck
open Core

/-- The scalar operations used by the source implementation of a multilinear round.
Each key has the specified signature in the very vocabulary used for admission. -/
structure ScalarRows (V : Vocabulary) where
  scalar : V.TypeKey
  free : V.linear scalar = false
  one : V.literal scalar 1 = true
  add : V.RowKey
  sub : V.RowKey
  mul : V.RowKey
  addType : V.row add = some ⟨[.nominal scalar, .nominal scalar], [.nominal scalar], .pure⟩
  subType : V.row sub = some ⟨[.nominal scalar, .nominal scalar], [.nominal scalar], .pure⟩
  mulType : V.row mul = some ⟨[.nominal scalar, .nominal scalar], [.nominal scalar], .pure⟩

namespace ScalarRows
variable {V : Vocabulary} (rows : ScalarRows V)
abbrev scalarTy : V.Ty := .nominal rows.scalar
abbrev fields : Tys V.TypeKey := .cons rows.scalarTy (.cons rows.scalarTy .nil)
abbrev pair : V.Ty := .tuple rows.fields
abbrev signature : RowSignature V.TypeKey V.RowKey := ⟨[rows.scalarTy, rows.scalarTy], [rows.scalarTy], .pure⟩
abbrev scalarHeader (k : Key) (inputs : List V.Ty) : FnHeader V :=
  ⟨k, inputs, [rows.scalarTy], false, none, ⟨[],[]⟩⟩

theorem freelyProjected : Tys.anyLinear V rows.fields = false := by
  simp [Tys.anyLinear, Ty.isLinear, rows.free]
theorem readsOne : V.Reads rows.scalarTy [1] := by simp [Vocabulary.Reads, Ty.scan, rows.one]

local macro "inputName " n:term:max : term => `(⟨$n, rfl⟩)

def boundaryBody (fns : List (FnHeader V)) (k : Key) :
    Fn V fns (rows.scalarHeader k [rows.pair]) (Names.counting 0 _) :=
  .op ⟨0⟩ (.owned (.getTuple rows.fields .head rows.freelyProjected)) (.cons (inputName 0) .nil) (.cons 1 .nil) <|
  .op ⟨1⟩ (.owned (.getTuple rows.fields (.tail .head) rows.freelyProjected)) (.cons (inputName 0) .nil) (.cons 2 .nil) <|
  .op ⟨2⟩ (.row rows.add rows.signature rows.addType) (.cons (inputName 1) (.cons (inputName 2) .nil)) (.cons 3 .nil) <|
  .ret (.cons (inputName 3) .nil)

def evaluateBody (fns : List (FnHeader V)) (k : Key) :
    Fn V fns (rows.scalarHeader k [rows.pair, rows.scalarTy]) (Names.counting 0 _) :=
  .op ⟨0⟩ (.literal rows.scalarTy [1] rows.readsOne) .nil (.cons 2 .nil) <|
  .op ⟨1⟩ (.row rows.sub rows.signature rows.subType) (.cons (inputName 2) (.cons (inputName 1) .nil)) (.cons 3 .nil) <|
  .op ⟨2⟩ (.owned (.getTuple rows.fields .head rows.freelyProjected)) (.cons (inputName 0) .nil) (.cons 4 .nil) <|
  .op ⟨3⟩ (.row rows.mul rows.signature rows.mulType) (.cons (inputName 3) (.cons (inputName 4) .nil)) (.cons 5 .nil) <|
  .op ⟨4⟩ (.owned (.getTuple rows.fields (.tail .head) rows.freelyProjected)) (.cons (inputName 0) .nil) (.cons 6 .nil) <|
  .op ⟨5⟩ (.row rows.mul rows.signature rows.mulType) (.cons (inputName 1) (.cons (inputName 6) .nil)) (.cons 7 .nil) <|
  .op ⟨6⟩ (.row rows.add rows.signature rows.addType) (.cons (inputName 5) (.cons (inputName 7) .nil)) (.cons 8 .nil) <|
  .ret (.cons (inputName 8) .nil)

/-- The alternate source expression takes the difference of the endpoints first. -/
def affineBody (fns : List (FnHeader V)) (k : Key) :
    Fn V fns (rows.scalarHeader k [rows.pair,rows.scalarTy]) (Names.counting 0 _) :=
  .op ⟨0⟩ (.owned (.getTuple rows.fields .head rows.freelyProjected)) (.cons (inputName 0) .nil) (.cons 2 .nil) <|
  .op ⟨1⟩ (.owned (.getTuple rows.fields (.tail .head) rows.freelyProjected)) (.cons (inputName 0) .nil) (.cons 3 .nil) <|
  .op ⟨2⟩ (.owned (.getTuple rows.fields .head rows.freelyProjected)) (.cons (inputName 0) .nil) (.cons 4 .nil) <|
  .op ⟨3⟩ (.row rows.sub rows.signature rows.subType) (.cons (inputName 3) (.cons (inputName 4) .nil)) (.cons 5 .nil) <|
  .op ⟨4⟩ (.row rows.mul rows.signature rows.mulType) (.cons (inputName 1) (.cons (inputName 5) .nil)) (.cons 6 .nil) <|
  .op ⟨5⟩ (.row rows.add rows.signature rows.addType) (.cons (inputName 2) (.cons (inputName 6) .nil)) (.cons 7 .nil) <|
  .ret (.cons (inputName 7) .nil)

variable (M : Model V)
abbrev F := M.Val rows.scalarTy
variable [Lean.Grind.Field (rows.F M)]

/-- The four mathematical obligations on the deployment's interpretation.
The projections of the pair use the Core-owned operations. -/
structure Arithmetic : Prop where
  one : Ty.readLiteral M rows.scalarTy [1] rows.readsOne = (1 : rows.F M)
  add : ∀ x y : rows.F M, M.apply rows.add rows.signature rows.addType (.cons x (.cons y .nil)) =
    some (.cons (x + y) .nil)
  sub : ∀ x y : rows.F M, M.apply rows.sub rows.signature rows.subType (.cons x (.cons y .nil)) =
    some (.cons (x - y) .nil)
  mul : ∀ x y : rows.F M, M.apply rows.mul rows.signature rows.mulType (.cons x (.cons y .nil)) =
    some (.cons (x * y) .nil)

omit [Lean.Grind.Field (rows.F M)] in
private theorem binary_value {fns} (table : FnTable M fns) (key : V.RowKey)
    (present : V.row key = some rows.signature) (f : rows.F M → rows.F M → rows.F M)
    (law : ∀ x y, M.apply key rows.signature present (.cons x (.cons y .nil)) = some (.cons (f x y) .nil))
    (x y : rows.F M) :
    localOp M table (.row key rows.signature present) (.cons x (.cons y .nil)) =
      .done (.cons (f x y) .nil) := by simp [localOp, law]

theorem boundary_value {fns} (table : FnTable M fns) (k : Key) (a z : rows.F M)
    (math : rows.Arithmetic M) :
    (rows.boundaryBody fns k).denote (localSem M _ table) []
      (Env.positional (.cons (a,z,()) .nil)) = .done (.cons (a + z) .nil) := by
  change (localOp M table (.row rows.add rows.signature rows.addType) (.cons a (.cons z .nil))).bind _ = _
  rw [binary_value rows M table _ _ _ math.add]
  rfl

theorem evaluate_value {fns} (table : FnTable M fns) (k : Key) (a z r : rows.F M)
    (math : rows.Arithmetic M) :
    (rows.evaluateBody fns k).denote (localSem M _ table) []
      (Env.positional (.cons (a,z,()) (.cons r .nil))) = .done (.cons (line (a,z) r) .nil) := by
  change (localOp M table (.row rows.sub rows.signature rows.subType)
    (.cons (Ty.readLiteral M rows.scalarTy [1] rows.readsOne) (.cons r .nil))).bind _ = _
  rw [math.one, binary_value rows M table _ _ _ math.sub]
  change (localOp M table (.row rows.mul rows.signature rows.mulType)
    (.cons (1-r) (.cons a .nil))).bind _ = _
  rw [binary_value rows M table _ _ _ math.mul]
  change (localOp M table (.row rows.mul rows.signature rows.mulType)
    (.cons r (.cons z .nil))).bind _ = _
  rw [binary_value rows M table _ _ _ math.mul]
  change (localOp M table (.row rows.add rows.signature rows.addType)
    (.cons ((1-r)*a) (.cons (r*z) .nil))).bind _ = _
  rw [binary_value rows M table _ _ _ math.add]
  rfl

theorem affine_value {fns} (table : FnTable M fns) (k : Key) (a z r : rows.F M)
    (math : rows.Arithmetic M) :
    (rows.affineBody fns k).denote (localSem M _ table) []
      (Env.positional (.cons (a,z,()) (.cons r .nil))) = .done (.cons (line (a,z) r) .nil) := by
  change (localOp M table (.row rows.sub rows.signature rows.subType)
    (.cons z (.cons a .nil))).bind _ = _
  rw [binary_value rows M table _ _ _ math.sub]
  change (localOp M table (.row rows.mul rows.signature rows.mulType)
    (.cons r (.cons (z-a) .nil))).bind _ = _
  rw [binary_value rows M table _ _ _ math.mul]
  change (localOp M table (.row rows.add rows.signature rows.addType)
    (.cons a (.cons (r*(z-a)) .nil))).bind _ = _
  rw [binary_value rows M table _ _ _ math.add, line_normalForm]
  rfl

#print axioms boundary_value
#print axioms evaluate_value
#print axioms affine_value

end ScalarRows
end Zkc.Formal.Interactive.Sumcheck
