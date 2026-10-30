module

public import Zkc.Source.DeriveRegion
public import Zkc.Source.Structured.DerivationRules
public import Zkc.Protocols.Multilinear.Source.PrimitiveShapeBodies
public import Zkc.Protocols.Multilinear.Source.PrimitiveTableBodies
public import Zkc.Protocols.Multilinear.Source.PrimitiveHalvesBodies

@[expose] public section

/-! Exact reusable helper expansions; closed Entry expansions are clients. -/
namespace ZkcExamples.Structured.PrimitiveExpansions
open Zkc.Source Zkc.Source.Structured
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem shape_body (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) :
    PrimitiveShapeViews.shapeBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 .nil))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index]).get =
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexConstant 0) .nil) : Closed (Values (assignment F G) [.index])).bind fun result0 =>
    (invoke table ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩ (.cons (result0.get .here) (.cons input2 .nil)) : Closed (Values (assignment F G) [.boolean])).bind fun result1 =>
    (if (result1.get .here) then
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexConstant 64) .nil) : Closed (Values (assignment F G) [.index])).bind fun result2 =>
    (invoke table ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩ (.cons input1 (.cons (result2.get .here) .nil)) : Closed (Values (assignment F G) [.boolean])).bind fun result3 =>
    .done (.cons (result3.get .here) .nil)
    else (.done (.cons false .nil) : Closed (Values (assignment F G) [.boolean])).bind fun result4 =>
    .done (.cons (result4.get .here) .nil) : Closed (Values (assignment F G) [.boolean])).bind fun result5 =>
    (if (result5.get .here) then
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.vectorLength "bls12-381.fr") (.cons input0 .nil)) : Closed (Values (assignment F G) [.index])).bind fun result6 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexMod) (.cons (result6.get .here) (.cons input2 .nil))) : Closed (Values (assignment F G) [.index])).bind fun result7 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexConstant 0) .nil) : Closed (Values (assignment F G) [.index])).bind fun result8 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexEqual) (.cons (result7.get .here) (.cons (result8.get .here) .nil))) : Closed (Values (assignment F G) [.boolean])).bind fun result9 =>
    .done (.cons (result9.get .here) .nil)
    else (.done (.cons false .nil) : Closed (Values (assignment F G) [.boolean])).bind fun result10 =>
    .done (.cons (result10.get .here) .nil) : Closed (Values (assignment F G) [.boolean])).bind fun result11 =>
    (if (result11.get .here) then
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.vectorLength "bls12-381.fr") (.cons input0 .nil)) : Closed (Values (assignment F G) [.index])).bind fun result12 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexDiv) (.cons (result12.get .here) (.cons input2 .nil))) : Closed (Values (assignment F G) [.index])).bind fun result13 =>
    (invoke table ⟨"s3h7a6b6311h6d756c74696c696e6561724h726f7773", .local, [.index], [.index]⟩ (.cons input1 .nil) : Closed (Values (assignment F G) [.index])).bind fun result14 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexEqual) (.cons (result13.get .here) (.cons (result14.get .here) .nil))) : Closed (Values (assignment F G) [.boolean])).bind fun result15 =>
    .done (.cons (result15.get .here) .nil)
    else (.done (.cons false .nil) : Closed (Values (assignment F G) [.boolean])).bind fun result16 =>
    .done (.cons (result16.get .here) .nil) : Closed (Values (assignment F G) [.boolean])).bind fun result17 =>
    .done (.cons (result17.get .here) .nil) := by
  derive_process using (exact branch_law _ _ _ _ _ _)

theorem table_body (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) :
    PrimitiveTableViews.tableBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 .nil))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index]).get =
    (invoke table ⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [.vector "bls12-381.fr", .index, .index], [.boolean]⟩ (.cons input0 (.cons input1 (.cons input2 .nil))) : Closed (Values (assignment F G) [.boolean])).bind fun result0 =>
    (if (result0.get .here) then
    .done .nil
    else .halt .reject : Closed (Values (assignment F G) [])).bind fun _ =>
    .done (.cons input0 (.cons input1 (.cons input2 .nil))) := by
  derive_process using (exact branch_law _ _ _ _ _ _)

theorem halves_body (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) :
    PrimitiveHalvesViews.halvesBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 .nil))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index]).get =
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexConstant 0) .nil) : Closed (Values (assignment F G) [.index])).bind fun result0 =>
    (invoke table ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩ (.cons (result0.get .here) (.cons input1 .nil)) : Closed (Values (assignment F G) [.boolean])).bind fun result1 =>
    (if (result1.get .here) then
    .done .nil
    else .halt .reject : Closed (Values (assignment F G) [])).bind fun _ =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.vectorSplit "bls12-381.fr") (.cons input0 .nil)) : Closed (Values (assignment F G) [.vector "bls12-381.fr", .vector "bls12-381.fr"])).bind fun result3 =>
    .done (.cons (result3.get .here) (.cons (result3.get (.there .here)) .nil)) := by
  derive_process using (exact branch_law _ _ _ _ _ _)

end ZkcExamples.Structured.PrimitiveExpansions
