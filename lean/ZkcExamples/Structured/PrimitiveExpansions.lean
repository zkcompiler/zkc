module

public import ZkcExamples.Structured.PrimitiveShapeViews
public import ZkcExamples.Structured.PrimitiveTableViews
public import ZkcExamples.Structured.PrimitiveHalvesViews
public import ZkcExamples.Structured.PrimitiveSequenceViews

@[expose] public section

/-! Exact body-expansion lemmas. These are proof normal forms for the
retained typed bodies, not a new execution path or assumed helper semantics. -/
namespace ZkcExamples.Structured.PrimitiveExpansions
open Zkc.Source Zkc.Source.Structured
-- Local transparency options below elaborate dependent source-view aliases;
-- every resulting equation is still checked by the kernel.
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
private theorem prepend_empty {Value : Ty → Type} {types : List Ty}
    (env : Environment Value types) (values : Values Value []) :
    @Eq (Environment Value types) (env.prepend values) env := by cases values; rfl
private theorem prepend_one {Value : Ty → Type} {types : List Ty} {type : Ty}
    (env : Environment Value types) (values : Values Value [type]) :
    @Eq (Environment Value (type :: types)) (env.prepend values) (env.push (values.get .here)) := by
  cases values with | cons value rest => cases rest; rfl
private theorem prepend_two {Value : Ty → Type} {types : List Ty} {first second : Ty}
    (env : Environment Value types) (values : Values Value [first, second]) :
    @Eq (Environment Value (first :: second :: types)) (env.prepend values)
      (Environment.push (Environment.push env (values.get (.there .here))) (values.get .here)) := by
  cases values with | cons a rest => cases rest with | cons b rest => cases rest; rfl
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

private theorem prepend_three {Value : Ty → Type} {types : List Ty} {type0 type1 type2 : Ty}
    (env : Environment Value types) (values : Values Value [type0, type1, type2]) :
    @Eq (Environment Value ([type0, type1, type2] ++ types)) (env.prepend values) (Environment.push (Environment.push (Environment.push env (values.get (.there (.there .here)))) (values.get (.there .here))) (values.get .here)) := by
  cases values with | cons value0 values => cases values with | cons value1 values => cases values with | cons value2 values => cases values; rfl

private theorem prepend_eight {Value : Ty → Type} {types : List Ty} {type0 type1 type2 type3 type4 type5 type6 type7 : Ty}
    (env : Environment Value types) (values : Values Value [type0, type1, type2, type3, type4, type5, type6, type7]) :
    @Eq (Environment Value ([type0, type1, type2, type3, type4, type5, type6, type7] ++ types)) (env.prepend values) (Environment.push (Environment.push (Environment.push (Environment.push (Environment.push (Environment.push (Environment.push (Environment.push env (values.get (.there (.there (.there (.there (.there (.there (.there .here))))))))) (values.get (.there (.there (.there (.there (.there (.there .here)))))))) (values.get (.there (.there (.there (.there (.there .here))))))) (values.get (.there (.there (.there (.there .here)))))) (values.get (.there (.there (.there .here))))) (values.get (.there (.there .here)))) (values.get (.there .here))) (values.get .here)) := by
  cases values with | cons value0 values => cases values with | cons value1 values => cases values with | cons value2 values => cases values with | cons value3 values => cases values with | cons value4 values => cases values with | cons value5 values => cases values with | cons value6 values => cases values with | cons value7 values => cases values; rfl

set_option backward.isDefEq.respectTransparency false in
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
  simp only [PrimitiveShapeViews.shapeBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, Values.get, prepend_empty, prepend_one, prepend_two, prepend_three, prepend_eight,
    Environment.prepend, Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Proc.bind, PIR.Proc.bind_assoc, Evaluation.invokeCallback, ite_apply]
  all_goals rfl

set_option backward.isDefEq.respectTransparency false in
theorem table_body (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) :
    PrimitiveTableViews.tableBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 .nil))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index]).get =
    (invoke table ⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [.vector "bls12-381.fr", .index, .index], [.boolean]⟩ (.cons input0 (.cons input1 (.cons input2 .nil))) : Closed (Values (assignment F G) [.boolean])).bind fun result0 =>
    (if (result0.get .here) then
    .done .nil
    else .halt .reject : Closed (Values (assignment F G) [])).bind fun _ =>
    .done (.cons input0 (.cons input1 (.cons input2 .nil))) := by
  simp only [PrimitiveTableViews.tableBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, Values.get, prepend_empty, prepend_one, prepend_two, prepend_three, prepend_eight,
    Environment.prepend, Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Proc.bind, PIR.Proc.bind_assoc, Evaluation.invokeCallback, ite_apply]
  all_goals rfl

set_option backward.isDefEq.respectTransparency false in
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
  simp only [PrimitiveHalvesViews.halvesBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, Values.get, prepend_empty, prepend_one, prepend_two, prepend_three, prepend_eight,
    Environment.prepend, Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Proc.bind, PIR.Proc.bind_assoc, Evaluation.invokeCallback, ite_apply]
  all_goals rfl

set_option backward.isDefEq.respectTransparency false in
theorem appendSummary_body (table : Meanings F G) (input0 : List F) (input1 : F) (input2 : Nat) :
    PrimitiveSequenceViews.appendSummaryBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 .nil))) : Values (assignment F G) [.vector "bls12-381.fr", .field "bls12-381.fr", .index]).get =
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.vectorLength "bls12-381.fr") (.cons input0 .nil)) : Closed (Values (assignment F G) [.index])).bind fun result0 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexConstant 1) .nil) : Closed (Values (assignment F G) [.index])).bind fun result1 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexAdd) (.cons (result0.get .here) (.cons (result1.get .here) .nil))) : Closed (Values (assignment F G) [.index])).bind fun result2 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.vectorAppend "bls12-381.fr") (.cons input0 (.cons input1 .nil))) : Closed (Values (assignment F G) [.vector "bls12-381.fr"])).bind fun result3 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexDiv) (.cons (result2.get .here) (.cons input2 .nil))) : Closed (Values (assignment F G) [.index])).bind fun result4 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexMod) (.cons (result2.get .here) (.cons input2 .nil))) : Closed (Values (assignment F G) [.index])).bind fun result5 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexConstant 1) .nil) : Closed (Values (assignment F G) [.index])).bind fun result6 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexSub) (.cons (result2.get .here) (.cons (result6.get .here) .nil))) : Closed (Values (assignment F G) [.index])).bind fun result7 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.vectorSum "bls12-381.fr") (.cons (result3.get .here) .nil)) : Closed (Values (assignment F G) [.field "bls12-381.fr"])).bind fun result8 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.vectorEqual "bls12-381.fr") (.cons input0 (.cons (result3.get .here) .nil))) : Closed (Values (assignment F G) [.boolean])).bind fun result9 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.fieldEqual "bls12-381.fr") (.cons (result8.get .here) (.cons input1 .nil))) : Closed (Values (assignment F G) [.boolean])).bind fun result10 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.vectorEmpty "bls12-381.fr") .nil) : Closed (Values (assignment F G) [.vector "bls12-381.fr"])).bind fun result11 =>
    .done (.cons (result3.get .here) (.cons (result4.get .here) (.cons (result5.get .here) (.cons (result7.get .here) (.cons (result8.get .here) (.cons (result9.get .here) (.cons (result10.get .here) (.cons (result11.get .here) .nil)))))))) := by
  simp only [PrimitiveSequenceViews.appendSummaryBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, Values.get, prepend_empty, prepend_one, prepend_two, prepend_three, prepend_eight,
    Environment.prepend, Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Proc.bind, PIR.Proc.bind_assoc, Evaluation.invokeCallback, ite_apply]
  all_goals rfl

set_option backward.isDefEq.respectTransparency false in
theorem shape_entry (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) :
    PrimitiveShapeViews.entryBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 .nil))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index]).get =
    (invoke table ⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [.vector "bls12-381.fr", .index, .index], [.boolean]⟩ (.cons input0 (.cons input1 (.cons input2 .nil))) : Closed (Values (assignment F G) [.boolean])).bind fun result0 =>
    .done (.cons (result0.get .here) .nil) := by
  simp only [PrimitiveShapeViews.entryBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, Values.get, prepend_empty, prepend_one, prepend_two, prepend_three, prepend_eight,
    Environment.prepend, Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Proc.bind, PIR.Proc.bind_assoc, Evaluation.invokeCallback, ite_apply]
  all_goals rfl

set_option backward.isDefEq.respectTransparency false in
theorem table_entry (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) :
    PrimitiveTableViews.entryBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 .nil))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index]).get =
    (invoke table ⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩ (.cons input0 (.cons input1 (.cons input2 .nil))) : Closed (Values (assignment F G) [.vector "bls12-381.fr", .index, .index])).bind fun result0 =>
    .done (.cons (result0.get .here) (.cons (result0.get (.there .here)) (.cons (result0.get (.there (.there .here))) .nil))) := by
  simp only [PrimitiveTableViews.entryBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, Values.get, prepend_empty, prepend_one, prepend_two, prepend_three, prepend_eight,
    Environment.prepend, Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Proc.bind, PIR.Proc.bind_assoc, Evaluation.invokeCallback, ite_apply]
  all_goals rfl

set_option backward.isDefEq.respectTransparency false in
theorem halves_entry (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) :
    PrimitiveHalvesViews.entryBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 .nil))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index]).get =
    (invoke table ⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩ (.cons input0 (.cons input1 (.cons input2 .nil))) : Closed (Values (assignment F G) [.vector "bls12-381.fr", .index, .index])).bind fun result0 =>
    (invoke table ⟨"zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .vector "bls12-381.fr"]⟩ (.cons (result0.get .here) (.cons (result0.get (.there .here)) (.cons (result0.get (.there (.there .here))) .nil))) : Closed (Values (assignment F G) [.vector "bls12-381.fr", .vector "bls12-381.fr"])).bind fun result1 =>
    .done (.cons (result1.get .here) (.cons (result1.get (.there .here)) .nil)) := by
  simp only [PrimitiveHalvesViews.entryBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, Values.get, prepend_empty, prepend_one, prepend_two, prepend_three, prepend_eight,
    Environment.prepend, Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Proc.bind, PIR.Proc.bind_assoc, Evaluation.invokeCallback, ite_apply]
  all_goals rfl

set_option backward.isDefEq.respectTransparency false in
theorem sequence_entry (table : Meanings F G) (input0 : List F) (input1 : F) (input2 : Nat) :
    PrimitiveSequenceViews.entryBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 .nil))) : Values (assignment F G) [.vector "bls12-381.fr", .field "bls12-381.fr", .index]).get =
    (invoke table ⟨"s18h7072696d69746976655f6578616d706c657314h617070656e645f73756d6d617279", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index], [.vector "bls12-381.fr", .index, .index, .index, .field "bls12-381.fr", .boolean, .boolean, .vector "bls12-381.fr"]⟩ (.cons input0 (.cons input1 (.cons input2 .nil))) : Closed (Values (assignment F G) [.vector "bls12-381.fr", .index, .index, .index, .field "bls12-381.fr", .boolean, .boolean, .vector "bls12-381.fr"])).bind fun result0 =>
    .done (.cons (result0.get .here) (.cons (result0.get (.there .here)) (.cons (result0.get (.there (.there .here))) (.cons (result0.get (.there (.there (.there .here)))) (.cons (result0.get (.there (.there (.there (.there .here))))) (.cons (result0.get (.there (.there (.there (.there (.there .here)))))) (.cons (result0.get (.there (.there (.there (.there (.there (.there .here))))))) (.cons (result0.get (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)))))))) := by
  simp only [PrimitiveSequenceViews.entryBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, Values.get, prepend_empty, prepend_one, prepend_two, prepend_three, prepend_eight,
    Environment.prepend, Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Proc.bind, PIR.Proc.bind_assoc, Evaluation.invokeCallback, ite_apply]
  all_goals rfl

set_option backward.isDefEq.respectTransparency false in
theorem appendSummary_body_observed {I : PIR.Signature} (sites : SiteObservations I) (table : Evaluation.Meanings F G I) (input0 : List F) (input1 : F) (input2 : Nat) :
    PrimitiveSequenceViews.appendSummaryBody.denote (Evaluation.meaning sites table)
      ((.cons input0 (.cons input1 (.cons input2 .nil))) : Values (assignment F G) [.vector "bls12-381.fr", .field "bls12-381.fr", .index]).get =
    (sites.mark "s0").bind fun _ =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.vectorLength "bls12-381.fr") (.cons input0 .nil)) : PIR.Proc I (Values (assignment F G) [.index])).bind fun result0 =>
    (sites.mark "s2").bind fun _ =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexConstant 1) .nil) : PIR.Proc I (Values (assignment F G) [.index])).bind fun result1 =>
    (sites.mark "s3").bind fun _ =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexAdd) (.cons (result0.get .here) (.cons (result1.get .here) .nil))) : PIR.Proc I (Values (assignment F G) [.index])).bind fun result2 =>
    (sites.mark "s5").bind fun _ =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.vectorAppend "bls12-381.fr") (.cons input0 (.cons input1 .nil))) : PIR.Proc I (Values (assignment F G) [.vector "bls12-381.fr"])).bind fun result3 =>
    (sites.mark "s7").bind fun _ =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexDiv) (.cons (result2.get .here) (.cons input2 .nil))) : PIR.Proc I (Values (assignment F G) [.index])).bind fun result4 =>
    (sites.mark "s9").bind fun _ =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexMod) (.cons (result2.get .here) (.cons input2 .nil))) : PIR.Proc I (Values (assignment F G) [.index])).bind fun result5 =>
    (sites.mark "s11").bind fun _ =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexConstant 1) .nil) : PIR.Proc I (Values (assignment F G) [.index])).bind fun result6 =>
    (sites.mark "s12").bind fun _ =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexSub) (.cons (result2.get .here) (.cons (result6.get .here) .nil))) : PIR.Proc I (Values (assignment F G) [.index])).bind fun result7 =>
    (sites.mark "s14").bind fun _ =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.vectorSum "bls12-381.fr") (.cons (result3.get .here) .nil)) : PIR.Proc I (Values (assignment F G) [.field "bls12-381.fr"])).bind fun result8 =>
    (sites.mark "s16").bind fun _ =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.vectorEqual "bls12-381.fr") (.cons input0 (.cons (result3.get .here) .nil))) : PIR.Proc I (Values (assignment F G) [.boolean])).bind fun result9 =>
    (sites.mark "s18").bind fun _ =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.fieldEqual "bls12-381.fr") (.cons (result8.get .here) (.cons input1 .nil))) : PIR.Proc I (Values (assignment F G) [.boolean])).bind fun result10 =>
    (sites.mark "s20").bind fun _ =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.vectorEmpty "bls12-381.fr") .nil) : PIR.Proc I (Values (assignment F G) [.vector "bls12-381.fr"])).bind fun result11 =>
    .done (.cons (result3.get .here) (.cons (result4.get .here) (.cons (result5.get .here) (.cons (result7.get .here) (.cons (result8.get .here) (.cons (result9.get .here) (.cons (result10.get .here) (.cons (result11.get .here) .nil)))))))) := by
  simp only [PrimitiveSequenceViews.appendSummaryBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, Values.get, prepend_empty, prepend_one, prepend_two, prepend_three, prepend_eight,
    Environment.prepend, Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Proc.bind, PIR.Proc.bind_assoc, Evaluation.invokeCallback, ite_apply]
  all_goals rfl

set_option backward.isDefEq.respectTransparency false in
theorem sequence_entry_observed {I : PIR.Signature} (sites : SiteObservations I) (table : Evaluation.Meanings F G I) (input0 : List F) (input1 : F) (input2 : Nat) :
    PrimitiveSequenceViews.entryBody.denote (Evaluation.meaning sites table)
      ((.cons input0 (.cons input1 (.cons input2 .nil))) : Values (assignment F G) [.vector "bls12-381.fr", .field "bls12-381.fr", .index]).get =
    (sites.mark "s0").bind fun _ =>
    (invoke table ⟨"s18h7072696d69746976655f6578616d706c657314h617070656e645f73756d6d617279", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index], [.vector "bls12-381.fr", .index, .index, .index, .field "bls12-381.fr", .boolean, .boolean, .vector "bls12-381.fr"]⟩ (.cons input0 (.cons input1 (.cons input2 .nil))) : PIR.Proc I (Values (assignment F G) [.vector "bls12-381.fr", .index, .index, .index, .field "bls12-381.fr", .boolean, .boolean, .vector "bls12-381.fr"])).bind fun result0 =>
    .done (.cons (result0.get .here) (.cons (result0.get (.there .here)) (.cons (result0.get (.there (.there .here))) (.cons (result0.get (.there (.there (.there .here)))) (.cons (result0.get (.there (.there (.there (.there .here))))) (.cons (result0.get (.there (.there (.there (.there (.there .here)))))) (.cons (result0.get (.there (.there (.there (.there (.there (.there .here))))))) (.cons (result0.get (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)))))))) := by
  simp only [PrimitiveSequenceViews.entryBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, Values.get, prepend_empty, prepend_one, prepend_two, prepend_three, prepend_eight,
    Environment.prepend, Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Proc.bind, PIR.Proc.bind_assoc, Evaluation.invokeCallback, ite_apply]
  all_goals rfl

end ZkcExamples.Structured.PrimitiveExpansions
