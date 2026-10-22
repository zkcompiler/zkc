module

public import Zkc.Source.DeriveRegion
public import ZkcExamples.Structured.MapFirstBodies
public import ZkcExamples.Structured.MapPrefixBodies

@[expose] public section

/-! Bounded exact expansions of actual-source body views into the existing Process,
derived operation by operation from the typed bodies. -/
namespace ZkcExamples.Structured.MapSourceExpansions
open Zkc.Source Zkc.Source.Structured
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem first_map (table : Meanings F G) (input0 : List F) (input1 : List F) (input2 : F) :
    MapFirstBodies.mapBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 .nil))) : Values (assignment F G) [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"]).get =
    (Evaluation.denoteMap table MapFirstBodies.mapSpec (.cons input0 (.cons input1 (.cons input2 .nil))) : Closed (Values (assignment F G) [.vector "bls12-381.fr"])).bind fun result0 =>
    .done (.cons (result0.get .here) .nil) := by
  derive_process

theorem first_widthRealization (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) :
    MapFirstBodies.widthRealizationBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 .nil))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index]).get =
    (invoke table ⟨"zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", .math, [.vector "bls12-381.fr", .index, .index], [.index]⟩ (.cons input0 (.cons input1 (.cons input2 .nil))) : Closed (Values (assignment F G) [.index])).bind fun result0 =>
    .done (.cons (result0.get .here) .nil) := by
  derive_process

theorem first_variablesRealization (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) :
    MapFirstBodies.variablesRealizationBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 .nil))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index]).get =
    (invoke table ⟨"zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", .math, [.vector "bls12-381.fr", .index, .index], [.index]⟩ (.cons input0 (.cons input1 (.cons input2 .nil))) : Closed (Values (assignment F G) [.index])).bind fun result0 =>
    .done (.cons (result0.get .here) .nil) := by
  derive_process

theorem first_valuesRealization (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) :
    MapFirstBodies.valuesRealizationBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 .nil))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index]).get =
    (invoke table ⟨"zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", .math, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩ (.cons input0 (.cons input1 (.cons input2 .nil))) : Closed (Values (assignment F G) [.vector "bls12-381.fr"])).bind fun result0 =>
    .done (.cons (result0.get .here) .nil) := by
  derive_process

theorem first_entry (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) (input3 : F) :
    MapFirstBodies.entryBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil)))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"]).get =
    (invoke table ⟨"s12h6d61705f6578616d706c65735h6669727374", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩ (.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil)))) : Closed (Values (assignment F G) [.vector "bls12-381.fr", .index, .index])).bind fun result0 =>
    .done (.cons (result0.get .here) (.cons (result0.get (.there .here)) (.cons (result0.get (.there (.there .here))) .nil))) := by
  derive_process

theorem first_wrapper (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) (input3 : F) :
    MapFirstBodies.wrapperBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil)))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"]).get =
    (invoke table ⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩ (.cons input0 (.cons input1 (.cons input2 .nil))) : Closed (Values (assignment F G) [.vector "bls12-381.fr", .index, .index])).bind fun result0 =>
    (invoke table ⟨"zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩ (.cons (result0.get .here) (.cons (result0.get (.there .here)) (.cons (result0.get (.there (.there .here))) (.cons input3 .nil)))) : Closed (Values (assignment F G) [.vector "bls12-381.fr", .index, .index])).bind fun result1 =>
    (invoke table ⟨"zkl_realization_0ce8d1f6fa18ecea2634e8a590d8d4d67ef3b2266fc521419daa7adb682a678a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩ (.cons (result1.get .here) (.cons (result1.get (.there .here)) (.cons (result1.get (.there (.there .here))) .nil))) : Closed (Values (assignment F G) [.vector "bls12-381.fr"])).bind fun result2 =>
    (invoke table ⟨"zkl_realization_cad7f4977a915cd19d3dc36089d25e60e203c526606ddf8f3c23bcb7a0610dc3", .local, [.vector "bls12-381.fr", .index, .index], [.index]⟩ (.cons (result1.get .here) (.cons (result1.get (.there .here)) (.cons (result1.get (.there (.there .here))) .nil))) : Closed (Values (assignment F G) [.index])).bind fun result3 =>
    (invoke table ⟨"zkl_realization_352d4a716b9eb002cfd13aef32bcb44994807d26b9eac630bc5dad5941c4b454", .local, [.vector "bls12-381.fr", .index, .index], [.index]⟩ (.cons (result1.get .here) (.cons (result1.get (.there .here)) (.cons (result1.get (.there (.there .here))) .nil))) : Closed (Values (assignment F G) [.index])).bind fun result4 =>
    .done (.cons (result2.get .here) (.cons (result3.get .here) (.cons (result4.get .here) .nil))) := by
  derive_process

theorem first_first (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) (input3 : F) :
    MapFirstBodies.firstBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil)))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"]).get =
    (invoke table ⟨"zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .vector "bls12-381.fr"]⟩ (.cons input0 (.cons input1 (.cons input2 .nil))) : Closed (Values (assignment F G) [.vector "bls12-381.fr", .vector "bls12-381.fr"])).bind fun result0 =>
    (invoke table ⟨"zkl_map_7aa10c0d106e0082840e035854d97e34de85744d05e64191205f7ada5a3efd95", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩ (.cons (result0.get .here) (.cons (result0.get (.there .here)) (.cons input3 .nil))) : Closed (Values (assignment F G) [.vector "bls12-381.fr"])).bind fun result1 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexConstant 1) .nil) : Closed (Values (assignment F G) [.index])).bind fun result2 =>
    (primitiveOutcome (Primitive.evaluate (F := F) (G := G) (.indexSub) (.cons input1 (.cons (result2.get .here) .nil))) : Closed (Values (assignment F G) [.index])).bind fun result3 =>
    .done (.cons (result1.get .here) (.cons (result3.get .here) (.cons input2 .nil))) := by
  derive_process

theorem first_interpolate (table : Meanings F G) (input0 : F) (input1 : F) (input2 : F) :
    MapFirstBodies.interpolateBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 .nil))) : Values (assignment F G) [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"]).get =
    (.done (.cons (input1 - input0) .nil) : Closed (Values (assignment F G) [.field "bls12-381.fr"])).bind fun result0 =>
    (.done (.cons ((result0.get .here) * input2) .nil) : Closed (Values (assignment F G) [.field "bls12-381.fr"])).bind fun result1 =>
    (.done (.cons (input0 + (result1.get .here)) .nil) : Closed (Values (assignment F G) [.field "bls12-381.fr"])).bind fun result2 =>
    .done (.cons (result2.get .here) .nil) := by
  derive_process

theorem first_values (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) :
    MapFirstBodies.valuesBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 .nil))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index]).get =
    .done (.cons input0 .nil) := by
  derive_process

theorem first_variables (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) :
    MapFirstBodies.variablesBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 .nil))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index]).get =
    .done (.cons input1 .nil) := by
  derive_process

theorem first_width (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) :
    MapFirstBodies.widthBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 .nil))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index]).get =
    .done (.cons input2 .nil) := by
  derive_process

theorem prefix_entry (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) (input3 : List F) :
    MapPrefixBodies.entryBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil)))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"]).get =
    (invoke table ⟨"s12h6d61705f6578616d706c65736h707265666978", .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩ (.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil)))) : Closed (Values (assignment F G) [.vector "bls12-381.fr", .index, .index])).bind fun result0 =>
    .done (.cons (result0.get .here) (.cons (result0.get (.there .here)) (.cons (result0.get (.there (.there .here))) .nil))) := by
  derive_process

theorem prefix_wrapper (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) (input3 : List F) :
    MapPrefixBodies.wrapperBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil)))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"]).get =
    (invoke table ⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩ (.cons input0 (.cons input1 (.cons input2 .nil))) : Closed (Values (assignment F G) [.vector "bls12-381.fr", .index, .index])).bind fun result0 =>
    (invoke table ⟨"zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩ (.cons (result0.get .here) (.cons (result0.get (.there .here)) (.cons (result0.get (.there (.there .here))) (.cons input3 .nil)))) : Closed (Values (assignment F G) [.vector "bls12-381.fr", .index, .index])).bind fun result1 =>
    (invoke table ⟨"zkl_realization_0ce8d1f6fa18ecea2634e8a590d8d4d67ef3b2266fc521419daa7adb682a678a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩ (.cons (result1.get .here) (.cons (result1.get (.there .here)) (.cons (result1.get (.there (.there .here))) .nil))) : Closed (Values (assignment F G) [.vector "bls12-381.fr"])).bind fun result2 =>
    (invoke table ⟨"zkl_realization_cad7f4977a915cd19d3dc36089d25e60e203c526606ddf8f3c23bcb7a0610dc3", .local, [.vector "bls12-381.fr", .index, .index], [.index]⟩ (.cons (result1.get .here) (.cons (result1.get (.there .here)) (.cons (result1.get (.there (.there .here))) .nil))) : Closed (Values (assignment F G) [.index])).bind fun result3 =>
    (invoke table ⟨"zkl_realization_352d4a716b9eb002cfd13aef32bcb44994807d26b9eac630bc5dad5941c4b454", .local, [.vector "bls12-381.fr", .index, .index], [.index]⟩ (.cons (result1.get .here) (.cons (result1.get (.there .here)) (.cons (result1.get (.there (.there .here))) .nil))) : Closed (Values (assignment F G) [.index])).bind fun result4 =>
    .done (.cons (result2.get .here) (.cons (result3.get .here) (.cons (result4.get .here) .nil))) := by
  derive_process

theorem prefix_prefix (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) (input3 : List F) :
    MapPrefixBodies.prefixBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil)))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"]).get =
    (invoke table ⟨"zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2", .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩ (.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil)))) : Closed (Values (assignment F G) [.vector "bls12-381.fr", .index, .index])).bind fun result0 =>
    .done (.cons (result0.get .here) (.cons (result0.get (.there .here)) (.cons (result0.get (.there (.there .here))) .nil))) := by
  derive_process

theorem prefix_step (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) (input3 : F) :
    MapPrefixBodies.stepBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil)))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"]).get =
    (invoke table ⟨"zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩ (.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil)))) : Closed (Values (assignment F G) [.vector "bls12-381.fr", .index, .index])).bind fun result0 =>
    .done (.cons (result0.get .here) (.cons (result0.get (.there .here)) (.cons (result0.get (.there (.there .here))) .nil))) := by
  derive_process

theorem prefix_foldWrapper (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) (input3 : List F) :
    MapPrefixBodies.foldWrapperBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil)))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"]).get =
    (invoke table ⟨"finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩ (.cons input3 (.cons input0 (.cons input1 (.cons input2 .nil)))) : Closed (Values (assignment F G) [.vector "bls12-381.fr", .index, .index])).bind fun result0 =>
    .done (.cons (result0.get .here) (.cons (result0.get (.there .here)) (.cons (result0.get (.there (.there .here))) .nil))) := by
  derive_process

theorem prefix_foldStep (table : Meanings F G) (input0 : List F) (input1 : Nat) (input2 : Nat) (input3 : F) (input4 : List F) :
    MapPrefixBodies.foldStepBody.denote (meaning F G table)
      ((.cons input0 (.cons input1 (.cons input2 (.cons input3 (.cons input4 .nil))))) : Values (assignment F G) [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr", .vector "bls12-381.fr"]).get =
    (invoke table ⟨"zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩ (.cons input0 (.cons input1 (.cons input2 (.cons input3 .nil)))) : Closed (Values (assignment F G) [.vector "bls12-381.fr", .index, .index])).bind fun result0 =>
    .done (.cons (result0.get .here) (.cons (result0.get (.there .here)) (.cons (result0.get (.there (.there .here))) .nil))) := by
  derive_process

end ZkcExamples.Structured.MapSourceExpansions
