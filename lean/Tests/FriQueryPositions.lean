module

public import ZkcExamples.Structured.FriSourceBodies
public import Zkc.Source.Structured.WordDerivation
public import ZkcTools.ConstructionBindings.MathRegion

@[expose] public section

/-! The controller's first child position reuses the original pair-index body.
The generated region retains nine captures but the source helper consumes two.
The common embedded rule derives that selected input view and its output frame.
The surrounding oracle/continuation installation is a separate obligation. -/
set_option autoImplicit false
namespace Tests.FriQueryPositions
open Zkc.Source Zkc.Source.Structured Zkc.Construction ConnectionMathRegion
open ZkcExamples.Structured.FriSourceBodies

def captures : List Ty :=
  [.field "koala-bear.ext8-binomial3", .index, .index,
    .field "koala-bear.ext8-binomial3", .field "koala-bear.ext8-binomial3",
    .field "koala-bear.ext8-binomial3", .field "koala-bear.ext8-binomial3",
    .field "koala-bear.ext8-binomial3", .index]

def selected : Operands captures [.index, .index] :=
  .cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.cons (.there .here) .nil)

def region : InstructionRegion :=
  ⟨captures.map .data,
    [⟨.calculate (.indexConstant 1), [], [.data .index], []⟩,
     ⟨.calculate .indexLogicalShiftRight, [1, 9], [.data .index], []⟩,
     ⟨.calculate (.indexConstant 1), [], [.data .index], []⟩,
     ⟨.calculate .indexWrappingSubtract, [10, 11], [.data .index], []⟩,
     ⟨.calculate .indexBitAnd, [8, 12], [.data .index], []⟩], [13]⟩

def spine : ConnectionTargetPrefix.Prefix :=
  .step (fun model ↦ Domain.View.calculation model (.indexConstant 1) [] [.data .index])
    (.step (fun model ↦ Domain.View.calculation model .indexLogicalShiftRight [1, 9] [.data .index])
    (.step (fun model ↦ Domain.View.calculation model (.indexConstant 1) [] [.data .index])
    (.step (fun model ↦ Domain.View.calculation model .indexWrappingSubtract [10, 11] [.data .index])
    (.step (fun model ↦ Domain.View.calculation model .indexBitAnd [8, 12] [.data .index]) .empty))))

def target : TargetBlock := spine.block

def connected : Alignment [] helper14Body [.data 8, .data 1] 9 target [13] 14 := by
  derive_math_region

/-- Every placement uses the same original checked helper body and shared
structural construction. Unused field and index captures retain their values without
being silently interpreted as source arguments. -/
noncomputable def actual (model : DomainModel) (program : Program) (context : Context)
    (values : Values model.Value captures) (environment : Domain.Environment model.toCarriers)
    (references : List Nat)
    (read : Domain.read environment references = Domain.encodeValues values) :
    Original.Simulation (fun result frame ↦ frame = environment ++ Original.encodeHelperResult result)
      (fun _ frame ↦ ArtifactBinding.Captures environment frame)
      ((helper14Body.denote (meaning model []) (selected.eval values.get).get).interpret
        (closedLift (I := Domain.effects model.toCarriers)))
      (Domain.step model program context ⟨.mathCompute, references, [.data .index], [region]⟩
        environment) :=
  connected.embedded (region := region) selected rfl model program context rfl rfl
    (by intro frame; rfl) rfl rfl rfl values environment references read

/-- Equal-typed source positions cannot be swapped just because both fit the
capture row. The structural proof is against the actual source operand order. -/
example : True := by
  fail_if_success
    have : Alignment [] helper14Body [.data 1, .data 8] 9 target [13] 14 := by
      derive_math_region
  trivial

#print axioms connected
#print axioms actual

def rightTail : Region dialect [.index, .index, .index] [.index] :=
  .letOp (.indexConstant 1) .nil .nil <|
  .letOp .indexLogicalShiftRight
    (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .letOp .indexWrappingAdd (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def rightBody := Region.bind helper14Body rightTail

/-- This is the second position already used by the original FRI source
connection. Its equation follows by the common word-operation constructor. -/
theorem right_value (model : DomainModel) (position rows : Nat) :
    rightBody.denote (meaning model [])
      (show Values model.Value [.index, .index] from .cons position (.cons rows .nil)).get =
    .done (.cons (wrappingAdd (bitAnd position (wrappingSubtract (logicalShiftRight rows 1) 1))
      (logicalShiftRight rows 1)) .nil) := by
  derive_word_process

def rightRegion : InstructionRegion :=
  ⟨captures.map .data, region.instructions ++
    [⟨.calculate (.indexConstant 1), [], [.data .index], []⟩,
     ⟨.calculate .indexLogicalShiftRight, [1, 14], [.data .index], []⟩,
     ⟨.calculate .indexWrappingAdd, [13, 15], [.data .index], []⟩], [16]⟩

def rightTarget : TargetBlock := spine.plug fun model ↦
  Domain.View.sequence (Domain.View.calculation model (.indexConstant 1) [] [.data .index])
    (Domain.View.sequence (Domain.View.calculation model .indexLogicalShiftRight [1, 14] [.data .index])
    (Domain.View.sequence (Domain.View.calculation model .indexWrappingAdd [13, 15] [.data .index])
      Domain.View.empty))

/-- The second query reuses the same original pair computation, followed by
the source's shift and addition. Source result and row order stay explicit. -/
def rightConnected : Alignment [] rightBody [.data 8, .data 1] 9 rightTarget [16] 17 := by
  apply Alignment.bind rfl connected
  derive_math_region

noncomputable def actualRight (model : DomainModel) (program : Program) (context : Context)
    (values : Values model.Value captures) (environment : Domain.Environment model.toCarriers)
    (references : List Nat)
    (read : Domain.read environment references = Domain.encodeValues values) :
    Original.Simulation (fun result frame ↦ frame = environment ++ Original.encodeHelperResult result)
      (fun _ frame ↦ ArtifactBinding.Captures environment frame)
      ((rightBody.denote (meaning model []) (selected.eval values.get).get).interpret
        (closedLift (I := Domain.effects model.toCarriers)))
      (Domain.step model program context ⟨.mathCompute, references, [.data .index], [rightRegion]⟩
        environment) :=
  rightConnected.embedded (region := rightRegion) selected rfl model program context rfl rfl
    (by intro frame; rfl) rfl rfl rfl values environment references read

#print axioms rightConnected
#print axioms actualRight
#print axioms right_value
end Tests.FriQueryPositions
