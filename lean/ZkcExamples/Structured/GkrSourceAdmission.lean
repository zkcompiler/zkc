module

public import ZkcExamples.Structured.GkrSourceGuards
public import ZkcExamples.Structured.SumcheckVerifierHelpers

@[expose] public section

/-! The current GKR validator's actual admission prefix. These statements are
about its retained participant, before any circuit representation is selected. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

namespace ZkcExamples.Structured.GkrSourceAdmission
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary SumcheckVerifierHelpers

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
private theorem present_cons {ty : Ty} {types : List Ty}
    (value : assignment F G ty) (rest : Values (assignment F G) types) :
    (Values.cons value rest).present = Values.cons (some value) rest.present := rfl

def inputs (initial outputs add mul : List F) (layers selector width handle : Nat) :
    Values (Component (assignment F G)) GkrSourceBodies.gkrSignature.inputs :=
  .cons (some initial) (.cons (some outputs) (.cons (some add) (.cons (some mul)
    (.cons (some layers) (.cons (some selector) (.cons (some width) (.cons (some handle) .nil)))))))

def participant (initial outputs add mul : List F) (layers selector width handle : Nat) :=
  GkrSourceViews.program.participant F G 1 (inputs (G := G) initial outputs add mul layers selector width handle)

private theorem plain_view_as (definition : CheckedProtocol)
    (member : definition ∈ GkrSourceViews.unit.protocols)
    (signature : ProtocolSignature) (same : definition.signature = signature)
    (region : Region protocolDialect signature.inputs signature.outputs)
    (raw : definition.raw = region.erase) (ctx : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) signature.inputs) :
    invokeProtocol (GkrSourceViews.unit.plainProtocolTable F G) signature ctx self args =
      (region.denote (participantMeaningWith (.silent _) (participantActions F G)
        (plainHelpers (F := F) (G := G) GkrSourceViews.unit) self
        (GkrSourceViews.unit.plainProtocolTable F G) ctx)
        (maskValues self (ctx.mapScopes signature.inputScopes) args).get).bind
          (fun results => .done (maskValues self (ctx.mapScopes signature.outputScopes) results)) := by
  subst signature
  exact protocol_invoke_body_view (.silent _) (participantActions F G)
    (plainHelpers (F := F) (G := G) GkrSourceViews.unit)
    GkrSourceViews.unit.protocols GkrSourceViews.unit.protocolsLinked
    definition member region raw ctx self args

theorem body (initial outputs add mul : List F) (layers selector width handle : Nat) :
    participant (G := G) initial outputs add mul layers selector width handle =
      (GkrSourceBodies.gkrBody.denote
        (participantMeaningWith (.silent _) (participantActions F G)
          (plainHelpers (F := F) (G := G) GkrSourceViews.unit) 1
          (GkrSourceViews.unit.plainProtocolTable F G) {})
        (inputs (G := G) initial outputs add mul layers selector width handle).get).bind
          (fun results => .done results) := by
  unfold participant
  refine (GkrSourceViews.unit.protocolTable_forgetSites (F := F) (G := G)
    GkrSourceBodies.gkrSignature {} 1 _).trans ?_
  have view := plain_view_as
    GkrSourceViews.gkrDefinition GkrSourceViews.gkr_member
    GkrSourceBodies.gkrSignature GkrSourceViews.gkr_signature
    GkrSourceBodies.gkrBody GkrSourceViews.gkr_raw ({} : ProtocolContext) 1
    (inputs (G := G) initial outputs add mul layers selector width handle)
  change _ = (GkrSourceBodies.gkrBody.denote
    (participantMeaningWith (.silent _) (participantActions F G)
      (plainHelpers (F := F) (G := G) GkrSourceViews.unit) 1
      (GkrSourceViews.unit.plainProtocolTable F G) {})
    (maskValues 1 [[0, 1], [1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [1]]
      (inputs (G := G) initial outputs add mul layers selector width handle)).get).bind
        (fun results => .done (maskValues 1 [[1]] results)) at view
  have masked : maskValues 1 [[0, 1], [1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [1]]
      (inputs (G := G) initial outputs add mul layers selector width handle) =
    inputs (G := G) initial outputs add mul layers selector width handle := by
    simp [inputs, GkrSourceBodies.gkrSignature, maskValues, Participant.restrict]
  have out (results : Values (Component (assignment F G)) [.boolean]) :
      maskValues 1 [[1]] results = results := by
    cases results with | cons value rest => cases rest; rfl
  simpa only [masked, out] using view

theorem comparison_plain (a b : Nat) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      PrimitiveShapeViews.lessHelper (.cons a (.cons b .nil)) =
      if a < indexLimit ∧ b < indexLimit then .done (boolResult (decide (a < b)))
      else .halt .refused := by
  rw [closed_invoke_plain]
  change (invoke (GkrSourceGuards.helpers (F := F) (G := G)) _ _).interpret _ = _
  rw [GkrSourceGuards.comparison_all]
  split <;> rfl

theorem shape_plain (xs : List F) (dimension : Nat) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      PrimitiveShapeViews.shapeHelper (PrimitiveLibrary.inputs xs dimension 1) =
      if dimension < indexLimit then
        if dimension < 64 then
          if xs.length < indexLimit then
            .done (boolResult (decide (xs.length = 2 ^ dimension)))
          else .halt .exhausted
        else .done (boolResult false)
      else .halt .refused := by
  rw [closed_invoke_plain]
  change (invoke (GkrSourceGuards.helpers (F := F) (G := G)) _ _).interpret _ = _
  rw [GkrSourceGuards.shape_all]
  by_cases representable : dimension < indexLimit <;>
    by_cases small : dimension < 64 <;> by_cases bounded : xs.length < indexLimit <;>
      simp [representable, small, bounded, PIR.Process.interpret]

theorem shape_plain_values (xs : List F) (dimension : Nat) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper4Helper (.cons xs (.cons dimension (.cons 1 .nil))) =
      if dimension < indexLimit then
        if dimension < 64 then
          if xs.length < indexLimit then
            .done (boolResult (decide (xs.length = 2 ^ dimension)))
          else .halt .exhausted
        else .done (boolResult false)
      else .halt .refused := shape_plain xs dimension

theorem index_add_plain (a b : Nat) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.sourceHelper4Helper (.cons a (.cons b .nil)) =
      if a < indexLimit ∧ b < indexLimit ∧ a + b < indexLimit then
        .done (.cons (a + b) .nil) else .halt .refused := by
  rw [closed_invoke_plain]
  change (invoke (GkrSourceGuards.helpers (F := F) (G := G)) _ _).interpret _ = _
  rw [GkrSourceGuards.index_add_all]
  split <;> rfl

theorem power_plain (exponent : Nat) (small : exponent < 64) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper18Helper (.cons exponent .nil) =
      .done (.cons (2 ^ exponent) .nil) := by
  rw [closed_invoke_plain]
  change (invoke (GkrSourceGuards.helpers (F := F) (G := G)) _ _).interpret _ = _
  rw [GkrSourceGuards.power_bounded exponent small]
  rfl

/-- Above the declared width, the new explicit guard rejects representable
inputs and preserves the checked-index refusal for unrepresentable inputs. -/
theorem width_refuses (initial outputs add mul : List F) (layers selector width handle : Nat)
    (outside : 4 < width) :
    participant (G := G) initial outputs add mul layers selector width handle =
      .halt (if width < indexLimit then .reject else .refused) := by
  rw [body]
  unfold GkrSourceBodies.gkrBody
  by_cases representable : width < indexLimit <;>
    repeat' (rw [Region.denote]; simp [participantMeaningWith,
    protocolOperationWith, Operands.eval, Regions.denote, Values.get,
    Environment.prepend, Environment.push, inputs, PIR.Process.bind,
    SiteObservations.silent, comparison_plain, Primitive.evaluate, primitiveOutcome,
    show 4 < indexLimit by decide, true_and, outside, decide_true,
    representable, ite_true, ite_false, Participant.restrict, ProtocolContext.roles,
    Evaluation.componentOperation, strictComponent,
    Participant.owned, Participant.guard, RoleFamily.sequence,
    boolResult, present_cons, Values.present, PIR.Process.interpret, participantActions,
    Evaluation.meaning, Evaluation.operation, Op.calculationRegions,
    GkrSourceBodies.gkrSignature, Op.results])


/-- The layer bound is checked before any output challenge. -/
theorem layers_refuses (initial outputs add mul : List F) (layers selector width handle : Nat)
    (widthBound : width ≤ 4) (outside : 4 < layers) :
    participant (G := G) initial outputs add mul layers selector width handle =
      .halt (if layers < indexLimit then .reject else .refused) := by
  rw [body]
  unfold GkrSourceBodies.gkrBody
  have widthSmall : width < indexLimit := lt_of_le_of_lt widthBound (by decide)
  have widthCheck : ¬ 4 < width := by omega
  by_cases representable : layers < indexLimit <;>
    repeat' (rw [Region.denote]; simp [participantMeaningWith,
    protocolOperationWith, Operands.eval, Regions.denote, Values.get,
    Environment.prepend, Environment.push, inputs, PIR.Process.bind,
    SiteObservations.silent, comparison_plain, Primitive.evaluate, primitiveOutcome,
    show 4 < indexLimit by decide, true_and, outside, widthSmall, widthCheck, decide_true,
    representable, ite_true, ite_false, Participant.restrict, ProtocolContext.roles,
    Evaluation.componentOperation, strictComponent,
    Participant.owned, Participant.guard, RoleFamily.sequence,
    boolResult, present_cons, Values.present, PIR.Process.interpret, participantActions,
    Evaluation.meaning, Evaluation.operation, Op.calculationRegions,
    GkrSourceBodies.gkrSignature, Op.results])

/-- Unused wiring still has to have its full shape at zero layers. -/
theorem zero_add_refuses (a b : F) (mul : List F) (handle : Nat) :
    participant (G := G) [a] [b] [] mul 0 0 0 handle = .halt .reject := by
  rw [body]
  unfold GkrSourceBodies.gkrBody
  repeat' (rw [Region.denote]; simp [participantMeaningWith,
    protocolOperationWith, Operands.eval, Regions.denote, Values.get,
    Environment.prepend, Environment.push, inputs, PIR.Process.bind,
    SiteObservations.silent, comparison_plain, Primitive.evaluate, primitiveOutcome,
    show 4 < indexLimit by decide, show 0 < indexLimit by decide,
    show 1 < indexLimit by decide, true_and, decide_true,
     ite_true, ite_false, Participant.restrict, ProtocolContext.roles,
    Evaluation.componentOperation, strictComponent,
    Participant.owned, Participant.guard, RoleFamily.sequence,
    boolResult, present_cons, Values.present, PIR.Process.interpret, participantActions,
    Evaluation.meaning, Evaluation.operation, Op.calculationRegions,
    GkrSourceBodies.gkrSignature, Op.results, shape_plain_values, index_add_plain])

theorem zero_mul_refuses (a b gate : F) (handle : Nat) :
    participant (G := G) [a] [b] [gate] [] 0 0 0 handle = .halt .reject := by
  rw [body]
  unfold GkrSourceBodies.gkrBody
  repeat' (rw [Region.denote]; simp [participantMeaningWith,
    protocolOperationWith, Operands.eval, Regions.denote, Values.get,
    Environment.prepend, Environment.push, inputs, PIR.Process.bind,
    SiteObservations.silent, comparison_plain, Primitive.evaluate, primitiveOutcome,
    show 4 < indexLimit by decide, show 0 < indexLimit by decide,
    show 1 < indexLimit by decide, true_and, decide_true,
     ite_true, ite_false, Participant.restrict, ProtocolContext.roles,
    Evaluation.componentOperation, strictComponent,
    Participant.owned, Participant.guard, RoleFamily.sequence,
    boolResult, present_cons, Values.present, PIR.Process.interpret, participantActions,
    Evaluation.meaning, Evaluation.operation, Op.calculationRegions,
    GkrSourceBodies.gkrSignature, Op.results, shape_plain_values, index_add_plain])

/-- Every malformed input table stops before any challenge, including a list
whose length cannot be represented by a machine index. -/
theorem initial_refuses (initial outputs add mul : List F) (layers selector width handle : Nat)
    (widthBound : width ≤ 4) (layersBound : layers ≤ 4)
    (malformed : initial.length ≠ 2 ^ width) :
    participant (G := G) initial outputs add mul layers selector width handle =
      .halt (if initial.length < indexLimit then .reject else .exhausted) := by
  rw [body]
  unfold GkrSourceBodies.gkrBody
  have widthSmall : width < indexLimit := lt_of_le_of_lt widthBound (by decide)
  have layerSmall : layers < indexLimit := lt_of_le_of_lt layersBound (by decide)
  have dimensionSmall : width < 64 := by omega
  have widthCheck : ¬ 4 < width := by omega
  have layerCheck : ¬ 4 < layers := by omega
  by_cases tableBound : initial.length < indexLimit <;>
    repeat' (rw [Region.denote]; simp [participantMeaningWith,
      protocolOperationWith, Operands.eval, Regions.denote, Values.get,
      Environment.prepend, Environment.push, inputs, PIR.Process.bind,
      SiteObservations.silent, comparison_plain, Primitive.evaluate, primitiveOutcome,
      show 4 < indexLimit by decide, show 1 < indexLimit by decide,
      widthSmall, layerSmall, dimensionSmall, widthCheck, layerCheck, tableBound,
      malformed, Participant.restrict, ProtocolContext.roles,
      Evaluation.componentOperation, strictComponent, Participant.owned,
      Participant.guard, RoleFamily.sequence, boolResult, present_cons, Values.present,
      PIR.Process.interpret, participantActions, Evaluation.meaning, Evaluation.operation,
      Op.calculationRegions, GkrSourceBodies.gkrSignature, Op.results, shape_plain_values])

/-- The claimed output has its own shape check; its contents are not an
assumption of the source input policy. -/
theorem outputs_refuse (initial outputs add mul : List F) (layers selector width handle : Nat)
    (widthBound : width ≤ 4) (layersBound : layers ≤ 4)
    (initialShape : initial.length = 2 ^ width) (malformed : outputs.length ≠ 2 ^ width) :
    participant (G := G) initial outputs add mul layers selector width handle =
      .halt (if outputs.length < indexLimit then .reject else .exhausted) := by
  rw [body]
  unfold GkrSourceBodies.gkrBody
  have widthSmall : width < indexLimit := lt_of_le_of_lt widthBound (by decide)
  have layerSmall : layers < indexLimit := lt_of_le_of_lt layersBound (by decide)
  have dimensionSmall : width < 64 := by omega
  have widthCheck : ¬ 4 < width := by omega
  have layerCheck : ¬ 4 < layers := by omega
  have initialBound : initial.length < indexLimit := by
    rw [initialShape]
    exact power_bound width dimensionSmall
  by_cases tableBound : outputs.length < indexLimit <;>
    repeat' (rw [Region.denote]; simp [participantMeaningWith,
      protocolOperationWith, Operands.eval, Regions.denote, Values.get,
      Environment.prepend, Environment.push, inputs, PIR.Process.bind,
      SiteObservations.silent, comparison_plain, Primitive.evaluate, primitiveOutcome,
      show 4 < indexLimit by decide, show 1 < indexLimit by decide,
      widthSmall, layerSmall, dimensionSmall, widthCheck, layerCheck, tableBound,
      malformed, Participant.restrict, ProtocolContext.roles,
      Evaluation.componentOperation, strictComponent, Participant.owned,
      Participant.guard, RoleFamily.sequence, boolResult, present_cons, Values.present,
      PIR.Process.interpret, participantActions, Evaluation.meaning, Evaluation.operation,
      Op.calculationRegions, GkrSourceBodies.gkrSignature, Op.results, shape_plain_values,
      initialShape, initialBound, power_bound width dimensionSmall])


/-- The add wiring is checked even when no layer is executed. -/
theorem add_refuses (initial outputs add mul : List F) (layers selector width handle : Nat)
    (widthBound : width ≤ 4) (layersBound : layers ≤ 4)
    (initialShape : initial.length = 2 ^ width) (outputShape : outputs.length = 2 ^ width)
    (dimensions : selector + width + width + width < 64)
    (malformed : add.length ≠ 2 ^ (selector + width + width + width)) :
    participant (G := G) initial outputs add mul layers selector width handle =
      .halt (if add.length < indexLimit then .reject else .exhausted) := by
  rw [body]
  unfold GkrSourceBodies.gkrBody
  have widthSmall : width < indexLimit := lt_of_le_of_lt widthBound (by decide)
  have layerSmall : layers < indexLimit := lt_of_le_of_lt layersBound (by decide)
  have dimensionSmall : width < 64 := by omega
  have widthCheck : ¬ 4 < width := by omega
  have layerCheck : ¬ 4 < layers := by omega
  have machineDimension : 64 < indexLimit := by decide
  have selectorBound : selector < indexLimit := by omega
  have firstBound : selector + width < indexLimit := by omega
  have secondBound : selector + width + width < indexLimit := by omega
  have thirdBound : selector + width + width + width < indexLimit := by omega
  by_cases tableBound : add.length < indexLimit <;>
    repeat' (rw [Region.denote]; simp [participantMeaningWith,
      protocolOperationWith, Operands.eval, Regions.denote, Values.get,
      Environment.prepend, Environment.push, inputs, PIR.Process.bind,
      SiteObservations.silent, comparison_plain, Primitive.evaluate, primitiveOutcome,
      show 4 < indexLimit by decide, show 1 < indexLimit by decide,
      widthSmall, layerSmall, dimensionSmall, widthCheck, layerCheck, tableBound,
      malformed, Participant.restrict, ProtocolContext.roles,
      Evaluation.componentOperation, strictComponent, Participant.owned,
      Participant.guard, RoleFamily.sequence, boolResult, present_cons, Values.present,
      PIR.Process.interpret, participantActions, Evaluation.meaning, Evaluation.operation,
      Op.calculationRegions, GkrSourceBodies.gkrSignature, Op.results, shape_plain_values,
      initialShape, outputShape, power_bound width dimensionSmall, index_add_plain,
      selectorBound, firstBound, secondBound, thirdBound, dimensions, ← Nat.add_assoc])


/-- The mul wiring is checked even when no layer is executed. -/
theorem mul_refuses (initial outputs add mul : List F) (layers selector width handle : Nat)
    (widthBound : width ≤ 4) (layersBound : layers ≤ 4)
    (initialShape : initial.length = 2 ^ width) (outputShape : outputs.length = 2 ^ width)
    (dimensions : selector + width + width + width < 64)
    (addShape : add.length = 2 ^ (selector + width + width + width))
    (malformed : mul.length ≠ 2 ^ (selector + width + width + width)) :
    participant (G := G) initial outputs add mul layers selector width handle =
      .halt (if mul.length < indexLimit then .reject else .exhausted) := by
  rw [body]
  unfold GkrSourceBodies.gkrBody
  have widthSmall : width < indexLimit := lt_of_le_of_lt widthBound (by decide)
  have layerSmall : layers < indexLimit := lt_of_le_of_lt layersBound (by decide)
  have dimensionSmall : width < 64 := by omega
  have widthCheck : ¬ 4 < width := by omega
  have layerCheck : ¬ 4 < layers := by omega
  have machineDimension : 64 < indexLimit := by decide
  have selectorBound : selector < indexLimit := by omega
  have firstBound : selector + width < indexLimit := by omega
  have secondBound : selector + width + width < indexLimit := by omega
  have thirdBound : selector + width + width + width < indexLimit := by omega
  by_cases tableBound : mul.length < indexLimit <;>
    repeat' (rw [Region.denote]; simp [participantMeaningWith,
      protocolOperationWith, Operands.eval, Regions.denote, Values.get,
      Environment.prepend, Environment.push, inputs, PIR.Process.bind,
      SiteObservations.silent, comparison_plain, Primitive.evaluate, primitiveOutcome,
      show 4 < indexLimit by decide, show 1 < indexLimit by decide,
      widthSmall, layerSmall, dimensionSmall, widthCheck, layerCheck, tableBound,
      malformed, Participant.restrict, ProtocolContext.roles,
      Evaluation.componentOperation, strictComponent, Participant.owned,
      Participant.guard, RoleFamily.sequence, boolResult, present_cons, Values.present,
      PIR.Process.interpret, participantActions, Evaluation.meaning, Evaluation.operation,
      Op.calculationRegions, GkrSourceBodies.gkrSignature, Op.results, shape_plain_values,
      initialShape, outputShape, power_bound width dimensionSmall, index_add_plain,
      selectorBound, firstBound, secondBound, thirdBound, dimensions, ← Nat.add_assoc, addShape, power_bound _ dimensions])


/-- Oversized selector dimensions preserve every checked-index refusal. A
representable dimension of at least 64 fails the actual shape guard. -/
theorem dimensions_refuse (initial outputs add mul : List F) (layers selector width handle : Nat)
    (widthBound : width ≤ 4) (layersBound : layers ≤ 4)
    (initialShape : initial.length = 2 ^ width) (outputShape : outputs.length = 2 ^ width)
    (outside : ¬ selector + width + width + width < 64) :
    participant (G := G) initial outputs add mul layers selector width handle =
      .halt (if selector + width + width + width < indexLimit then .reject else .refused) := by
  rw [body]
  unfold GkrSourceBodies.gkrBody
  have widthSmall : width < indexLimit := lt_of_le_of_lt widthBound (by decide)
  have layerSmall : layers < indexLimit := lt_of_le_of_lt layersBound (by decide)
  have dimensionSmall : width < 64 := by omega
  have widthCheck : ¬ 4 < width := by omega
  have layerCheck : ¬ 4 < layers := by omega
  by_cases selectorBound : selector < indexLimit <;>
    by_cases firstBound : selector + width < indexLimit <;>
    by_cases secondBound : selector + width + width < indexLimit <;>
    by_cases thirdBound : selector + width + width + width < indexLimit
  all_goals try omega
  all_goals
    repeat' (rw [Region.denote]; simp [participantMeaningWith,
      protocolOperationWith, Operands.eval, Regions.denote, Values.get,
      Environment.prepend, Environment.push, inputs, PIR.Process.bind,
      SiteObservations.silent, comparison_plain, Primitive.evaluate, primitiveOutcome,
      show 4 < indexLimit by decide, show 1 < indexLimit by decide,
      widthSmall, layerSmall, dimensionSmall, widthCheck, layerCheck,
      Participant.restrict, ProtocolContext.roles,
      Evaluation.componentOperation, strictComponent, Participant.owned,
      Participant.guard, RoleFamily.sequence, boolResult, present_cons, Values.present,
      PIR.Process.interpret, participantActions, Evaluation.meaning, Evaluation.operation,
      Op.calculationRegions, GkrSourceBodies.gkrSignature, Op.results, shape_plain_values,
      initialShape, outputShape, power_bound width dimensionSmall, index_add_plain,
      selectorBound, firstBound, secondBound, thirdBound, outside, ← Nat.add_assoc])


/-- A shape-correct wiring stack must still cover every requested layer. -/
theorem capacity_refuses (initial outputs add mul : List F) (layers selector width handle : Nat)
    (widthBound : width ≤ 4) (layersBound : layers ≤ 4)
    (initialShape : initial.length = 2 ^ width) (outputShape : outputs.length = 2 ^ width)
    (dimensions : selector + width + width + width < 64)
    (addShape : add.length = 2 ^ (selector + width + width + width))
    (mulShape : mul.length = 2 ^ (selector + width + width + width))
    (outside : ¬ layers ≤ 2 ^ selector) :
    participant (G := G) initial outputs add mul layers selector width handle = .halt .reject := by
  rw [body]
  unfold GkrSourceBodies.gkrBody
  have widthSmall : width < indexLimit := lt_of_le_of_lt widthBound (by decide)
  have layerSmall : layers < indexLimit := lt_of_le_of_lt layersBound (by decide)
  have dimensionSmall : width < 64 := by omega
  have selectorSmall : selector < 64 := by omega
  have widthCheck : ¬ 4 < width := by omega
  have layerCheck : ¬ 4 < layers := by omega
  have machineDimension : 64 < indexLimit := by decide
  have selectorBound : selector < indexLimit := by omega
  have firstBound : selector + width < indexLimit := by omega
  have secondBound : selector + width + width < indexLimit := by omega
  have thirdBound : selector + width + width + width < indexLimit := by omega
  have capacityCheck : 2 ^ selector < layers := by omega
  repeat' (rw [Region.denote]; simp [participantMeaningWith,
    protocolOperationWith, Operands.eval, Regions.denote, Values.get,
    Environment.prepend, Environment.push, inputs, PIR.Process.bind,
    SiteObservations.silent, comparison_plain, Primitive.evaluate, primitiveOutcome,
    show 4 < indexLimit by decide, show 1 < indexLimit by decide,
    widthSmall, layerSmall, dimensionSmall, widthCheck, layerCheck,
    Participant.restrict, ProtocolContext.roles,
    Evaluation.componentOperation, strictComponent, Participant.owned,
    Participant.guard, RoleFamily.sequence, boolResult, present_cons, Values.present,
    PIR.Process.interpret, participantActions, Evaluation.meaning, Evaluation.operation,
    Op.calculationRegions, GkrSourceBodies.gkrSignature, Op.results, shape_plain_values,
    initialShape, outputShape, power_bound width dimensionSmall, index_add_plain,
    selectorBound, firstBound, secondBound, thirdBound, dimensions, ← Nat.add_assoc,
    addShape, mulShape, power_bound _ dimensions, power_plain _ selectorSmall,
    power_bound selector selectorSmall, capacityCheck])

end ZkcExamples.Structured.GkrSourceAdmission
