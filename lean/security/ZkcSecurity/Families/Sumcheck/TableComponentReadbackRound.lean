module

public import ZkcSecurity.Families.Sumcheck.CompiledRound
public import ZkcSecurity.FiatShamir.HonestReadbackLoops
public import Mathlib.Tactic.FailIfNoProgress

@[expose] public section

/-! Reusable honest coupling for the actual table producer and scalar validator
round schemas. Exact generated block equations instantiate this library once
per source occurrence; all retained captures and SSA offsets are arbitrary. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace ZkcSecurity.Families.Sumcheck.TableComponent.ReadbackRound
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir
open Zkc.Polynomial.Multilinear

private theorem getInternal_suffix {α : Type} (captured suffix : List α) (index : Nat) :
    (captured ++ suffix).get?Internal (captured.length + index) = suffix.get?Internal index :=
  CompiledRound.lookup_suffix captured suffix index

private theorem getInternal_zero {α : Type} (head : α) (tail : List α) :
    (head :: tail).get?Internal 0 = some head := rfl

private theorem getInternal_succ {α : Type} (head : α) (tail : List α) (index : Nat) :
    (head :: tail).get?Internal (index + 1) = tail.get?Internal index := rfl

structure Plan extends CompiledRound.Plan where
  field : String
  validator : String
  sumsHelper : String
  firstHelper : String

def producerBlock {F G : Type} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (plan : Plan) (program : Structured.Program)
    (context : Context) (offset : Nat) : Domain.View.Block (ringModel F G).toCarriers :=
  let field := plan.field
  Domain.View.sequence (Domain.View.helper (ringModel F G) program plan.sumsHelper
    [offset + 1, offset + 2, offset + 3] [.data (.field field), .data (.field field)]) (
  Domain.View.sequence (Domain.View.send plan.lowSite plan.lowSite plan.validator (offset + 6) []) (
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) (
  Domain.View.sequence (Domain.View.indicesAppend (offset + 8) offset [.indices]) (
  Domain.View.sequence (Domain.View.observe context context.suite plan.lowTemplate
    (offset + 5) (offset + 6) (offset + 9) [.transcript context.suite]) (
  Domain.View.sequence (Domain.View.send plan.highSite plan.highSite plan.validator (offset + 7) []) (
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) (
  Domain.View.sequence (Domain.View.indicesAppend (offset + 11) offset [.indices]) (
  Domain.View.sequence (Domain.View.observe context context.suite plan.highTemplate
    (offset + 10) (offset + 7) (offset + 12) [.transcript context.suite]) (
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) (
  Domain.View.sequence (Domain.View.indicesAppend (offset + 14) offset [.indices]) (
  Domain.View.sequence (Domain.View.challenge context context.suite field plan.queryTemplate
    (offset + 13) (offset + 15) [.data (.field field), .transcript context.suite]) (
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) (
  Domain.View.sequence (Domain.View.indicesAppend (offset + 18) offset [.indices]) (
  Domain.View.sequence (Domain.View.observe context context.suite plan.deliveryTemplate
    (offset + 17) (offset + 16) (offset + 19) [.transcript context.suite]) (
  Domain.View.sequence (Domain.View.helper (ringModel F G) program plan.firstHelper
    [offset + 1, offset + 2, offset + 3, offset + 16]
    [.data (.vector field), .data .index, .data .index]) (
  Domain.View.sequence (Domain.View.helper (ringModel F G) program plan.appendHelper
    [offset + 4, offset + 16] [.data (.vector field)]) Domain.View.empty))))))))))))))))

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Semantic equations are supplied by the example's complete admitted bodies.
The family has no dependency on a particular source definition or helper name. -/
structure HelperLaws (program : Structured.Program) (plan : Plan) : Prop where
  sums : ∀ raw dimension, raw.length = 2 ^ dimension → raw.length < indexLimit →
    dimension < 64 → 0 < dimension →
    Domain.callHelper (ringModel F G) program plan.sumsHelper
      [.data (.field plan.field), .data (.field plan.field)]
      [.data (.vector plan.field raw), .data (.index dimension), .data (.index 1)] =
      .returned [.data (.field plan.field (raw.take (raw.length / 2)).sum),
        .data (.field plan.field (raw.drop (raw.length / 2)).sum)]
  first : ∀ raw dimension challenge, raw.length = 2 ^ dimension → raw.length < indexLimit →
    dimension < 64 → 0 < dimension →
    Domain.callHelper (ringModel F G) program plan.firstHelper
      [.data (.vector plan.field), .data .index, .data .index]
      [.data (.vector plan.field raw), .data (.index dimension), .data (.index 1),
        .data (.field plan.field challenge)] =
      .returned [.data (.vector plan.field (restrictValues raw challenge)),
        .data (.index (dimension - 1)), .data (.index 1)]
  append : ∀ point challenge,
    Domain.callHelper (ringModel F G) program plan.appendHelper [.data (.vector plan.field)]
      [.data (.vector plan.field point), .data (.field plan.field challenge)] =
      .returned [.data (.vector plan.field (point ++ [challenge]))]

theorem readback (plan : Plan) (program : Structured.Program)
    (helpers : HelperLaws (F := F) (G := G) program plan)
    (context : Context) (index : Nat)
    (low high query delivery : Origin)
    (lowFound : Domain.templateOrigin context plan.lowTemplate [index] = some low)
    (highFound : Domain.templateOrigin context plan.highTemplate [index] = some high)
    (queryFound : Domain.queryOrigin context context.suite plan.field plan.queryTemplate [index] = some query)
    (deliveryFound : Domain.templateOrigin context plan.deliveryTemplate [index] = some delivery)
    (lowMessage : low.request = none) (highMessage : high.request = none)
    (deliveryMessage : delivery.request = none) (request : query.request = some (.draw plan.field))
    (leftCaptured rightCaptured : Domain.Environment (ringModel F G).toCarriers)
    (raw point : List F) (dimension : Nat)
    (shape : raw.length = 2 ^ dimension)
    (bounded : raw.length < indexLimit) (dimensionSmall : dimension < 64)
    (positive : 0 < dimension)
    (history : Domain.History (ringModel F G).toCarriers) :
    Readback
      (fun left right => ∃ challenge : F,
        Domain.read left [leftCaptured.length + 21, leftCaptured.length + 22, leftCaptured.length + 23,
            leftCaptured.length + 24, leftCaptured.length + 20] = some
          [.data (.vector plan.field (restrictValues raw challenge)), .data (.index (dimension - 1)),
            .data (.index 1), .data (.vector plan.field (point ++ [challenge])),
            .transcript context.suite (TableComponent.Execution.finalHistory plan.field low high query delivery
              history (raw.take (raw.length / 2)).sum (raw.drop (raw.length / 2)).sum challenge)] ∧
        Domain.read right [rightCaptured.length + 21, rightCaptured.length + 26, rightCaptured.length + 20] = some
          [.data (.vector plan.field (point ++ [challenge])),
            .data (.field plan.field ((1 - challenge) * (raw.take (raw.length / 2)).sum +
              challenge * (raw.drop (raw.length / 2)).sum)),
            .transcript context.suite (TableComponent.Execution.finalHistory plan.field low high query delivery
              history (raw.take (raw.length / 2)).sum (raw.drop (raw.length / 2)).sum challenge)])
      (producerBlock plan program context leftCaptured.length
        (leftCaptured ++ [.data (.index index), .data (.vector plan.field raw), .data (.index dimension),
          .data (.index 1), .data (.vector plan.field point), .transcript context.suite history]))
      (CompiledRound.block plan.toPlan program context plan.field rightCaptured.length
        (CompiledRound.input plan.field context.suite rightCaptured index point raw.sum history)) := by
  have sumsLaw := helpers.sums raw dimension shape bounded dimensionSmall positive
  have firstLaw := helpers.first raw dimension
  have appendLaw := helpers.append point
  have boundary : raw.sum = (raw.take (raw.length / 2)).sum + (raw.drop (raw.length / 2)).sum := by
    rw [← List.sum_append, List.take_append_drop]
  simp only [producerBlock, CompiledRound.block, Domain.View.sequence, CompiledRound.input]
  repeat first
    | with_reducible apply Readback.checkpointLeft
    | with_reducible apply Readback.checkpointRight
    | with_reducible apply Readback.observeLeft
    | with_reducible apply Readback.observeRight
    | with_reducible refine Readback.sendReceive (carriers := (ringModel F G).toCarriers) (ty := .field plan.field) _ _ _ _ _ _ (.field plan.field (raw.take (raw.length / 2)).sum) (raw.take (raw.length / 2)).sum (by simp [Domain.Payload.value]) ?_
    | with_reducible refine Readback.sendReceive (carriers := (ringModel F G).toCarriers) (ty := .field plan.field) _ _ _ _ _ _ (.field plan.field (raw.drop (raw.length / 2)).sum) (raw.drop (raw.length / 2)).sum (by simp [Domain.Payload.value]) ?_
    | fail_if_no_progress (with_reducible rw [sumsLaw])
    | fail_if_no_progress (with_reducible rw [Domain.Calculations.fieldAdd (F := F) (G := G)])
    | fail_if_no_progress (with_reducible rw [Domain.Calculations.fieldEqual (F := F) (G := G)])
    | fail_if_no_progress (simp only [Domain.View.helper, Domain.View.send, Domain.View.receive,
        Domain.View.guard, Domain.View.indicesEmpty, Domain.View.indicesAppend,
        Domain.View.observe, Domain.View.challenge, Domain.View.calculation, Domain.View.empty,
        Domain.View.append, Domain.read, Domain.Value.encode, Domain.Payload.ofValue,
        Domain.sortsMatch, Domain.Value.sort, Domain.Payload.ty, Domain.dataType, List.append_assoc,
        lowFound, highFound, queryFound, deliveryFound, lowMessage, highMessage, deliveryMessage, request,
        boundary, PIR.Process.bind, List.mapM_cons, List.mapM_nil, List.getElem?_cons_zero, List.getElem?_cons_succ,
        List.cons_append, List.nil_append, Bind.bind, Option.bind, Option.pure_def, Option.map_some,
        List.map_cons, List.map_nil, beq_self_eq_true, and_self, decide_true,
        and_true, CompiledRound.lookup_suffix, CompiledRound.lookup_first_suffix,
        ↓reduceIte, ↓reduceDIte,
        ])
    | fail_if_no_progress (dsimp only [Bind.bind, Pure.pure, instMonadOption,
        Option.bind, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal])
  refine .query _ _ (DomainReduction.drawRequest_of_request request) ?_
  intro reply
  let challenge : F := by simpa only [Domain.Raw, request, Request.draw] using reply
  have firstReturned := firstLaw challenge shape bounded dimensionSmall positive
  have appendReturned := appendLaw challenge
  repeat first
    | with_reducible apply Readback.checkpointLeft
    | with_reducible apply Readback.checkpointRight
    | with_reducible apply Readback.observeLeft
    | with_reducible apply Readback.observeRight
    | fail_if_no_progress (with_reducible rw [firstReturned])
    | fail_if_no_progress (with_reducible rw [appendReturned])
    | fail_if_no_progress (with_reducible rw [Domain.Calculations.fieldConstant (F := F) (G := G)])
    | fail_if_no_progress (with_reducible rw [Domain.Calculations.fieldSubtract (F := F) (G := G)])
    | fail_if_no_progress (with_reducible rw [Domain.Calculations.fieldMultiply (F := F) (G := G)])
    | fail_if_no_progress (with_reducible rw [Domain.Calculations.fieldAdd (F := F) (G := G)])
    | fail_if_no_progress (simp only [Domain.Value.sort, Domain.Payload.ty, List.append_assoc,
        PIR.Process.bind, List.cons_append, List.nil_append, List.map_cons, List.map_nil, beq_self_eq_true, getInternal_suffix, getInternal_zero, getInternal_succ, ↓reduceIte, ])
    | fail_if_no_progress (dsimp only [Bind.bind, Pure.pure, instMonadOption,
        Option.bind, GetElem?.getElem?, List.instGetElem?NatLtLength, List.get?Internal])
  apply Readback.done
  refine ⟨challenge, ?_, ?_⟩ <;>
    simp [TableComponent.Execution.finalHistory, TableComponent.Execution.receivedHistory, List.append_assoc, challenge]

end ZkcSecurity.Families.Sumcheck.TableComponent.ReadbackRound
