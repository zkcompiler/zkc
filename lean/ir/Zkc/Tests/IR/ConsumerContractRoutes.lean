module

public import Zkc.IR.Construction.OriginalRoutingCongruence
public import Zkc.Tests.IR.IndexServices

@[expose] public section

/-! Source-backed index/block controls for generic route extensionality.
Mixed lists, absent routes, ambiguity and method mismatch retain their original
resolution behavior. Field route equality alone leaves typed services unconstrained. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace Tests.ConsumerContractRoutes
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Construction.Original
open Tests.IndexServices

private def malformed : Template := ⟨"unrelated", [], ["malformed"]⟩
private def mixed (routing : Routing) (query message : Template) : Routing :=
  { routing with messages := [query, malformed, message], draws := [message, query, malformed] }
private def filtered (routing : Routing) : Routing :=
  { routing with
    messages := routing.messages.filter (fun template => template.messageSite?.isSome)
    draws := routing.draws.filter (fun template => template.querySite?.isSome) }
private def scalar : Routing := mixed (Scalar.routing .validator)
  Scalar.queryTemplate Scalar.messageTemplate
private def block : Routing := mixed (Block.routing .validator)
  Block.queryTemplate Block.messageTemplate

example : scalar.serviceRequest [] "label_706f736974696f6e" (.sampleIndex 8) 17 =
    some (Scalar.context.query "label_706f736974696f6e" (.sampleIndex 8)) := by decide +kernel
example : block.serviceRequest [] "label_706f736974696f6e73" (.sampleIndices 8 3) 17 =
    some (Block.context.query "label_706f736974696f6e73" (.sampleIndices 8 3)) := by decide +kernel
example : (filtered scalar).serviceRequest [] "label_706f736974696f6e" (.sampleIndex 8) 17 =
    scalar.serviceRequest [] "label_706f736974696f6e" (.sampleIndex 8) 17 :=
  serviceRequest_filter scalar _ _ _ _
example : (filtered block).serviceRequest [] "label_706f736974696f6e73" (.sampleIndices 8 3) 17 =
    block.serviceRequest [] "label_706f736974696f6e73" (.sampleIndices 8 3) 17 :=
  serviceRequest_filter block _ _ _ _
example : (filtered scalar).message [] "label_64656c6976657279_0" 1 0 =
    scalar.message [] "label_64656c6976657279_0" 1 0 := message_filter scalar _ _ _ _

-- Wrong handle, bound, block count, method and dynamic ancestry remain refusals.
example : (filtered scalar).serviceRequest [] "label_706f736974696f6e" (.sampleIndex 8) 18 =
    none := by decide +kernel
example : (filtered scalar).serviceRequest [] "label_706f736974696f6e" (.sampleIndex 7) 17 =
    none := by decide +kernel
example : (filtered block).serviceRequest [] "label_706f736974696f6e73" (.sampleIndices 8 2) 17 =
    none := by decide +kernel
example : (filtered scalar).serviceRequest [] "label_706f736974696f6e" (.sampleIndices 8 1) 17 =
    none := by decide +kernel
example : (filtered scalar).serviceRequest [⟨"forged", 0⟩] "label_706f736974696f6e"
    (.sampleIndex 8) 17 = none := by decide +kernel
example : (filtered scalar).serviceRequest [] "label_706f736974696f6e" (.sampleIndex 0) 17 =
    none := by decide +kernel

private def duplicated : Routing :=
  { scalar with draws := [Scalar.messageTemplate, Scalar.queryTemplate, Scalar.queryTemplate] }
example : duplicated.serviceRequest [] "label_706f736974696f6e" (.sampleIndex 8) 17 = none := by
  decide +kernel
example : (filtered duplicated).serviceRequest [] "label_706f736974696f6e" (.sampleIndex 8) 17 =
    none := by decide +kernel
example : (filtered { scalar with draws := [] }).serviceRequest [] "label_706f736974696f6e"
    (.sampleIndex 8) 17 = none := by decide +kernel

-- A method-mismatched query template cannot be reclassified as a message.
example : { Scalar.queryTemplate with event :=
    ["query", Scalar.Source.snapshot.entry, "label_706f736974696f6e", "input_0", contract,
      "indices", "role00000001"] }.origin
      (Scalar.context.mapReplacement fun replacement =>
        { replacement with request := some (.sampleIndex 8) }) = none := by decide +kernel

private def indexSource (carriers : Carriers) :
    PIR.Process (Occurrence.signature carriers) Nat :=
  .call (.action (.query "label_706f736974696f6e" (.sampleIndex contract)
    (.cons 17 (.cons 8 .nil)))) .done
private def blockSource (carriers : Carriers) :
    PIR.Process (Occurrence.signature carriers) (List Nat) :=
  .call (.action (.query "label_706f736974696f6e73" (.sampleIndices contract)
    (.cons 17 (.cons 8 (.cons 3 .nil))))) .done
private def indexReceive (carriers : Carriers) :
    PIR.Process (Occurrence.signature carriers) Nat :=
  .call (.action (.receive .index "label_64656c6976657279_0" 1)) .done
private def blockReceive (carriers : Carriers) :
    PIR.Process (Occurrence.signature carriers) (List Nat) :=
  .call (.action (.receive .indices "label_64656c6976657279_0" 1)) .done

example (carriers : Carriers) (state : State carriers) :
    fold (filtered scalar) (indexSource carriers) state =
      fold scalar (indexSource carriers) state := fold_filter scalar _ _
example (carriers : Carriers) (state : State carriers) :
    fold (filtered block) (blockSource carriers) state =
      fold block (blockSource carriers) state := fold_filter block _ _
example (carriers : Carriers) (state : State carriers) (reason : PIR.Stop) :
    fold (filtered block) ((blockSource carriers).bind fun _ => .halt reason : PIR.Process _ Unit)
        state =
      fold block ((blockSource carriers).bind fun _ => .halt reason : PIR.Process _ Unit) state :=
  fold_filter block _ _
example (carriers : Carriers) (state : State carriers) :
    let routing := { scalar with mode := .producer }
    fold (filtered routing) (indexReceive carriers) state =
      fold routing (indexReceive carriers) state :=
  fold_filter { scalar with mode := .producer } _ _
example (carriers : Carriers) (state : State carriers) :
    let routing := { block with mode := .producer }
    fold (filtered routing) (blockReceive carriers) state =
      fold routing (blockReceive carriers) state := fold_filter { block with mode := .producer } _ _

example : { scalar with mode := .producer }.typedDelivery [] "label_64656c6976657279_0"
    .index 1 = some (.sampleIndex 8,
      Scalar.context.query "label_706f736974696f6e" (.sampleIndex 8),
      Scalar.context.message "label_64656c6976657279_0" 1 0) := by decide +kernel
example : { block with mode := .producer }.typedDelivery [] "label_64656c6976657279_0"
    .indices 1 = some (.sampleIndices 8 3,
      Block.context.query "label_706f736974696f6e73" (.sampleIndices 8 3),
      Block.context.message "label_64656c6976657279_0" 1 0) := by decide +kernel
example : { block with mode := .producer }.typedDelivery [] "label_64656c6976657279_0"
    .index 1 = none := by decide +kernel
example (carriers : Carriers) :
    fold (filtered duplicated) (indexSource carriers) {} = .halt .refused := rfl

-- Local generic routes stay separate from public service selection.
private def localRouting : Routing :=
  ⟨Local.Source.snapshot, Local.context, .producer, 99, [], [], [],
    [⟨23, Local.port, Local.template⟩]⟩
example : localRouting.localRequest [] "s0" (.sampleIndex 3) 23 =
    some (Local.port, Origin.query Local.context.entry "s0" "input_0" contract
      Local.port.owner (.sampleIndex 3)) := by decide +kernel
example : localRouting.localRequest [] "s0" (.sampleIndex 8) 23 = none := by decide +kernel
example : (filtered localRouting).localRequest [] "s0" (.sampleIndex 3) 23 =
    localRouting.localRequest [] "s0" (.sampleIndex 3) 23 := rfl

-- Both routings satisfy all of the old field-only premises, but differ on an index query.
private def withoutQueries : Routing := { (Scalar.routing .validator) with draws := [] }
private theorem field_draw_none (frames : Frames) (site field : String) (handle : Nat) :
    (Scalar.routing .validator).draw frames site field handle = none := by
  have absent : Scalar.queryTemplate.origin Scalar.context = none := by decide +kernel
  unfold Routing.draw
  split
  · change OccurrenceResolution.resolve Scalar.Source.snapshot Scalar.context
      (Scalar.context.query site (.draw field)) frames [Scalar.queryTemplate] = none
    simp [OccurrenceResolution.resolve, OccurrenceResolution.matchesOccurrence, absent]
  · rfl

private theorem field_routes_equal :
    (∀ frames site sender receiver,
      (Scalar.routing .validator).message frames site sender receiver =
        withoutQueries.message frames site sender receiver) ∧
    (∀ frames site field handle,
      (Scalar.routing .validator).draw frames site field handle =
        withoutQueries.draw frames site field handle) ∧
    (∀ frames site field sender,
      (Scalar.routing .validator).delivery frames site field sender =
        withoutQueries.delivery frames site field sender) ∧
    (∀ frames site field handle,
      (Scalar.routing .validator).local frames site field handle =
        withoutQueries.local frames site field handle) := by
  refine ⟨by intros; rfl, ?_, by intros; rfl, by intros; rfl⟩
  intro frames site field handle
  rw [field_draw_none]
  unfold withoutQueries Routing.draw
  split <;> rfl

example : (Scalar.routing .validator).context = withoutQueries.context := rfl
example : (Scalar.routing .validator).mode = withoutQueries.mode := rfl
example : (Scalar.routing .validator).serviceRequest [] "label_706f736974696f6e"
    (.sampleIndex 8) 17 ≠ withoutQueries.serviceRequest [] "label_706f736974696f6e"
      (.sampleIndex 8) 17 := by decide +kernel

/-- Identical field routes still permit a queried index process to issue an
effect in one routing and refuse in the other. This refutes the old API's scope. -/
private theorem typed_folds_differ (carriers : Carriers) :
    fold (Scalar.routing .validator) (indexSource carriers) {} ≠
      fold withoutQueries (indexSource carriers) {} := by
  intro same
  have shape := congrArg (fun process => match process with
    | .call .. => true
    | _ => false) same
  change true = false at shape
  cases shape

#print axioms Zkc.Construction.Original.fold_congr
#print axioms Zkc.Construction.Original.fold_filter
end Tests.ConsumerContractRoutes
