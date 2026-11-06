module

public import Zkc.Construction.ConnectionRootRoutes
public import ZkcExamples.Structured.FriClearDescriptor
public import ZkcExamples.Structured.FriSourceData
public import ZkcSecurity.Bindings.Transcript.QueryTreeSource.Placement
public import ZkcSecurity.Bindings.Transcript.QueryTreeSource.Composition.Cache

@[expose] public section

/-! Scalar-query placement on the retained clear FRI root. Only the two
draw/delivery associations in the native policy are given. Both template
paths, their original service operands and the repeat stacks are rediscovered
from the original unit. -/
set_option autoImplicit false
namespace ZkcSecurity.Examples.FriScalarQueries
open Zkc.Source Zkc.Construction ZkcSecurity.FiatShamir QueryTreeSource QueryTree
open OracleComp OracleSpec

abbrev snapshot := ZkcExamples.Structured.FriSourceData.snapshot

abbrev policy := ZkcExamples.Structured.FriClearDescriptor.policy

theorem descriptor_original : ZkcExamples.Structured.FriClearDescriptor.original = snapshot.source := rfl

def context : Context :=
  (Context.ofPolicy policy [policy.producer, policy.validator] "random.koala-bear.ext8-binomial3/0"
    (some (.draw "koala-bear.ext8-binomial3"))).get (by decide +kernel)

set_option maxRecDepth 10000 in
def discovered : Original.Routing :=
  (ConnectionRootRoutes.publicRouting snapshot context .validator 0).toOption.get (by decide +kernel)

def publicRoutes : Original.Routing where
  snapshot := snapshot
  context := context
  mode := .validator
  selectedHandle := 0
  messages := discovered.messages
  draws := discovered.draws
  deliveries := discovered.deliveries

/-- Capability identity is supplied by the caller. The public port belongs to the original. -/
def routing (mode : Domain.Mode) (handle : Nat) : Original.Routing :=
  { publicRoutes with mode, selectedHandle := handle }

def edge : Original.Delivery :=
  (Placement.select publicRoutes 32 (fun _ => true)).get (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem certificate : Placement publicRoutes 32 edge := by
  constructor
  · constructor <;> first | rfl | decide +kernel
  · constructor <;> first | rfl | decide +kernel
  · decide +kernel

theorem installed (mode : Domain.Mode) (handle : Nat) : Placement (routing mode handle) 32 edge :=
  certificate.rebind mode handle

def segment : Segment := Placement.segment publicRoutes 32 edge []

/-- There is one enclosing repeat in the entire source path, at any ordinal. -/
def frames (ordinal : Nat) : Original.Frames :=
  (SourceOccurrences.repeatSites edge.draw).map fun site => ⟨site, ordinal⟩

theorem stack (ordinal : Nat) : (frames ordinal).map (·.site) =
    SourceOccurrences.repeatSites edge.draw := by simp [frames, List.map_map, Function.comp_def]

theorem indices (ordinal : Nat) : (frames ordinal).map (·.index) = [ordinal] := by
  have depth : (SourceOccurrences.repeatSites edge.draw).length = 1 := by decide +kernel
  simp [frames, List.map_map, Function.comp_def, List.map_const', depth]

variable {carriers : Structured.Carriers}

/-- The original service operation queries the exact node under its preceding
history. The caller may supply any segment-entry history and any scalar prefix. -/
theorem sourceQuery (handle : Nat) (root : Domain.History carriers) (node : Node (Fin 32) 8) :
    let key := encode segment (root, node)
    let state : Original.State carriers := ⟨frames (nodePrefix node).length, key.1⟩
    Original.service (routing .validator handle) state (Placement.querySite edge)
      context.contract (.sampleIndex 32) handle =
        Original.queryRequest state key.2 (.sampleIndex 32) :=
  by
  dsimp only
  apply (installed .validator handle).query (outer := []) (ordinal := (nodePrefix node).length)
  · exact stack _
  · exact indices _
  · rfl

/-- At the sending participant the same returned scalar is the message
observation. At the receiving participant it is the value of that query. -/
theorem sourceDelivery (handle ordinal : Nat) :
    (routing .producer handle).typedDelivery (frames ordinal) (Placement.messageSite edge)
      .index context.validator =
      some (.sampleIndex 32, segment.queryAt ordinal, segment.deliveryAt ordinal) ∧
    (routing .validator handle).message (frames ordinal) (Placement.messageSite edge)
      context.validator context.producer = some (segment.deliveryAt ordinal) :=
  ⟨(installed .producer handle).receiveRoute _ [] ordinal (stack _) (indices _),
   (installed .validator handle).sendRoute _ [] ordinal (stack _) (indices _)⟩

noncomputable section
local instance (priority := 2000) (α : Type) : DecidableEq α := Classical.decEq α
attribute [local instance] Composition.rawSampler Composition.otherSampler
  Composition.primitiveSampler Composition.macroSampler

/-- Exact change of oracle for any adaptive typed program and event on its
result, at the retained source placement. An event implication from accepting
the whole verifier is a separate obligation. -/
theorem scalarTree_event [∀ event, SampleableType (Domain.Raw (carriers := carriers) event)]
    {α : Type} (program : OracleComp (ofFn (Typed.ByLast (@Domain.Raw carriers))) α)
    (event : α → Prop) :
    Pr{let value ← (simulateQ randomOracle program).run' ∅}[event value] =
      Pr{let value ← (simulateQ randomOracle (Composition.fullTranslate
        (height := 8) (bound := 32) segment program)).run' ∅}[event value] :=
  Composition.full_event_eq segment program event

end
end ZkcSecurity.Examples.FriScalarQueries
