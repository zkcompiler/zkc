module

public import Zkc.Realization.RecordAllocator

@[expose] public section

/-! The generated immutable lookup checks the constructor before accessing its
store. This rule describes the actual instruction sequence for arbitrary record
types and SSA placements. Publication identity is supplied by the storage relation.
-/

set_option autoImplicit false
namespace Zkc.Realization.RecordLookup
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Layout where
  constructor : Nat
  element : Ty

structure Placement where
  start : Nat
  constructor : Nat
  slot : Nat
  store : Nat
  site : String

def instructions (layout : Layout) (placement : Placement) : List Construction.Instruction :=
  [⟨.execute (.indexConstant layout.constructor), [], [.data .index], []⟩,
   ⟨.execute .indexEqual, [placement.constructor, placement.start], [.data .boolean], []⟩,
   ⟨.require placement.site, [placement.start + 1], [], []⟩,
   ⟨.execute (.sequenceAt layout.element), [placement.store, placement.slot],
     [.data layout.element], []⟩]

structure Recognized (body : List Construction.Instruction) where
  layout : Layout
  placement : Placement
  exactBody : body = instructions layout placement

/-- Read the actual operand graph and then check the entire four-instruction
fragment, including nominal types, result sorts and the guard position. -/
def recognize (body : List Construction.Instruction) : Option (Recognized body) := do
  let [tag, comparison, guard, lookup] := body | none
  let .execute (.indexConstant constructor) := tag.operation | none
  let [actual, start] := comparison.operands | none
  let .require site := guard.operation | none
  let .execute (.sequenceAt element) := lookup.operation | none
  let [store, slot] := lookup.operands | none
  let layout : Layout := ⟨constructor, element⟩
  let placement : Placement := ⟨start, actual, slot, store, site⟩
  if matched : body = instructions layout placement then
    some ⟨layout, placement, matched⟩
  else none

def spine (layout : Layout) (placement : Placement) : ConnectionTargetPrefix.Prefix :=
  .step (fun model ↦ Domain.View.execute model (.indexConstant layout.constructor) [] [.data .index])
  (.step (fun model ↦ Domain.View.execute model .indexEqual
    [placement.constructor, placement.start] [.data .boolean])
  (.step (fun _ ↦ Domain.View.require (placement.start + 1) [])
  (.step (fun model ↦ Domain.View.execute model (.sequenceAt layout.element)
    [placement.store, placement.slot] [.data layout.element]) .empty)))

theorem correspondence (model : DomainModel) (program : Program) (context : Context)
    (layout : Layout) (placement : Placement) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      (instructions layout placement) ((spine layout placement).block model) :=
  Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _)
    (Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _)
      (Domain.Correspondence.sequence (Domain.Correspondence.require _ _ _)
        (Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _)
          Domain.Correspondence.empty)))

theorem Recognized.correspondence {body : List Construction.Instruction}
    (checked : Recognized body) (model : DomainModel) (program : Program) (context : Context) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      body ((spine checked.layout checked.placement).block model) := by
  rcases checked with ⟨layout, placement, rfl⟩
  exact RecordLookup.correspondence model program context layout placement

/-- Lookup returns the selected record and preserves every cell in the caller
frame. Constructor agreement is checked before the sequence access. -/
noncomputable def simulation (model : DomainModel) (layout : Layout)
    (data : layout.element.isHandle = false)
    (environment : Domain.Environment model.toCarriers) (constructor slot store : Nat)
    (site : String) (position : Nat) (records : List (model.Value layout.element))
    (record : model.Value layout.element)
    (readTag : environment[constructor]? = some (.data (.index layout.constructor)))
    (readSlot : environment[slot]? = some (.data (.index position)))
    (readStore : environment[store]? = some (.data ⟨.sequence layout.element, data, records⟩))
    (found : records[position]? = some record) (tagBound : layout.constructor < indexLimit) :
    Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (environment ++ [.data (.index layout.constructor), .data (.boolean true),
        .data ⟨layout.element, data, record⟩]))
      ((spine layout ⟨environment.length, constructor, slot, store, site⟩).block model environment) := by
  let tag : Domain.Value model.toCarriers := .data (.index layout.constructor)
  let yes : Domain.Value model.toCarriers := .data (.boolean true)
  let payload : Domain.Value model.toCarriers := .data ⟨layout.element, data, record⟩
  have elementLocal : Domain.localType layout.element = true := by
    simp [Domain.localType, Domain.dataType, data]
  have tagStep : Domain.View.execute model (.indexConstant layout.constructor) [] [.data .index]
      environment = .done (environment ++ [tag]) := by
    have law := ConnectionPrimitives.view_execute model (.indexConstant layout.constructor)
      .nil rfl rfl environment [] rfl
    simpa [Primitive.results, Primitive.evaluateOn, tagBound, primitiveOutcome,
      Original.encodeHelperResult, Domain.encodeValues_cons, Domain.encodeValues_nil,
      Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle, tag, PIR.Process.bind] using law
  have equalRead : Domain.read (environment ++ [tag]) [constructor, environment.length] =
      Domain.encodeValues (tys := [.index, .index])
        (.cons layout.constructor (.cons layout.constructor .nil)) := by
    simp [Domain.read, Original.read_append readTag [tag], Domain.encodeValues_cons,
      Domain.encodeValues_nil, Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle, tag]
  have equalStep : Domain.View.execute model .indexEqual [constructor, environment.length]
      [.data .boolean] (environment ++ [tag]) = .done (environment ++ [tag, yes]) := by
    have law := ConnectionPrimitives.view_execute model .indexEqual
      (.cons layout.constructor (.cons layout.constructor .nil)) rfl rfl _ _ equalRead
    simpa [Primitive.results, Primitive.evaluateOn, checkedIndices, tagBound, primitiveOutcome,
      Original.encodeHelperResult, Domain.encodeValues_cons, Domain.encodeValues_nil,
      Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle, yes, PIR.Process.bind,
      List.append_assoc] using law
  have guardStep : Domain.View.require (environment.length + 1) [] (environment ++ [tag, yes]) =
      .done (environment ++ [tag, yes]) := by simp [Domain.View.require, yes]
  have recordRead : Domain.read (environment ++ [tag, yes]) [store, slot] =
      Domain.encodeValues (tys := [.sequence layout.element, .index])
        (.cons records (.cons position .nil)) := by
    simp [Domain.read, Original.read_append readStore [tag, yes],
      Original.read_append readSlot [tag, yes], Domain.encodeValues_cons, Domain.encodeValues_nil,
      Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle, data]
  have lookupStep : Domain.View.execute model (.sequenceAt layout.element) [store, slot]
      [.data layout.element] (environment ++ [tag, yes]) =
      .done (environment ++ [tag, yes, payload]) := by
    have law := ConnectionPrimitives.view_execute model (.sequenceAt layout.element)
      (.cons records (.cons position .nil))
      (by simp [Primitive.arguments, Domain.localType, Domain.dataType, Ty.isHandle, data])
      (by simpa [Primitive.results] using elementLocal) _ _ recordRead
    have encoded : Domain.Value.encode layout.element record = some payload :=
      Domain.Value.encode_ofPayload (by simp [Domain.Payload.ofValue, data])
    simpa [Primitive.results, Primitive.evaluateOn, found, primitiveOutcome,
      Original.encodeHelperResult, Domain.encodeValues_cons, Domain.encodeValues_nil,
      encoded, PIR.Process.bind, List.append_assoc] using law
  apply RecordAllocator.silent_sequence tagStep (List.prefix_refl _) (by simp)
  apply RecordAllocator.silent_sequence equalStep (by simp) (by simp)
  apply RecordAllocator.silent_sequence guardStep (by simp) (by simp)
  apply RecordAllocator.silent_sequence lookupStep (by simp) (by simp)
  exact .done rfl

/-- Apply the physical rule to a recognized fragment in its current frame. -/
noncomputable def Recognized.simulation {body : List Construction.Instruction}
    (checked : Recognized body) (model : DomainModel) (program : Program) (context : Context)
    (data : checked.layout.element.isHandle = false)
    (environment : Domain.Environment model.toCarriers) (position : Nat)
    (records : List (model.Value checked.layout.element))
    (record : model.Value checked.layout.element)
    (start : checked.placement.start = environment.length)
    (readTag : environment[checked.placement.constructor]? =
      some (.data (.index checked.layout.constructor)))
    (readSlot : environment[checked.placement.slot]? = some (.data (.index position)))
    (readStore : environment[checked.placement.store]? =
      some (.data ⟨.sequence checked.layout.element, data, records⟩))
    (found : records[position]? = some record)
    (tagBound : checked.layout.constructor < indexLimit) :
    Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (environment ++ [.data (.index checked.layout.constructor), .data (.boolean true),
        .data ⟨checked.layout.element, data, record⟩]))
      (Domain.evaluate model program context body environment) := by
  rw [checked.correspondence model program context]
  rcases checked with ⟨layout, ⟨offset, constructor, slot, store, site⟩, matched⟩
  dsimp only at start ⊢
  subst offset
  exact RecordLookup.simulation model layout data environment constructor slot store site position
    records record readTag readSlot readStore found tagBound

end Zkc.Realization.RecordLookup
