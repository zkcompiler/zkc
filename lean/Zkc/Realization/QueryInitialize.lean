module

public import Zkc.Realization.RecordProjection
public import Zkc.Realization.CaptureLayout
public import Zkc.Construction.ConnectionClosedSimulation

@[expose] public section

/-! Initialize the actual controller header and empty typed stores. The root
constructor and instance are projected from the supplied nominal reference;
the query position is read from the caller. No source author supplies an
equation for the generated initial state or its output ordering.
-/
set_option autoImplicit false
namespace Zkc.Realization.QueryInitialize
open Zkc.Source Zkc.Source.Structured Zkc.Construction

def referenceLayout (identity : String) : RecordProjection.Layout :=
  ⟨identity, "Record", CaptureLayout.referenceFields⟩

def emptyInstructions (types : List Ty) : List Construction.Instruction :=
  types.map fun type ↦ ⟨.execute (.sequenceEmpty type), [], [.data (.sequence type)], []⟩

def emptySpine : List Ty → ConnectionTargetPrefix.Prefix
  | [] => .empty
  | type :: rest => .step (fun model ↦ Domain.View.execute model (.sequenceEmpty type)
      [] [.data (.sequence type)]) (emptySpine rest)

def emptyValues (model : DomainModel) : List Ty → Domain.Environment model.toCarriers
  | [] => []
  | type :: rest =>
      Original.encodeHelperResult (tys := [.sequence type])
        (.cons ([] : List (model.Value type)) .nil) ++ emptyValues model rest

theorem emptyCorrespondence (model : DomainModel) (program : Program) (context : Context)
    (types : List Ty) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      (emptyInstructions types) ((emptySpine types).block model) := by
  induction types with
  | nil => exact Domain.Correspondence.empty
  | cons type rest ih =>
      exact Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _) ih

theorem emptyValues_length (model : DomainModel) (types : List Ty)
    (localTypes : ∀ type ∈ types, Domain.localType (.sequence type) = true) :
    (emptyValues model types).length = types.length := by
  induction types with
  | nil => rfl
  | cons type rest ih =>
      have localType := localTypes type (by simp)
      have encoded := Original.encodeHelperResult_eq (carriers := model.toCarriers)
        (tys := [.sequence type]) (by simpa using localType)
        (.cons ([] : List (model.Value type)) .nil)
      have length := congrArg List.length (Domain.encodeValues_sorts encoded)
      simp only [List.length_map, List.length_cons, List.length_nil] at length
      simp only [emptyValues, List.length_append, List.length_cons, length]
      have tail := ih (fun element present ↦ localTypes element (by simp [present]))
      omega

set_option backward.isDefEq.respectTransparency false in
theorem emptySimulation (model : DomainModel) (types : List Ty)
    (localTypes : ∀ type ∈ types, Domain.localType (.sequence type) = true)
    (environment captured : Domain.Environment model.toCarriers)
    (preserved : captured <+: environment) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ captured <+: frame)
      (.done (environment ++ emptyValues model types))
      ((emptySpine types).block model environment)) := by
  induction types generalizing environment with
  | nil => exact ⟨by simpa [emptyValues, emptySpine, ConnectionTargetPrefix.Prefix.block,
      ConnectionTargetPrefix.Prefix.plug, Domain.View.empty] using
        (Original.Simulation.done (returns := Eq) (live := fun _ frame ↦ captured <+: frame)
          (a := environment) rfl)⟩
  | cons type rest ih =>
      let value := Original.encodeHelperResult (carriers := model.toCarriers)
        (tys := [.sequence type]) (.cons ([] : List (model.Value type)) .nil)
      have step : Domain.View.execute model (.sequenceEmpty type) [] [.data (.sequence type)]
          environment = .done (environment ++ value) := by
        have law := ConnectionPrimitives.view_execute model (.sequenceEmpty type) .nil rfl
          (by simpa [Primitive.results] using localTypes type (by simp)) environment [] rfl
        simpa [Primitive.evaluateOn, Primitive.results, primitiveOutcome, PIR.Process.bind, value]
          using law
      obtain ⟨tail⟩ := ih (fun element present ↦ localTypes element (by simp [present]))
        (environment ++ value) (preserved.trans (List.prefix_append _ _))
      refine ⟨?_⟩
      change Original.Simulation _ _ _ (Domain.View.sequence _ _ environment)
      apply RecordAllocator.silent_sequence step preserved
        (preserved.trans (List.prefix_append _ _))
      simpa only [emptyValues, value, List.append_assoc, ConnectionTargetPrefix.Prefix.block]
        using tail

def instructions (identity : String) (reference : Nat) (types : List Ty) :
    List Construction.Instruction :=
  RecordProjection.instructions (referenceLayout identity) reference
    (RecordProjection.allFields CaptureLayout.referenceFields) ++
    ⟨.execute (.indexConstant 0), [], [.data .index], []⟩ :: emptyInstructions types

def spine (identity : String) (reference : Nat) (types : List Ty) : ConnectionTargetPrefix.Prefix :=
  (RecordProjection.spine (referenceLayout identity) reference
    (RecordProjection.allFields CaptureLayout.referenceFields)).append
      (.step (fun model ↦ Domain.View.execute model (.indexConstant 0) [] [.data .index])
        (emptySpine types))

theorem correspondence (model : DomainModel) (program : Program) (context : Context)
    (identity : String) (reference : Nat) (types : List Ty) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      (instructions identity reference types) ((spine identity reference types).block model) :=
  ConnectionTargetPrefix.correspondence_append model program context
    (RecordProjection.correspondence _ _ _ _ _ _)
    (Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _)
      (emptyCorrespondence _ _ _ _))

def results (model : DomainModel) (constructor anchorInstance : Nat) (types : List Ty) :
    Domain.Environment model.toCarriers :=
  [.data (.index constructor), .data (.index anchorInstance), .data (.index 0)] ++
    emptyValues model types

set_option backward.isDefEq.respectTransparency false in
theorem simulation (model : DomainModel) (identity : String) (reference : Nat) (types : List Ty)
    (localTypes : ∀ type ∈ types, Domain.localType (.sequence type) = true)
    (environment : Domain.Environment model.toCarriers) (constructor anchorInstance : Nat)
    (readReference : environment[reference]? =
      some (.data ⟨CaptureLayout.referenceType identity, rfl, (constructor, anchorInstance, ())⟩)) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (environment ++ results model constructor anchorInstance types))
      ((spine identity reference types).block model environment)) := by
  obtain ⟨projection⟩ := RecordProjection.simulation model (referenceLayout identity) rfl
    (RecordProjection.allFields CaptureLayout.referenceFields)
    (RecordProjection.allFields_local _ rfl) environment environment (List.prefix_refl _)
    reference (constructor, anchorInstance, ()) readReference
  have projected : RecordProjection.results model (referenceLayout identity)
      (constructor, anchorInstance, ()) (RecordProjection.allFields CaptureLayout.referenceFields) =
        [.data (.index constructor), .data (.index anchorInstance)] := by
    unfold referenceLayout
    rw [RecordProjection.results_all model identity "Record" CaptureLayout.referenceFields _ rfl]
    simp [Original.encodeHelperResult, CaptureLayout.referenceFields, ProductFields.unpack,
      Domain.encodeValues_cons, Domain.encodeValues_nil, Domain.Value.encode,
      Domain.Payload.ofValue, Ty.isHandle]
  rw [projected] at projection
  let afterProjection := environment ++ [.data (.index constructor), .data (.index anchorInstance)]
  have zero : Domain.View.execute model (.indexConstant 0) [] [.data .index] afterProjection =
      .done (afterProjection ++ [.data (.index 0)]) := by
    have law := ConnectionPrimitives.view_execute model (.indexConstant 0) .nil rfl rfl
      afterProjection [] rfl
    simpa [Primitive.results, Primitive.evaluateOn, primitiveOutcome, PIR.Process.bind, indexLimit,
      Original.encodeHelperResult, Domain.encodeValues_cons, Domain.encodeValues_nil,
      Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle] using law
  have kept : environment <+: afterProjection ++ [.data (.index 0)] :=
    (List.prefix_append _ _).trans (List.prefix_append _ _)
  obtain ⟨empties⟩ := emptySimulation model types localTypes _ environment kept
  refine ⟨?_⟩
  unfold spine ConnectionTargetPrefix.Prefix.block
  rw [ConnectionTargetPrefix.Prefix.append_plug, ConnectionTargetPrefix.Prefix.plug_eq_bind]
  apply projection.continueDone (fun _ held ↦ held)
  change Original.Simulation _ _ _ (Domain.View.sequence _ _ afterProjection)
  apply RecordAllocator.silent_sequence zero (List.prefix_append _ _) kept
  simpa only [results, afterProjection, List.append_assoc, List.cons_append, List.nil_append,
    ConnectionTargetPrefix.Prefix.block]
    using empties

/-- The five zero fields initialize outer continuation, outer instance, root
kind, Enter phase and answer index. Store order follows the emitted types. -/
def outputReferences (start position : Nat) (types : List Ty) : List Nat :=
  [start, start + 1, position, start + 2, start + 2, start + 2, start + 2, start + 2] ++
    List.range' (start + 3) types.length

def initialState (model : DomainModel) (constructor anchorInstance position : Nat)
    (types : List Ty) : Domain.Environment model.toCarriers :=
  [constructor, anchorInstance, position, 0, 0, 0, 0, 0].map
    (fun value ↦ .data (.index value)) ++ emptyValues model types


theorem read_output (model : DomainModel) (types : List Ty)
    (localTypes : ∀ type ∈ types, Domain.localType (.sequence type) = true)
    (environment : Domain.Environment model.toCarriers) (constructor anchorInstance position : Nat)
    (positionReference : Nat)
    (readPosition : environment[positionReference]? = some (.data (.index position))) :
    Domain.read (environment ++ results model constructor anchorInstance types)
      (outputReferences environment.length positionReference types) =
        some (initialState model constructor anchorInstance position types) := by
  let header : Domain.Environment model.toCarriers :=
    [.data (.index constructor), .data (.index anchorInstance), .data (.index 0)]
  have tail := RecordAllocator.read_appended (environment ++ header) (emptyValues model types)
  rw [emptyValues_length model types localTypes] at tail
  have length : (environment ++ header).length = environment.length + 3 := by simp [header]
  rw [length] at tail
  have headerRead : Domain.read (environment ++ results model constructor anchorInstance types)
      [environment.length, environment.length + 1, positionReference,
        environment.length + 2, environment.length + 2, environment.length + 2,
        environment.length + 2, environment.length + 2] =
      some ([constructor, anchorInstance, position, 0, 0, 0, 0, 0].map
        (fun value ↦ Domain.Value.data (.index value))) := by
    have retained := Original.read_append readPosition
      (results model constructor anchorInstance types)
    simp only [results, List.cons_append, List.nil_append] at retained
    simp [Domain.read, results, retained]
  change Domain.read (environment ++ results model constructor anchorInstance types)
    (_ ++ List.range' (environment.length + 3) types.length) = _
  simp only [Domain.read, List.mapM_append] at headerRead tail ⊢
  rw [headerRead]
  have tailRead : (List.range' (environment.length + 3) types.length).mapM
      (fun reference ↦
        (environment ++ results model constructor anchorInstance types)[reference]?) =
        some (emptyValues model types) := by
    simpa only [results, header, List.append_assoc] using tail
  rw [tailRead]
  rfl

structure Recognized (body : List Construction.Instruction) (returned : List Nat) where
  identity : String
  reference : Nat
  start : Nat
  position : Nat
  types : List Ty
  exactBody : body = instructions identity reference types
  exactOutput : returned = outputReferences start position types

/-- Check the complete initialization and its returned state. Equal-typed
header coordinates and arenas retain their exact emitted order. -/
def recognize (start : Nat) (body : List Construction.Instruction) (returned : List Nat) :
    Option (Recognized body returned) := do
  let first :: _ :: _ :: stores := body | none
  let .calculate (.getProduct identity _ _ _ _) := first.operation | none
  let [reference] := first.operands | none
  let some position := returned[2]? | none
  let types ← stores.mapM fun instruction ↦ match instruction.operation with
    | .execute (.sequenceEmpty type) => some type
    | _ => none
  if exactBody : body = instructions identity reference types then
    if exactOutput : returned = outputReferences start position types then
      some ⟨identity, reference, start, position, types, exactBody, exactOutput⟩
    else none
  else none

theorem Recognized.output {body : List Construction.Instruction} {returned : List Nat}
    (checked : Recognized body returned) (model : DomainModel)
    (program : Program) (context : Context)
    (localTypes : ∀ type ∈ checked.types, Domain.localType (.sequence type) = true)
    (environment : Domain.Environment model.toCarriers)
    (start : checked.start = environment.length) (constructor anchorInstance position : Nat)
    (readReference : environment[checked.reference]? = some
      (.data ⟨CaptureLayout.referenceType checked.identity, rfl,
        (constructor, anchorInstance, ())⟩))
    (readPosition : environment[checked.position]? = some (.data (.index position))) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (initialState model constructor anchorInstance position checked.types))
      ((Domain.evaluate model program context body environment).bind fun final ↦
        match Domain.read final returned with
        | some values => .done values
        | none => .halt .refused)) := by
  rcases checked with ⟨identity, reference, offset, positionReference, types, rfl, rfl⟩
  dsimp only at localTypes start readReference readPosition ⊢
  subst offset
  rw [correspondence]
  obtain ⟨head⟩ := simulation model identity reference types localTypes environment
    constructor anchorInstance readReference
  refine ⟨?_⟩
  apply head.continueDone (fun _ held ↦ held)
  rw [read_output model types localTypes environment constructor anchorInstance position
    positionReference readPosition]
  exact .done rfl

end Zkc.Realization.QueryInitialize
