module

public import Zkc.Realization.RecordAllocator

@[expose] public section

/-! Ordered reads from the controller's typed answer arenas. A placement names
actual SSA operands; the readback relation identifies their arena and index.
The common proof preserves the caller prefix at every checkpoint. It does not
choose a continuation or establish that the controller has reached these reads. -/
set_option autoImplicit false
namespace Zkc.Realization.AnswerReads
open Zkc.Source Zkc.Source.Structured Zkc.Construction

inductive Placement : List Ty → Type where
  | nil : Placement []
  | cons {type : Ty} {types : List Ty} (arena index : Nat) (rest : Placement types) :
      Placement (type :: types)

def Placement.instructions : {types : List Ty} → Placement types → List Construction.Instruction
  | _, .nil => []
  | type :: _, .cons arena index rest =>
      ⟨.execute (.sequenceAt type), [arena, index], [.data type], []⟩ :: rest.instructions

def Placement.spine : {types : List Ty} → Placement types → ConnectionTargetPrefix.Prefix
  | _, .nil => .empty
  | type :: _, .cons arena index rest =>
      .step (fun model ↦ Domain.View.execute model (.sequenceAt type) [arena, index] [.data type]) rest.spine

structure Recognized (body : List Construction.Instruction) where
  types : List Ty
  placement : Placement types
  exactBody : body = placement.instructions

/-- Recognition reads types and operands from the actual body. It accepts no
origin-name alias and checks result sorts and the absence of nested regions. -/
def recognize : (body : List Construction.Instruction) → Option (Recognized body)
  | [] => some ⟨[], .nil, rfl⟩
  | instruction :: rest => do
      let .execute (.sequenceAt type) := instruction.operation | none
      let [arena, index] := instruction.operands | none
      let tail ← recognize rest
      let placement := Placement.cons (type := type) arena index tail.placement
      if matched : instruction :: rest = placement.instructions then
        some ⟨type :: tail.types, placement, matched⟩
      else none

theorem Placement.correspondence {types : List Ty} (placement : Placement types)
    (model : DomainModel) (program : Program) (context : Context) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      placement.instructions (placement.spine.block model) := by
  induction placement with
  | nil => exact Domain.Correspondence.empty
  | cons arena index rest ih =>
      exact Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _) ih

inductive Readback (model : DomainModel) (environment : Domain.Environment model.toCarriers) :
    {types : List Ty} → Placement types → Values model.Value types → Prop where
  | nil : Readback model environment .nil .nil
  | cons {type : Ty} {types : List Ty} {arena index : Nat} {rest : Placement types}
      {value : model.Value type} {values : Values model.Value types}
      (records : List (model.Value type)) (slot : Nat)
      (inputData : (Primitive.sequenceAt type).arguments.all Domain.localType = true)
      (outputData : (Primitive.sequenceAt type).results.all Domain.localType = true)
      (read : Domain.read environment [arena, index] = Domain.encodeValues
        (tys := [.sequence type, .index]) (.cons records (.cons slot .nil)))
      (found : records[slot]? = some value) (tail : Readback model environment rest values) :
      Readback model environment (.cons arena index rest) (.cons value values)

set_option backward.isDefEq.respectTransparency false in
theorem Readback.extended {model : DomainModel} {environment : Domain.Environment model.toCarriers}
    {types : List Ty} {placement : Placement types} {values : Values model.Value types}
    (readback : Readback model environment placement values) (suffix : Domain.Environment model.toCarriers) :
    Readback model (environment ++ suffix) placement values := by
  induction readback with
  | nil => exact .nil
  | cons records slot inputData outputData read found tail ih =>
      apply Readback.cons records slot inputData outputData _ found ih
      have encoding := Original.encodeHelperResult_eq (carriers := model.toCarriers)
        inputData (.cons records (.cons slot .nil))
      rw [encoding] at read ⊢
      exact RecordAllocator.read_extended _ _ _ _ read

set_option backward.isDefEq.respectTransparency false in
/-- One reached operand graph determines one ordered answer tuple. In
particular, equal result types do not justify exchanging distinct answers. -/
theorem Readback.unique {model : DomainModel} {environment : Domain.Environment model.toCarriers}
    {types : List Ty} {placement : Placement types} {left right : Values model.Value types}
    (first : Readback model environment placement left)
    (second : Readback model environment placement right) : left = right := by
  induction first with
  | nil => cases second; rfl
  | cons records slot inputData outputData read found tail ih =>
    cases second with
    | cons other otherSlot otherInput otherOutput otherRead otherFound otherTail =>
      have encoded := Original.encodeHelperResult_eq (carriers := model.toCarriers)
        inputData (.cons records (.cons slot .nil))
      have same := Option.some.inj
        ((Domain.decodeValues_encodeValues encoded).symm.trans
          (Domain.decodeValues_encodeValues (otherRead.symm.trans (read.trans encoded))))
      have sameRecords : records = other := congrArg (fun values ↦ values.get .here) same
      have sameSlot : slot = otherSlot := congrArg (fun values ↦ values.get (.there .here)) same
      subst other
      subst otherSlot
      cases Option.some.inj (found.symm.trans otherFound)
      cases ih otherTail
      rfl

/-- Every intermediate answer is appended in the declared order. This avoids
reconstructing a heterogeneous tuple from an untyped list. -/
def encoded {model : DomainModel} : {types : List Ty} → Values model.Value types → Domain.Environment model.toCarriers
  | _, .nil => []
  | _, .cons value rest => Original.encodeHelperResult (.cons value .nil) ++ encoded rest

theorem Readback.encoding {model : DomainModel} {environment : Domain.Environment model.toCarriers}
    {types : List Ty} {placement : Placement types} {values : Values model.Value types}
    (readback : Readback model environment placement values) :
    Domain.encodeValues values = some (encoded values) := by
  induction readback with
  | nil => rfl
  | @cons type types arena index rest value values records slot inputData outputData read found tail ih =>
      have localType : Domain.localType type = true := by simpa [Primitive.results] using outputData
      obtain ⟨head, encodedHead⟩ := Domain.Value.encode_local_exists (carriers := model.toCarriers) localType value
      simp only [encoded, Original.encodeHelperResult, Domain.encodeValues_cons,
        Domain.encodeValues_nil, encodedHead, ih]
      rfl

/-- Per-step appends are exactly the existing whole-tuple encoding. A later
mathematical call consumes that same typed tuple without another representation. -/
theorem Readback.encoded_eq {model : DomainModel} {environment : Domain.Environment model.toCarriers}
    {types : List Ty} {placement : Placement types} {values : Values model.Value types}
    (readback : Readback model environment placement values) :
    encoded values = Original.encodeHelperResult values := by
  simp only [Original.encodeHelperResult, readback.encoding, Option.getD_some]

set_option backward.isDefEq.respectTransparency false in
theorem Readback.simulation {model : DomainModel}
    {environment : Domain.Environment model.toCarriers}
    {types : List Ty} {placement : Placement types} {values : Values model.Value types}
    (readback : Readback model environment placement values)
    (captured : Domain.Environment model.toCarriers) (preserved : captured <+: environment) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ captured <+: frame)
      (.done (environment ++ encoded values)) (placement.spine.block model environment)) := by
  induction placement generalizing environment with
  | nil => cases readback; exact ⟨.done (by simp [encoded])⟩
  | @cons type types arena index rest ih =>
    cases readback with
    | @cons _ _ _ _ _ value values records slot inputData outputData read found tail =>
      have step : Domain.View.execute model (.sequenceAt type) [arena, index] [.data type] environment =
          .done (environment ++ Original.encodeHelperResult (.cons value .nil)) := by
        have law := ConnectionPrimitives.view_execute model (.sequenceAt type)
          (.cons records (.cons slot .nil)) inputData outputData environment [arena, index] read
        simpa only [Primitive.evaluateOn, found, primitiveOutcome, PIR.Process.bind,
          Primitive.results, List.map_cons, List.map_nil] using law
      obtain ⟨continued⟩ := ih (tail.extended (Original.encodeHelperResult (.cons value .nil)))
        (preserved.trans (List.prefix_append _ _))
      refine ⟨RecordAllocator.silent_sequence step preserved
        (preserved.trans (List.prefix_append _ _)) ?_⟩
      simpa only [encoded, List.append_assoc, ConnectionTargetPrefix.Prefix.block] using continued

/-- The theorem concerns the actual constructed instructions, including their
checkpoints, rather than a separately chosen list of decoded answers. -/
theorem Readback.actual {model : DomainModel}
    {environment : Domain.Environment model.toCarriers}
    {types : List Ty} {placement : Placement types} {values : Values model.Value types}
    (readback : Readback model environment placement values) (program : Program) (context : Context) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (environment ++ encoded values))
      (Domain.evaluate model program context placement.instructions environment)) := by
  rw [placement.correspondence]
  exact readback.simulation environment (List.prefix_refl _)

/-- Failed lookup retains its pre-read checkpoint and never evaluates a
later answer read. The suffix can even have invalid operands. -/
theorem missing (model : DomainModel) (type : Ty) {types : List Ty}
    (rest : Placement types) (arena index : Nat)
    (records : List (model.Value type)) (slot : Nat)
    (inputData : (Primitive.sequenceAt type).arguments.all Domain.localType = true)
    (outputData : (Primitive.sequenceAt type).results.all Domain.localType = true)
    (environment : Domain.Environment model.toCarriers)
    (read : Domain.read environment [arena, index] = Domain.encodeValues
      (tys := [.sequence type, .index]) (.cons records (.cons slot .nil)))
    (absent : records[slot]? = none) (program : Program) (context : Context) :
    Nonempty (Original.Simulation (Eq (α := Domain.Environment model.toCarriers))
      (fun _ frame ↦ environment <+: frame) (.halt .refused)
      (Domain.evaluate model program context
        (Placement.cons (type := type) arena index rest).instructions environment)) := by
  have step : Domain.View.execute model (.sequenceAt type) [arena, index] [.data type] environment =
      .halt .refused := by
    have law := ConnectionPrimitives.view_execute model (.sequenceAt type)
      (.cons records (.cons slot .nil)) inputData outputData environment [arena, index] read
    simpa only [Primitive.evaluateOn, absent, primitiveOutcome, PIR.Process.bind,
      Primitive.results, List.map_cons, List.map_nil] using law
  rw [Placement.correspondence]
  change Nonempty (Original.Simulation _ _ _ (Domain.View.sequence _ _ environment))
  rw [Domain.View.sequence_stop _ _ _ .refused step]
  exact ⟨.checkpoint environment (List.prefix_refl _) (.halt .refused)⟩

theorem Recognized.simulation {body : List Construction.Instruction}
    (checked : Recognized body) {model : DomainModel} (program : Program) (context : Context)
    {environment : Domain.Environment model.toCarriers} {values : Values model.Value checked.types}
    (readback : Readback model environment checked.placement values) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (environment ++ encoded values)) (Domain.evaluate model program context body environment)) := by
  rcases checked with ⟨types, placement, rfl⟩
  exact readback.actual program context

end Zkc.Realization.AnswerReads
