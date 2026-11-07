module

public import Zkc.Realization.QueryControllerSibling

@[expose] public section
set_option autoImplicit false
namespace Tests.QueryControllerSibling
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization QueryController

def state := List.range 10
def parentLayout : RecordProjection.Layout := ⟨"SiblingParent", "Record", .cons .index .nil⟩
def oldLayout := QueryContinuation.layout "EarlierFrame" 1
def newLayout := QueryContinuation.layout "LaterFrame" 2
theorem oldData : oldLayout.type.isHandle = false := rfl
theorem newData : newLayout.type.isHandle = false := rfl
theorem parentData : parentLayout.type.isHandle = false := rfl
def oldFrameBody := QueryContinuation.loadInstructions "EarlierFrame" 1 16 8 4
def lookupPlacement : RecordLookup.Placement := ⟨23, 22, 19, 10, "parent"⟩
def lookupBody := RecordLookup.instructions ⟨3, parentLayout.type⟩ lookupPlacement ++
  RecordProjection.instructions parentLayout 25 (RecordProjection.allFields parentLayout.fields)
def lookup : RecordLookupProjection.Recognized lookupBody :=
  ⟨_, _, ⟨⟨3, parentLayout.type⟩, lookupPlacement, rfl⟩,
    ⟨parentLayout, 25, RecordProjection.allFields parentLayout.fields, rfl⟩, rfl, rfl, rfl⟩
def returnBody := RequiredIndices.constantInstructions 12 3 7 "continuation" ++
  RequiredIndices.constantInstructions 14 5 0 "kind" ++ oldFrameBody ++
  IndexLiterals.instructions [3] ++ lookupBody
def restore : ReturnPrefix.Recognized returnBody :=
  ⟨12, state, 7, 3, "continuation", 0, 5, "kind", oldFrameBody,
    ⟨"EarlierFrame", 1, 16, 8, 4, rfl⟩, lookupBody, lookup,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
def newPlacement : RecordAppend.Placement := ⟨27, 9, [17, 18, 19, 20, 21, 7]⟩
def newFrameBody := RecordAppend.instructions newLayout newPlacement
def positionInstruction : Zkc.Construction.Instruction :=
  ⟨.execute (.indexConstant 5), [], [.data .index], []⟩
def childBody := newFrameBody ++ [positionInstruction] ++ Child.referenceInstructions "SiblingReference" 11 ++
  IndexLiterals.instructions [8]
def child : Child.Recognized childBody :=
  ⟨newFrameBody, ⟨newLayout, newPlacement, rfl⟩, positionInstruction, "SiblingReference", 11, [8], rfl⟩
def output : Child.Output := ⟨33, 14, 14, 7, [8], []⟩
def body := returnBody ++ childBody
def yielded := output.references 27
def checked : Sibling.Recognized body yielded :=
  ⟨returnBody, childBody, restore, child, output, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def header (answer : Nat) : Header := ⟨⟨9, 17, 19, 7, 0⟩, 0, 1, answer⟩
def frame (outer outerInstance position prior : Nat) : QueryContinuation.Frame :=
  ⟨outer, outerInstance, 0, position, [prior]⟩
def oldRecord (model : DomainModel) (outer outerInstance position prior : Nat) : model.Value oldLayout.type :=
  (outer, outerInstance, 0, position, prior, ())
def parent (model : DomainModel) : model.Value parentLayout.type := (29, ())
def stores (model : DomainModel) (record : model.Value oldLayout.type)
    (frames : List (model.Value newLayout.type)) : Domain.Environment model.toCarriers :=
  [.data ⟨.sequence oldLayout.type, oldData, [record]⟩, .data ⟨.sequence newLayout.type, newData, frames⟩]
def environment (model : DomainModel) (record : model.Value oldLayout.type)
    (frames : List (model.Value newLayout.type)) (answer constructor anchorInstance : Nat) :
    Domain.Environment model.toCarriers :=
  (header answer).encode (stores model record frames) ++
    [.data ⟨.sequence parentLayout.type, parentData, [parent model]⟩,
     .data ⟨(Child.referenceLayout "SiblingReference").type, rfl, (constructor, anchorInstance, ())⟩]

theorem recognized : (Sibling.recognize 12 state body yielded).isSome = true := by decide +kernel

set_option backward.isDefEq.respectTransparency false in
/-- The current child's instance and position differ from the saved parent's.
The preceding reply and current reply retain their order for every arena size. -/
theorem actual (model : DomainModel) (program : Program) (context : Context)
    (frames : List (model.Value newLayout.type))
    (outer outerInstance position prior answer constructor anchorInstance : Nat) :
    let initial := environment model (oldRecord model outer outerInstance position prior)
      frames answer constructor anchorInstance
    ∃ record, Sibling.Encodes (model := model) newLayout 1 rfl (frame outer outerInstance position prior) answer record ∧
      Nonempty (Original.Simulation Eq (fun _ live ↦ initial <+: live)
        (if frames.length < indexLimit then
          .done (Child.outputValues model newLayout newData frames record 5 constructor anchorInstance
            8 0 answer [.data ⟨.sequence oldLayout.type, oldData,
              [oldRecord model outer outerInstance position prior]⟩] [])
         else .halt .exhausted)
        ((Domain.evaluate model program context body initial).bind fun final ↦
          (Domain.read final yielded).elim (.halt .refused) .done)) := by
  dsimp only
  have positionLaw (record : model.Value oldLayout.type)
      (_encoded : QueryContinuation.Encodes "EarlierFrame" 1
        (frame outer outerInstance position prior) record)
      (next : model.Value newLayout.type)
      (_encoding : Sibling.Encodes (model := model) newLayout 1 rfl
        (frame outer outerInstance position prior) answer next) :
      let ready := ReturnPrefix.projected restore model parentData
        (environment model (oldRecord model outer outerInstance position prior)
          frames answer constructor anchorInstance)
        record (frame outer outerInstance position prior) (parent model)
      Nonempty (Original.Simulation
        (fun value final ↦ final = Child.positioned model newLayout newData ready frames next value)
        (fun _ live ↦ ArtifactBinding.Captures (RecordAppend.result model newLayout newData ready frames next) live)
        (PIR.Process.done (I := Domain.effects model.toCarriers) 5)
        (Domain.step model program context positionInstruction
          (RecordAppend.result model newLayout newData ready frames next))) := by
    dsimp only
    rw [show positionInstruction =
      ⟨.execute (.indexConstant 5), [], [.data .index], []⟩ from rfl,
      Domain.Correspondence.execute]
    have law := ConnectionPrimitives.view_execute model (.indexConstant 5)
      .nil rfl rfl (RecordAppend.result model newLayout newData
        (ReturnPrefix.projected restore model parentData
          (environment model (oldRecord model outer outerInstance position prior)
            frames answer constructor anchorInstance)
          record (frame outer outerInstance position prior) (parent model)) frames next) [] rfl
    simp [Primitive.results, Primitive.evaluateOn, indexLimit, primitiveOutcome,
      PIR.Process.bind, Original.encodeHelperResult, Domain.encodeValues_cons,
      Domain.encodeValues_nil, Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle] at law
    rw [law]
    exact ⟨.done rfl⟩
  have restoration := checked.simulation model program context (header answer)
    (stores model (oldRecord model outer outerInstance position prior) frames)
    (environment model (oldRecord model outer outerInstance position prior) frames answer constructor anchorInstance)
    rfl rfl rfl rfl (by decide) (by decide)
  dsimp only [checked, restore, child, lookup, newPlacement] at restoration
  have loaded := restoration
    [oldRecord model outer outerInstance position prior] (frame outer outerInstance position prior)
    (show QueryContinuation.Stored "EarlierFrame" 1
      [oldRecord model outer outerInstance position prior] 0 (frame outer outerInstance position prior)
      from ⟨oldRecord model outer outerInstance position prior, rfl, (prior, ()), rfl, rfl⟩)
    (show (environment model (oldRecord model outer outerInstance position prior)
      frames answer constructor anchorInstance)[8]? =
      some (.data ⟨.sequence oldLayout.type, QueryContinuation.frameData "EarlierFrame" 1,
        [oldRecord model outer outerInstance position prior]⟩) from rfl)
  have parentLoaded := loaded parentData (RecordProjection.allFields_local _ rfl)
    [parent model] (parent model) rfl rfl (by decide)
  have dispatch := parentLoaded newData frames constructor anchorInstance
    (by intro record encoded; exact ⟨rfl, rfl⟩)
    (by intro value member; simp only [List.mem_singleton] at member; subst value; decide)
  have whole := dispatch (.done 5)
    (by
      intro record encoded next encoding
      simpa only [PIR.Process.interpret, restore, lookup] using
        positionLaw record encoded next encoding) 8 0
    (by
      intro record encoded next encoding childPosition
      simp [Child.result, Child.positioned, RecordAppend.result,
        ReturnPrefix.projected, ReturnPrefix.restored, environment, Header.encode,
        Header.values, QueryResumption.Coordinates.values, stores, frame,
        QueryContinuation.Frame.values, output, IndexLiterals.encode,
        RecordProjection.results, RecordProjection.allFields,
        parent, parentLayout, Original.encodeHelperResult, ProductFields.unpack,
        Domain.encodeValues_cons, Domain.encodeValues_nil,
        Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle])
  simpa [PIR.Process.interpret, PIR.Process.bind, header, output, stores] using whole

/-- Swapping the prior reply and current reply remains type-correct but does
not encode the actual source return order. Whole-arm admission rejects it. -/
theorem swapped_answers :
    (Sibling.recognize 12 state
      (returnBody ++ RecordAppend.instructions newLayout { newPlacement with fields := [17, 18, 19, 20, 7, 21] } ++
        [positionInstruction] ++ Child.referenceInstructions "SiblingReference" 11 ++
        IndexLiterals.instructions [8]) yielded).isNone = true := by decide +kernel

theorem wrong_store_output :
    (Sibling.recognize 12 state body ((output.references 27).set 8 9)).isNone = true := by decide +kernel

#print axioms actual
#print axioms swapped_answers
#print axioms wrong_store_output
end Tests.QueryControllerSibling
