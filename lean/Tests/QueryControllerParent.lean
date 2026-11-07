module

public import Zkc.Realization.QueryControllerParent

@[expose] public section
set_option autoImplicit false
namespace Tests.QueryControllerParent
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization QueryController

def state := List.range 11
def parentLayout : RecordProjection.Layout := ⟨"AnswerParent", "Record", .cons .index .nil⟩
def frameLayout := QueryContinuation.layout "AnswerFrame" 1
theorem frameData : frameLayout.type.isHandle = false := rfl
theorem parentData : parentLayout.type.isHandle = false := rfl
def frameBody := QueryContinuation.loadInstructions "AnswerFrame" 1 15 8 4
def lookupPlacement : RecordLookup.Placement := ⟨22, 21, 18, 9, "parent"⟩
def lookupBody := RecordLookup.instructions ⟨3, parentLayout.type⟩ lookupPlacement ++
  RecordProjection.instructions parentLayout 24 (RecordProjection.allFields parentLayout.fields)
def lookup : RecordLookupProjection.Recognized lookupBody :=
  ⟨_, _, ⟨⟨3, parentLayout.type⟩, lookupPlacement, rfl⟩,
    ⟨parentLayout, 24, RecordProjection.allFields parentLayout.fields, rfl⟩, rfl, rfl, rfl⟩
def returnBody := RequiredIndices.constantInstructions 11 3 7 "continuation" ++
  RequiredIndices.constantInstructions 13 5 0 "kind" ++ frameBody ++
  IndexLiterals.instructions [3] ++ lookupBody
def restore : ReturnPrefix.Recognized returnBody :=
  ⟨11, state, 7, 3, "continuation", 0, 5, "kind", frameBody,
    ⟨"AnswerFrame", 1, 15, 8, 4, rfl⟩, lookupBody, lookup,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
def reads : AnswerReads.Placement [.index, .index] := .cons 10 20 (.cons 10 7 .nil)
def answerInstruction : Zkc.Construction.Instruction :=
  ⟨.execute (.indexConstant 5), [], [.data .index], []⟩
def answerBody := reads.instructions ++ [answerInstruction] ++
  QueryResumption.appendInstructions .index 10 28
def answer : Answer.Recognized answerBody :=
  ⟨26, reads.instructions, ⟨[.index, .index], reads, rfl⟩, answerInstruction, .index, 10, [],
    by simp [answerBody, IndexLiterals.instructions]⟩
def output : Answer.Output := ⟨⟨21, 18, 19, 16, 17⟩, 5, 6, [8, 9], []⟩
def body := returnBody ++ answerBody
def yielded := output.references 28
def checked : Parent.Recognized body yielded :=
  ⟨returnBody, answerBody, restore, answer, output, 7, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def header (current : Nat) : Header := ⟨⟨9, 17, 19, 7, 0⟩, 0, 1, current⟩
def frame (outer outerInstance position prior : Nat) : QueryContinuation.Frame :=
  ⟨outer, outerInstance, 0, position, [prior]⟩
def record (model : DomainModel) (outer outerInstance position prior : Nat) : model.Value frameLayout.type :=
  (outer, outerInstance, 0, position, prior, ())
def parent (model : DomainModel) : model.Value parentLayout.type := (29, ())
def stores (model : DomainModel) (saved : model.Value frameLayout.type)
    (answers : List Nat) : Domain.Environment model.toCarriers :=
  [.data ⟨.sequence frameLayout.type, frameData, [saved]⟩,
   .data ⟨.sequence parentLayout.type, parentData, [parent model]⟩,
   .data ⟨.sequence .index, rfl, answers⟩]
def environment (model : DomainModel) (saved : model.Value frameLayout.type)
    (answers : List Nat) (current : Nat) : Domain.Environment model.toCarriers :=
  (header current).encode (stores model saved answers)

theorem recognized : (Parent.recognize 11 state body yielded).isSome = true := by decide +kernel

set_option backward.isDefEq.respectTransparency false in
/-- An arbitrary saved outer frame and two actual arena cells compose through
the complete parent arm. All read traversal and coordinates are derived, while
answer insertion retains the capacity failure for arbitrary arena lengths. -/
theorem actual (model : DomainModel) (program : Program) (context : Context)
    (answers : List Nat) (outer outerInstance position prior current left right : Nat)
    (priorFound : answers[prior]? = some left) (currentFound : answers[current]? = some right) :
    let initial := environment model (record model outer outerInstance position prior) answers current
    Nonempty (Original.Simulation Eq (fun _ live ↦ initial <+: live)
      (if answers.length < indexLimit then
        .done (Answer.outputValues model .index rfl ⟨3, 0, position, outer, outerInstance⟩ 0 answers 5
          ((stores model (record model outer outerInstance position prior) answers).take 2) [])
       else .halt .exhausted)
      ((Domain.evaluate model program context body initial).bind fun final ↦
        (Domain.read final yielded).elim (.halt .refused) .done)) := by
  dsimp only
  let initial := environment model (record model outer outerInstance position prior) answers current
  have answerLaw (saved : model.Value frameLayout.type) :
      let ready := ReturnPrefix.projected restore model parentData initial saved
        (frame outer outerInstance position prior) (parent model) ++
          AnswerReads.encoded (model := model) (types := [.index, .index]) (.cons left (.cons right .nil))
      Nonempty (Original.Simulation
        (fun value final ↦ final = Answer.computed model .index rfl ready value)
        (fun _ live ↦ ArtifactBinding.Captures ready live)
        (PIR.Process.done (I := Domain.effects model.toCarriers) (5 : Nat))
        (Domain.step model program context answerInstruction ready)) := by
    dsimp only
    rw [show answerInstruction =
      ⟨.execute (.indexConstant 5), [], [.data .index], []⟩ from rfl, Domain.Correspondence.execute]
    have law := ConnectionPrimitives.view_execute model (.indexConstant 5) .nil rfl rfl
      (ReturnPrefix.projected restore model parentData initial saved
        (frame outer outerInstance position prior) (parent model) ++
          AnswerReads.encoded (model := model) (types := [.index, .index]) (.cons left (.cons right .nil))) [] rfl
    simp [Primitive.results, Primitive.evaluateOn, indexLimit, primitiveOutcome,
      PIR.Process.bind, Original.encodeHelperResult, Domain.encodeValues_cons,
      Domain.encodeValues_nil, Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle] at law
    rw [law]
    exact ⟨.done rfl⟩
  have restoration := checked.simulation (Kind := Unit) model program context (header current)
    (stores model (record model outer outerInstance position prior) answers) initial
    rfl rfl rfl rfl (by decide) (by decide)
  dsimp only [checked, restore, answer, lookup, output] at restoration
  have loaded := restoration [record model outer outerInstance position prior]
    (frame outer outerInstance position prior)
    (show QueryContinuation.Stored "AnswerFrame" 1
      [record model outer outerInstance position prior] 0 (frame outer outerInstance position prior)
      from ⟨record model outer outerInstance position prior, rfl, (prior, ()), rfl, rfl⟩) rfl
    parentData (RecordProjection.allFields_local _ rfl) [parent model] (parent model) rfl rfl (by decide)
  have installed := loaded (fun (_ : Unit) ↦ Ty.index) [(), ()] rfl (fun _ ↦ answers)
    (by intro saved encoded; exact .cons rfl rfl (.cons rfl rfl .nil))
    (.cons left (.cons right .nil)) (.cons priorFound (.cons currentFound .nil)) rfl answers
    (by intro saved encoded; rfl) (by intro value member; cases member)
  have whole := installed (.done (5 : Nat))
    (by intro saved encoded; simpa only [PIR.Process.interpret, restore, lookup,
      QueryAnswerReads.values] using answerLaw saved)
    0 (by
      intro saved encoded value
      simp [Answer.result, Answer.computed, QueryResumption.appendResults,
        ReturnPrefix.projected, ReturnPrefix.restored, initial, environment, header, Header.encode,
        Header.values, QueryResumption.Coordinates.values, stores, frame,
        QueryContinuation.Frame.values, IndexLiterals.encode, QueryAnswerReads.values, AnswerReads.encoded,
        RecordProjection.results, RecordProjection.allFields, parent, parentLayout,
        Original.encodeHelperResult, ProductFields.unpack, Domain.encodeValues_cons,
        Domain.encodeValues_nil, Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle])
  simpa [PIR.Process.interpret, PIR.Process.bind, header, Parent.restoredCoordinates,
    frame, stores] using whole

/-- Two index-typed reply operands are not interchangeable. -/
theorem swapped_answers :
    (Parent.recognize 11 state
      (returnBody ++ (AnswerReads.Placement.cons (type := .index) 10 7
        (.cons (type := .index) 10 20 .nil)).instructions ++ [answerInstruction] ++
          QueryResumption.appendInstructions .index 10 28) yielded).isNone = true := by decide +kernel

theorem child_coordinates_refused :
    (Parent.recognize 11 state body (yielded.set 1 1)).isNone = true := by decide +kernel

#print axioms actual
#print axioms swapped_answers
#print axioms child_coordinates_refused
end Tests.QueryControllerParent
