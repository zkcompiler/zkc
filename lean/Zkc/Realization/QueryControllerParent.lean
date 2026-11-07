module

public import Zkc.Realization.QueryControllerReturn
public import Zkc.Realization.QueryControllerAnswer
public import Zkc.Realization.QueryAnswerReads

@[expose] public section

/-! Complete parent arms restore one saved frame, read exactly its prior answer
indices followed by the current reply, and return the computed parent answer.
The certificate fixes coordinate order and operands; installation retains each
answer kind until its physical arena reads have been justified.
-/
set_option autoImplicit false
namespace Zkc.Realization.QueryController.Parent
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Recognized (body : List Construction.Instruction) (returned : List Nat) where
  returnBody : List Construction.Instruction
  answerBody : List Construction.Instruction
  restore : ReturnPrefix.Recognized returnBody
  answer : Answer.Recognized answerBody
  output : Answer.Output
  currentAnswer : Nat
  answerStart : answer.start =
    restore.frame.start + 9 + restore.frame.count + restore.lookup.projection.selections.length
  answerField : restore.state[7]? = some currentAnswer
  answerOrder : answer.reads.placement.indices =
    List.range' (restore.frame.start + 5) restore.frame.count ++ [currentAnswer]
  coordinates : output.coordinates =
    ⟨restore.frame.start + 5 + restore.frame.count, restore.frame.start + 3,
      restore.frame.start + 4, restore.frame.start + 1, restore.frame.start + 2⟩
  storeSplit : restore.state.drop 8 = output.before ++ answer.arena :: output.after
  exactBody : body = returnBody ++ answerBody
  exactOutput : returned = output.references (answer.start + answer.reads.types.length)

/-- Check the whole arm and its output, including equal-typed answer order and
the restored parent coordinates. The mathematical operation is checked by its
existing source connection rather than identified by a protocol-specific name. -/
def recognize (start : Nat) (state : List Nat) (body : List Construction.Instruction)
    (returned : List Nat) : Option (Recognized body returned) :=
  (List.range (body.length + 1)).findSome? fun split ↦ do
    let returnBody := body.take split
    let answerBody := body.drop split
    let restore ← ReturnPrefix.recognize start state returnBody
    let answer ← Answer.recognize
      (restore.frame.start + 9 + restore.frame.count + restore.lookup.projection.selections.length)
      answerBody
    let some currentAnswer := state[7]? | none
    let some kind := returned[5]? | none
    let some phase := returned[6]? | none
    let stores := state.drop 8
    let slot := stores.idxOf answer.arena
    let coordinates : QueryResumption.Coordinates :=
      ⟨restore.frame.start + 5 + restore.frame.count, restore.frame.start + 3,
        restore.frame.start + 4, restore.frame.start + 1, restore.frame.start + 2⟩
    let output : Answer.Output :=
      ⟨coordinates, kind, phase, stores.take slot, stores.drop (slot + 1)⟩
    if answerStart : answer.start =
        restore.frame.start + 9 + restore.frame.count + restore.lookup.projection.selections.length then
      if answerField : restore.state[7]? = some currentAnswer then
        if answerOrder : answer.reads.placement.indices =
            List.range' (restore.frame.start + 5) restore.frame.count ++ [currentAnswer] then
          if coordinateFields : output.coordinates =
              ⟨restore.frame.start + 5 + restore.frame.count, restore.frame.start + 3,
                restore.frame.start + 4, restore.frame.start + 1, restore.frame.start + 2⟩ then
            if storeSplit : restore.state.drop 8 = output.before ++ answer.arena :: output.after then
              if exactOutput : returned = output.references (answer.start + answer.reads.types.length) then
                some ⟨returnBody, answerBody, restore, answer, output, currentAnswer,
                  answerStart, answerField, answerOrder, coordinateFields, storeSplit,
                  (List.take_append_drop split body).symm, exactOutput⟩
              else none
            else none
          else none
        else none
      else none
    else none

def restoredCoordinates (constructor : Nat) (frame : QueryContinuation.Frame) :
    QueryResumption.Coordinates :=
  ⟨constructor, frame.parentInstance, frame.position, frame.outer, frame.outerInstance⟩

/-- The emitted read indices come from the saved prior replies followed by the
current child's reply. Neither answer values nor their order are chosen here. -/
theorem read_answer_indices {body : List Construction.Instruction} {returned : List Nat}
    (checked : Recognized body returned) (model : DomainModel)
    (data : checked.restore.lookup.projection.layout.type.isHandle = false)
    (environment : Domain.Environment model.toCarriers)
    (start : checked.restore.start = environment.length)
    (record : model.Value
      (QueryContinuation.layout checked.restore.frame.identity checked.restore.frame.count).type)
    (frame : QueryContinuation.Frame)
    (encoded : QueryContinuation.Encodes checked.restore.frame.identity
      checked.restore.frame.count frame record)
    (parent : model.Value checked.restore.lookup.projection.layout.type)
    (header : Header) (stores : Domain.Environment model.toCarriers)
    (read : Domain.read environment checked.restore.state = some (header.encode stores)) :
    Domain.read (ReturnPrefix.projected checked.restore model data environment record frame parent)
      checked.answer.reads.placement.indices =
        some (IndexLiterals.encode (frame.answers ++ [header.answer])) := by
  let prefixValues : Domain.Environment model.toCarriers :=
    environment ++ [.data (.index checked.restore.continuation), .data (.boolean true)] ++
      [.data (.index checked.restore.kind), .data (.boolean true)] ++
      [.data ⟨(QueryContinuation.layout checked.restore.frame.identity checked.restore.frame.count).type,
        QueryContinuation.frameData _ _, record⟩] ++
      IndexLiterals.encode [frame.outer, frame.outerInstance, frame.parentInstance, frame.position]
  have prefixLength : prefixValues.length = checked.restore.frame.start + 5 := by
    simp [prefixValues, IndexLiterals.encode, checked.restore.frameStart, start]
  have prior := RecordAllocator.read_appended prefixValues (IndexLiterals.encode frame.answers)
  rw [prefixLength] at prior
  have priorRestored : Domain.read (ReturnPrefix.restored checked.restore model environment record frame)
      (List.range' (checked.restore.frame.start + 5) checked.restore.frame.count) =
        some (IndexLiterals.encode frame.answers) := by
    simpa [IndexLiterals.encode, encoded.answers_length, prefixValues,
      ReturnPrefix.restored, QueryContinuation.Frame.values, List.append_assoc] using prior
  have priorProjected : Domain.read
      (ReturnPrefix.projected checked.restore model data environment record frame parent)
      (List.range' (checked.restore.frame.start + 5) checked.restore.frame.count) =
        some (IndexLiterals.encode frame.answers) :=
    RecordAllocator.read_extended _ _ _ _ (RecordAllocator.read_extended _ _ _ _
      (RecordAllocator.read_extended _ _ _ _ priorRestored))
  have current : environment[checked.currentAnswer]? = some (.data (.index header.answer)) := by
    have selected := Domain.View.read_getElem? read 7
    rw [checked.answerField] at selected
    simpa [Header.encode, Header.values, QueryResumption.Coordinates.values] using selected.symm
  have projectedCurrent :
      (ReturnPrefix.projected checked.restore model data environment record frame parent)[checked.currentAnswer]? =
        some (.data (.index header.answer)) :=
    Original.read_append (Original.read_append (Original.read_append
      (Original.read_append (Original.read_append (Original.read_append
        (Original.read_append current _) _) _) _) _) _) _
  rw [checked.answerOrder]
  simp only [Domain.read, List.mapM_append] at priorProjected ⊢
  rw [priorProjected]
  simp [List.mapM_cons, projectedCurrent, IndexLiterals.encode, List.map_append]

/-- Common source/store installation supplies the ordered semantic replies and
their kind-specific arenas. The loaded frame determines every physical index,
and the common read rule constructs the resulting heterogeneous tuple. -/
theorem read_answers {body : List Construction.Instruction} {returned : List Nat}
    (checked : Recognized body returned) (model : DomainModel)
    (data : checked.restore.lookup.projection.layout.type.isHandle = false)
    (environment : Domain.Environment model.toCarriers)
    (start : checked.restore.start = environment.length)
    (record : model.Value
      (QueryContinuation.layout checked.restore.frame.identity checked.restore.frame.count).type)
    (frame : QueryContinuation.Frame)
    (encoded : QueryContinuation.Encodes checked.restore.frame.identity
      checked.restore.frame.count frame record)
    (parent : model.Value checked.restore.lookup.projection.layout.type)
    (header : Header) (stores : Domain.Environment model.toCarriers)
    (read : Domain.read environment checked.restore.state = some (header.encode stores))
    {Kind : Type} (answerType : Kind → Ty) (kinds : List Kind)
    (types : checked.answer.reads.types = kinds.map answerType)
    (arenas : (kind : Kind) → List (model.Value (answerType kind)))
    (installed : QueryAnswerReads.Arenas model answerType arenas
      (ReturnPrefix.projected checked.restore model data environment record frame parent)
      (types ▸ checked.answer.reads.placement))
    (answers : Values (fun kind ↦ model.Value (answerType kind)) kinds)
    (stored : QueryContinuation.AnswersRead arenas (frame.answers ++ [header.answer]) answers) :
    AnswerReads.Readback model
      (ReturnPrefix.projected checked.restore model data environment record frame parent)
      checked.answer.reads.placement (types.symm ▸ QueryAnswerReads.values answers) := by
  have indices := read_answer_indices checked model data environment start record frame encoded parent
    header stores read
  have operands := installed.operands (frame.answers ++ [header.answer])
    (by simpa [IndexLiterals.encode] using indices)
  have readback := (operands.readback stored).cast types.symm
  have undo : ∀ {left right : List Ty} (same : left = right) (placement : AnswerReads.Placement left),
      (same.symm ▸ same ▸ placement) = placement := by
    intro left right same placement
    cases same
    rfl
  simpa only [undo] using readback

/-- Derive the entire restored coordinate tuple from the loaded frame and the
selected parent's static constructor. The child's same-typed coordinates cannot
substitute for these fields. -/
theorem read_coordinates {body : List Construction.Instruction} {returned : List Nat}
    (checked : Recognized body returned) (model : DomainModel)
    (data : checked.restore.lookup.projection.layout.type.isHandle = false)
    (environment : Domain.Environment model.toCarriers)
    (start : checked.restore.start = environment.length)
    (record : model.Value
      (QueryContinuation.layout checked.restore.frame.identity checked.restore.frame.count).type)
    (frame : QueryContinuation.Frame)
    (encoded : QueryContinuation.Encodes checked.restore.frame.identity
      checked.restore.frame.count frame record)
    (parent : model.Value checked.restore.lookup.projection.layout.type) :
    Domain.read (ReturnPrefix.projected checked.restore model data environment record frame parent)
      checked.output.coordinates.values = some (IndexLiterals.encode
        (restoredCoordinates checked.restore.lookup.lookup.layout.constructor frame).values) := by
  let restored := ReturnPrefix.restored checked.restore model environment record frame
  have length : restored.length = checked.restore.frame.start + 5 + checked.restore.frame.count := by
    simp [restored, ReturnPrefix.restored, QueryContinuation.Frame.values,
      encoded.answers_length, checked.restore.frameStart, start]
    omega
  have tag :
      (ReturnPrefix.projected checked.restore model data environment record frame parent)[checked.restore.frame.start + 5 + checked.restore.frame.count]? =
          some (.data (.index checked.restore.lookup.lookup.layout.constructor)) := by
    change (restored ++ _ ++ _ ++ _)[_]? = _
    rw [← length]
    simp [List.append_assoc]
  rw [checked.coordinates]
  simp only [QueryResumption.Coordinates.values, Domain.read, List.mapM_cons,
    List.mapM_nil, tag]
  simp [ReturnPrefix.projected, ReturnPrefix.restored, QueryContinuation.Frame.values,
    checked.restore.frameStart, start, List.append_assoc, Nat.add_assoc,
    restoredCoordinates, IndexLiterals.encode, List.getElem?_append]

/-- Compose the complete actual parent arm. Common installation supplies the
ordered, kind-specific answer readback and the original answer computation.
Restored coordinates, retained stores, insertion and final projection are all
constructed here, with every source stop and capacity failure retained. -/
theorem Recognized.simulation {body : List Construction.Instruction} {returned : List Nat}
    (checked : Recognized body returned) (model : DomainModel) (program : Program) (context : Context)
    (header : Header) (stores environment : Domain.Environment model.toCarriers)
    (start : checked.restore.start = environment.length)
    (read : Domain.read environment checked.restore.state = some (header.encode stores))
    (continuation : header.continuation = checked.restore.continuation)
    (kind : header.kind = checked.restore.kind)
    (continuationBound : checked.restore.continuation < indexLimit)
    (kindBound : checked.restore.kind < indexLimit)
    (oldFrames : List (model.Value
      (QueryContinuation.layout checked.restore.frame.identity checked.restore.frame.count).type))
    (frame : QueryContinuation.Frame)
    (stored : QueryContinuation.Stored checked.restore.frame.identity checked.restore.frame.count
      oldFrames header.continuationInstance frame)
    (readOldFrames : environment[checked.restore.frame.store]? = some (.data
      ⟨.sequence (QueryContinuation.layout checked.restore.frame.identity checked.restore.frame.count).type,
        QueryContinuation.frameData _ _, oldFrames⟩))
    (data : checked.restore.lookup.projection.layout.type.isHandle = false)
    (localFields : ∀ selection ∈ checked.restore.lookup.projection.selections,
      Domain.localType selection.type = true)
    (parents : List (model.Value checked.restore.lookup.projection.layout.type))
    (parent : model.Value checked.restore.lookup.projection.layout.type)
    (readParents : environment[checked.restore.lookup.lookup.placement.store]? =
      some (.data ⟨.sequence checked.restore.lookup.projection.layout.type, data, parents⟩))
    (found : parents[frame.parentInstance]? = some parent)
    (tagBound : checked.restore.lookup.lookup.layout.constructor < indexLimit)
    {Kind : Type} (answerType : Kind → Ty) (kinds : List Kind)
    (answerTypes : checked.answer.reads.types = kinds.map answerType)
    (sourceArenas : (kind : Kind) → List (model.Value (answerType kind)))
    (installedArenas : ∀ record, QueryContinuation.Encodes checked.restore.frame.identity
        checked.restore.frame.count frame record →
      QueryAnswerReads.Arenas model answerType sourceArenas
        (ReturnPrefix.projected checked.restore model data environment record frame parent)
        (answerTypes ▸ checked.answer.reads.placement))
    (sourceAnswers : Values (fun kind ↦ model.Value (answerType kind)) kinds)
    (storedAnswers : QueryContinuation.AnswersRead sourceArenas
      (frame.answers ++ [header.answer]) sourceAnswers)
    (answerData : checked.answer.type.isHandle = false)
    (answers : List (model.Value checked.answer.type))
    (readArena : ∀ record, QueryContinuation.Encodes checked.restore.frame.identity
        checked.restore.frame.count frame record →
      (ReturnPrefix.projected checked.restore model data environment record frame parent)[checked.answer.arena]? =
        some (.data ⟨.sequence checked.answer.type, answerData, answers⟩))
    (literalBounds : ∀ value ∈ checked.answer.literals, value < indexLimit)
    (source : Closed (model.Value checked.answer.type))
    (answerLaw : ∀ record, QueryContinuation.Encodes checked.restore.frame.identity
        checked.restore.frame.count frame record →
      let ready := ReturnPrefix.projected checked.restore model data environment record frame parent
      Nonempty (Original.Simulation
        (fun answer final ↦ final = Answer.computed model checked.answer.type answerData
          (ready ++ AnswerReads.encoded (answerTypes.symm ▸ QueryAnswerReads.values sourceAnswers)) answer)
        (fun _ live ↦ ArtifactBinding.Captures (ready ++ AnswerReads.encoded (answerTypes.symm ▸ QueryAnswerReads.values sourceAnswers)) live)
        (source.interpret (closedLift (I := Domain.effects model.toCarriers)))
        (Domain.step model program context checked.answer.answer (ready ++ AnswerReads.encoded (answerTypes.symm ▸ QueryAnswerReads.values sourceAnswers)))))
    (parentKind : Nat)
    (readLiterals : ∀ record, QueryContinuation.Encodes checked.restore.frame.identity
        checked.restore.frame.count frame record → ∀ answer,
      let ready := ReturnPrefix.projected checked.restore model data environment record frame parent
      let final := Answer.result model checked.answer.type answerData (ready ++ AnswerReads.encoded (answerTypes.symm ▸ QueryAnswerReads.values sourceAnswers))
        answers answer checked.answer.literals
      final[checked.output.kind]? = some (.data (.index parentKind)) ∧
        final[checked.output.phase]? = some (.data (.index 1))) :
    Nonempty (Original.Simulation Eq (fun _ live ↦ environment <+: live)
      ((source.interpret (closedLift (I := Domain.effects model.toCarriers))).bind fun answer ↦
        if answers.length < indexLimit then
          .done (Answer.outputValues model checked.answer.type answerData
            (restoredCoordinates checked.restore.lookup.lookup.layout.constructor frame) parentKind
            answers answer (stores.take checked.output.before.length)
              (stores.drop (checked.output.before.length + 1)))
        else .halt .exhausted)
      ((Domain.evaluate model program context body environment).bind fun final ↦
        (Domain.read final returned).elim (.halt .refused) .done)) := by
  obtain ⟨record, encoded, restore⟩ := checked.restore.simulation model program context
    header stores environment start read continuation kind continuationBound kindBound
    oldFrames frame stored readOldFrames data localFields parents parent readParents found tagBound
  obtain ⟨restore⟩ := restore
  let ready := ReturnPrefix.projected checked.restore model data environment record frame parent
  have readyLength : ready.length = checked.answer.start := by
    rw [checked.answerStart]
    simp [ready, ReturnPrefix.projected, ReturnPrefix.restored,
      QueryContinuation.Frame.values, encoded.answers_length,
      RecordProjection.results_length model _ parent _ localFields,
      checked.restore.frameStart, start]
    omega
  have retained : environment <+: ready :=
    ((((((List.prefix_append _ _).trans (List.prefix_append _ _)).trans
      (List.prefix_append _ _)).trans (List.prefix_append _ _)).trans
      (List.prefix_append _ _)).trans (List.prefix_append _ _)).trans (List.prefix_append _ _)
  have stateRead : Domain.read ready checked.restore.state = some (header.encode stores) :=
    RecordAllocator.read_extended _ _ _ _ (RecordAllocator.read_extended _ _ _ _
      (RecordAllocator.read_extended _ _ _ _ (RecordAllocator.read_extended _ _ _ _
        (RecordAllocator.read_extended _ _ _ _ (RecordAllocator.read_extended _ _ _ _
          (RecordAllocator.read_extended _ _ _ _ read))))))
  have storesRead : Domain.read ready (checked.restore.state.drop 8) = some stores := by
    have selected := (Phase.read_parts ready checked.restore.state (header.encode stores) stateRead 8).2
    simpa [Header.encode, Header.values, QueryResumption.Coordinates.values] using selected
  have beforeRead : Domain.read ready checked.output.before = some (stores.take checked.output.before.length) := by
    have first := (Phase.read_parts ready _ stores storesRead checked.output.before.length).1
    rw [checked.storeSplit] at first
    simpa using first
  have afterRead : Domain.read ready checked.output.after = some (stores.drop (checked.output.before.length + 1)) := by
    have last := (Phase.read_parts ready _ stores storesRead (checked.output.before.length + 1)).2
    rw [checked.storeSplit] at last
    simpa using last
  have coordinates := read_coordinates checked model data environment start record frame encoded parent
  obtain ⟨math⟩ := answerLaw record encoded
  obtain ⟨answer⟩ := checked.answer.output model program context answerData ready readyLength.symm
    (answerTypes.symm ▸ QueryAnswerReads.values sourceAnswers)
    (read_answers checked model data environment start record frame encoded parent header stores read
      answerType kinds answerTypes sourceArenas (installedArenas record encoded) sourceAnswers storedAnswers) answers (readArena record encoded) literalBounds source math
    checked.output (restoredCoordinates checked.restore.lookup.lookup.layout.constructor frame) parentKind
    (stores.take checked.output.before.length) (stores.drop (checked.output.before.length + 1))
    coordinates beforeRead afterRead (readLiterals record encoded)
  rw [← checked.exactOutput] at answer
  have weakened := answer.mapRelations (fun _ _ equal ↦ equal)
    (fun _ _ held ↦ retained.trans held)
  refine ⟨?_⟩
  simp only [checked.exactBody, Domain.evaluate_append, PIR.Process.bind_assoc]
  exact restore.continueDone (fun _ held ↦ held) weakened

end Zkc.Realization.QueryController.Parent
