module

public import Zkc.Realization.QueryControllerChild
public import Zkc.Realization.QueryAnswerReads

@[expose] public section

/-! Parent completion reads the ordered child answers, computes the original
answer, and inserts it into its kind's arena. Insertion may reuse existing phase
and kind literals. The complete emitted suffix is checked without prescribing
whether common-subexpression elimination retains those constants. -/
set_option autoImplicit false
namespace Zkc.Realization.QueryController.Answer
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Recognized (body : List Construction.Instruction) where
  start : Nat
  readsBody : List Construction.Instruction
  reads : AnswerReads.Recognized readsBody
  answer : Construction.Instruction
  type : Ty
  arena : Nat
  literals : List Nat
  exactBody : body = readsBody ++ [answer] ++
    QueryResumption.appendInstructions type arena (start + reads.types.length) ++
    IndexLiterals.instructions literals

def recognize (start : Nat) (body : List Construction.Instruction) : Option (Recognized body) :=
  (List.range (body.length + 1)).findSome? fun split ↦ do
    let readsBody := body.take split
    let reads ← AnswerReads.recognize readsBody
    let answer :: length :: _ :: constants := body.drop split | none
    let .execute (.sequenceLength type) := length.operation | none
    let [arena] := length.operands | none
    let literals ← constants.mapM fun instruction ↦
      match instruction.operation with
      | .execute (.indexConstant value) => some value
      | _ => none
    if exactBody : body = readsBody ++ [answer] ++
        QueryResumption.appendInstructions type arena (start + reads.types.length) ++
        IndexLiterals.instructions literals then
      some ⟨start, readsBody, reads, answer, type, arena, literals, exactBody⟩
    else none

def computed (model : DomainModel) (type : Ty) (data : type.isHandle = false)
    (environment : Domain.Environment model.toCarriers) (answer : model.Value type) :
    Domain.Environment model.toCarriers := environment ++ [.data ⟨type, data, answer⟩]

def result (model : DomainModel) (type : Ty) (data : type.isHandle = false)
    (environment : Domain.Environment model.toCarriers) (answers : List (model.Value type))
    (answer : model.Value type) (literals : List Nat) : Domain.Environment model.toCarriers :=
  computed model type data environment answer ++ QueryResumption.appendResults model type data answers answer ++
    IndexLiterals.encode literals

/-- Complete suffix execution. The source answer's stops precede arena capacity;
no successful result or arbitrary output tuple is assumed. Ordered readback is
the common saved-frame/arena relation, separate from the mathematical law. -/
theorem Recognized.simulation {body : List Construction.Instruction} (checked : Recognized body)
    (model : DomainModel) (program : Program) (context : Context)
    (data : checked.type.isHandle = false)
    (environment : Domain.Environment model.toCarriers)
    (start : checked.start = environment.length)
    (values : Values model.Value checked.reads.types)
    (read : AnswerReads.Readback model environment checked.reads.placement values)
    (answers : List (model.Value checked.type))
    (readArena : environment[checked.arena]? =
      some (.data ⟨.sequence checked.type, data, answers⟩))
    (literalBounds : ∀ value ∈ checked.literals, value < indexLimit)
    (source : Closed (model.Value checked.type))
    (answerLaw : Original.Simulation
      (fun answer frame ↦ frame = computed model checked.type data
        (environment ++ AnswerReads.encoded values) answer)
      (fun _ frame ↦ ArtifactBinding.Captures (environment ++ AnswerReads.encoded values) frame)
      (source.interpret (closedLift (I := Domain.effects model.toCarriers)))
      (Domain.step model program context checked.answer (environment ++ AnswerReads.encoded values))) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      ((source.interpret (closedLift (I := Domain.effects model.toCarriers))).bind fun answer ↦
        if answers.length < indexLimit then
          .done (result model checked.type data (environment ++ AnswerReads.encoded values)
            answers answer checked.literals)
        else .halt .exhausted)
      (Domain.evaluate model program context body environment)) := by
  have width : (AnswerReads.encoded values).length = checked.reads.types.length := by
    have sorts := Domain.encodeValues_sorts read.encoding
    simpa using congrArg List.length sorts
  obtain ⟨reads⟩ := read.actual program context
  rw [← checked.reads.exactBody] at reads
  refine ⟨?_⟩
  simp only [checked.exactBody, Domain.evaluate_append, PIR.Process.bind_assoc]
  apply reads.continueDone (fun _ held ↦ held)
  rw [Domain.Correspondence.evaluate_cons]
  refine .checkpoint _ (List.prefix_append _ _) ?_
  rw [PIR.Process.bind_assoc]
  apply answerLaw.bind
  · intro process frame retained
    exact (List.prefix_append _ _).trans (List.prefix_iff_eq_take.mpr retained.symm)
  · intro answer frame equal
    subst frame
    simp only [PIR.Process.bind]
    let ready := computed model checked.type data (environment ++ AnswerReads.encoded values) answer
    have retained : environment <+: ready :=
      (List.prefix_append _ _).trans (List.prefix_append _ _)
    refine .checkpoint _ retained ?_
    have readResult : ready[checked.start + checked.reads.types.length]? =
        some (.data ⟨checked.type, data, answer⟩) := by
      simp [ready, computed, start, ← width]
    have arena : ready[checked.arena]? =
        some (.data ⟨.sequence checked.type, data, answers⟩) :=
      Original.read_append (Original.read_append readArena _) _
    have insert := Classical.choice (QueryResumption.appendSimulation model checked.type data
      ready environment retained checked.arena (checked.start + checked.reads.types.length)
      answers answer arena readResult)
    rw [← QueryResumption.appendCorrespondence model program context] at insert
    by_cases room : answers.length < indexLimit
    · simp only [room, ↓reduceIte] at insert ⊢
      apply insert.continueDone (fun _ held ↦ held)
      exact (IndexLiterals.simulation model program context checked.literals literalBounds
        (ready ++ QueryResumption.appendResults model checked.type data answers answer)).mapRelations
          (fun _ _ equal ↦ equal)
          (fun _ _ held ↦ (retained.trans (List.prefix_append _ _)).trans held)
    · simp only [room, ↓reduceIte] at insert ⊢
      exact insert.continueHalt _ (fun _ held ↦ held)

structure Output where
  coordinates : QueryResumption.Coordinates
  kind : Nat
  phase : Nat
  before : List Nat
  after : List Nat

def Output.references (output : Output) (answerSlot : Nat) : List Nat :=
  output.coordinates.values ++ [output.kind, output.phase, answerSlot + 1] ++
    output.before ++ [answerSlot + 2] ++ output.after

def outputValues (model : DomainModel) (type : Ty) (data : type.isHandle = false)
    (coordinates : QueryResumption.Coordinates) (kind : Nat) (answers : List (model.Value type))
    (answer : model.Value type) (before after : Domain.Environment model.toCarriers) :
    Domain.Environment model.toCarriers :=
  (show Header from ⟨coordinates, kind, 1, answers.length⟩).encode
    (before ++ [.data ⟨.sequence type, data, answers ++ [answer]⟩] ++ after)

theorem read_output (model : DomainModel) (type : Ty) (data : type.isHandle = false)
    (environment : Domain.Environment model.toCarriers) (answers : List (model.Value type))
    (answer : model.Value type) (literals : List Nat) (output : Output)
    (coordinates : QueryResumption.Coordinates) (kind : Nat)
    (before after : Domain.Environment model.toCarriers)
    (readCoordinates : Domain.read environment output.coordinates.values =
      some (IndexLiterals.encode coordinates.values))
    (readBefore : Domain.read environment output.before = some before)
    (readAfter : Domain.read environment output.after = some after)
    (readKind : (result model type data environment answers answer literals)[output.kind]? =
      some (.data (.index kind)))
    (readPhase : (result model type data environment answers answer literals)[output.phase]? =
      some (.data (.index 1))) :
    Domain.read (result model type data environment answers answer literals)
      (output.references environment.length) =
        some (outputValues model type data coordinates kind answers answer before after) := by
  let final := result model type data environment answers answer literals
  have coordinatesRead : Domain.read final output.coordinates.values =
      some (IndexLiterals.encode coordinates.values) :=
    RecordAllocator.read_extended _ _ _ _ (RecordAllocator.read_extended _ _ _ _
      (RecordAllocator.read_extended _ _ _ _ readCoordinates))
  have beforeRead : Domain.read final output.before = some before :=
    RecordAllocator.read_extended _ _ _ _ (RecordAllocator.read_extended _ _ _ _
      (RecordAllocator.read_extended _ _ _ _ readBefore))
  have afterRead : Domain.read final output.after = some after :=
    RecordAllocator.read_extended _ _ _ _ (RecordAllocator.read_extended _ _ _ _
      (RecordAllocator.read_extended _ _ _ _ readAfter))
  have length : final[environment.length + 1]? = some (.data (.index answers.length)) := by
    simp [final, result, computed, QueryResumption.appendResults, List.append_assoc]
  have arena : final[environment.length + 2]? =
      some (.data ⟨.sequence type, data, answers ++ [answer]⟩) := by
    simp [final, result, computed, QueryResumption.appendResults, List.append_assoc]
  have header : Domain.read final [output.kind, output.phase, environment.length + 1] =
      some [.data (.index kind), .data (.index 1), .data (.index answers.length)] := by
    simp [Domain.read, readKind, readPhase, length, final]
  have store : Domain.read final [environment.length + 2] =
      some [.data ⟨.sequence type, data, answers ++ [answer]⟩] := by simp [Domain.read, arena]
  change Domain.read final _ = _
  simp only [Output.references, Domain.read, List.mapM_append] at coordinatesRead header beforeRead store afterRead ⊢
  rw [coordinatesRead, header, beforeRead, store, afterRead]
  rfl

/-- Output routing is shared by all parent-answer suffixes. The five restored
coordinates and surrounding stores are retained; the answer slot names the
newly inserted value. The source calculation and insertion retain their stops. -/
theorem Recognized.output {body : List Construction.Instruction} (checked : Recognized body)
    (model : DomainModel) (program : Program) (context : Context)
    (data : checked.type.isHandle = false)
    (environment : Domain.Environment model.toCarriers) (start : checked.start = environment.length)
    (values : Values model.Value checked.reads.types)
    (read : AnswerReads.Readback model environment checked.reads.placement values)
    (answers : List (model.Value checked.type))
    (readArena : environment[checked.arena]? = some (.data ⟨.sequence checked.type, data, answers⟩))
    (literalBounds : ∀ value ∈ checked.literals, value < indexLimit)
    (source : Closed (model.Value checked.type))
    (answerLaw : Original.Simulation
      (fun answer frame ↦ frame = computed model checked.type data
        (environment ++ AnswerReads.encoded values) answer)
      (fun _ frame ↦ ArtifactBinding.Captures (environment ++ AnswerReads.encoded values) frame)
      (source.interpret (closedLift (I := Domain.effects model.toCarriers)))
      (Domain.step model program context checked.answer (environment ++ AnswerReads.encoded values)))
    (output : Output) (coordinates : QueryResumption.Coordinates) (kind : Nat)
    (before after : Domain.Environment model.toCarriers)
    (readCoordinates : Domain.read environment output.coordinates.values =
      some (IndexLiterals.encode coordinates.values))
    (readBefore : Domain.read environment output.before = some before)
    (readAfter : Domain.read environment output.after = some after)
    (readLiterals : ∀ answer,
      let final := result model checked.type data (environment ++ AnswerReads.encoded values)
        answers answer checked.literals
      final[output.kind]? = some (.data (.index kind)) ∧ final[output.phase]? = some (.data (.index 1))) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      ((source.interpret (closedLift (I := Domain.effects model.toCarriers))).bind fun answer ↦
        if answers.length < indexLimit then
          .done (outputValues model checked.type data coordinates kind answers answer before after)
        else .halt .exhausted)
      ((Domain.evaluate model program context body environment).bind fun final ↦
        (Domain.read final (output.references (checked.start + checked.reads.types.length))).elim (.halt .refused) .done)) := by
  obtain ⟨head⟩ := checked.simulation model program context data environment start values read answers
    readArena literalBounds source answerLaw
  have width : (AnswerReads.encoded values).length = checked.reads.types.length := by
    simpa using congrArg List.length (Domain.encodeValues_sorts read.encoding)
  refine ⟨?_⟩
  by_cases room : answers.length < indexLimit
  · simp only [room, ↓reduceIte] at head ⊢
    apply head.continueClosed source
      (fun answer ↦ result model checked.type data (environment ++ AnswerReads.encoded values)
        answers answer checked.literals) (fun _ _ _ held ↦ held)
    intro answer
    have projected := read_output model checked.type data (environment ++ AnswerReads.encoded values)
      answers answer checked.literals output coordinates kind before after
      (RecordAllocator.read_extended _ _ _ _ readCoordinates)
      (RecordAllocator.read_extended _ _ _ _ readBefore)
      (RecordAllocator.read_extended _ _ _ _ readAfter)
      (readLiterals answer).1 (readLiterals answer).2
    rw [List.length_append, width, ← start] at projected
    rw [projected]
    exact .done rfl
  · simp only [room, ↓reduceIte] at head ⊢
    cases source with
    | done answer => exact head.continueHalt _ (fun _ held ↦ held)
    | halt reason => exact head.continueHalt _ (fun _ held ↦ held)
    | call operation _ => exact nomatch operation

end Zkc.Realization.QueryController.Answer
