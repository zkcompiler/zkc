module

public import Zkc.Realization.QueryControllerAnswer

@[expose] public section
set_option autoImplicit false
namespace Tests.QueryControllerAnswer
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization QueryController

def readPlacement : AnswerReads.Placement [.index, .index] := .cons 8 9 (.cons 8 10 .nil)
def answerInstruction : Zkc.Construction.Instruction :=
  ⟨.execute (.indexConstant 5), [], [.data .index], []⟩
def body := readPlacement.instructions ++ [answerInstruction] ++
  QueryResumption.appendInstructions .index 8 13
def checked : Answer.Recognized body :=
  ⟨11, readPlacement.instructions, ⟨[.index, .index], readPlacement, rfl⟩,
    answerInstruction, .index, 8, [], by simp [body, IndexLiterals.instructions]⟩
def output : Answer.Output := ⟨⟨0, 1, 2, 3, 4⟩, 5, 6, [], []⟩
def coordinates : QueryResumption.Coordinates := ⟨3, 7, 11, 13, 17⟩
def environment (model : DomainModel) (answers : List Nat) (first second : Nat) :
    Domain.Environment model.toCarriers :=
  (show Header from ⟨coordinates, 0, 1, 19⟩).encode
    [.data ⟨.sequence .index, rfl, answers⟩, .data (.index first), .data (.index second)]

theorem recognized : (Answer.recognize 11 body).isSome = true := by decide +kernel

/-- Parent completion may reuse both phase and kind cells. The ordered child
reads precede a constant source answer, then insertion checks arena capacity. -/
theorem actual (model : DomainModel) (program : Program) (context : Context)
    (answers : List Nat) (first second left right : Nat)
    (firstFound : answers[first]? = some left) (secondFound : answers[second]? = some right) :
    Nonempty (Original.Simulation Eq
      (fun _ live ↦ environment model answers first second <+: live)
      (if answers.length < indexLimit then
        .done (Answer.outputValues model .index rfl coordinates 0 answers 5 [] [])
       else .halt .exhausted)
      ((Domain.evaluate model program context body (environment model answers first second)).bind fun final ↦
        (Domain.read final (output.references 13)).elim (.halt .refused) .done)) := by
  let initial := environment model answers first second
  have read : AnswerReads.Readback model initial readPlacement
      (show Values model.Value [.index, .index] from .cons left (.cons right .nil)) :=
    .cons answers first rfl rfl rfl firstFound (.cons answers second rfl rfl rfl secondFound .nil)
  let ready := initial ++ AnswerReads.encoded (model := model) (types := [.index, .index])
    (.cons left (.cons right .nil))
  have law : Domain.step model program context answerInstruction ready =
      .done (Answer.computed model .index rfl ready 5) := by
    rw [show answerInstruction =
      ⟨.execute (.indexConstant 5), [], [.data .index], []⟩ from rfl,
      Domain.Correspondence.execute]
    have constant := ConnectionPrimitives.view_execute model (.indexConstant 5) .nil rfl rfl ready [] rfl
    simpa [Primitive.results, Primitive.evaluateOn, indexLimit, primitiveOutcome,
      PIR.Process.bind, Original.encodeHelperResult, Domain.encodeValues_cons,
      Domain.encodeValues_nil, Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle,
      Answer.computed] using constant
  have answerLaw : Original.Simulation
      (fun answer final ↦ final = Answer.computed model .index rfl ready answer)
      (fun _ live ↦ ArtifactBinding.Captures ready live)
      (PIR.Process.done (I := Domain.effects model.toCarriers) (5 : Nat))
      (Domain.step model program context answerInstruction ready) := by
    rw [law]
    exact .done rfl
  exact checked.output model program context rfl initial rfl (.cons left (.cons right .nil)) read
    answers rfl (by intro value member; cases member) (.done (5 : Nat)) answerLaw output coordinates 0 [] []
    rfl rfl rfl (by intro answer; exact ⟨rfl, rfl⟩)

/-- Appending a preceding child result in place of the calculated parent answer
is type-correct but fails the complete suffix check. -/
theorem wrong_answer_slot :
    (Answer.recognize 11 (readPlacement.instructions ++ [answerInstruction] ++
      QueryResumption.appendInstructions .index 8 12)).isNone = true := by decide +kernel

#print axioms actual
#print axioms wrong_answer_slot
end Tests.QueryControllerAnswer
