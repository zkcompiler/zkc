module

public import ZkcExamples.Structured.SchnorrResponseOriginalData
public import ZkcExamples.Structured.SchnorrResponseCandidateData
public import ZkcExamples.Structured.SchnorrResponseMutatedData
public import Zkc.Source.Structured.Inlining
public import Mathlib.Algebra.Ring.Int.Defs

@[expose] public section

/-! Exact original/prepared model equality for the authored scalar response.
The subject is nonce + challenge * secret, not an interactive Schnorr protocol.
Constructor data is compared with fresh native exports by the sibling driver. -/

namespace ZkcExamples.Structured.SchnorrResponse
open Zkc.Source Zkc.Source.Structured

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def original : Program := (check SchnorrResponseOriginalData.snapshot).toOption.get (by decide +kernel)
def candidate : Program := (check SchnorrResponseCandidateData.snapshot).toOption.get (by decide +kernel)
def mutated : Program := (check SchnorrResponseMutatedData.snapshot).toOption.get (by decide +kernel)

def originalImported : Imported SchnorrResponseOriginalData.snapshot := ⟨original, rfl⟩
def candidateImported : Imported SchnorrResponseCandidateData.snapshot := ⟨candidate, rfl⟩
def mutatedImported : Imported SchnorrResponseMutatedData.snapshot := ⟨mutated, rfl⟩

private abbrev scalar : Ty := .field "bls12-381.fr"
private abbrev helper : Helper :=
  ⟨"s16h7363686e6f72725f726573706f6e73658h726573706f6e7365", [scalar, scalar, scalar], [scalar]⟩

/-- Named checked declaration; clients do not depend on its table index. -/
private def responseDefinition : CheckedDefinition :=
  (original.payload.definitions.find? fun definition => definition.name == helper.name).get
    (by decide +kernel)

private def responseBody : Region dialect [scalar, scalar, scalar] [scalar] :=
  .letOp (.fieldMultiply "bls12-381.fr")
    (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil
    (.letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil
      (.ret (.cons .here .nil)))

private def originalBody : Region dialect [scalar, scalar, scalar] [scalar] :=
  .letOp (.invoke helper) (Operands.identity _) .nil (.ret (.cons .here .nil))

private theorem response_exact : responseDefinition.raw = responseBody.erase := rfl
private theorem original_exact : original.payload.entry.raw = originalBody.erase := rfl
private theorem candidate_exact : candidate.payload.entry.raw = responseBody.erase := rfl

variable {F : Type} [CommRing F] [DecidableEq F]

def inputs (nonce challenge secret : F) : Values (scalarAssignment F)
    [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] :=
  .cons nonce (.cons challenge (.cons secret .nil))

/-- An exact checked-body contract supplies the generic inlining premise for
every actual tuple, including repeated or reordered caller operands. -/
private theorem invoke_response (actual : Values (scalarAssignment F) helper.inputs) :
    invoke (original.payload.meanings F) helper actual =
      responseBody.denote (meaning F (original.payload.meanings F)) actual.get :=
  original.payload.invoke_body_view responseDefinition (List.get_find?_mem _)
    responseBody response_exact actual

/-- Equality of complete processes for the exact native original and prepared
candidate, universally over the chosen commutative ring and scalar inputs. -/
theorem original_eq_candidate (nonce challenge secret : F) :
    original.denote F (inputs nonce challenge secret) =
      candidate.denote F (inputs nonce challenge secret) := by
  exact (original.payload.denote_body_view originalBody original_exact
    (inputs nonce challenge secret)).trans
    ((inline_invoke (original.payload.meanings F) helper responseBody invoke_response
      (Operands.identity _) (.ret (.cons .here .nil)) (inputs nonce challenge secret).get).trans
      ((by rfl : (Region.bind (responseBody.rename (Operands.identity _).get)
        (.ret (.cons .here .nil))).denote (meaning F (original.payload.meanings F))
          (inputs nonce challenge secret).get =
        responseBody.denote (meaning F (candidate.payload.meanings F))
          (inputs nonce challenge secret).get).trans
        (candidate.payload.denote_body_view responseBody candidate_exact
          (inputs nonce challenge secret)).symm))

theorem candidate_eq_response (nonce challenge secret : F) :
    candidate.denote F (inputs nonce challenge secret) =
      .done (.cons (nonce + challenge * secret) .nil) :=
  (candidate.payload.denote_body_view responseBody candidate_exact
    (inputs nonce challenge secret)).trans (by rfl)

theorem original_eq_response (nonce challenge secret : F) :
    original.denote F (inputs nonce challenge secret) =
      .done (.cons (nonce + challenge * secret) .nil) :=
  (original_eq_candidate nonce challenge secret).trans (candidate_eq_response nonce challenge secret)

private def mutatedBody : Region dialect [scalar, scalar, scalar] [scalar] :=
  .letOp (.fieldMultiply "bls12-381.fr")
    (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil
    (.letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil
      (.ret (.cons .here .nil)))

theorem mutated_eq_subtraction (nonce challenge secret : F) :
    mutated.denote F (inputs nonce challenge secret) =
      .done (.cons (nonce - challenge * secret) .nil) :=
  (mutated.payload.denote_body_view mutatedBody (by rfl)
    (inputs nonce challenge secret)).trans (by rfl)

/-- Both programs pass admission. Replacing only the prepared entry's addition
with subtraction changes the model result from 17 to -13 at (2, 3, 5). -/
theorem admitted_mutation_changes_meaning :
    original.denote Int (inputs 2 3 5) ≠ mutated.denote Int (inputs 2 3 5) := by
  rw [original_eq_response, mutated_eq_subtraction]
  intro same
  have impossible : (17 : Int) = -13 := congrArg
    (fun process => match closedOutcome process with
      | .returned result => result.get .here
      | .stopped _ => 0) same
  exact (by decide : (17 : Int) ≠ -13) impossible

end ZkcExamples.Structured.SchnorrResponse
