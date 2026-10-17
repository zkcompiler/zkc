module

public import ZkcExamples.Structured.SchnorrResponseOriginalData
public import ZkcExamples.Structured.SchnorrResponseCandidateData
public import ZkcExamples.Structured.SchnorrResponseMutatedData
public import Zkc.Source.Structured.Inlining
public import Zkc.Source.Structured.ClosedProfile
public import Mathlib.Algebra.Ring.Int.Defs

@[expose] public section

/-! Exact original/prepared model equality for the authored scalar response.
The subject is nonce + challenge * secret, not an interactive Schnorr protocol.
Constructor data is compared with fresh native exports by the sibling driver. -/

namespace ZkcExamples.Structured.SchnorrResponse
open Zkc.Source Zkc.Source.Structured

set_option maxRecDepth 20000
-- Keep reductions of admitted subjects direct; body constructors use normal unfolding.
set_option smartUnfolding false
set_option maxHeartbeats 4000000

def original : ClosedProgram := (checkClosed SchnorrResponseOriginalData.snapshot).toOption.get (by decide +kernel)
def candidate : ClosedProgram := (checkClosed SchnorrResponseCandidateData.snapshot).toOption.get (by decide +kernel)
def mutated : ClosedProgram := (checkClosed SchnorrResponseMutatedData.snapshot).toOption.get (by decide +kernel)

def originalImported : ClosedImported SchnorrResponseOriginalData.snapshot := ⟨original, rfl⟩
def candidateImported : ClosedImported SchnorrResponseCandidateData.snapshot := ⟨candidate, rfl⟩
def mutatedImported : ClosedImported SchnorrResponseMutatedData.snapshot := ⟨mutated, rfl⟩

private abbrev scalar : Ty := .field "bls12-381.fr"
private abbrev helper : Helper :=
  ⟨"s16h7363686e6f72725f726573706f6e73658h726573706f6e7365", .math, [scalar, scalar, scalar], [scalar]⟩

/-- Named checked declaration; clients do not depend on its table index. -/
private def responseDefinition : CheckedDefinition :=
  (original.payload.definitions.find? fun definition => definition.name == helper.name).get
    (by decide +kernel)

set_option smartUnfolding true in
private def responseBody : Region dialect [scalar, scalar, scalar] [scalar] :=
  .letOp (.fieldMultiply "bls12-381.fr")
    (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil
    (.letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil
      (.ret (.cons .here .nil)))

set_option smartUnfolding true in
private def originalBody : Region dialect [scalar, scalar, scalar] [scalar] :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.invoke helper) (Operands.identity _) .nil (.ret (.cons .here .nil))

set_option smartUnfolding true in
private def candidateBody : Region dialect [scalar, scalar, scalar] [scalar] :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.fieldMultiply "bls12-381.fr")
    (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil
    (.letOp (.mark "") .nil .nil <|
    .letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil
      (.ret (.cons .here .nil)))

private theorem response_exact : responseDefinition.raw = responseBody.erase := rfl
private theorem original_exact : original.payload.entry.raw = originalBody.erase := rfl
private theorem candidate_exact : candidate.payload.entry.raw = candidateBody.erase := rfl

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def inputs (nonce challenge secret : F) : Values (assignment F G)
    [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] :=
  .cons nonce (.cons challenge (.cons secret .nil))

/-- An exact checked-body contract supplies the generic inlining premise for
every actual tuple, including repeated or reordered caller operands. -/
private theorem invoke_response (actual : Values (assignment F G) helper.inputs) :
    invoke (original.payload.meanings F G) helper actual =
      responseBody.denote (meaning F G (original.payload.meanings F G)) actual.get :=
  Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    original.payload responseDefinition (List.get_find?_mem _)
    responseBody response_exact actual

/-- Equality of complete processes for the exact native original and prepared
candidate, universally over the chosen scalar ring, lawful group module and inputs. -/
theorem original_eq_candidate (nonce challenge secret : F) :
    original.denote F G (inputs nonce challenge secret) =
      candidate.denote F G (inputs nonce challenge secret) := by
  exact (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    original.payload originalBody original_exact
    (inputs nonce challenge secret)).trans
    ((inline_invoke (original.payload.meanings F G) helper responseBody invoke_response
      (Operands.identity _) (.ret (.cons .here .nil)) (inputs nonce challenge secret).get).trans
      ((by rfl : (Region.bind (responseBody.rename (Operands.identity _).get)
        (.ret (.cons .here .nil))).denote (meaning F G (original.payload.meanings F G))
          (inputs nonce challenge secret).get =
        candidateBody.denote (meaning F G (candidate.payload.meanings F G))
          (inputs nonce challenge secret).get).trans
        (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
          candidate.payload candidateBody candidate_exact
          (inputs nonce challenge secret)).symm))

theorem candidate_eq_response (nonce challenge secret : F) :
    candidate.denote F G (inputs nonce challenge secret) =
      .done (.cons (nonce + challenge * secret) .nil) :=
  (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    candidate.payload candidateBody candidate_exact
    (inputs nonce challenge secret)).trans (by rfl)

theorem original_eq_response (nonce challenge secret : F) :
    original.denote F G (inputs nonce challenge secret) =
      .done (.cons (nonce + challenge * secret) .nil) :=
  (original_eq_candidate (G := G) nonce challenge secret).trans
    (candidate_eq_response (G := G) nonce challenge secret)

set_option smartUnfolding true in
private def mutatedBody : Region dialect [scalar, scalar, scalar] [scalar] :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.fieldMultiply "bls12-381.fr")
    (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil
    (.letOp (.mark "") .nil .nil <|
    .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil
      (.ret (.cons .here .nil)))

theorem mutated_eq_subtraction (nonce challenge secret : F) :
    mutated.denote F G (inputs nonce challenge secret) =
      .done (.cons (nonce - challenge * secret) .nil) :=
  (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    mutated.payload mutatedBody (by rfl)
    (inputs nonce challenge secret)).trans (by rfl)

/-- Both programs pass admission. Replacing only the prepared entry's addition
with subtraction changes the model result from 17 to -13 at (2, 3, 5). -/
theorem admitted_mutation_changes_meaning :
    original.denote Int Int (inputs 2 3 5) ≠ mutated.denote Int Int (inputs 2 3 5) := by
  rw [original_eq_response, mutated_eq_subtraction]
  intro same
  have impossible : (17 : Int) = -13 := congrArg
    (fun process => match closedOutcome process with
      | .returned result => result.get .here
      | .stopped _ => 0) same
  exact (by decide : (17 : Int) ≠ -13) impossible

end ZkcExamples.Structured.SchnorrResponse
