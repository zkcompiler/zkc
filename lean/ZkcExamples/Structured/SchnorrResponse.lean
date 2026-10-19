module

public import ZkcExamples.Structured.SchnorrResponseOriginalData
public import ZkcExamples.Structured.SchnorrResponseCandidateData
public import ZkcExamples.Structured.SchnorrResponseMutatedData
public import Zkc.Source.Structured.Inlining
public import Zkc.Source.Structured.ClosedProfile
public import Zkc.Source.Structured.UnitViews
public import Mathlib.Algebra.Ring.Int.Defs

@[expose] public section

/-! Exact original/prepared model equality for the authored scalar response.
The subject is nonce + challenge * secret, not an interactive Schnorr protocol.
Constructor data is compared with fresh native exports by the sibling driver. -/

namespace ZkcExamples.Structured.SchnorrResponse
open Zkc.Source Zkc.Source.Structured

-- Keep reductions of admitted subjects direct; body constructors use normal unfolding.
set_option smartUnfolding false

abbrev scalar : Ty := .field "bls12-381.fr"
abbrev helper : Helper :=
  ⟨"s16h7363686e6f72725f726573706f6e73658h726573706f6e7365", .math, [scalar, scalar, scalar], [scalar]⟩

set_option smartUnfolding true in
def responseBody : Region dialect [scalar, scalar, scalar] [scalar] :=
  .letOp (.fieldMultiply "bls12-381.fr")
    (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil
    (.letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil
      (.ret (.cons .here .nil)))

set_option smartUnfolding true in
def originalBody : Region dialect [scalar, scalar, scalar] [scalar] :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.invoke helper) (Operands.identity _) .nil (.ret (.cons .here .nil))

set_option smartUnfolding true in
def candidateBody : Region dialect [scalar, scalar, scalar] [scalar] :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.fieldMultiply "bls12-381.fr")
    (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil
    (.letOp (.mark "") .nil .nil <|
    .letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil
      (.ret (.cons .here .nil)))


namespace Original
def protocolSignature : ProtocolSignature where
  name := "s16h7363686e6f72725f726573706f6e73658h526573706f6e7365"
  roles := ["role00000000"]
  inputs := [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")]
  outputs := [(.field "bls12-381.fr")]
  inputScopes := [[0], [0], [0]]
  outputScopes := [[0]]

set_option smartUnfolding true in
def protocolBody : Region protocolDialect protocolSignature.inputs protocolSignature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke {name := "s16h7363686e6f72725f726573706f6e73658h726573706f6e7365", kind := .math, inputs := [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], outputs := [.field "bls12-381.fr"]}) rfl) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

structured_closed_views SchnorrResponseOriginalData.snapshot
  helpers [response := (helper, responseBody)]
  protocols [protocol]
  root originalBody
end Original

namespace Candidate
def protocolSignature : ProtocolSignature where
  name := "s16h7363686e6f72725f726573706f6e73658h526573706f6e7365"
  roles := ["role00000000"]
  inputs := [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")]
  outputs := [(.field "bls12-381.fr")]
  inputScopes := [[0], [0], [0]]
  outputScopes := [[0]]

set_option smartUnfolding true in
def protocolBody : Region protocolDialect protocolSignature.inputs protocolSignature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

structured_closed_views SchnorrResponseCandidateData.snapshot
  helpers [response := (helper, responseBody)]
  protocols [protocol]
  root candidateBody
end Candidate

def original : ClosedProgram := Original.program
def candidate : ClosedProgram := Candidate.program

def originalImported : ClosedImported SchnorrResponseOriginalData.snapshot := Original.imported
def candidateImported : ClosedImported SchnorrResponseCandidateData.snapshot := Candidate.imported

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
    original.payload Original.responseDefinition Original.response_member
    responseBody Original.response_exact actual

/-- Equality of complete processes for the exact native original and prepared
candidate, universally over the chosen scalar ring, lawful group module and inputs. -/
theorem original_eq_candidate (nonce challenge secret : F) :
    original.denote F G (inputs nonce challenge secret) =
      candidate.denote F G (inputs nonce challenge secret) := by
  exact (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    original.payload originalBody Original.entry_exact
    (inputs nonce challenge secret)).trans
    ((inline_invoke (original.payload.meanings F G) helper responseBody invoke_response
      (Operands.identity _) (.ret (.cons .here .nil)) (inputs nonce challenge secret).get).trans
      ((by rfl : (Region.bind (responseBody.rename (Operands.identity _).get)
        (.ret (.cons .here .nil))).denote (meaning F G (original.payload.meanings F G))
          (inputs nonce challenge secret).get =
        candidateBody.denote (meaning F G (candidate.payload.meanings F G))
          (inputs nonce challenge secret).get).trans
        (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
          candidate.payload candidateBody Candidate.entry_exact
          (inputs nonce challenge secret)).symm))

theorem candidate_eq_response (nonce challenge secret : F) :
    candidate.denote F G (inputs nonce challenge secret) =
      .done (.cons (nonce + challenge * secret) .nil) :=
  (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    candidate.payload candidateBody Candidate.entry_exact
    (inputs nonce challenge secret)).trans (by rfl)

theorem original_eq_response (nonce challenge secret : F) :
    original.denote F G (inputs nonce challenge secret) =
      .done (.cons (nonce + challenge * secret) .nil) :=
  (original_eq_candidate (G := G) nonce challenge secret).trans
    (candidate_eq_response (G := G) nonce challenge secret)

set_option smartUnfolding true in
def mutatedBody : Region dialect [scalar, scalar, scalar] [scalar] :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.fieldMultiply "bls12-381.fr")
    (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil
    (.letOp (.mark "") .nil .nil <|
    .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil
      (.ret (.cons .here .nil)))

namespace Mutated
def protocolSignature : ProtocolSignature where
  name := "s16h7363686e6f72725f726573706f6e73658h526573706f6e7365"
  roles := ["role00000000"]
  inputs := [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")]
  outputs := [(.field "bls12-381.fr")]
  inputScopes := [[0], [0], [0]]
  outputScopes := [[0]]

set_option smartUnfolding true in
def protocolBody : Region protocolDialect protocolSignature.inputs protocolSignature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldSubtract "bls12-381.fr") rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

structured_closed_views SchnorrResponseMutatedData.snapshot
  helpers [response := (helper, responseBody)]
  protocols [protocol]
  root mutatedBody
end Mutated

def mutated : ClosedProgram := Mutated.program
def mutatedImported : ClosedImported SchnorrResponseMutatedData.snapshot := Mutated.imported

theorem mutated_eq_subtraction (nonce challenge secret : F) :
    mutated.denote F G (inputs nonce challenge secret) =
      .done (.cons (nonce - challenge * secret) .nil) :=
  (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    mutated.payload mutatedBody Mutated.entry_exact
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
