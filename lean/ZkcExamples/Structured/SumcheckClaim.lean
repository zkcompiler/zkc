module

public import ZkcExamples.Structured.SumcheckClaimOriginalData
public import ZkcExamples.Structured.SumcheckClaimCandidateData
public import Zkc.Source.Structured.Inlining
public import Zkc.Source.Structured.ClosedProfile
public import Zkc.Source.Structured.UnitViews

@[expose] public section

/-! Exact original/prepared model equality for a multilinear claim update.
The same nested helper is called with two different actual tuples. This scalar
computation is not the interactive Sumcheck protocol or a soundness theorem. -/

namespace ZkcExamples.Structured.SumcheckClaim
open Zkc.Source Zkc.Source.Structured

-- Keep reductions of admitted subjects direct; body constructors use normal unfolding.
set_option smartUnfolding false

abbrev scalar : Ty := .field "bls12-381.fr"
abbrev weightedHelper : Helper :=
  ⟨"s14h73756d636865636b5f636c61696d8h7765696768746564", .math, [scalar, scalar], [scalar]⟩
abbrev claimHelper : Helper :=
  ⟨"s14h73756d636865636b5f636c61696d5h636c61696d", .math, [scalar, scalar, scalar], [scalar]⟩


set_option smartUnfolding true in
def weightedBody : Region dialect [scalar, scalar] [scalar] :=
  .letOp (.fieldMultiply "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil
    (.ret (.cons .here .nil))

set_option smartUnfolding true in
def claimBody : Region dialect [scalar, scalar, scalar] [scalar] :=
  .letOp (.fieldConstant "bls12-381.fr" 1) .nil .nil
    (.letOp (.fieldSubtract "bls12-381.fr")
      (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil
      (.letOp (.invoke weightedHelper)
        (.cons (.there (.there .here)) (.cons .here .nil)) .nil
        (.letOp (.invoke weightedHelper)
          (.cons (.there (.there (.there (.there .here))))
            (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil
          (.letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil
            (.ret (.cons .here .nil))))))

set_option smartUnfolding true in
def originalBody : Region dialect [scalar, scalar, scalar] [scalar] :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.invoke claimHelper) (Operands.identity _) .nil (.ret (.cons .here .nil))

set_option smartUnfolding true in
def candidateBody : Region dialect [scalar, scalar, scalar] [scalar] :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.fieldConstant "bls12-381.fr" 1) .nil .nil
    (.letOp (.mark "") .nil .nil <|
      .letOp (.fieldSubtract "bls12-381.fr")
      (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil
      (.letOp (.mark "") .nil .nil <|
      .letOp (.fieldMultiply "bls12-381.fr")
        (.cons .here (.cons (.there (.there .here)) .nil)) .nil
        (.letOp (.mark "") .nil .nil <|
          .letOp (.fieldMultiply "bls12-381.fr")
          (.cons (.there (.there (.there (.there (.there .here)))))
            (.cons (.there (.there (.there (.there .here)))) .nil)) .nil
          (.letOp (.mark "") .nil .nil <|
            .letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil
            (.ret (.cons .here .nil))))))


namespace Original
def protocolSignature : ProtocolSignature where
  name := "s14h73756d636865636b5f636c61696d5h436c61696d"
  roles := ["role00000000"]
  inputs := [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")]
  outputs := [(.field "bls12-381.fr")]
  inputScopes := [[0], [0], [0]]
  outputScopes := [[0]]

set_option smartUnfolding true in
def protocolBody : Region protocolDialect protocolSignature.inputs protocolSignature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke {name := "s14h73756d636865636b5f636c61696d5h636c61696d", kind := .math, inputs := [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], outputs := [.field "bls12-381.fr"]}) rfl) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

structured_closed_views SumcheckClaimOriginalData.snapshot
  helpers [weighted := (weightedHelper, weightedBody), claim := (claimHelper, claimBody)]
  protocols [protocol]
  root originalBody
end Original

namespace Candidate
def protocolSignature : ProtocolSignature where
  name := "s14h73756d636865636b5f636c61696d5h436c61696d"
  roles := ["role00000000"]
  inputs := [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")]
  outputs := [(.field "bls12-381.fr")]
  inputScopes := [[0], [0], [0]]
  outputScopes := [[0]]

set_option smartUnfolding true in
def protocolBody : Region protocolDialect protocolSignature.inputs protocolSignature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldConstant "bls12-381.fr" 1) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldSubtract "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

structured_closed_views SumcheckClaimCandidateData.snapshot
  helpers [weighted := (weightedHelper, weightedBody), claim := (claimHelper, claimBody)]
  protocols [protocol]
  root candidateBody
end Candidate

def original : ClosedProgram := Original.program
def candidate : ClosedProgram := Candidate.program

def originalImported : ClosedImported SumcheckClaimOriginalData.snapshot := Original.imported
def candidateImported : ClosedImported SumcheckClaimCandidateData.snapshot := Candidate.imported

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

variable (F G) in
private def table : Meanings F G := original.payload.meanings F G

private def output (value : F) : Values (assignment F G) [scalar] := .cons value .nil

def inputs (a0 a1 r : F) : Values (assignment F G)
    [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] :=
  .cons a0 (.cons a1 (.cons r .nil))

/-- Named checked-body contract, reused at distinct actual arguments. -/
private theorem invoke_weighted (value weight : F) :
    invoke (table F G) weightedHelper (.cons value (.cons weight .nil)) =
      .done (.cons (weight * value) .nil) :=
  (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    original.payload Original.weightedDefinition Original.weighted_member
    weightedBody Original.weighted_exact (.cons value (.cons weight .nil))).trans (by rfl)

private theorem claim_contract (a0 a1 r : F) :
    claimBody.denote (meaning F G (table F G)) (inputs a0 a1 r).get =
      .done (.cons ((1 - r) * a0 + r * a1) .nil) := by
  change (invoke (table F G) weightedHelper (.cons a0 (.cons ((1 : Nat) - r) .nil))).bind
      (fun first => (invoke (table F G) weightedHelper (.cons a1 (.cons r .nil))).bind
        (fun second => .done (output (first.get .here + second.get .here)))) =
    .done (output ((1 - r) * a0 + r * a1))
  set_option smartUnfolding true in
    simp only [Nat.cast_one, invoke_weighted, PIR.Proc.bind, Values.get]

private theorem invoke_claim (a0 a1 r : F) :
    invoke (table F G) claimHelper (inputs a0 a1 r) =
      .done (.cons ((1 - r) * a0 + r * a1) .nil) :=
  (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    original.payload Original.claimDefinition Original.claim_member
    claimBody Original.claim_exact (inputs a0 a1 r)).trans (claim_contract a0 a1 r)

theorem original_eq_claim (a0 a1 r : F) :
    original.denote F G (inputs a0 a1 r) = .done (.cons ((1 - r) * a0 + r * a1) .nil) := by
  refine (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    original.payload originalBody Original.entry_exact (inputs a0 a1 r)).trans ?_
  change (invoke (table F G) claimHelper (inputs a0 a1 r)).bind
    (fun result => .done (output (result.get .here))) = .done (output ((1 - r) * a0 + r * a1))
  rw [invoke_claim]
  rfl

theorem candidate_eq_claim (a0 a1 r : F) :
    candidate.denote F G (inputs a0 a1 r) = .done (.cons ((1 - r) * a0 + r * a1) .nil) :=
  (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    candidate.payload candidateBody Candidate.entry_exact (inputs a0 a1 r)).trans (by
    change PIR.Proc.done (output (((1 : Nat) - r) * a0 + r * a1)) =
      (PIR.Proc.done (output ((1 - r) * a0 + r * a1)) : Closed _)
    simp only [Nat.cast_one])

/-- Complete process equality for these exact exports, for all scalar inputs.
The two invocations of the shared helper are justified independently. -/
theorem original_eq_candidate (a0 a1 r : F) :
    original.denote F G (inputs a0 a1 r) = candidate.denote F G (inputs a0 a1 r) :=
  (original_eq_claim (G := G) a0 a1 r).trans (candidate_eq_claim (G := G) a0 a1 r).symm

end ZkcExamples.Structured.SumcheckClaim
