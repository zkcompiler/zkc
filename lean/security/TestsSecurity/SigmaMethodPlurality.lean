import ZkcSecurity.Families.Sigma.ResponseDifference
import ZkcSecurity.Examples.Subjects.Schnorr.Claims
import ZkcSecurity.Examples.Subjects.SchnorrAnd.Claims
import Mathlib.Data.ZMod.Basic

/-! Two substantive algebraic methods for the same actual source request:
upstream Schnorr special soundness and checked coefficient certificates. They
share the fixed response-difference algorithm, verifier correspondence and
forking consumer. These shared semantic links are not duplicated proof methods.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
namespace TestsSecurity.SigmaMethodPlurality
open Zkc.Claims ZkcSecurity.Claims ZkcSecurity.Endpoint
open ZkcSecurity.Tools.ClaimConstruction
open ZkcSecurity.Families.Sigma

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
  [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType G]

theorem proveCertificate {endpoint : Semantics}
    (request : KnowledgeRequest (ZkcSecurity.Examples.Subjects.Schnorr.Registration.subject (F := F) (G := G) endpoint)) :
    request.meaning := by
  have same := request.profile_eq (ZkcSecurity.Examples.Subjects.Schnorr.Registration.extractionProfile (F := F) (G := G)) rfl rfl
  apply knowledgeEndpoint request
  rw [same]
  exact { ZkcSecurity.Examples.Subjects.Schnorr.Registration.justification endpoint with
    family := { ZkcSecurity.Examples.Subjects.Schnorr.family (F := F) (G := G) with
      sound := fun statement => ResponseDifference.speciallySound (F := F) (G := G)
        (ZkcSecurity.Examples.Subjects.Schnorr.parts statement).1 } }

def library : Library := { ZkcSecurity.Examples.Subjects.Schnorr.Registration.library with
  methods := ZkcSecurity.Examples.Subjects.Schnorr.Registration.library.methods ++ [(⟨"sigma.linear_certificate", 0⟩, ``proveCertificate)]
  normalization := ZkcSecurity.Examples.Subjects.Schnorr.Registration.library.normalization ++ [``ZkcSecurity.Examples.Subjects.Schnorr.request1Data] }

def certificateData : Wire.Request := ZkcSecurity.Examples.Subjects.Schnorr.request1Data

claim_request certificateData using library method
  (some (⟨⟨"sigma.linear_certificate", 0⟩, []⟩ : Wire.Application))

/-- The receipt is accepted at the existing request's exact evaluated type. -/
example (application : String) : Receipt (ZkcSecurity.Examples.Subjects.Schnorr.request1Evaluated (F := F) (G := G) application) :=
  (certificateReceipt (F := F) (G := G) application).receipt

example (application : String) : Receipt (certificateEvaluated (F := F) (G := G) application) :=
  (ZkcSecurity.Examples.Subjects.Schnorr.request1Receipt (F := F) (G := G) application).receipt

/-- Changing attribution does not change the canonical proposition or links. -/
example (application : String) :
    (certificateReceipt (F := F) (G := G) application).receipt.provenance.method =
      ⟨"sigma.linear_certificate", 0⟩ := rfl

example (application : String) :
    (ZkcSecurity.Examples.Subjects.Schnorr.request1Receipt (F := F) (G := G) application).receipt.provenance.method =
      ⟨"fs.forking", 0⟩ := rfl

/-- The same certificate method supplies both branches of the existing AND
composition. Its shared challenge and componentwise extractor remain fixed by
the registered request, and its forking consumer is unchanged. -/
theorem proveConjunctionCertificate
    (request : KnowledgeRequest (ZkcSecurity.Examples.Subjects.SchnorrAnd.Registration.subject (F := F) (G := G))) :
    request.meaning := by
  have same := request.profile_eq
    (ZkcSecurity.Examples.Subjects.SchnorrAnd.Registration.extractionProfile (F := F) (G := G)) rfl rfl
  apply knowledgeEndpoint request
  rw [same]
  exact { ZkcSecurity.Examples.Subjects.SchnorrAnd.Registration.justification (F := F) (G := G) with
    family := { ZkcSecurity.Examples.Subjects.SchnorrAnd.family (F := F) (G := G) with
      sound := fun statement => ZkcSecurity.VCVio.SigmaAnd.speciallySound _ _
        (ResponseDifference.speciallySound (F := F) (G := G)
          (ZkcSecurity.Examples.Subjects.SchnorrAnd.parts statement).1)
        (ResponseDifference.speciallySound (F := F) (G := G)
          (ZkcSecurity.Examples.Subjects.SchnorrAnd.parts statement).2.2.1) } }

def conjunctionLibrary : Library := { ZkcSecurity.Examples.Subjects.SchnorrAnd.Registration.library with
  methods := ZkcSecurity.Examples.Subjects.SchnorrAnd.Registration.library.methods ++
    [(⟨"sigma.linear_certificate", 0⟩, ``proveConjunctionCertificate)]
  normalization := ZkcSecurity.Examples.Subjects.SchnorrAnd.Registration.library.normalization ++
    [``ZkcSecurity.Examples.Subjects.SchnorrAnd.request0Data] }

def conjunctionData : Wire.Request := ZkcSecurity.Examples.Subjects.SchnorrAnd.request0Data

claim_request conjunctionData using conjunctionLibrary method
  (some (⟨⟨"sigma.linear_certificate", 0⟩, []⟩ : Wire.Application))

example (application : String) : Receipt
    (ZkcSecurity.Examples.Subjects.SchnorrAnd.request0Evaluated (F := F) (G := G) application) :=
  (conjunctionReceipt (F := F) (G := G) application).receipt

section Refusals
open ZkcSecurity.Families.Sigma
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- With equal challenges the fixed quotient cannot cancel the key coefficient. -/
example : LinearCertificate.check
    (ResponseDifference.rows (1 : ZMod 7) 1 2 2)
    (ResponseDifference.target 1 1 2 2) (ResponseDifference.coefficients 1 1) = false := by decide +kernel

/-- A witness-search proposal cannot substitute another target in the same
certificate. The two valid transcripts below fix the recovered value to 3. -/
example : LinearCertificate.check
    (ResponseDifference.rows (1 : ZMod 7) 2 3 6)
    ![4, -1, 0] (ResponseDifference.coefficients 1 2) = false := by decide +kernel

/-- Unequal challenges between the two AND branches cannot reuse the first
branch's recovery denominator. Each separate transcript pair still verifies. -/
example : (3 : ZMod 7) = 0 + 1 * 3 ∧ (6 : ZMod 7) = 0 + 2 * 3 ∧
    (6 : ZMod 7) = 0 + 2 * 3 ∧ (5 : ZMod 7) = 0 + 4 * 3 ∧
    ((6 : ZMod 7) - 5) / ((1 : ZMod 7) - 2) ≠ 3 := by decide +kernel

end Refusals

#print axioms proveCertificate
#print axioms certificateReceipt
#print axioms conjunctionReceipt
#print axioms ZkcSecurity.Examples.Subjects.Schnorr.request1Receipt

end TestsSecurity.SigmaMethodPlurality
