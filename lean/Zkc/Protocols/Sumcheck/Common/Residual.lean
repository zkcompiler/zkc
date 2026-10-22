module

public import Zkc.Protocols.Sumcheck.Common.Program

@[expose] public section

/-! The actual two-round residual, before a selected terminal continuation. -/
set_option autoImplicit false
namespace Zkc.Protocols.Sumcheck.Common
open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native

structure Residual (F : Type) where
  first : F
  second : F
  claim : F
  deriving DecidableEq

variable {F : Type} [Field F] [DecidableEq F]

def roundsWith (wiring : Wiring) (arithmetic : VerifierArithmetic F)
    (claim : F) (service : Nat) : PIR.Process (actions (F := F)) (Residual F) :=
  .call (.receive (.field wiring.fieldDomain) wiring.firstSites.1 wiring.prover) fun a =>
  .call (.receive (.field wiring.fieldDomain) wiring.firstSites.2.1 wiring.prover) fun b =>
  .call (.receive (.field wiring.fieldDomain) wiring.firstSites.2.2 wiring.prover) fun c =>
  if decide (arithmetic.boundary ⟨a,b,c⟩ = claim) then
    .call (.query wiring.firstChallenge wiring.fieldDomain (.cons service .nil)) fun first =>
    .call (.send (ty := .field wiring.fieldDomain) wiring.firstDelivery wiring.prover first) fun _ =>
    .call (.receive (.field wiring.fieldDomain) wiring.secondSites.1 wiring.prover) fun d =>
    .call (.receive (.field wiring.fieldDomain) wiring.secondSites.2.1 wiring.prover) fun e =>
    .call (.receive (.field wiring.fieldDomain) wiring.secondSites.2.2 wiring.prover) fun f =>
    if decide (arithmetic.boundary ⟨d,e,f⟩ = arithmetic.message ⟨a,b,c⟩ first) then
      .call (.query wiring.secondChallenge wiring.fieldDomain (.cons service .nil)) fun second =>
      .call (.send (ty := .field wiring.fieldDomain) wiring.secondDelivery wiring.prover second) fun _ =>
      .done ⟨first, second, arithmetic.message ⟨d,e,f⟩ second⟩
    else .halt .reject
  else .halt .reject

abbrev rounds (wiring : Wiring) (claim : F) (service : Nat) :=
  roundsWith wiring (standardArithmetic (F := F)) claim service

private theorem bind_if {I : PIR.Signature} {A B : Type} (p : Prop) [Decidable p]
    (left right : PIR.Process I A) (next : A → PIR.Process I B) :
    (if p then left else right).bind next = if p then left.bind next else right.bind next := by
  split <;> rfl

omit [Field F] in
theorem rounds_terminal (wiring : Wiring) (arithmetic : VerifierArithmetic F)
    (coefficients : Coefficients F) (claim : F) (service : Nat) :
    (roundsWith wiring arithmetic claim service).bind (fun residual =>
      .done (some (decide (residual.claim = arithmetic.statement coefficients residual.first residual.second)))) =
    experimentWith wiring arithmetic coefficients claim service := by
  simp only [roundsWith, experimentWith, PIR.Process.bind, bind_if]

structure ResidualContract (wiring : Wiring)
    (implementation : F → Nat → PIR.Process (actions (F := F)) (Residual F)) : Prop where
  realizes : ∀ claim service, PIR.ExactRefinement (implementation claim service) (rounds wiring claim service)

theorem ResidualContract.compose {wiring : Wiring}
    {implementation : F → Nat → PIR.Process (actions (F := F)) (Residual F)}
    (certificate : ResidualContract wiring implementation)
    {A : Type} {left right : Residual F → PIR.Process (actions (F := F)) A}
    (terminal : ∀ residual, PIR.ExactRefinement (left residual) (right residual))
    (claim : F) (service : Nat) :
    PIR.ExactRefinement ((implementation claim service).bind left)
      ((rounds wiring claim service).bind right) :=
  (certificate.realizes claim service).bind_congr terminal

end Zkc.Protocols.Sumcheck.Common
