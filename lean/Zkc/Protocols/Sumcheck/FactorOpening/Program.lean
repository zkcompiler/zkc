module

public import Zkc.Protocols.Sumcheck.Common.Residual

@[expose] public section

/-! Two-round Sumcheck followed by two sequential factor-opening checks.
The executable public-factor instance verifies evaluations directly. Abstract
checks have no correctness or cryptographic law unless one is supplied.
-/
set_option autoImplicit false
namespace Zkc.Protocols.Sumcheck.FactorOpening
open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native
open Zkc.Protocols.Sumcheck.Common

structure Factor (F : Type) where
  constant : F
  second : F
  first : F
  mixed : F

structure Statement (F : Type) where
  left : Factor F
  right : Factor F

structure Wiring where
  rounds : Common.Wiring
  leftSite : String
  rightSite : String

variable {F : Type} [Field F] [DecidableEq F]

def value (factor : Factor F) (first second : F) : F :=
  factor.constant + second * factor.second + first * (factor.first + second * factor.mixed)

def coefficients (statement : Statement F) : Coefficients F :=
  let l := statement.left
  let r := statement.right
  ⟨⟨l.constant * r.constant,
      l.constant * r.second + l.second * r.constant,
      l.second * r.second⟩,
    ⟨l.constant * r.first + l.first * r.constant,
      l.constant * r.mixed + l.second * r.first + l.first * r.second + l.mixed * r.constant,
      l.second * r.mixed + l.mixed * r.second⟩,
    ⟨l.first * r.first,
      l.first * r.mixed + l.mixed * r.first,
      l.mixed * r.mixed⟩⟩

omit [DecidableEq F] in
theorem evaluate_product (statement : Statement F) (first second : F) :
    Common.evaluate (coefficients statement) first second =
      value statement.left first second * value statement.right first second := by
  dsimp [coefficients, Common.evaluate, wireEvaluate, value]
  ring

structure Checks (F : Type) where
  left : Statement F → Residual F → F → Bool
  right : Statement F → Residual F → F → Bool

def publicChecks : Checks F where
  left statement residual opening := decide (opening = value statement.left residual.first residual.second)
  right statement residual opening := decide (opening = value statement.right residual.first residual.second)

def terminal (wiring : Wiring) (checks : Checks F) (statement : Statement F) (residual : Residual F) :
    PIR.Process (actions (F := F)) (Option Bool) :=
  .call (.receive (.field wiring.rounds.fieldDomain) wiring.leftSite wiring.rounds.prover) fun left =>
  if checks.left statement residual left then
    .call (.receive (.field wiring.rounds.fieldDomain) wiring.rightSite wiring.rounds.prover) fun right =>
    .done (some (checks.right statement residual right && decide (residual.claim = left * right)))
  else .halt .reject

def experimentWith (wiring : Wiring) (checks : Checks F) (statement : Statement F) (claim : F) (service : Nat) :
    PIR.Process (actions (F := F)) (Option Bool) :=
  (rounds wiring.rounds claim service).bind (terminal wiring checks statement)

abbrev experiment (wiring : Wiring) (statement : Statement F) (claim : F) (service : Nat) :=
  experimentWith wiring (publicChecks (F := F)) statement claim service

abbrev Verifier (F : Type) [Field F] := Statement F → F → Nat → PIR.Process (actions (F := F)) (Option Bool)

structure VerifierContract (wiring : Wiring) (checks : Checks F) (implementation : Verifier F) : Prop where
  realizes : ∀ statement claim service,
    PIR.ExactRefinement (implementation statement claim service) (experimentWith wiring checks statement claim service)

/-- Separate certificates meet at the actual returned residual, with no state reset. -/
theorem compose_contract {wiring : Wiring} {checks : Checks F}
    {implementation : F → Nat → PIR.Process (actions (F := F)) (Residual F)}
    (roundCertificate : ResidualContract wiring.rounds implementation)
    {finish : Statement F → Residual F → PIR.Process (actions (F := F)) (Option Bool)}
    (openingCertificate : ∀ statement residual,
      PIR.ExactRefinement (finish statement residual) (terminal wiring checks statement residual)) :
    VerifierContract wiring checks (fun statement claim service =>
      (implementation claim service).bind (finish statement)) :=
  ⟨fun statement claim service => roundCertificate.compose (openingCertificate statement) claim service⟩

end Zkc.Protocols.Sumcheck.FactorOpening
