module

public import ZkcSecurity.Realizations.Gkr.HonestProducerRoundAlgorithm
public import ZkcSecurity.Realizations.Gkr.HonestProducerComposition
public import Zkc.Source.Structured.CommonAdapter

@[expose] public section

/-! Synchronization of computed GKR round packets, with actual construction
state and unrestricted typed challenge replies. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace ZkcSecurity.Realizations.Gkr.HonestProducerPair
open Zkc Source Structured Construction
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcExamples.Structured
open ZkcSecurity.Examples.Components
open ZkcSecurity.FiatShamir HonestProducerComposition HonestProducerRounds

variable {F G : Type} [Field F] [DecidableEq F]

/-- Exact source-owned nominal routes at the reached occurrence stack. These
conditions concern admission/routing, not packet or helper correctness. -/
structure RoundRoutes (routing : Original.Routing) (ctx : ProtocolContext)
    (frames : Original.Frames) (handle : Nat) where
  producer : ctx.roles 0 = routing.context.producer
  validator : ctx.roles 1 = routing.context.validator
  zeroOrigin : Origin
  oneOrigin : Origin
  twoOrigin : Origin
  drawOrigin : Origin
  deliveryOrigin : Origin
  zeroRoute : routing.message frames (GkrRoundsNormalForms.round0Site ctx)
    routing.context.producer routing.context.validator = some zeroOrigin
  oneRoute : routing.message frames (GkrRoundsNormalForms.round1Site ctx)
    routing.context.producer routing.context.validator = some oneOrigin
  twoRoute : routing.message frames (GkrRoundsNormalForms.round2Site ctx)
    routing.context.producer routing.context.validator = some twoOrigin
  queryRoute : routing.draw frames (GkrRoundsNormalForms.challengeSite ctx)
    "bls12-381.fr" handle = some drawOrigin
  deliveryRoute : routing.delivery frames (GkrRoundsNormalForms.deliverySite ctx)
    "bls12-381.fr" routing.context.validator = some (drawOrigin, deliveryOrigin)
  sentRoute : routing.message frames (GkrRoundsNormalForms.deliverySite ctx)
    routing.context.validator routing.context.producer = some deliveryOrigin
  request : drawOrigin.request = some (.draw "bls12-381.fr")

def validator {A : Type} (routing : Original.Routing)
    (source : PIR.Process (Actions F G) A) (state : State (F := F) (G := G)) :=
  constructed { routing with mode := .validator } (source.interpret CommonAdapter.embed) state

omit [DecidableEq F] in
theorem boundary {n : Nat} (reference : GkrRoundsReference.State F (n + 1))
    (allowed : GkrRoundsReference.admissible reference) :
    GkrRoundsReference.total reference =
      (GkrRoundsReference.message reference).constant +
      (GkrRoundsReference.message reference).constant +
      (GkrRoundsReference.message reference).linear +
      (GkrRoundsReference.message reference).quadratic := by
  have law := GkrRoundsReference.laws (F := F) |>.boundary_eq reference allowed
  change (Zkc.Protocols.Sumcheck.messagePolynomial (GkrRoundsReference.message reference)).eval 0 +
    (Zkc.Protocols.Sumcheck.messagePolynomial (GkrRoundsReference.message reference)).eval 1 = _ at law
  rw [Zkc.Protocols.Sumcheck.messagePolynomial_eval,
    Zkc.Protocols.Sumcheck.messagePolynomial_eval] at law
  simpa [GkrRoundsReference.data, Zkc.Protocols.AlgebraicRounds.Message.evaluate, add_assoc] using law.symm

omit [DecidableEq F] in
theorem evaluation {n : Nat} (reference : GkrRoundsReference.State F (n + 1))
    (allowed : GkrRoundsReference.admissible reference) (r : F) :
    (GkrRoundsReference.message reference).constant +
      r * ((GkrRoundsReference.message reference).linear +
        r * (GkrRoundsReference.message reference).quadratic) =
      GkrRoundsReference.total (GkrRoundsReference.restrict reference r) := by
  rw [← GkrRoundsReference.evaluation reference r allowed.1]
  simp only [Zkc.Protocols.AlgebraicRounds.Message.evaluate]
  ring

/-- The complete computed producer loop synchronizes with the same verifier
body used by soundness. Neither transcript packets nor message laws are input
hypotheses. The result includes the full actual construction state. -/
theorem rounds (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (ctx : ProtocolContext) (handle count : Nat) {n : Nat}
    (reference : GkrRoundsReference.State F (n + count)) (raw : Raw F) (point : List F)
    (allowed : GkrRoundsReference.admissible reference)
    (state : State (F := F) (G := G))
    (routes : RoundRoutes routing ctx state.frames handle) :
    Readback (fun left right => ∃ result history,
      left = (result, { state with history := history }) ∧
      right = ((result.point, GkrRoundsReference.total result.reference),
        { state with history := history }))
      (constructed { routing with mode := .producer }
        (execute ctx count reference raw point) state)
      (validator routing (PIR.repeatN count (GkrVerifier.round ctx handle)
        (point, GkrRoundsReference.total reference)) state) := by
  induction count generalizing raw point state with
  | zero => exact .done ⟨⟨reference, raw, point⟩, state.history, rfl, rfl⟩
  | succ count ih =>
    simp only [execute, PIR.repeatN, GkrVerifier.round, GkrVerifier.roundFirst,
      GkrVerifier.roundSecond, PIR.Process.bind, validator, PIR.Process.interpret,
      CommonAdapter.embed, routes.producer, routes.validator]
    rw [routes.validator, routes.producer]
    apply message_step routing replacement profile state _ "bls12-381.fr" _ routes.zeroOrigin routes.zeroRoute
    let after0 : State (F := F) (G := G) := { state with history := state.history ++
      [.message routes.zeroOrigin (.field "bls12-381.fr" (GkrRoundsReference.message reference).constant)] }
    apply message_step routing replacement profile after0 _ "bls12-381.fr" _ routes.oneOrigin routes.oneRoute
    let after1 : State (F := F) (G := G) := { after0 with history := after0.history ++
      [.message routes.oneOrigin (.field "bls12-381.fr" (GkrRoundsReference.message reference).linear)] }
    apply message_step routing replacement profile after1 _ "bls12-381.fr" _ routes.twoOrigin routes.twoRoute
    let after2 : State (F := F) (G := G) := { after1 with history := after1.history ++
      [.message routes.twoOrigin (.field "bls12-381.fr" (GkrRoundsReference.message reference).quadratic)] }
    have checked := boundary reference allowed
    simp only [GkrVerifier.roundCheck, checked, ite_true, PIR.Process.bind,
      PIR.Process.interpret, CommonAdapter.embed, GkrVerifier.roundChallenge,
      routes.producer, routes.validator]
    rw [routes.producer]
    apply challenge_step routing replacement profile after2 _ _ "bls12-381.fr" handle routes.drawOrigin
      routes.deliveryOrigin routes.deliveryRoute routes.queryRoute routes.sentRoute routes.request
    intro r
    rw [evaluation reference allowed r]
    let reached : State (F := F) (G := G) := { after2 with history := after2.history ++
      [.challenge routes.drawOrigin, .message routes.deliveryOrigin (.field "bls12-381.fr" r)] }
    apply (ih (GkrRoundsReference.restrict reference r) (raw.restrict r)
      (point ++ [r]) (allowed.2 r) reached routes).mono
    rintro left right ⟨result, history, rfl, rfl⟩
    exact ⟨result, history, rfl, rfl⟩

end ZkcSecurity.Realizations.Gkr.HonestProducerPair
