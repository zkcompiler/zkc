module

public import ZkcSecurityExamples.Gkr.HonestProducerOccurrences
public import ZkcSecurity.Bindings.Sumcheck.Residual
public import ZkcSecurity.Bindings.Source.PublicUniform

@[expose] public section

/-! The actual three-coefficient Sumcheck application. Its implementation
state retains the source iteration coordinate and pending point. The generic
Sumcheck family supplies the adversarial round mathematics at degree two. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.SourceRounds
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Obligations
open ZkcExamples.Structured ZkcSecurity.Examples.Components
open ZkcSecurity.Source ZkcSecurity.Families.Sumcheck
open ZkcSecurity.FiatShamir OracleComp OracleSpec
variable {F G : Type} [Field F] [DecidableEq F]

abbrev State (F : Type) (n : Nat) := Nat × Rounds.State F n

def program (ctx : ProtocolContext) (site : String) (handle : Nat) :
    Program (Occurrence.signature (uniformCarriers F G)) Unit (State F) (Message.coefficientTriples F) where
  claim state := state.2.claim
  receive _ state :=
    .call (.enter ⟨site, state.1⟩) fun _ =>
    .call (.action (.receive (.field "bls12-381.fr") (GkrVerifier.roundSite ctx "0") (ctx.roles 0))) fun a =>
    .call (.action (.receive (.field "bls12-381.fr") (GkrVerifier.roundSite ctx "1") (ctx.roles 0))) fun b =>
    .call (.action (.receive (.field "bls12-381.fr") (GkrVerifier.roundSite ctx "2") (ctx.roles 0))) fun c =>
    .done (some (a,b,c))
  query _ _ _ := .action (.query (GkrVerifier.challengeSite ctx) "bls12-381.fr" (.cons handle .nil))
  challenge _ _ _ r := r
  deliver _ state _ r :=
    .call (.action (.send (ty := (.field "bls12-381.fr")) (GkrVerifier.deliverySite ctx) (ctx.roles 0) r)) fun _ =>
    .call (.leave ⟨site, state.1⟩) fun _ => .done ()
  advance _ state m r := (state.1 + 1, Rounds.advance state.2 m r)

def representation (ctx : ProtocolContext) (site : String) (handle : Nat) :
    Representation (program (F := F) (G := G) ctx site handle) (GkrRoundsReference.data F) where
  state state := state.2.reference
  advance _ _ _ _ := rfl
  claim _ _ _ _ := rfl

theorem binding (ctx : ProtocolContext) (site : String) (handle count : Nat) {n : Nat}
    (state : State F (n + count)) :
    ((program (G := G) ctx site handle).remaining count () state).bind
      (fun final => .done (Rounds.project final.2)) =
    HonestProducerOccurrences.validatorRounds ctx handle site state.1 count (Rounds.project state.2) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [Program.remaining, HonestProducerOccurrences.validatorRounds]
    simp only [program, IterationObservations.within_eq, Occurrence.iterations,
      IterationObservations.enter, IterationObservations.leave,
      GkrVerifier.round, GkrVerifier.roundFirst, GkrVerifier.roundSecond,
      PIR.Process.interpret, CommonAdapter.embed, Occurrence.actions, PIR.Process.bind]
    congr 1; funext entered; congr 1; funext a; congr 1; funext b; congr 1; funext c
    have boundary : (Message.ofTriple (a,b,c)).boundary = a+a+b+c := by
      simp only [Message.ofTriple, Zkc.Protocols.AlgebraicRounds.Message.boundary,
        Zkc.Protocols.AlgebraicRounds.Message.evaluate]; ring
    have evaluation (r : F) : (Message.ofTriple (a,b,c)).evaluate r = a+r*(b+r*c) := by
      simp only [Message.ofTriple, Zkc.Protocols.AlgebraicRounds.Message.evaluate]; ring
    by_cases checked : state.2.claim = a+a+b+c
    · simp only [boundary, Rounds.project, GkrVerifier.roundCheck, checked, eq_self, ↓reduceIte,
        GkrVerifier.roundChallenge, PIR.Process.bind, PIR.Process.interpret,
        CommonAdapter.embed, Occurrence.actions]
      congr 1; funext r; congr 1; funext sent; congr 1; funext left
      simpa only [program, Rounds.advance, Rounds.project, evaluation] using
        ih (state.1+1, Rounds.advance state.2 (a,b,c) r)
    · simp only [boundary, Rounds.project, GkrVerifier.roundCheck, checked, Ne.symm checked,
        ↓reduceIte, PIR.Process.bind, PIR.Process.interpret]

def queries (ctx : ProtocolContext) (site : String) (handle : Nat) :
    QueryInterface (program (F := F) (G := G) ctx site handle) PublicProperties.interface where
  event _ _ _ := .challenge (GkrVerifier.challengeSite ctx) "bls12-381.fr" handle
  decode _ _ _ := some
  challenge _ _ _ := id
  absorbed _ _ _ := rfl
  decoded _ _ _ _ _ decoded := (Option.some.inj decoded).symm

variable [Fintype F] [SampleableType F]
attribute [local instance] OccurrenceReading.rawSampleable

def residual (ctx : ProtocolContext) (site : String) (handle start count : Nat) {n : Nat}
    (root : GkrRoundsReference.State F (n+count)) (claim : F)
    (allowed : GkrRoundsReference.admissible root) (wrong : claim ≠ GkrRoundsReference.total root)
    (price : ENNReal) (covers : 2 / (Fintype.card F : ENNReal) ≤ price)
    (history : List (PublicProperties.Event (uniformCarriers F G))) :
    Derivation PublicProperties.interface (PublicProperties.escape price)
      (fun _ result => Rounds.Residual (n := n) root result) history
      (HonestProducerOccurrences.validatorRounds ctx handle site start count ([],claim)) := by
  let initial : State F (n+count) := (start, ⟨root, [], claim⟩)
  have derived := SumcheckResidual.remaining (representation (G := G) ctx site handle)
    Message.coefficientTriples_laws GkrRoundsReference.laws (queries ctx site handle)
    (PublicUniform.empty price) (by
      intro k context state admissible m reached p q different left right
      exact PublicUniform.bound price _ _ _ _
        ((ZkcSecurity.Algebra.Polynomial.agreement_uniform_le p q different left right).trans
          (by simpa only [max_self, Nat.cast_ofNat] using covers)) reached)
    count () initial history ⟨allowed,wrong⟩
  let interaction : PIR.Interaction (Occurrence.signature (uniformCarriers F G)) :=
    ⟨Unit, Unit, fun _ => (), fun _ _ => True, fun _ _ _ => ()⟩
  have returns := Program.returns (program (G := G) ctx site handle) interaction
    (fun state => Rounds.Anchored root state.2)
    (fun _ state anchored m r => Rounds.anchored_advance root state.2 anchored m r)
    count () initial () (Rounds.anchored_initial root claim)
  have framed := derived.frameReturns interaction (fun state => Rounds.Anchored root state.2) () returns
  have projected : Derivation PublicProperties.interface (PublicProperties.escape price)
      (fun _ result => Rounds.Residual (n := n) root result) history
      (((program ctx site handle).remaining count () initial).bind
        (fun state => .done (Rounds.project state.2))) :=
    framed.bind (fun state => .done (Rounds.project state.2))
    (fun reached state holds => Derivation.done
      ⟨state.2, holds.2, holds.1.1, holds.1.2, rfl⟩)
  exact projected.transport (binding ctx site handle count initial).symm

#print axioms residual
end ZkcSecurity.Realizations.Gkr.SourceRounds
