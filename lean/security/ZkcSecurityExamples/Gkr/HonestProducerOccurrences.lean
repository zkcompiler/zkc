module

public import ZkcSecurityExamples.Gkr.HonestProducerRoundAlgorithm
public import ZkcSecurity.Bindings.Source.PairFrames
public import Zkc.Source.Structured.CommonAdapter
public import Zkc.Source.Structured.ObservedLoop

@[expose] public section

/-! The complete honest round loop with real source occurrence boundaries.
The shared finite fold retains enter/leave; no protocol evaluator is added.
Erasure identifies the same algorithmic source view proved in HonestProducerRounds. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZkcSecurity.Realizations.Gkr.HonestProducerOccurrences
open Zkc Source Structured Construction
open ZkcExamples.Structured
open ZkcSecurity.Examples.Components
open ZkcSecurity.Source HonestProducerRounds
open GkrRoundsRealization (RawState)

variable {F G : Type} [Field F] [DecidableEq F]

abbrev Signature (F G : Type) := Occurrence.signature (uniformCarriers F G)

/-- The shrinking reference dimension is logical state in the same observed
fold. No runtime factor, delivered reply or complete point prefix is dropped. -/
def producerRounds (ctx : ProtocolContext) (site : String) (start count : Nat) {n : Nat}
    (reference : GkrRoundsReference.State F (n + count)) (raw : RawState F) (point : List F) :
    PIR.Process (Signature F G) (Output F n) :=
  ObservedLoop.descending (State := fun remaining => Output F (n + remaining)) Occurrence.iterations site
    (fun _ state _ => (execute ctx 1 state.reference state.raw state.point).interpret Occurrence.actions)
    start count ⟨reference, raw, point⟩

def validatorRounds (ctx : ProtocolContext) (handle : Nat) (site : String)
    (start count : Nat) (value : List F × F) : PIR.Process (Signature F G) (List F × F) :=
  ObservedLoop.counted Occurrence.iterations site (fun value _ =>
    ((GkrVerifier.round ctx handle value).interpret CommonAdapter.embed).interpret Occurrence.actions)
    start count value

omit [Field F] [DecidableEq F] in
theorem actions_erase {A : Type} (source : PIR.Process (participantInterface F G) A) :
    (source.interpret Occurrence.actions).interpret Occurrence.erase = source := by
  rw [PIR.Process.interpret_interchange Occurrence.actions Occurrence.erase
    (fun operation => .call operation .done) (fun _ => rfl)]
  exact PIR.Process.interpret_identity source

omit [DecidableEq F] in
theorem producerRounds_erase (ctx : ProtocolContext) (site : String) (start count : Nat) {n : Nat}
    (reference : GkrRoundsReference.State F (n + count)) (raw : RawState F) (point : List F) :
    (producerRounds (G := G) ctx site start count reference raw point).interpret Occurrence.erase =
      execute ctx count reference raw point := by
  rw [producerRounds, ObservedLoop.descending_interpret _ Occurrence.iterations_erase]
  simp only [actions_erase]
  exact ObservedLoop.descending_eq (State := fun remaining => Output F (n + remaining))
    IterationObservations.silent site _
    (fun _ count state => execute ctx count (n := n) state.reference state.raw state.point)
    (fun _ _ => rfl) (fun _ _ _ => rfl) start count ⟨reference, raw, point⟩

theorem validatorRounds_erase (ctx : ProtocolContext) (handle : Nat) (site : String)
    (start count : Nat) (value : List F × F) :
    (validatorRounds (G := G) ctx handle site start count value).interpret Occurrence.erase =
      (PIR.repeatN count (GkrVerifier.round ctx handle) value).interpret CommonAdapter.embed := by
  exact ObservedLoop.interpret_repeated Occurrence.erase Occurrence.iterations_erase site _
    (GkrVerifier.round ctx handle) CommonAdapter.embed (fun _ => actions_erase _) start count value

omit [Field F] [DecidableEq F] in
/-- All-return facts are insensitive to observation boundaries, while the
construction still checks every reached leave and may refuse it. -/
theorem erased_yields {A : Type} (source : PIR.Process (Signature F G) A)
    (property : A → Prop) (holds : PIR.Yields property (source.interpret Occurrence.erase)) :
    PIR.Yields property source := by
  induction source with
  | done => exact holds
  | halt => trivial
  | call operation next ih =>
    cases operation with
    | enter frame => exact fun _ => ih () holds
    | leave frame => exact fun _ => ih () holds
    | action operation => exact fun reply => ih reply (holds reply)

omit [DecidableEq F] in
/-- The complete producer carries an arbitrary pending point prefix without
changing its computed messages or any actual iteration boundary. -/
theorem producerRounds_prefix (ctx : ProtocolContext) (site : String)
    (start count : Nat) {n : Nat} (reference : GkrRoundsReference.State F (n + count))
    (raw : RawState F) (precedingPoint point : List F) :
    producerRounds (G := G) ctx site start count reference raw (precedingPoint ++ point) =
      (producerRounds ctx site start count reference raw point).bind fun result =>
        .done { result with point := precedingPoint ++ result.point } := by
  induction count generalizing start raw point with
  | zero => rfl
  | succ count ih =>
    simp only [producerRounds, ObservedLoop.descending_succ, IterationObservations.within, Occurrence.iterations,
      execute, PIR.Process.interpret, Occurrence.actions, PIR.Process.bind]
    congr 1
    funext _
    congr 1
    funext _
    congr 1
    funext _
    congr 1
    funext _
    congr 1
    funext r
    change F at r
    congr 1
    funext _
    simpa only [List.append_assoc, producerRounds, Occurrence.iterations, execute,
      PIR.Process.interpret, Occurrence.actions, PIR.Process.bind] using ih (start + 1)
      (GkrRoundsReference.restrict reference r) (raw.restrict r) (point ++ [r])

/-- Pending claims carry their complete input prefix. Adding that prefix is
an exact common-verifier equation, including failed checks and stopped runs. -/
theorem validatorRounds_prefix (ctx : ProtocolContext) (handle : Nat) (site : String)
    (start count : Nat) (precedingPoint point : List F) (claim : F) :
    validatorRounds (G := G) ctx handle site start count (precedingPoint ++ point, claim) =
      (validatorRounds ctx handle site start count (point, claim)).bind
        fun result => .done (precedingPoint ++ result.1, result.2) := by
  induction count generalizing start point claim with
  | zero => rfl
  | succ count ih =>
    simp only [validatorRounds, ObservedLoop.counted_succ, IterationObservations.within, Occurrence.iterations,
      GkrVerifier.round, GkrVerifier.roundFirst, GkrVerifier.roundSecond,
      PIR.Process.interpret, CommonAdapter.embed, Occurrence.actions, PIR.Process.bind]
    congr 1
    funext _
    congr 1
    funext c0
    congr 1
    funext c1
    congr 1
    funext c2
    simp only [GkrVerifier.roundCheck]
    by_cases check : claim = c0 + c0 + c1 + c2
    · simp only [check, ite_true, PIR.Process.interpret, CommonAdapter.embed,
        Occurrence.actions, PIR.Process.bind, GkrVerifier.roundChallenge]
      congr 1
      funext r
      change F at r
      congr 1
      funext _
      congr 1
      funext _
      simpa only [List.append_assoc, validatorRounds, Occurrence.iterations,
        GkrVerifier.round, GkrVerifier.roundFirst, GkrVerifier.roundSecond, GkrVerifier.roundCheck,
        PIR.Process.interpret, CommonAdapter.embed, Occurrence.actions, PIR.Process.bind] using
        ih (start + 1) (point ++ [r]) (c0 + r * (c1 + r * c2))
    · simp only [check, ite_false, PIR.Process.interpret, PIR.Process.bind]

omit [Field F] [DecidableEq F] in
/-- Splitting the complete pending point recovers exactly the two independent
endpoints used by the line polynomial. No verifier-only point is introduced. -/
theorem split_pending_point (width : Nat) (left right : List F) (sized : left.length = width) :
    (left ++ right).take width = left ∧ (left ++ right).drop width = right := by
  subst width
  simp

/-- Honest source pairing is proved before routing. The same mathematical
message and restriction laws are used by the degree-two Sumcheck reference. -/
theorem rounds (ctx : ProtocolContext) (scope : PairScope)
    (roles : ctx.roles 0 = scope.producer ∧ ctx.roles 1 = scope.validator)
    (handle : Nat) (site : String) (start count : Nat) {n : Nat}
    (reference : GkrRoundsReference.State F (n + count)) (raw : RawState F) (point : List F)
    (allowed : GkrRoundsReference.admissible reference)
    (delivery : (GkrVerifier.challengeSite ctx,
      GkrVerifier.deliverySite ctx) ∈ scope.deliveries) :
    Pair scope (fun result value => value =
      (result.point, GkrRoundsReference.total result.reference))
      (producerRounds (G := G) ctx site start count reference raw point)
      (validatorRounds ctx handle site start count (point, GkrRoundsReference.total reference)) := by
  induction count generalizing start raw point with
  | zero => exact .done rfl
  | succ count ih =>
    rw [producerRounds, ObservedLoop.descending_succ, validatorRounds, ObservedLoop.counted_succ]
    have boundary : GkrRoundsReference.total reference =
        (GkrRoundsReference.message reference).constant +
        (GkrRoundsReference.message reference).constant +
        (GkrRoundsReference.message reference).linear +
        (GkrRoundsReference.message reference).quadratic := by
      have law := GkrRoundsReference.laws.boundary_eq reference allowed
      change (Zkc.Protocols.Sumcheck.messagePolynomial (GkrRoundsReference.message reference)).eval 0 +
        (Zkc.Protocols.Sumcheck.messagePolynomial (GkrRoundsReference.message reference)).eval 1 = _ at law
      rw [Zkc.Protocols.Sumcheck.messagePolynomial_eval, Zkc.Protocols.Sumcheck.messagePolynomial_eval] at law
      simpa [Zkc.Protocols.AlgebraicRounds.Message.evaluate, GkrRoundsReference.data, add_assoc] using law.symm
    have one : Pair scope
        (fun (result : Output F (n + count)) value =>
          value = (result.point, GkrRoundsReference.total result.reference) ∧
          GkrRoundsReference.admissible result.reference)
        ((execute (G := G) ctx 1 reference raw point).interpret Occurrence.actions)
        (((GkrVerifier.round (G := G) ctx handle (point, GkrRoundsReference.total reference)).interpret
          CommonAdapter.embed).interpret Occurrence.actions) := by
      simp only [execute, GkrVerifier.round, GkrVerifier.roundFirst,
        GkrVerifier.roundSecond, PIR.Process.interpret, CommonAdapter.embed,
        Occurrence.actions, PIR.Process.bind]
      apply Pair.message _ _ _ _ _ rfl roles
      apply Pair.message _ _ _ _ _ rfl roles
      apply Pair.message _ _ _ _ _ rfl roles
      simp only [GkrVerifier.roundCheck, boundary, ↓reduceIte,
        GkrVerifier.roundChallenge, PIR.Process.interpret, CommonAdapter.embed,
        Occurrence.actions, PIR.Process.bind]
      apply Pair.challenge _ _ _ _ _ _ roles delivery
      intro r
      exact .done ⟨by
        have law := GkrRoundsReference.evaluation reference r allowed.1
        apply congrArg (fun scalar => (point ++ [r], scalar))
        change _ = GkrRoundsReference.total (GkrRoundsReference.restrict reference r)
        rw [← law]
        simp only [Zkc.Protocols.AlgebraicRounds.Message.evaluate]
        ring, allowed.2 r⟩
    exact (one.within site start).bind _ _ (by
      rintro result value ⟨rfl, admissible⟩
      exact ih (start + 1) result.reference result.raw result.point admissible)

end ZkcSecurity.Realizations.Gkr.HonestProducerOccurrences
