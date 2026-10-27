module

public import ZkcSecurity.Realizations.Gkr.HonestProducerPair

@[expose] public section

/-! The complete honest round loop with real source occurrence boundaries.
The existing Original.fold handles enter/leave; no protocol evaluator is added.
Erasure identifies the same algorithmic source view proved in HonestProducerRounds. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZkcSecurity.Realizations.Gkr.HonestProducerOccurrences
open Zkc Source Structured Construction
open ZkcExamples.Structured
open ZkcSecurity.Examples.Components
open ZkcSecurity.FiatShamir HonestProducerComposition HonestProducerRounds HonestProducerPair

variable {F G : Type} [Field F] [DecidableEq F]

abbrev Signature (F G : Type) := Occurrence.signature (uniformCarriers F G)

def producerRounds (ctx : ProtocolContext) (site : String) : (start count : Nat) → {n : Nat} →
    GkrRoundsReference.State F (n + count) → Raw F → List F → PIR.Process (Signature F G) (Output F n)
  | _, 0, _, reference, raw, point => .done ⟨reference, raw, point⟩
  | start, count + 1, _, reference, raw, point =>
    (Occurrence.iterations.within site start
      ((execute ctx 1 reference raw point).interpret Occurrence.actions)).bind fun result =>
    producerRounds ctx site (start + 1) count result.reference result.raw result.point

def validatorRounds (ctx : ProtocolContext) (handle : Nat) (site : String) :
    Nat → Nat → List F × F → PIR.Process (Signature F G) (List F × F)
  | _, 0, value => .done value
  | start, count + 1, value =>
    (Occurrence.iterations.within site start
      (((GkrVerifier.round ctx handle value).interpret CommonAdapter.embed).interpret Occurrence.actions)).bind fun result =>
    validatorRounds ctx handle site (start + 1) count result

omit [Field F] [DecidableEq F] in
theorem actions_erase {A : Type} (source : PIR.Process (participantInterface F G) A) :
    (source.interpret Occurrence.actions).interpret Occurrence.erase = source := by
  induction source with
  | done => rfl
  | halt => rfl
  | call operation next ih =>
    simp only [PIR.Process.interpret, Occurrence.actions, Occurrence.erase, PIR.Process.bind, ih]

omit [DecidableEq F] in
theorem producerRounds_erase (ctx : ProtocolContext) (site : String) (start count : Nat) {n : Nat}
    (reference : GkrRoundsReference.State F (n + count)) (raw : Raw F) (point : List F) :
    (producerRounds (G := G) ctx site start count reference raw point).interpret Occurrence.erase =
      execute ctx count reference raw point := by
  induction count generalizing start raw point with
  | zero => rfl
  | succ count ih =>
    rw [producerRounds, PIR.Process.interpret_bind,
      IterationObservations.within_interpret _ Occurrence.iterations_erase,
      IterationObservations.silent_within, actions_erase]
    simp only [execute, PIR.Process.bind]
    congr 1; funext _; congr 1; funext _; congr 1; funext _; congr 1; funext r
    exact ih (start + 1) (GkrRoundsReference.restrict reference r) (raw.restrict r) (point ++ [r])

theorem validatorRounds_erase (ctx : ProtocolContext) (handle : Nat) (site : String)
    (start count : Nat) (value : List F × F) :
    (validatorRounds (G := G) ctx handle site start count value).interpret Occurrence.erase =
      (PIR.repeatN count (GkrVerifier.round ctx handle) value).interpret CommonAdapter.embed := by
  induction count generalizing start value with
  | zero => rfl
  | succ count ih =>
    rw [validatorRounds, PIR.Process.interpret_bind,
      IterationObservations.within_interpret _ Occurrence.iterations_erase,
      IterationObservations.silent_within, actions_erase, PIR.repeatN, PIR.Process.interpret_bind]
    apply congrArg (PIR.Process.bind _)
    funext next
    exact ih (start + 1) next

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

omit [Field F] [DecidableEq F] in
theorem fold_yields {A : Type} (routing : Original.Routing) (source : PIR.Process (Signature F G) A)
    (property : A → Prop) (holds : PIR.Yields property source) (state : State (F := F) (G := G)) :
    PIR.Yields (fun result => property result.1) (Original.fold routing source state) := by
  have all {I : PIR.Signature} {B : Type} (process : PIR.Process I B) :
      PIR.Yields (fun _ => True) process := by
    induction process with
    | done => trivial
    | halt => trivial
    | call _ _ ih => exact ih
  induction source generalizing state with
  | done => exact holds
  | halt => trivial
  | call operation next ih =>
    simp only [Original.fold, PIR.Process.interpretState]
    apply (all (Original.operations routing operation state)).bind
    rintro ⟨reply, reached⟩ _
    exact ih reply (holds reply) reached

omit [DecidableEq F] in
/-- The complete producer carries an arbitrary pending point prefix without
changing its computed messages or any actual iteration boundary. -/
theorem producerRounds_prefix (ctx : ProtocolContext) (site : String)
    (start count : Nat) {n : Nat} (reference : GkrRoundsReference.State F (n + count))
    (raw : Raw F) (precedingPoint point : List F) :
    producerRounds (G := G) ctx site start count reference raw (precedingPoint ++ point) =
      (producerRounds ctx site start count reference raw point).bind fun result =>
        .done { result with point := precedingPoint ++ result.point } := by
  induction count generalizing start raw point with
  | zero => rfl
  | succ count ih =>
    simp only [producerRounds, IterationObservations.within, Occurrence.iterations,
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
    simpa only [List.append_assoc] using ih (start + 1)
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
    simp only [validatorRounds, IterationObservations.within, Occurrence.iterations,
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
      simpa only [List.append_assoc] using ih (start + 1) (point ++ [r]) (c0 + r * (c1 + r * c2))
    · simp only [check, ite_false, PIR.Process.interpret, PIR.Process.bind]

omit [Field F] [DecidableEq F] in
/-- Splitting the complete pending point recovers exactly the two independent
endpoints used by the line polynomial. No verifier-only point is introduced. -/
theorem split_pending_point (width : Nat) (left right : List F) (sized : left.length = width) :
    (left ++ right).take width = left ∧ (left ++ right).drop width = right := by
  subst width
  simp

/-- Exact routes are required at each actual induction index, inside its real
frame. The enclosing stack and history are carried without restriction. -/
theorem rounds (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (ctx : ProtocolContext) (handle : Nat) (site : String) (start count : Nat) {n : Nat}
    (reference : GkrRoundsReference.State F (n + count)) (raw : Raw F) (point : List F)
    (allowed : GkrRoundsReference.admissible reference)
    (state : State (F := F) (G := G))
    (routes : ∀ index, RoundRoutes routing ctx (state.frames ++ [⟨site, index⟩]) handle) :
    Readback (fun left right => ∃ result history,
      left = (result, { state with history := history }) ∧
      right = ((result.point, GkrRoundsReference.total result.reference), { state with history := history }))
      (Original.fold { routing with mode := .producer }
        (producerRounds ctx site start count reference raw point) state)
      (Original.fold { routing with mode := .validator }
        (validatorRounds ctx handle site start count (point, GkrRoundsReference.total reference)) state) := by
  induction count generalizing start raw point state with
  | zero => exact .done ⟨⟨reference, raw, point⟩, state.history, rfl, rfl⟩
  | succ count ih =>
    rw [producerRounds, validatorRounds, Original.fold_bind, Original.fold_bind]
    let entered : State (F := F) (G := G) := { state with frames := state.frames ++ [⟨site, start⟩] }
    have one := HonestProducerPair.rounds (F := F) (G := G) routing replacement profile ctx handle 1
      reference raw point allowed entered (routes start)
    simp only [PIR.repeatN, PIR.Process.bind_done] at one
    have invariant : PIR.Yields (fun output => GkrRoundsReference.admissible output.reference)
        (execute (G := G) ctx 1 reference raw point) := by
      intro _ _ _ r
      exact allowed.2 r
    have framed := frame_left one (constructed_yields _ _ _ invariant entered)
    have wrapped := within routing site start state
      ((execute ctx 1 reference raw point).interpret Occurrence.actions)
      (((GkrVerifier.round ctx handle (point, GkrRoundsReference.total reference)).interpret
        CommonAdapter.embed).interpret Occurrence.actions)
      (fun left right => ∃ result history,
        left = (result, { state with history := history }) ∧
        right = ((result.point, GkrRoundsReference.total result.reference), { state with history := history }) ∧
        GkrRoundsReference.admissible result.reference)
      (framed.mono (by
        rintro left right ⟨⟨result, history, rfl, rfl⟩, allowedResult⟩
        exact ⟨rfl, rfl, result, history, rfl, rfl, allowedResult⟩))
    apply wrapped.bind
    rintro left right ⟨result, history, rfl, rfl, allowedResult⟩
    exact ih (start + 1) result.reference result.raw result.point allowedResult
      { state with history := history } routes

end ZkcSecurity.Realizations.Gkr.HonestProducerOccurrences
