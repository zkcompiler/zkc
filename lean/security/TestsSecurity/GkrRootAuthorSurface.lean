import ZkcSecurityExamples.Gkr.HonestProducerSource

/-! Complete executions of the single enriched presentation and actual source
invocation, including failed handlers, incomplete input and role projection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace TestsSecurity.GkrRootAuthorSurface
open Zkc Source Structured
open ZkcExamples.Structured
open ZkcSecurity.Examples.Components
open ZkcSecurity.Realizations.Gkr HonestProducerRounds
open GkrRoundsRealization (RawState)

abbrev Actions := (participantInterface ℚ ℚ).Op
abbrev Events := Nat × Actions

/-- A history-sensitive delivery and optional stop at any reached action. The
stopping action still records its event and updates the private handler state. -/
def handler (stop : Option Nat) (reason : PIR.Stop) :
    PIR.Handler (participantInterface ℚ ℚ) Nat Events := fun operation tick =>
  if stop = some tick then ⟨.stopped reason, tick + 1, [(tick, operation)]⟩
  else match operation with
  | .send .. => ⟨.returned (), tick + 1, [(tick, operation)]⟩
  | .receive (.field _) .. => ⟨.returned ((tick + 1 : Nat) : ℚ), tick + 1, [(tick, operation)]⟩
  | _ => ⟨.stopped .refused, tick + 1, [(tick, operation)]⟩

/-- Expected events include the actual payloads, roles and qualified sites. -/
def packets {n : Nat} (ctx : ProtocolContext) (state : GkrRoundsReference.State ℚ (n + 1))
    (tick : Nat) : List Events :=
  [(tick, .send (ty := .field scalarDomain) (GkrVerifier.roundSite ctx "0") (ctx.roles 1)
      (GkrRoundsReference.message state).constant),
   (tick + 1, .send (ty := .field scalarDomain) (GkrVerifier.roundSite ctx "1") (ctx.roles 1)
      (GkrRoundsReference.message state).linear),
   (tick + 2, .send (ty := .field scalarDomain) (GkrVerifier.roundSite ctx "2") (ctx.roles 1)
      (GkrRoundsReference.message state).quadratic),
   (tick + 3, .receive (.field scalarDomain) (GkrVerifier.deliverySite ctx) (ctx.roles 1))]

/-- Two actual deliveries depend on the reached history. The result retains
all four restricted vectors, the old point prefix and the shrinking state. -/
theorem complete_enriched {n : Nat} (ctx : ProtocolContext)
    (state : GkrRoundsReference.State ℚ (n + 2)) (raw : RawState ℚ) (point : List ℚ) :
    (execute (G := ℚ) ctx 2 state raw point).run (handler none .abort) 10 =
      ⟨.returned ⟨GkrRoundsReference.restrict (GkrRoundsReference.restrict state 14) 18,
        (raw.restrict 14).restrict 18, (point ++ [14]) ++ [18]⟩, 18,
        packets ctx state 10 ++ packets ctx (GkrRoundsReference.restrict state 14) 14⟩ := rfl

/-- Forgetting changes only the complete returned value, with the same state
and exact event history. No decoding or successful-callback premise is needed. -/
theorem complete_forgotten {n : Nat} (ctx : ProtocolContext)
    (state : GkrRoundsReference.State ℚ (n + 2)) (raw : RawState ℚ) (point : List ℚ) :
    (loop (G := ℚ) ctx 2 state raw point).run (handler none .abort) 10 =
      ⟨.returned (values ((raw.restrict 14).restrict 18) ((point ++ [14]) ++ [18])), 18,
        packets ctx state 10 ++ packets ctx (GkrRoundsReference.restrict state 14) 14⟩ := rfl

/-- Every send and receive can stop, including after a previous round returned.
The stopping reason, updated private state and attempted-action prefix survive. -/
theorem stopped_forgotten {n : Nat} (ctx : ProtocolContext)
    (state : GkrRoundsReference.State ℚ (n + 2)) (raw : RawState ℚ) (point : List ℚ)
    (cut : Fin 8) (reason : PIR.Stop) :
    (loop (G := ℚ) ctx 2 state raw point).run (handler (some (10 + cut.val)) reason) 10 =
      ⟨.stopped reason, 11 + cut.val,
        (packets ctx state 10 ++ packets ctx (GkrRoundsReference.restrict state 14) 14).take
          (cut.val + 1)⟩ := by
  fin_cases cut <;> rfl

/-- The public forgetting equation applies to arbitrary handlers and their
complete outcomes, including handlers that stop at the very first operation. -/
theorem arbitrary_handler {n : Nat} {H E : Type} (ctx : ProtocolContext) (count : Nat)
    (state : GkrRoundsReference.State ℚ (n + count)) (raw : RawState ℚ) (point : List ℚ)
    (run : PIR.Handler (participantInterface ℚ ℚ) H E) (initial : H) :
    (loop ctx count state raw point).run run initial =
      ((execute ctx count state raw point).run run initial).follow
        (fun result reached => ⟨.returned (values result.raw result.point), reached, []⟩) :=
  PIR.run_bind run _ _ initial

/-- Both role masks are derived from the actual input scopes. Optional missing
inputs stay missing; a verifier service never appears in the producer view. -/
theorem input_masks (view : SourceRows.RoundsInputs.View (Component (assignment ℚ ℚ))) :
    SourceRows.RoundsInputs.mask 0 view =
      { view with pending := none, claim := none, service := none } ∧
    SourceRows.RoundsInputs.mask 1 view =
      { add := none, mul := none, left := none, right := none,
        pending := view.pending, claim := view.claim, count := view.count, service := view.service } :=
  ⟨rfl, rfl⟩

/-- All seven result coordinates are retained, with complementary private
components and no promotion of absent data. -/
theorem result_masks (view : SourceRows.RoundsResults.View (Component (assignment ℚ ℚ))) :
    SourceRows.RoundsResults.mask 0 view = { view with pending := none, claim := none } ∧
    SourceRows.RoundsResults.mask 1 view =
      { point := none, add := none, mul := none, left := none, right := none,
        pending := view.pending, claim := view.claim } := ⟨rfl, rfl⟩

/-- A mask at a role outside the actual roster cannot retain a service or any
other supplied coordinate. -/
theorem outside_roster (view : SourceRows.RoundsInputs.View (Component (assignment ℚ ℚ))) :
    SourceRows.RoundsInputs.pack (SourceRows.RoundsInputs.mask 2 view) =
      Values.absent (assignment ℚ ℚ) SourceRows.RoundsInputs.types := rfl

/-- Aliasing the two roles invalidates the exact roster premise used by both
mask transport and the installed complete source equation. -/
theorem aliased_roles : ¬ NormalForm.RosterDistinct { roles := fun _ => 0 } 0 2 := by
  intro distinct
  exact distinct 1 (by decide) (by decide) rfl

/-- The actual invocation returns the entire result row for zero iterations,
while verifier-only pending data, claim and capability remain hidden. -/
theorem source_zero (add mul left right pending : Option (List ℚ))
    (claim : Option ℚ) (service : Option Nat) :
    invokeProtocol (HonestProducerSource.beforeRoot (F := ℚ) (G := ℚ))
      GkrSourceBodies.roundsSignature {} 0
      (SourceRows.RoundsInputs.pack { add, mul, left, right, pending, claim, count := some 0, service }) =
      .done (SourceRows.RoundsResults.pack
        { point := some [], add, mul, left, right, pending := none, claim := none }) := by
  rw [HonestProducerSource.rounds_invocation _ rfl rfl]
  dsimp only [HonestProducerSource.roundsPresentation, HonestProducerSource.roundsPresentation_certificate,
    NormalForm.runsAtOn, NormalForm.meaningAtOn]
  erw [OccurrencePresentation.closed_helper, HonestProducerRounds.empty_plain]
  rfl

/-- A missing repeat count fails before any callback, even with arbitrary
optional payloads and a supplied verifier capability. -/
theorem source_missing_count (view : SourceRows.RoundsInputs.View (Component (assignment ℚ ℚ))) :
    invokeProtocol (HonestProducerSource.beforeRoot (F := ℚ) (G := ℚ))
      GkrSourceBodies.roundsSignature {} 0
      (SourceRows.RoundsInputs.pack { view with count := none }) = .halt .incomplete := by
  rw [HonestProducerSource.rounds_invocation _ rfl rfl]
  dsimp only [HonestProducerSource.roundsPresentation, HonestProducerSource.roundsPresentation_certificate,
    NormalForm.runsAtOn, NormalForm.meaningAtOn]
  erw [OccurrencePresentation.closed_helper, HonestProducerRounds.empty_plain]
  rfl

/-- The actual source keeps its declared repeat bound, even when every other
optional input is malformed. Refusal occurs before any observed callback. -/
theorem source_excess_count (view : SourceRows.RoundsInputs.View (Component (assignment ℚ ℚ))) :
    invokeProtocol (HonestProducerSource.beforeRoot (F := ℚ) (G := ℚ))
      GkrSourceBodies.roundsSignature {} 0
      (SourceRows.RoundsInputs.pack { view with count := some 5 }) = .halt .refused := by
  rw [HonestProducerSource.rounds_invocation _ rfl rfl]
  dsimp only [HonestProducerSource.roundsPresentation, HonestProducerSource.roundsPresentation_certificate,
    NormalForm.runsAtOn, NormalForm.meaningAtOn]
  erw [OccurrencePresentation.closed_helper, HonestProducerRounds.empty_plain]
  rfl

abbrev ObservedEvents := Nat × (Occurrence.signature (uniformCarriers ℚ ℚ)).Op

def observedHandler (stop : Option Nat) (reason : PIR.Stop) :
    PIR.Handler (Occurrence.signature (uniformCarriers ℚ ℚ)) Nat ObservedEvents :=
  fun operation tick =>
    if stop = some tick then ⟨.stopped reason, tick + 1, [(tick, operation)]⟩
    else match operation with
    | .enter _ | .leave _ => ⟨.returned (), tick + 1, [(tick, operation)]⟩
    | .action action =>
      let result := handler none reason action tick
      ⟨result.outcome, result.state, result.events.map fun (tick, action) => (tick, .action action)⟩

noncomputable def observedPackets {n : Nat} (state : GkrRoundsReference.State ℚ (n + 1)) : List ObservedEvents :=
  [(10, .enter ⟨Generated.Presentations.Gkr.Rounds.roundSite.site, 0⟩)] ++
    (packets {} state 11).map (fun (tick, action) => (tick, .action action)) ++
    [(15, .leave ⟨Generated.Presentations.Gkr.Rounds.roundSite.site, 0⟩)]

/-- The actual nonempty source invocation returns every coordinate. Its real
enter/leave events surround the three payloads and history-dependent delivery. -/
theorem source_complete {n : Nat} (state : GkrRoundsReference.State ℚ (n + 1))
    (raw : RawState ℚ) (decoded : GkrRoundsRealization.Decodes raw state)
    (capacity : 2 ^ (n + 1) < indexLimit)
    (pending : Option (List ℚ)) (claim : Option ℚ) (service : Option Nat) :
    (invokeProtocol (HonestProducerSource.beforeRoot (F := ℚ) (G := ℚ))
      GkrSourceBodies.roundsSignature {} 0
      (SourceRows.RoundsInputs.pack
        { add := some raw.add, mul := some raw.mul, left := some raw.left,
          right := some raw.right, pending, claim, count := some 1, service })).run
      (observedHandler none .abort) 10 =
      ⟨.returned (SourceRows.RoundsResults.pack
        { point := some [15], add := some (raw.restrict 15).add, mul := some (raw.restrict 15).mul,
          left := some (raw.restrict 15).left, right := some (raw.restrict 15).right,
          pending := none, claim := none }), 16, observedPackets state⟩ := by
  rw [HonestProducerSource.rounds_observed _ rfl rfl 1 (by decide) state raw decoded capacity]
  rfl

/-- All six reached operations can stop: enter, each payload, receive and leave.
Even a stopped leave retains its updated state and complete attempted history. -/
theorem source_stops {n : Nat} (state : GkrRoundsReference.State ℚ (n + 1))
    (raw : RawState ℚ) (decoded : GkrRoundsRealization.Decodes raw state)
    (capacity : 2 ^ (n + 1) < indexLimit)
    (pending : Option (List ℚ)) (claim : Option ℚ) (service : Option Nat)
    (cut : Fin 6) (reason : PIR.Stop) :
    (invokeProtocol (HonestProducerSource.beforeRoot (F := ℚ) (G := ℚ))
      GkrSourceBodies.roundsSignature {} 0
      (SourceRows.RoundsInputs.pack
        { add := some raw.add, mul := some raw.mul, left := some raw.left,
          right := some raw.right, pending, claim, count := some 1, service })).run
      (observedHandler (some (10 + cut.val)) reason) 10 =
      ⟨.stopped reason, 11 + cut.val, (observedPackets state).take (cut.val + 1)⟩ := by
  rw [HonestProducerSource.rounds_observed _ rfl rfl 1 (by decide) state raw decoded capacity]
  fin_cases cut <;> rfl

#print axioms source_excess_count
#print axioms source_complete
#print axioms source_stops
#print axioms complete_enriched
#print axioms complete_forgotten
#print axioms stopped_forgotten
#print axioms arbitrary_handler
#print axioms input_masks
#print axioms result_masks
#print axioms outside_roster
#print axioms aliased_roles
#print axioms source_zero
#print axioms source_missing_count
end TestsSecurity.GkrRootAuthorSurface
