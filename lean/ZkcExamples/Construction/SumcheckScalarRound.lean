module

public import ZkcExamples.Construction.SumcheckScalarProtocol

@[expose] public section
/-! The mapped legacy oracle at the actual nominal round. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Construction.SumcheckDomainConnection
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform.DomainAdapter
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def readbackRoundK {R : Type} (initial : History F G)
    (next : List F → F → History F G → Proof F G → m (PIR.Outcome R × Proof F G))
    (state : RoundState F G) (proof : Proof F G) : m (PIR.Outcome R × Proof F G) :=
  match readbackHistory Origin.withoutCoordinates state.history with
  | some suffix => next state.point state.scalar (initial ++ suffix) proof
  | none => pure (.stopped .refused, proof)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem mapped_messages (history : Domain.History (uniformCarriers F G)) (suffix : History F G)
    (mapped : readbackHistory Origin.withoutCoordinates history = some suffix) (index : Nat) (low high : F) :
    readbackHistory Origin.withoutCoordinates (history ++
      [.message (Domain.atCoordinates (staticOrigin lowTemplate) [index]) (.field "bls12-381.fr" low),
        .message (Domain.atCoordinates (staticOrigin highTemplate) [index]) (.field "bls12-381.fr" high)]) =
      some (suffix ++ [.message (staticOrigin lowTemplate) (.field "bls12-381.fr" low),
        .message (staticOrigin highTemplate) (.field "bls12-381.fr" high)]) := by
  rw [readbackHistory_append, mapped]
  simp [readbackHistory, readbackEvent, readbackPayload, (legacy_origins index).1,
    (legacy_origins index).2.1]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem mapped_round (history : Domain.History (uniformCarriers F G)) (suffix : History F G)
    (mapped : readbackHistory Origin.withoutCoordinates history = some suffix) (index : Nat) (low high answer : F) :
    readbackHistory Origin.withoutCoordinates (history ++
      [.message (Domain.atCoordinates (staticOrigin lowTemplate) [index]) (.field "bls12-381.fr" low),
        .message (Domain.atCoordinates (staticOrigin highTemplate) [index]) (.field "bls12-381.fr" high),
        .challenge (Domain.atCoordinates (staticOrigin drawTemplate) [index]),
        .message (Domain.atCoordinates (staticOrigin deliveryTemplate) [index]) (.field "bls12-381.fr" answer)]) =
      some (suffix ++ [.message (staticOrigin lowTemplate) (.field "bls12-381.fr" low),
        .message (staticOrigin highTemplate) (.field "bls12-381.fr" high),
        .challenge (staticOrigin drawTemplate),
        .message (staticOrigin deliveryTemplate) (.field "bls12-381.fr" answer)]) := by
  rw [readbackHistory_append, mapped]
  simp [readbackHistory, readbackEvent, readbackPayload, (legacy_origins index).1,
    (legacy_origins index).2.1, (legacy_origins index).2.2.1, (legacy_origins index).2.2.2]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem round_mapped (history : Domain.History (uniformCarriers F G)) (suffix : History F G)
    (mapped : readbackHistory Origin.withoutCoordinates history = some suffix) (index : Nat) (point : List F) (scalar : F) :
    PIR.Yields (fun state => (readbackHistory Origin.withoutCoordinates state.history).isSome)
      (roundState index point scalar history) := by
  simp only [roundState, PIR.Yields]
  intro low ignoredLow high ignoredHigh
  split
  · intro answer ignoredDelivery
    simpa only [roundDrawOrigin_actual, PIR.Yields] using
      Option.isSome_iff_exists.mpr ⟨_, mapped_round history suffix mapped index low high answer⟩
  · trivial

/-- The same oracle function, in the same monad, is called at the adapted key.
Both malformed-message cases preserve the exact unread head. -/
theorem scalar_round {R : Type} (challenge : History F G → m F) (initial : History F G)
    (index : Nat) (point : List F) (scalar : F)
    (history : Domain.History (uniformCarriers F G)) (suffix : History F G)
    (mapped : readbackHistory Origin.withoutCoordinates history = some suffix) (proof : Proof F G)
    (next : List F → F → History F G → Proof F G → m (PIR.Outcome R × Proof F G)) :
    runK Origin.withoutCoordinates initial challenge (roundState index point scalar history) proof
        (readbackRoundK initial next) =
      scalarRoundK challenge point scalar (initial ++ suffix) proof next := by
  have mappedOrigin : Origin.withoutCoordinates (roundDrawOrigin index) = staticOrigin drawTemplate := by
    rw [roundDrawOrigin_actual]
    exact (legacy_origins index).2.2.1
  have queried (low high : F) := query_of_draw Origin.withoutCoordinates initial challenge _ (roundDrawOrigin index)
    "bls12-381.fr" rfl _ (mapped_messages history suffix mapped index low high)
  simp only [mappedOrigin, List.append_assoc] at queried
  have allowed : Domain.drawRequest (roundDrawOrigin index) = true := rfl
  cases proof with
  | nil => rfl
  | cons low unread =>
      cases low with
      | boolean => rfl
      | group => rfl
      | field domain low =>
          by_cases lowDomain : domain = "bls12-381.fr"
          · subst domain
            cases unread with
            | nil => rfl
            | cons high rest =>
                cases high with
                | boolean => rfl
                | group => rfl
                | field domain high =>
                    by_cases highDomain : domain = "bls12-381.fr"
                    · subst domain
                      simp only [roundState, runK, Value.decode, scalarRoundK, ite_true]
                      by_cases valid : scalar = low + high
                      all_goals simp only [valid, ite_true, ite_false, runK]
                      simp only [allowed, ite_true, queried, bind_assoc, pure_bind,
                        List.append_assoc, List.cons_append, List.nil_append]
                      congr 1
                      funext answer
                      simp only [readbackRoundK, roundDrawOrigin_actual, mapped_round history suffix mapped]
                      kernel_rfl
                    · simp [roundState, runK, Value.decode, scalarRoundK, highDomain, eq_comm]
          · simp [roundState, runK, Value.decode, scalarRoundK, lowDomain, eq_comm]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem reduce_mapped (indices : List Nat) (point : List F) (scalar : F)
    (history : Domain.History (uniformCarriers F G)) (suffix : History F G)
    (mapped : readbackHistory Origin.withoutCoordinates history = some suffix) :
    PIR.Yields (fun state => (readbackHistory Origin.withoutCoordinates state.history).isSome)
      (reduce indices point scalar history) := by
  induction indices generalizing point scalar history suffix with
  | nil => exact Option.isSome_iff_exists.mpr ⟨suffix, mapped⟩
  | cons index rest ih =>
      apply PIR.Yields.bind (round_mapped history suffix mapped index point scalar)
      intro state hasMapping
      obtain ⟨current, found⟩ := Option.isSome_iff_exists.mp hasMapping
      exact ih state.point state.scalar state.history current found

end ZkcExamples.Construction.SumcheckDomainConnection
