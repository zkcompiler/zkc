module

public import ZkcExamples.Construction.SumcheckScalarRound
public import ZkcExamples.Construction.SumcheckLegacyRound

@[expose] public section
/-! All-reply comparison of the retained loop with the Domain Process.
The immutable capture and arbitrary iteration list are explicit. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 800000
namespace ZkcExamples.Construction.SumcheckDomainConnection
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform.DomainAdapter
attribute [local irreducible] roundState
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def legacyCarried (point : List F) (scalar : F) (history : History F G) : List (Value F G) :=
  [.vector "bls12-381.fr" point, .data (.field "bls12-381.fr" scalar), .transcript history]

def readbackCarriedK {R : Type} (initial : History F G)
    (next : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)) :=
  readbackRoundK initial (fun point scalar history unread => next (legacyCarried point scalar history) unread)

theorem legacy_loop {R : Type} (challenge : History F G → m F) (initial : History F G)
    (a b c d e : Value F G) (indices : List Nat) (point : List F) (scalar : F)
    (history : Domain.History (uniformCarriers F G)) (suffix : History F G)
    (mapped : readbackHistory Origin.withoutCoordinates history = some suffix) (proof : Proof F G)
    (next : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)) :
    iterateM
        (fun start unread continuation => idealK SumcheckProof.context challenge
          (Uniform.helperTable SumcheckProof.program F G) roundBody start unread continuation)
        [a, b, c, d, e] [26, 31, 25] indices (legacyCarried point scalar (initial ++ suffix)) proof next =
      runK Origin.withoutCoordinates initial challenge (reduce indices point scalar history) proof (readbackCarriedK initial next) := by
  induction indices generalizing point scalar history suffix proof with
  | nil => simp only [iterateM, reduce, runK, readbackCarriedK, readbackRoundK, mapped]
  | cons index rest ih =>
      rw [iterateM]
      change idealK _ _ _ roundBody _ proof
        (legacyYieldK (fun values unread => iterateM _ _ _ rest values unread next)) = _
      simp only [legacyCarried]
      rw [legacy_round (F := F) (G := G)]
      simp only [reduce, runK_bind]
      rw [← scalar_round challenge initial index point scalar history suffix mapped proof]
      apply runK_congr_yields _ _ _ _ _ (round_mapped history suffix mapped index point scalar)
      intro state unread hasMapping
      cases found : readbackHistory Origin.withoutCoordinates state.history with
      | none => simp [found] at hasMapping
      | some current =>
          simp only [readbackRoundK, found]
          exact ih state.point state.scalar state.history current found unread

end ZkcExamples.Construction.SumcheckDomainConnection
