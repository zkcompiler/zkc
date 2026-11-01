module

public import ZkcSecurity.Bindings.Gkr.Rounds
public import ZkcSecurity.Bindings.Gkr.RoundsRealization
public import Zkc.Protocols.Sumcheck.Source.VerifierHelpers
public import Zkc.Protocols.Gkr.Source.VerifierProcess
public import Zkc.Semantics.Yields
public import ZkcExamples.Structured.GkrSourceLaws
public import ZkcExamples.Structured.Generated.Presentations.Gkr

@[expose] public section

/-! Computed producer round loops, independent of generated helper bindings.
The laws quantify over every field delivery and retain all four factors and
the complete point prefix. HonestProducerRounds supplies the source bridge. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZkcSecurity.Realizations.Gkr.HonestProducerRounds
open Zkc Source Structured
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcExamples.Structured GkrSourceLaws SumcheckVerifierHelpers
open ZkcSecurity.Examples.Components
open GkrRoundsRealization (RawState Decodes restriction_decodes)

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev Result (F : Type) :=
  Option (List F) × Option (List F) × Option (List F) × Option (List F) × Option (List F)

omit [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem cast_admissible {n m : Nat} (same : n = m) (reference : GkrRoundsReference.State F n)
    (allowed : GkrRoundsReference.admissible reference) :
    GkrRoundsReference.admissible (same ▸ reference) := by
  subst m
  exact allowed

omit [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem cast_total {n m : Nat} (same : n = m) (reference : GkrRoundsReference.State F n) :
    GkrRoundsReference.total (same ▸ reference) = GkrRoundsReference.total reference := by
  subst m
  rfl

omit [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem cast_value {n m : Nat} (same : n = m) (reference : GkrRoundsReference.State F n)
    (point : List F) :
    Rounds.value (same ▸ reference) (coordinates m point) = Rounds.value reference (coordinates n point) := by
  subst m
  rfl

/-- Proof state follows the actual four restricted vectors. It is erased from
the source return and is never a verifier input. -/
structure Output (F : Type) (n : Nat) where
  reference : GkrRoundsReference.State F n
  raw : RawState F
  point : List F

def values (raw : RawState F) (point : List F) : Result F :=
  (some raw.add, some raw.mul, some raw.left, some raw.right, some point)

/-- The single operational presentation retains the shrinking mathematical
state alongside the four vectors and the complete delivered point prefix. -/
def execute (ctx : ProtocolContext) : (count : Nat) → {n : Nat} →
    GkrRoundsReference.State F (n + count) → RawState F → List F →
    PIR.Process (participantInterface F G) (Output F n)
  | 0, _, state, raw, point => .done ⟨state, raw, point⟩
  | count + 1, _, state, raw, point =>
    .call (.send (ty := .field scalarDomain) (GkrVerifier.roundSite ctx "0") (ctx.roles 1)
      (GkrRoundsReference.message state).constant) fun _ =>
    .call (.send (ty := .field scalarDomain) (GkrVerifier.roundSite ctx "1") (ctx.roles 1)
      (GkrRoundsReference.message state).linear) fun _ =>
    .call (.send (ty := .field scalarDomain) (GkrVerifier.roundSite ctx "2") (ctx.roles 1)
      (GkrRoundsReference.message state).quadratic) fun _ =>
    .call (.receive (.field scalarDomain) (GkrVerifier.deliverySite ctx) (ctx.roles 1)) fun challenge =>
    execute ctx count (GkrRoundsReference.restrict state challenge)
      (raw.restrict challenge) (point ++ [challenge])

/-- Forget only the final proof state. Binding the same presentation preserves
every reached operation, arbitrary reply, handler stop and history. -/
def loop (ctx : ProtocolContext) (count : Nat) {n : Nat}
    (state : GkrRoundsReference.State F (n + count)) (raw : RawState F) (point : List F) :
    PIR.Process (participantInterface F G) (Result F) :=
  (execute ctx count state raw point).bind fun result => .done (values result.raw result.point)

omit [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem execute_erases (ctx : ProtocolContext) (count : Nat) {n : Nat}
    (state : GkrRoundsReference.State F (n + count)) (raw : RawState F) (point : List F) :
    (execute (G := G) ctx count state raw point).bind
      (fun result => .done (values result.raw result.point)) = loop ctx count state raw point := rfl

omit [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem execute_yields (ctx : ProtocolContext) (count : Nat) {n : Nat}
    (state : GkrRoundsReference.State F (n + count)) (raw : RawState F) (point : List F)
    (decoded : Decodes raw state)
    (allowed : GkrRoundsReference.admissible state) :
    PIR.Yields (fun result => Decodes result.raw result.reference ∧
      GkrRoundsReference.admissible result.reference ∧ ∃ suffix : List F,
      result.point = point ++ suffix ∧ suffix.length = count ∧
      ∀ tail : List F, Rounds.value result.reference (coordinates n tail) =
        Rounds.value state (coordinates (n + count) (suffix ++ tail)))
      (execute (G := G) ctx count state raw point) := by
  induction count generalizing raw point with
  | zero =>
    exact ⟨decoded, allowed, [], by simp, rfl, fun _ => rfl⟩
  | succ count ih =>
    simp only [execute, PIR.Yields]
    intro _ _ _ challenge
    apply (ih (GkrRoundsReference.restrict state challenge) (raw.restrict challenge)
      (point ++ [challenge]) (restriction_decodes raw state decoded challenge)
      (allowed.2 challenge)).mono
    rintro result ⟨decoded', allowed', suffix, pointEq, sized, anchored⟩
    refine ⟨decoded', allowed', challenge :: suffix, ?_, by simp [sized], ?_⟩
    · simpa only [List.append_assoc, List.singleton_append] using pointEq
    intro tail
    rw [anchored, Rounds.value_restrict]
    rfl

omit [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Every possible return retains the exact original four-factor prefix
restriction. This invariant is independent of the scalar claim and honesty. -/
theorem loop_yields (ctx : ProtocolContext) (count : Nat) {n : Nat}
    (state : GkrRoundsReference.State F (n + count)) (raw : RawState F) (point : List F) :
    PIR.Yields (fun result => ∃ challenges : Fin count → F,
      result = values (raw.prefix count challenges) (point ++ List.ofFn challenges))
      (loop (G := G) ctx count state raw point) := by
  induction count generalizing raw point with
  | zero => exact ⟨Fin.elim0, by simp [values, RawState.prefix]⟩
  | succ count ih =>
    simp only [loop]
    intro _ _ _ challenge
    apply (ih (GkrRoundsReference.restrict state challenge) (raw.restrict challenge)
      (point ++ [challenge])).mono
    rintro result ⟨tail, rfl⟩
    refine ⟨Fin.cons challenge tail, ?_⟩
    simp only [RawState.prefix, Fin.cons_zero, Fin.cons_succ,
      List.ofFn_succ, List.append_assoc, List.singleton_append]
    rfl

end ZkcSecurity.Realizations.Gkr.HonestProducerRounds
