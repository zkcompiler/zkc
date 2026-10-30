module

public import ZkcSecurity.Bindings.Gkr.Rounds
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

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The four finite vectors carried by a producer call. Their decoding law
is independent of any generated helper declaration or source checkpoint. -/
structure Raw (F : Type) where
  add : List F
  mul : List F
  left : List F
  right : List F

def Decodes {n : Nat} (raw : Raw F) (state : GkrRoundsReference.State F n) : Prop :=
  ofList? n raw.add = some state.add ∧ ofList? n raw.mul = some state.mul ∧
  ofList? n raw.left = some state.left ∧ ofList? n raw.right = some state.right

def Raw.restrict (raw : Raw F) (r : F) : Raw F :=
  ⟨restrictValues raw.add r, restrictValues raw.mul r,
    restrictValues raw.left r, restrictValues raw.right r⟩

def Raw.prefix : (count : Nat) → Raw F → (Fin count → F) → Raw F
  | 0, raw, _ => raw
  | count + 1, raw, challenges =>
    Raw.prefix count (raw.restrict (challenges 0)) (challenges ∘ Fin.succ)

omit [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem restriction_decodes {n : Nat} (raw : Raw F) (state : GkrRoundsReference.State F (n + 1))
    (decoded : Decodes raw state) (r : F) : Decodes (raw.restrict r) (GkrRoundsReference.restrict state r) :=
  ⟨ofList?_restrictValues _ _ r decoded.1, ofList?_restrictValues _ _ r decoded.2.1,
    ofList?_restrictValues _ _ r decoded.2.2.1, ofList?_restrictValues _ _ r decoded.2.2.2⟩

abbrev Result (F : Type) :=
  Option (List F) × Option (List F) × Option (List F) × Option (List F) × Option (List F)

def encode {n : Nat} (reference : GkrRoundsReference.State F n) : Raw F :=
  ⟨GkrRoundsLayout.encode reference.add, GkrRoundsLayout.encode reference.mul,
    GkrRoundsLayout.encode reference.left, GkrRoundsLayout.encode reference.right⟩

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem encode_decodes {n : Nat} (reference : GkrRoundsReference.State F n) :
    Decodes (encode reference) reference :=
  ⟨GkrRoundsLayout.decode_encode _, GkrRoundsLayout.decode_encode _,
    GkrRoundsLayout.decode_encode _, GkrRoundsLayout.decode_encode _⟩

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem cast_decodes {n m : Nat} (same : n = m) (reference : GkrRoundsReference.State F n)
    (raw : Raw F) (decoded : Decodes raw reference) :
    Decodes raw (same ▸ reference) := by
  subst m
  exact decoded

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
  raw : Raw F
  point : List F

def values (raw : Raw F) (point : List F) : Result F :=
  (some raw.add, some raw.mul, some raw.left, some raw.right, some point)

/-- Context-parametric complete loop, retaining exact source role and sites. -/
def loop (ctx : ProtocolContext) : (count : Nat) → {n : Nat} →
    GkrRoundsReference.State F (n + count) → Raw F → List F →
    PIR.Process (participantInterface F G) (Result F)
  | 0, _, _, raw, point => .done (values raw point)
  | count + 1, _, state, raw, point =>
    .call (.send (ty := .field scalarDomain) (GkrVerifier.roundSite ctx "0") (ctx.roles 1)
      (GkrRoundsReference.message state).constant) fun _ =>
    .call (.send (ty := .field scalarDomain) (GkrVerifier.roundSite ctx "1") (ctx.roles 1)
      (GkrRoundsReference.message state).linear) fun _ =>
    .call (.send (ty := .field scalarDomain) (GkrVerifier.roundSite ctx "2") (ctx.roles 1)
      (GkrRoundsReference.message state).quadratic) fun _ =>
    .call (.receive (.field scalarDomain) (GkrVerifier.deliverySite ctx) (ctx.roles 1)) fun challenge =>
    loop ctx count (GkrRoundsReference.restrict state challenge)
      (raw.restrict challenge) (point ++ [challenge])

/-- A proof-state presentation of the same source loop. -/
def execute (ctx : ProtocolContext) : (count : Nat) → {n : Nat} →
    GkrRoundsReference.State F (n + count) → Raw F → List F →
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

omit [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem execute_erases (ctx : ProtocolContext) (count : Nat) {n : Nat}
    (state : GkrRoundsReference.State F (n + count)) (raw : Raw F) (point : List F) :
    (execute (G := G) ctx count state raw point).bind
      (fun result => .done (values result.raw result.point)) = loop ctx count state raw point := by
  induction count generalizing raw point with
  | zero => rfl
  | succ count ih =>
    simp only [execute, loop, PIR.Process.bind]
    congr 1; funext _; congr 1; funext _; congr 1; funext _; congr 1; funext challenge
    exact ih (GkrRoundsReference.restrict state challenge) (raw.restrict challenge) (point ++ [challenge])

omit [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem execute_yields (ctx : ProtocolContext) (count : Nat) {n : Nat}
    (state : GkrRoundsReference.State F (n + count)) (raw : Raw F) (point : List F)
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
    (state : GkrRoundsReference.State F (n + count)) (raw : Raw F) (point : List F) :
    PIR.Yields (fun result => ∃ challenges : Fin count → F,
      result = values (raw.prefix count challenges) (point ++ List.ofFn challenges))
      (loop (G := G) ctx count state raw point) := by
  induction count generalizing raw point with
  | zero => exact ⟨Fin.elim0, by simp [values, Raw.prefix]⟩
  | succ count ih =>
    simp only [loop, PIR.Yields]
    intro _ _ _ challenge
    apply (ih (GkrRoundsReference.restrict state challenge) (raw.restrict challenge)
      (point ++ [challenge])).mono
    rintro result ⟨tail, rfl⟩
    refine ⟨Fin.cons challenge tail, ?_⟩
    simp only [Raw.prefix, Fin.cons_zero, Fin.cons_succ,
      List.ofFn_succ, List.append_assoc, List.singleton_append]
    rfl

end ZkcSecurity.Realizations.Gkr.HonestProducerRounds
