module

public import ZkcSecurity.FiatShamir.Soundness

@[expose] public section

/-! Sequential composition of round-by-round certificates.

A sub-validator that returns a value rather than a decision has a reduction
certificate (`Reduction final error`): a doomed set of its residuals that
received and sent messages cannot leave, that a fresh uniform challenge leaves
with probability at most `error`, and whose returned values satisfy `final`.
Binding a continuation that is doomed whenever `final` holds composes the two
certificates (`Reduction.bind`); repeating a step whose certificate for `m + 1`
remaining iterations returns states of its certificate for `m` composes the
certificates of all iterations (`Reduction.repeatN`). A reduction certificate
whose final predicate excludes acceptance is a round-by-round certificate of
the soundness theorem (`Reduction.roundByRound`). Challenge budgets add up along
the same compositions (`QueryBound.bind`, `QueryBound.repeatN`).
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir
open OracleComp OracleSpec
open Zkc.Source Zkc.Construction

variable {F G A B : Type}

section Certificates
variable [SampleableType F]

/-- The local obligation of a doomed set of sub-validator residuals whose
returned values satisfy `final`. -/
def StepTo (doomed : PIR.Proc (Actions F G) A → Prop) (final : A → Prop) (error : ENNReal) :
    PIR.Proc (Actions F G) A → Prop
  | .done value => final value
  | .halt _ => True
  | .call (.receive _ _ _) next => ∀ value, doomed (next value)
  | .call (.send _ _ _) next => doomed (next ())
  | .call (.query _ _ _) next => Pr{let challenge ← $ᵗ F}[¬ doomed (next challenge)] ≤ error

/-- A reduction certificate: a doomed set whose every member meets its local
obligation. -/
structure Reduction (final : A → Prop) (error : ENNReal) where
  doomed : PIR.Proc (Actions F G) A → Prop
  step : ∀ process, doomed process → StepTo doomed final error process

/-- Enlarging the doomed set, weakening the final predicate and raising the
error keep every local obligation. -/
theorem StepTo.mono {final final' : A → Prop} {error error' : ENNReal}
    {small large : PIR.Proc (Actions F G) A → Prop}
    (included : ∀ process, small process → large process)
    (weaker : ∀ value, final value → final' value) (larger : error ≤ error') :
    ∀ process, StepTo small final error process → StepTo large final' error' process
  | .done value, step => weaker value step
  | .halt _, step => step
  | .call (.receive _ _ _) _, step => fun value => included _ (step value)
  | .call (.send _ _ _) _, step => included _ step
  | .call (.query _ _ _) next, step =>
      ((prEvent_mono _ _ (fun challenge => ¬ small (next challenge))
        (fun _ outside inside => outside (included _ inside))).trans step).trans larger

/-- The same certificate for a weaker final predicate and a larger error. -/
def Reduction.mono {final final' : A → Prop} {error error' : ENNReal}
    (certificate : Reduction (F := F) (G := G) final error)
    (weaker : ∀ value, final value → final' value) (larger : error ≤ error') :
    Reduction (F := F) (G := G) final' error' where
  doomed := certificate.doomed
  step process member :=
    StepTo.mono (fun _ inside => inside) weaker larger process (certificate.step process member)

/-- A certificate whose returned values are never accepted is a round-by-round
certificate. -/
def Reduction.roundByRound {accepts : A → Prop} {error : ENNReal}
    (certificate : Reduction (F := F) (G := G) (fun value => ¬ accepts value) error) :
    RoundByRound (F := F) (G := G) accepts error :=
  RoundByRound.ofStep certificate.doomed fun process member => by
    have step := certificate.step process member
    match process, step with
    | .done _, step => exact step
    | .halt _, _ => trivial
    | .call (.receive _ _ _) _, step => exact step
    | .call (.send _ _ _) _, step => exact step
    | .call (.query _ _ _) _, step => exact step

/-- Sequential composition: the residuals of the first sub-validator followed by
the continuation, and the doomed residuals of the continuation. -/
def Reduction.bind {final : A → Prop} {final' : B → Prop} {error : ENNReal}
    (first : Reduction (F := F) (G := G) final error) (continuation : A → PIR.Proc (Actions F G) B)
    (second : Reduction (F := F) (G := G) final' error)
    (linked : ∀ value, final value → second.doomed (continuation value)) :
    Reduction (F := F) (G := G) final' error where
  doomed process := (∃ head, first.doomed head ∧ process = head.bind continuation) ∨
    second.doomed process
  step := by
    rintro _ (⟨head, member, rfl⟩ | member)
    · have step := first.step head member
      match head, step with
      | .done value, step =>
          exact StepTo.mono (fun _ inside => .inr inside) (fun _ holds => holds) le_rfl _
            (second.step _ (linked value step))
      | .halt _, _ => trivial
      | .call (.receive _ _ _) _, step => exact fun value => .inl ⟨_, step value, rfl⟩
      | .call (.send _ _ _) _, step => exact .inl ⟨_, step, rfl⟩
      | .call (.query _ _ _) next, step =>
          refine (prEvent_mono _ _ (fun challenge => ¬ first.doomed (next challenge))
            (fun _ outside inside => ?_)).trans step
          exact outside (.inl ⟨_, inside, rfl⟩)
    · exact StepTo.mono (fun _ inside => .inr inside) (fun _ holds => holds) le_rfl _
        (second.step _ member)

/-- The union of a family of certificates with the same final predicate. -/
def Reduction.union {final : A → Prop} {error : ENNReal} {ι : Type}
    (family : ι → Reduction (F := F) (G := G) final error) :
    Reduction (F := F) (G := G) final error where
  doomed process := ∃ index, (family index).doomed process
  step process member := by
    obtain ⟨index, member⟩ := member
    exact StepTo.mono (fun _ inside => ⟨index, inside⟩) (fun _ holds => holds) le_rfl _
      ((family index).step process member)

/-- A received message followed by certified continuations. -/
def Reduction.receive {final : A → Prop} {error : ENNReal} (ty : Zkc.Source.Common.Native.Ty)
    (site : String) (sender : Nat)
    (next : Zkc.Source.Common.Native.ScalarValue F G ty → PIR.Proc (Actions F G) A)
    (continuation : Zkc.Source.Common.Native.ScalarValue F G ty →
      Reduction (F := F) (G := G) final error)
    (linked : ∀ value, (continuation value).doomed (next value)) :
    Reduction (F := F) (G := G) final error where
  doomed process := process = .call (.receive ty site sender) next ∨
    ∃ value, (continuation value).doomed process
  step := by
    rintro _ (rfl | ⟨value, member⟩)
    · exact fun value => .inr ⟨value, linked value⟩
    · exact StepTo.mono (fun _ inside => .inr ⟨value, inside⟩) (fun _ holds => holds) le_rfl _
        ((continuation value).step _ member)

theorem Reduction.bind_doomed {final : A → Prop} {final' : B → Prop} {error : ENNReal}
    (first : Reduction (F := F) (G := G) final error) (continuation : A → PIR.Proc (Actions F G) B)
    (second : Reduction (F := F) (G := G) final' error)
    (linked : ∀ value, final value → second.doomed (continuation value))
    (head : PIR.Proc (Actions F G) A) (member : first.doomed head) :
    (first.bind continuation second linked).doomed (head.bind continuation) :=
  .inl ⟨head, member, rfl⟩

/-- Bounded repetition. `invariant m` holds of the states from which `m`
iterations remain; `certificate m` covers one iteration from such a state with
`m + 1` remaining, and its returned states satisfy `invariant m`. -/
def Reduction.repeatN {invariant : Nat → A → Prop} {error : ENNReal}
    (step : A → PIR.Proc (Actions F G) A)
    (certificate : ∀ remaining, Reduction (F := F) (G := G) (invariant remaining) error)
    (entry : ∀ remaining state, invariant (remaining + 1) state →
      (certificate remaining).doomed (step state)) :
    Reduction (F := F) (G := G) (invariant 0) error where
  doomed process :=
    (∃ remaining state, invariant remaining state ∧ process = PIR.repeatN remaining step state) ∨
    (∃ remaining head, (certificate remaining).doomed head ∧
      process = head.bind (PIR.repeatN remaining step))
  step := by
    let doomed : PIR.Proc (Actions F G) A → Prop := fun process =>
      (∃ remaining state, invariant remaining state ∧ process = PIR.repeatN remaining step state) ∨
      (∃ remaining head, (certificate remaining).doomed head ∧
        process = head.bind (PIR.repeatN remaining step))
    have both : ∀ remaining,
        (∀ state, invariant remaining state →
          StepTo doomed (invariant 0) error (PIR.repeatN remaining step state)) ∧
        (∀ head, (certificate remaining).doomed head →
          StepTo doomed (invariant 0) error (head.bind (PIR.repeatN remaining step))) := by
      have calls : ∀ remaining (head : PIR.Proc (Actions F G) A),
          (certificate remaining).doomed head →
          (∀ value, (certificate remaining).doomed (.done value) →
            head = .done value →
            StepTo doomed (invariant 0) error (PIR.repeatN remaining step value)) →
          StepTo doomed (invariant 0) error (head.bind (PIR.repeatN remaining step)) := by
        intro remaining head member done
        have obligation := (certificate remaining).step head member
        match head, obligation with
        | .done value, _ => exact done value member rfl
        | .halt _, _ => trivial
        | .call (.receive _ _ _) _, obligation => exact fun value => .inr ⟨remaining, _, obligation value, rfl⟩
        | .call (.send _ _ _) _, obligation => exact .inr ⟨remaining, _, obligation, rfl⟩
        | .call (.query _ _ _) next, obligation =>
            refine (prEvent_mono _ _ (fun challenge => ¬ (certificate remaining).doomed (next challenge))
              (fun _ outside inside => ?_)).trans obligation
            exact outside (.inr ⟨remaining, _, inside, rfl⟩)
      intro remaining
      induction remaining with
      | zero =>
          refine ⟨fun state holds => holds, fun head member => calls 0 head member ?_⟩
          intro value member _
          exact (certificate 0).step _ member
      | succ remaining ih =>
          have first : ∀ state, invariant (remaining + 1) state →
              StepTo doomed (invariant 0) error (PIR.repeatN (remaining + 1) step state) :=
            fun state holds => ih.2 (step state) (entry remaining state holds)
          refine ⟨first, fun head member => calls (remaining + 1) head member ?_⟩
          intro value member _
          exact first value ((certificate (remaining + 1)).step _ member)
    rintro _ (⟨remaining, state, holds, rfl⟩ | ⟨remaining, head, member, rfl⟩)
    · exact (both remaining).1 state holds
    · exact (both remaining).2 head member

theorem Reduction.repeatN_doomed {invariant : Nat → A → Prop} {error : ENNReal}
    (step : A → PIR.Proc (Actions F G) A)
    (certificate : ∀ remaining, Reduction (F := F) (G := G) (invariant remaining) error)
    (entry : ∀ remaining state, invariant (remaining + 1) state →
      (certificate remaining).doomed (step state))
    (remaining : Nat) (state : A) (holds : invariant remaining state) :
    (Reduction.repeatN step certificate entry).doomed (PIR.repeatN remaining step state) :=
  .inl ⟨remaining, state, holds, rfl⟩

end Certificates

/-! ## Challenge budgets -/

theorem QueryBound.bind {A B : Type} (head : PIR.Proc (Actions F G) A)
    (continuation : A → PIR.Proc (Actions F G) B) {first second : Nat}
    (headBound : QueryBound head first) (continuationBound : ∀ value, QueryBound (continuation value) second) :
    QueryBound (head.bind continuation) (first + second) := by
  induction head generalizing first with
  | done value =>
      exact QueryBound.mono _ (continuationBound value) (Nat.le_add_left _ _)
  | halt _ => trivial
  | call operation next ih =>
      cases operation with
      | receive ty site sender => exact fun value => ih value (headBound value)
      | send site receiver sent => exact ih () headBound
      | query site op arguments =>
          refine ⟨Nat.lt_of_lt_of_le headBound.1 (Nat.le_add_right _ _), fun challenge => ?_⟩
          have remaining := ih challenge (headBound.2 challenge)
          have arithmetic : first - 1 + second = first + second - 1 := by
            have := headBound.1
            omega
          rwa [arithmetic] at remaining

theorem QueryBound.repeatN {A : Type} (step : A → PIR.Proc (Actions F G) A) {each : Nat}
    (stepBound : ∀ state, QueryBound (step state) each) :
    ∀ (remaining : Nat) (state : A), QueryBound (PIR.repeatN remaining step state) (remaining * each)
  | 0, _ => trivial
  | remaining + 1, state => by
      have bound := QueryBound.bind (step state) (PIR.repeatN remaining step) (stepBound state)
        (QueryBound.repeatN step stepBound remaining)
      have arithmetic : (remaining + 1) * each = each + remaining * each := by
        rw [Nat.succ_mul, Nat.add_comm]
      rw [arithmetic]
      exact bound

end ZkcSecurity.FiatShamir
