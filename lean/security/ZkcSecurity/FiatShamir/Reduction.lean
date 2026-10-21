module

public import ZkcSecurity.FiatShamir.Typed
public import ZkcSecurity.FiatShamir.Composition
public import ZkcSecurity.FiatShamir.Lifting

@[expose] public section

/-! # Charged reductions: the composition API of the typed engine

A sub-validator that returns a value rather than a decision has a charged
reduction (`Reduction absorb Post charge`): a set of doomed pairs of an absorbed
history and a residual, closed under received and sent messages, left by a
query's decoded fresh raw answer with probability at most the charge of its key,
and whose returned values satisfy the postcondition `Post` at the history where
they are returned (`ChargedStepTo`). The endpoint certificate is the
specialization whose postcondition implies rejection: `Reduction.toCertificate`
turns a reduction into a charged certificate, and every charged certificate is a
reduction with the postcondition "not accepted" (`ChargedCertificate.toReduction`).

Composition rules, all over any transcript interface and any per-key charge:

- `Reduction.bind`: a reduction of a head whose postcondition, at the history
  where the head returns, makes the continuation doomed at that history
  (`Post₁ history value → doomed₂ history (continuation value)`) composes with
  the continuation's reduction;
- `Reduction.repeatN`: bounded repetition, with an invariant indexed by the
  absorbed history, the remaining iterations and the carried state;
- `Reduction.union` and `Reduction.union₂`: the union of reductions with one
  charge, or with two charges both dominated by a common charge;
- `Reduction.receive`: a received message followed by certified continuations,
  one per message.

Certificates of every other form reach the reduction through the charged
certificate: per-event certificates (`Certificate.toReduction`), round-by-round
certificates over the common participant actions (`RoundByRound.typed`), the
uniform-sort certificates of law interfaces (`UniformCertificate.toReduction`),
the upstream import (`ZkcSecurity.FiatShamir.Upstream.ofWorstCase`), and the
reductions over the common participant actions with a uniform error
(`ZkcSecurity.FiatShamir.Reduction.typed`).
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir.Typed
open OracleComp OracleSpec

variable {I : PIR.Signature} {E P A B : Type} {Raw : E → Type} [∀ event, SampleableType (Raw event)]

/-- The local obligation of a doomed set of sub-validator residuals indexed by
the absorbed history, at one residual reached after `history`: a returned value
satisfies `Post` at that history; after a receive whose event recovers a reply,
and after a send, the residual is doomed at the extended history; and a doomed
query's decoded fresh raw answer leaves the doomed set at the extended history
with probability at most `charge history event`. -/
def ChargedStepTo (absorb : Interface I E P Raw) (doomed : List E → PIR.Proc I A → Prop)
    (Post : List E → A → Prop) (charge : List E → E → ENNReal) (history : List E) :
    PIR.Proc I A → Prop
  | .done value => Post history value
  | .halt _ => True
  | .call operation next =>
      match absorb operation with
      | .receive event recover => ∀ message value, recover (event message) = some value →
          doomed (history ++ [event message]) (next value)
      | .send event value => doomed (history ++ [event]) (next value)
      | .query event decode =>
          Pr{let raw ← $ᵗ (Raw event)}[
            ∃ value, decode raw = some value ∧
              ¬ doomed (history ++ [event]) (next value)] ≤ charge history event
      | .refuse => True

/-- A charged reduction: a set of doomed pairs of an absorbed history and a
residual whose every member meets `ChargedStepTo`. -/
structure Reduction (absorb : Interface I E P Raw) (Post : List E → A → Prop)
    (charge : List E → E → ENNReal) where
  doomed : List E → PIR.Proc I A → Prop
  step : ∀ history process, doomed history process →
    ChargedStepTo absorb doomed Post charge history process

variable (absorb : Interface I E P Raw)

/-- Enlarging the doomed set, weakening the postcondition and raising the charge
keep every local obligation. -/
theorem ChargedStepTo.mono {Post Post' : List E → A → Prop} {charge larger : List E → E → ENNReal}
    {small large : List E → PIR.Proc I A → Prop}
    (included : ∀ history process, small history process → large history process)
    (weaker : ∀ history value, Post history value → Post' history value)
    (le : ∀ history event, charge history event ≤ larger history event) (history : List E) :
    ∀ process, ChargedStepTo absorb small Post charge history process →
      ChargedStepTo absorb large Post' larger history process
  | .done value, step => weaker history value step
  | .halt _, step => step
  | .call operation next, step => by
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [ChargedStepTo, absorbed] at step ⊢
        exact fun message value recovered => included _ _ (step message value recovered)
      · simp only [ChargedStepTo, absorbed] at step ⊢
        exact included _ _ step
      · simp only [ChargedStepTo, absorbed] at step ⊢
        refine ((prEvent_mono _ _
          (fun raw => ∃ value, decode raw = some value ∧ ¬ small (history ++ [event]) (next value))
          (fun _ escaping => ?_)).trans step).trans (le history event)
        obtain ⟨value, decoded, outside⟩ := escaping
        exact ⟨value, decoded, fun inside => outside (included _ _ inside)⟩
      · simp only [ChargedStepTo, absorbed]

/-- The same reduction for a weaker postcondition and a larger charge. -/
def Reduction.mono {Post Post' : List E → A → Prop} {charge larger : List E → E → ENNReal}
    (reduction : Reduction absorb Post charge)
    (weaker : ∀ history value, Post history value → Post' history value)
    (le : ∀ history event, charge history event ≤ larger history event) :
    Reduction absorb Post' larger where
  doomed := reduction.doomed
  step history process member :=
    ChargedStepTo.mono absorb (fun _ _ inside => inside) weaker le history process
      (reduction.step history process member)

/-- A reduction whose returned values are never accepted is a charged
certificate with the same doomed pairs. -/
def Reduction.toCertificate {Post : List E → A → Prop} {charge : List E → E → ENNReal}
    {accepts : A → Prop} (reduction : Reduction absorb Post charge)
    (rejects : ∀ history value, Post history value → ¬ accepts value) :
    ChargedCertificate absorb accepts charge where
  doomed := reduction.doomed
  step history process member := by
    have step := reduction.step history process member
    match process, step with
    | .done value, step => exact rejects history value step
    | .halt _, _ => trivial
    | .call _ _, step => exact step

/-- A charged certificate is a reduction whose postcondition is rejection. -/
def ChargedCertificate.toReduction {accepts : A → Prop} {charge : List E → E → ENNReal}
    (certificate : ChargedCertificate absorb accepts charge) :
    Reduction absorb (fun _ value => ¬ accepts value) charge where
  doomed := certificate.doomed
  step history process member := by
    have step := certificate.step history process member
    match process, step with
    | .done _, step => exact step
    | .halt _, _ => trivial
    | .call _ _, step => exact step

/-- A per-event certificate as a reduction, through its charged certificate. -/
def Certificate.toReduction {accepts : A → Prop} {error : E → ENNReal}
    (certificate : Certificate absorb accepts error) :
    Reduction absorb (fun _ value => ¬ accepts value) fun _ event => error event :=
  (certificate.charged absorb).toReduction absorb

/-- Sequential composition: the head's doomed residuals followed by the
continuation, and the continuation's doomed residuals. The link makes the
continuation doomed, at the history where the head returns, at every returned
value the head's postcondition admits. -/
def Reduction.bind {Post₁ : List E → A → Prop} {Post₂ : List E → B → Prop}
    {charge : List E → E → ENNReal} (first : Reduction absorb Post₁ charge)
    (continuation : A → PIR.Proc I B) (second : Reduction absorb Post₂ charge)
    (link : ∀ history value, Post₁ history value → second.doomed history (continuation value)) :
    Reduction absorb Post₂ charge where
  doomed history process :=
    (∃ head, first.doomed history head ∧ process = head.bind continuation) ∨
      second.doomed history process
  step := by
    rintro history _ (⟨head, member, rfl⟩ | member)
    · have step := first.step history head member
      match head, step with
      | .done value, step =>
          exact ChargedStepTo.mono absorb (fun _ _ inside => .inr inside) (fun _ _ holds => holds)
            (fun _ _ => le_rfl) history _ (second.step _ _ (link history value step))
      | .halt _, _ => trivial
      | .call operation next, step =>
          show ChargedStepTo absorb _ Post₂ charge history
            (.call operation fun reply => (next reply).bind continuation)
          rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
            ⟨event, decode⟩ | _
          · simp only [ChargedStepTo, absorbed] at step ⊢
            exact fun message value recovered => .inl ⟨_, step message value recovered, rfl⟩
          · simp only [ChargedStepTo, absorbed] at step ⊢
            exact .inl ⟨_, step, rfl⟩
          · simp only [ChargedStepTo, absorbed] at step ⊢
            refine (prEvent_mono _ _
              (fun raw => ∃ value, decode raw = some value ∧
                ¬ first.doomed (history ++ [event]) (next value))
              (fun _ escaping => ?_)).trans step
            obtain ⟨value, decoded, outside⟩ := escaping
            exact ⟨value, decoded, fun inside => outside (.inl ⟨_, inside, rfl⟩)⟩
          · simp only [ChargedStepTo, absorbed]
    · exact ChargedStepTo.mono absorb (fun _ _ inside => .inr inside) (fun _ _ holds => holds)
        (fun _ _ => le_rfl) history _ (second.step _ _ member)

theorem Reduction.bind_doomed {Post₁ : List E → A → Prop} {Post₂ : List E → B → Prop}
    {charge : List E → E → ENNReal} (first : Reduction absorb Post₁ charge)
    (continuation : A → PIR.Proc I B) (second : Reduction absorb Post₂ charge)
    (link : ∀ history value, Post₁ history value → second.doomed history (continuation value))
    (history : List E) (head : PIR.Proc I A) (member : first.doomed history head) :
    (first.bind absorb continuation second link).doomed history (head.bind continuation) :=
  .inl ⟨head, member, rfl⟩

/-- The union of a family of reductions with one postcondition and one charge. -/
def Reduction.union {Post : List E → A → Prop} {charge : List E → E → ENNReal} {ι : Type}
    (family : ι → Reduction absorb Post charge) : Reduction absorb Post charge where
  doomed history process := ∃ index, (family index).doomed history process
  step history process member := by
    obtain ⟨index, member⟩ := member
    exact ChargedStepTo.mono absorb (fun _ _ inside => ⟨index, inside⟩) (fun _ _ holds => holds)
      (fun _ _ => le_rfl) history process ((family index).step history process member)

/-- Two reductions with different charges, for example the two sides of a
branch, under a common charge dominating both. -/
def Reduction.union₂ {Post : List E → A → Prop} {charge₁ charge₂ charge : List E → E → ENNReal}
    (first : Reduction absorb Post charge₁) (second : Reduction absorb Post charge₂)
    (dominates₁ : ∀ history event, charge₁ history event ≤ charge history event)
    (dominates₂ : ∀ history event, charge₂ history event ≤ charge history event) :
    Reduction absorb Post charge :=
  Reduction.union absorb (ι := Bool) fun side =>
    match side with
    | true => first.mono absorb (fun _ _ holds => holds) dominates₁
    | false => second.mono absorb (fun _ _ holds => holds) dominates₂

/-- A received message at `history` followed by certified continuations, one per
message: the receive is doomed at `history` when every message whose event
recovers a reply leads to a doomed continuation at the extended history. -/
def Reduction.receive {Post : List E → A → Prop} {charge : List E → E → ENNReal}
    {operation : I.Op} {event : P → E} {recover : E → Option (I.Reply operation)}
    (absorbed : absorb operation = .receive event recover) (history : List E)
    (next : I.Reply operation → PIR.Proc I A) (continuation : P → Reduction absorb Post charge)
    (linked : ∀ message value, recover (event message) = some value →
      (continuation message).doomed (history ++ [event message]) (next value)) :
    Reduction absorb Post charge where
  doomed reached process := (reached = history ∧ process = .call operation next) ∨
    ∃ message, (continuation message).doomed reached process
  step := by
    rintro reached _ (⟨rfl, rfl⟩ | ⟨message, member⟩)
    · simp only [ChargedStepTo, absorbed]
      exact fun message value recovered => .inr ⟨message, linked message value recovered⟩
    · exact ChargedStepTo.mono absorb (fun _ _ inside => .inr ⟨message, inside⟩)
        (fun _ _ holds => holds) (fun _ _ => le_rfl) reached _
        ((continuation message).step reached _ member)

/-- Bounded repetition. `invariant history m state` holds of the states from
which `m` iterations remain, at the absorbed history; `certificate m` covers one
iteration from such a state with `m + 1` remaining, and its returned states
satisfy `invariant · m`. -/
def Reduction.repeatN {invariant : List E → ℕ → A → Prop} {charge : List E → E → ENNReal}
    (step : A → PIR.Proc I A)
    (certificate : ∀ remaining, Reduction absorb (fun history => invariant history remaining) charge)
    (entry : ∀ history remaining state, invariant history (remaining + 1) state →
      (certificate remaining).doomed history (step state)) :
    Reduction absorb (fun history => invariant history 0) charge where
  doomed history process :=
    (∃ remaining state, invariant history remaining state ∧
      process = PIR.repeatN remaining step state) ∨
    (∃ remaining head, (certificate remaining).doomed history head ∧
      process = head.bind (PIR.repeatN remaining step))
  step := by
    let doomed : List E → PIR.Proc I A → Prop := fun history process =>
      (∃ remaining state, invariant history remaining state ∧
        process = PIR.repeatN remaining step state) ∨
      (∃ remaining head, (certificate remaining).doomed history head ∧
        process = head.bind (PIR.repeatN remaining step))
    have calls : ∀ remaining history (head : PIR.Proc I A),
        (certificate remaining).doomed history head →
        (∀ value, (certificate remaining).doomed history (.done value) → head = .done value →
          ChargedStepTo absorb doomed (fun history => invariant history 0) charge history
            (PIR.repeatN remaining step value)) →
        ChargedStepTo absorb doomed (fun history => invariant history 0) charge history
          (head.bind (PIR.repeatN remaining step)) := by
      intro remaining history head member done
      have obligation := (certificate remaining).step history head member
      match head, obligation with
      | .done value, _ => exact done value member rfl
      | .halt _, _ => trivial
      | .call operation next, obligation =>
          show ChargedStepTo absorb doomed _ charge history
            (.call operation fun reply => (next reply).bind (PIR.repeatN remaining step))
          rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
            ⟨event, decode⟩ | _
          · simp only [ChargedStepTo, absorbed] at obligation ⊢
            exact fun message value recovered =>
              .inr ⟨remaining, _, obligation message value recovered, rfl⟩
          · simp only [ChargedStepTo, absorbed] at obligation ⊢
            exact .inr ⟨remaining, _, obligation, rfl⟩
          · simp only [ChargedStepTo, absorbed] at obligation ⊢
            refine (prEvent_mono _ _
              (fun raw => ∃ value, decode raw = some value ∧
                ¬ (certificate remaining).doomed (history ++ [event]) (next value))
              (fun _ escaping => ?_)).trans obligation
            obtain ⟨value, decoded, outside⟩ := escaping
            exact ⟨value, decoded, fun inside => outside (.inr ⟨remaining, _, inside, rfl⟩)⟩
          · simp only [ChargedStepTo, absorbed]
    have both : ∀ remaining,
        (∀ history state, invariant history remaining state →
          ChargedStepTo absorb doomed (fun history => invariant history 0) charge history
            (PIR.repeatN remaining step state)) ∧
        (∀ history head, (certificate remaining).doomed history head →
          ChargedStepTo absorb doomed (fun history => invariant history 0) charge history
            (head.bind (PIR.repeatN remaining step))) := by
      intro remaining
      induction remaining with
      | zero =>
          refine ⟨fun history state holds => holds, fun history head member =>
            calls 0 history head member ?_⟩
          intro value member _
          exact (certificate 0).step history _ member
      | succ remaining ih =>
          have first : ∀ history state, invariant history (remaining + 1) state →
              ChargedStepTo absorb doomed (fun history => invariant history 0) charge history
                (PIR.repeatN (remaining + 1) step state) :=
            fun history state holds => ih.2 history (step state) (entry history remaining state holds)
          refine ⟨first, fun history head member => calls (remaining + 1) history head member ?_⟩
          intro value member _
          exact first history value ((certificate (remaining + 1)).step history _ member)
    rintro history _ (⟨remaining, state, holds, rfl⟩ | ⟨remaining, head, member, rfl⟩)
    · exact (both remaining).1 history state holds
    · exact (both remaining).2 history head member

theorem Reduction.repeatN_doomed {invariant : List E → ℕ → A → Prop}
    {charge : List E → E → ENNReal} (step : A → PIR.Proc I A)
    (certificate : ∀ remaining, Reduction absorb (fun history => invariant history remaining) charge)
    (entry : ∀ history remaining state, invariant history (remaining + 1) state →
      (certificate remaining).doomed history (step state))
    (history : List E) (remaining : ℕ) (state : A) (holds : invariant history remaining state) :
    (Reduction.repeatN absorb step certificate entry).doomed history
      (PIR.repeatN remaining step state) :=
  .inl ⟨remaining, state, holds, rfl⟩

section Laws
variable {Raw' : E → Type} [∀ event, SampleableType (Raw' event)]

/-- A uniform-sort certificate of a law interface as a reduction, through its
lift to a charged certificate. -/
def UniformCertificate.toReduction (laws : LawInterface I E P Raw') {accepts : A → Prop}
    {error : List E → I.Op → ENNReal} (certificate : UniformCertificate laws accepts error)
    (charge : List E → E → ENNReal)
    (covers : ∀ history operation (event : E) (sort : SampleableType (I.Reply operation))
      (law : LawRecord (Raw' event) (I.Reply operation)), laws operation = .query event sort law →
      law.factor * error history operation + law.slack ≤ charge history event) :
    Reduction laws.absorb (fun _ value => ¬ accepts value) charge :=
  (certificate.charged laws charge covers).toReduction laws.absorb

end Laws

end ZkcSecurity.FiatShamir.Typed

namespace ZkcSecurity.FiatShamir
open OracleComp OracleSpec
open Zkc.Source Zkc.Construction

variable {F G A B : Type} [SampleableType F] [SampleableType B]

/-- A reduction over the common participant actions with a uniform error is a
charged reduction over their transcript interface, with the same doomed
residuals at every history, the final predicate as postcondition, and the bound
`escape` gives for the decoded challenges as the charge of every key. -/
def Reduction.typed {final : A → Prop} {error : ENNReal}
    (reduction : Reduction (F := F) (G := G) final error) (context : Context) (decode : B → F)
    (bound : ENNReal)
    (escape : ∀ event : F → Prop, Pr{let challenge ← $ᵗ F}[event challenge] ≤ error →
      Pr{let answer ← $ᵗ B}[event (decode answer)] ≤ bound) :
    Typed.Reduction (interface (G := G) context decode) (fun _ value => final value)
      (fun _ _ => bound) where
  doomed _ process := reduction.doomed process
  step history process member := by
    have step := reduction.step process member
    match process, step with
    | .done value, step => exact step
    | .halt _, _ => trivial
    | .call operation next, step =>
        cases operation with
        | receive ty site sender => exact fun _ value _ => step value
        | send site receiver sent =>
            simp only [Typed.ChargedStepTo, interface]
            cases Payload.ofValue _ sent with
            | none => trivial
            | some payload => exact step
        | query site op arguments =>
            refine le_trans (le_of_eq (prEvent_congr _ _
              (fun raw => ¬ reduction.doomed (next (decode raw))) fun raw => ?_)) (escape _ step)
            exact ⟨fun ⟨_, decoded, outside⟩ => by
                cases Option.some.inj decoded
                exact outside,
              fun outside => ⟨_, rfl, outside⟩⟩

end ZkcSecurity.FiatShamir
