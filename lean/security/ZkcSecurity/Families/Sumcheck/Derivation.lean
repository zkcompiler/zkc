module

public import ZkcSecurity.Families.Sumcheck.Process
public import ZkcSecurity.Obligations.Derivation

@[expose] public section

/-! Checked consumers over the whole component. Raw answers remain indexed by
the actual occurrence. Conditional bounds concern that raw distribution and the
proved decoder, with the arbitrary received message fixed before the query. -/

set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck
open ZkcSecurity.Algebra.Polynomial
open OracleComp OracleSpec Zkc.Transcript Zkc.Obligations
open ZkcSecurity.Obligations

variable {F : Type} [Field F] {I : PIR.Signature} {Context : Type}
  {State : Nat → Type} {message : Message F} {reference : Reference F}
  {E P : Type} {Raw : E → Type}

structure QueryInterface (program : Program I Context State message)
    (absorb : Interface I E P Raw) where
  event : {n : Nat} → Context → State (n + 1) → message.Carrier → E
  decode : {n : Nat} → (context : Context) → (s : State (n + 1)) →
    (m : message.Carrier) → Raw (event context s m) → Option (I.Reply (program.query context s m))
  challenge : {n : Nat} → (context : Context) → (s : State (n + 1)) →
    (m : message.Carrier) → Raw (event context s m) → F
  absorbed : ∀ {n} (context : Context) (s : State (n + 1)) m,
    absorb (program.query context s m) = .query (event context s m) (decode context s m)
  decoded : ∀ {n} (context : Context) (s : State (n + 1)) m raw reply,
    decode context s m raw = some reply →
    program.challenge context s m reply = challenge context s m raw

namespace QueryInterface

variable {program : Program I Context State message} {absorb : Interface I E P Raw}
  (queries : QueryInterface program absorb) [∀ event, SampleableType (Raw event)]

/-- A theorem about the selected raw sampler and actual decoder, at the reached
history. No uniform field instance, target truth or honest-message law occurs. -/
def ConditionalBound (representation : Representation program reference)
    (messageDegree referenceDegree : Nat) (charge : List E → E → ENNReal) : Prop :=
  ∀ {n} (context : Context) (s : State (n + 1)), representation.Allowed s →
    ∀ (m : message.Carrier) history (p q : Polynomial F), p ≠ q →
      p.natDegree ≤ messageDegree → q.natDegree ≤ referenceDegree →
      Pr{let raw ← $ᵗ (Raw (queries.event context s m))}[
        p.eval (queries.challenge context s m raw) = q.eval (queries.challenge context s m raw)] ≤
        charge history (queries.event context s m)

/-- Optional finite-field specialization after proving the actual raw decoder's
pushforward law. The event-indexed raw carrier is retained throughout. -/
theorem conditional_of_uniform [Fintype F] [DecidableEq F] [SampleableType F]
    (representation : Representation program reference) (messageDegree referenceDegree : Nat)
    (uniform : ∀ {n} (context : Context) (s : State (n + 1)) m (predicate : F → Prop),
      Pr{let raw ← $ᵗ (Raw (queries.event context s m))}[
        predicate (queries.challenge context s m raw)] = Pr{let r ← $ᵗ F}[predicate r]) :
    queries.ConditionalBound representation messageDegree referenceDegree
      (fun _ _ => (max messageDegree referenceDegree : Nat) / (Fintype.card F : ENNReal)) := by
  intro n context s _ m history p q different left right
  rw [uniform context s m (fun r => p.eval r = q.eval r)]
  exact agreement_uniform_le p q different left right

end QueryInterface

namespace Consumers

variable {program : Program I Context State message} {absorb : Interface I E P Raw}
  [∀ event, SampleableType (Raw event)] {charge : List E → E → ENNReal}

/-- Remaining-round falsehood, with actual histories and full returned state.
The received message is unrestricted; only its actual boundary is checked. -/
noncomputable def residual [DecidableEq F]
    (representation : Representation program reference)
    {messageDegree referenceDegree : Nat}
    (messageLaws : MessageLaws message messageDegree)
    (referenceLaws : ReferenceLaws reference referenceDegree)
    (queries : QueryInterface program absorb)
    (sampling : queries.ConditionalBound representation messageDegree referenceDegree charge)
    {n : Nat} (count : Nat) (context : Context) (s : State (n + count))
    (history : List E) (wrong : representation.No s) :
    Derivation absorb (boundedEscape charge) (fun _ result => representation.No result)
      history (program.remaining count context s) := by
  induction count generalizing history with
  | zero => exact .done wrong
  | succ count ih =>
      unfold Program.remaining
      apply (ZkcSecurity.Obligations.unrestricted (program.receive context s) history).bind
      intro reached decoded _
      cases decoded with
      | none => exact .halt .refused
      | some m =>
          apply Derivation.guard (message.boundary m = program.claim s)
          intro checked
          let bad := fun raw : Raw (queries.event context s m) =>
            (message.polynomial m).eval (queries.challenge context s m raw) =
              (reference.polynomial (representation.state s)).eval (queries.challenge context s m raw)
          refine .query (queries.absorbed context s m) bad ?_ ?_
          · exact sampling context s wrong.1 m reached _ _
              (checked_polynomial_ne referenceLaws messageLaws _ wrong.1 _ wrong.2 m checked)
              (messageLaws.degree_le m) (referenceLaws.degree_le _ wrong.1)
          · intro raw reply decoded outside
            apply (ZkcSecurity.Obligations.unrestricted
              (program.deliver context s m (program.challenge context s m reply)) _).bind
            intro delivered _ _
            apply ih _ _
            have falsehood := false_round referenceLaws messageLaws (representation.state s)
              wrong.1 m (queries.challenge context s m raw) outside
            constructor
            · exact representation.advance_allowed referenceLaws context s wrong.1 m _
            · rw [representation.claim, representation.advance, queries.decoded context s m raw reply decoded]
              exact falsehood.1

theorem residual_doomed [DecidableEq F]
    (representation : Representation program reference)
    {messageDegree referenceDegree : Nat}
    (messageLaws : MessageLaws message messageDegree)
    (referenceLaws : ReferenceLaws reference referenceDegree)
    (queries : QueryInterface program absorb)
    (sampling : queries.ConditionalBound representation messageDegree referenceDegree charge)
    {n : Nat} (count : Nat) (context : Context) (s : State (n + count))
    (history : List E) (wrong : representation.No s) :
    (reduction absorb (fun _ (result : State n) => representation.No result) charge).doomed
      history (program.remaining count context s) :=
  derived_doomed (residual representation messageLaws referenceLaws queries sampling
    count context s history wrong)

/-- Transport the same full Process binding later used by honest execution. -/
noncomputable def boundResidual [DecidableEq F]
    (representation : Representation program reference)
    {messageDegree referenceDegree : Nat}
    (messageLaws : MessageLaws message messageDegree)
    (referenceLaws : ReferenceLaws reference referenceDegree)
    (queries : QueryInterface program absorb)
    (sampling : queries.ConditionalBound representation messageDegree referenceDegree charge)
    {n : Nat} (count : Nat) (context : Context) (s : State (n + count))
    (actual : PIR.Process I (State n)) (binding : actual = program.remaining count context s)
    (history : List E) (wrong : representation.No s) :
    Derivation absorb (boundedEscape charge) (fun _ result => representation.No result) history actual :=
  (residual representation messageLaws referenceLaws queries sampling count context s history wrong).transport binding

/-- State zero is insufficient by itself: the caller supplies terminal adequacy
for the actual acceptance predicate on the complete returned value. -/
def terminalCertificate {n : Nat} (representation : Representation program reference)
    (accepts : State n → Prop) (terminal : ∀ result, representation.No result → ¬ accepts result) :
    ZkcSecurity.FiatShamir.Typed.ChargedCertificate absorb accepts charge :=
  certificate accepts (fun _ result => terminal result)

end Consumers
end ZkcSecurity.Families.Sumcheck
