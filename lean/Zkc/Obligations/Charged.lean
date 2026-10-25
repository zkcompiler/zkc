module

public import Zkc.Semantics.Fold
public import Zkc.Transcript.Interface

public section

/-! A structural reading with an abstract escape judgment. This is a reading
of `Transcript.Interface`, not a second operational semantics. Security gives
the judgment its probability meaning. Stops have no returned-value obligation;
this one-sided reading does not assert completion or an honest execution.
-/

set_option autoImplicit false
namespace Zkc.Transcript
variable {I : PIR.Signature} {E P : Type} {Raw : E → Type}

abbrev EscapeJudgment (E : Type) (Raw : E → Type) : Type :=
  (history : List E) → (event : E) → (Raw event → Prop) → Prop

/-- Chargeability is closed under taking smaller exceptional events. -/
@[expose] def EscapeJudgment.Antitone (escape : EscapeJudgment E Raw) : Prop :=
  ∀ history event (smaller larger : Raw event → Prop),
    (∀ raw, smaller raw → larger raw) → escape history event larger → escape history event smaller

@[expose] def Absorption.ChargedNode {Reply : Type} (escape : EscapeJudgment E Raw) :
    Absorption E P Raw Reply → (Reply → List E → Prop) → List E → Prop
  | .receive event recover, next, history =>
      ∀ message value, recover (event message) = some value → next value (history ++ [event message])
  | .send event value, next, history => next value (history ++ [event])
  | .query event decode, next, history =>
      escape history event fun raw =>
        ∃ value, decode raw = some value ∧ ¬ next value (history ++ [event])
  | .refuse, _, _ => True

@[expose] def Interface.Charged (absorb : Interface I E P Raw) (escape : EscapeJudgment E Raw) {A : Type}
    (Post : List E → A → Prop) (process : PIR.Process I A) : List E → Prop :=
  process.foldReplies (fun value history => Post history value) (fun _ _ => True)
    fun operation next => (absorb operation).ChargedNode escape next

@[expose] def Interface.EscapeStep (absorb : Interface I E P Raw) (escape : EscapeJudgment E Raw)
    {A : Type} (doomed : List E → PIR.Process I A → Prop) (Post : List E → A → Prop)
    (history : List E) : PIR.Process I A → Prop
  | .done value => Post history value
  | .halt _ => True
  | .call operation next =>
      (absorb operation).ChargedNode escape (fun reply after => doomed after (next reply)) history

theorem Absorption.chargedNode_mono {Reply : Type} {escape : EscapeJudgment E Raw}
    (antitone : escape.Antitone) (absorption : Absorption E P Raw Reply)
    {lower upper : Reply → List E → Prop}
    (included : ∀ reply history, lower reply history → upper reply history) (history : List E)
    (holds : absorption.ChargedNode escape lower history) :
    absorption.ChargedNode escape upper history := by
  cases absorption with
  | receive event recover =>
      exact fun message value recovered => included _ _ (holds message value recovered)
  | send event value => exact included _ _ holds
  | query event decode =>
      refine antitone history event _ _ ?_ holds
      rintro raw ⟨value, decoded, outside⟩
      exact ⟨value, decoded, fun inside => outside (included _ _ inside)⟩
  | refuse => trivial

variable (absorb : Interface I E P Raw)

theorem Interface.chargedNode_monotone {escape : EscapeJudgment E Raw}
    (antitone : escape.Antitone) :
    PIR.Process.MonotoneNode (L := List E → Prop)
      (fun operation (next : I.Reply operation → List E → Prop) =>
        (absorb operation).ChargedNode escape next) := by
  intro operation lower upper included history holds
  exact (absorb operation).chargedNode_mono antitone
    (fun reply after inside => included reply after inside) history holds

theorem Interface.charged_done (escape : EscapeJudgment E Raw) {A : Type}
    (Post : List E → A → Prop) (value : A) (history : List E) :
    absorb.Charged escape Post (.done value) history = Post history value := rfl

theorem Interface.charged_halt (escape : EscapeJudgment E Raw) {A : Type}
    (Post : List E → A → Prop) (reason : PIR.Stop) (history : List E) :
    absorb.Charged escape Post (.halt reason) history = True := rfl

theorem Interface.charged_call (escape : EscapeJudgment E Raw) {A : Type}
    (Post : List E → A → Prop) (operation : I.Op) (next : I.Reply operation → PIR.Process I A)
    (history : List E) :
    absorb.Charged escape Post (.call operation next) history =
      (absorb operation).ChargedNode escape
        (fun reply after => absorb.Charged escape Post (next reply) after) history := rfl

theorem Interface.charged_bind (escape : EscapeJudgment E Raw) {A B : Type}
    (Post : List E → B → Prop) (process : PIR.Process I A) (next : A → PIR.Process I B) :
    absorb.Charged escape Post (process.bind next) =
      absorb.Charged escape (fun history value => absorb.Charged escape Post (next value) history)
        process := by
  unfold Interface.Charged
  exact PIR.Process.foldReplies_bind _ _ _ process next

/-- Deterministic interpretation transport retains each expansion's returned
reply and reached history. It supplies no random-oracle coupling by itself. -/
theorem Interface.charged_interpret {J : PIR.Signature} (target : Interface J E P Raw)
    (escape : EscapeJudgment E Raw) {A : Type} (Post : List E → A → Prop)
    (operations : PIR.OperationInterpretation I J) (process : PIR.Process I A) :
    target.Charged escape Post (process.interpret operations) =
      process.foldReplies (fun value history => Post history value) (fun _ _ => True)
        (fun operation next =>
          target.Charged escape (fun history reply => next reply history) (operations operation)) := by
  unfold Interface.Charged
  exact PIR.Process.foldReplies_interpret operations _ _ _ process

theorem Interface.Charged.mono {escape : EscapeJudgment E Raw} (antitone : escape.Antitone)
    {A : Type} {Post Weaker : List E → A → Prop} {process : PIR.Process I A} {history : List E}
    (holds : absorb.Charged escape Post process history)
    (weaker : ∀ reached value, Post reached value → Weaker reached value) :
    absorb.Charged escape Weaker process history :=
  PIR.Process.foldReplies_mono (absorb.chargedNode_monotone antitone)
    (leaf := fun value history => Post history value)
    (leaf' := fun value history => Weaker history value)
    (stop := fun _ _ => True) (stop' := fun _ _ => True)
    (fun value reached inside => weaker reached value inside) (fun _ _ inside => inside)
    process history holds

theorem Interface.charged_iff_escapeStep (escape : EscapeJudgment E Raw) {A : Type}
    (Post : List E → A → Prop) (process : PIR.Process I A) (history : List E) :
    absorb.Charged escape Post process history ↔
      absorb.EscapeStep escape (fun reached residual => absorb.Charged escape Post residual reached)
        Post history process := by
  cases process <;> exact Iff.rfl

/-- Every closed reduction lies in the reading, under the actual escape law. -/
theorem Interface.le_charged {escape : EscapeJudgment E Raw} (antitone : escape.Antitone)
    {A : Type} {Post : List E → A → Prop} (doomed : List E → PIR.Process I A → Prop)
    (closed : ∀ history process, doomed history process →
      absorb.EscapeStep escape doomed Post history process)
    (history : List E) (process : PIR.Process I A) (member : doomed history process) :
    absorb.Charged escape Post process history :=
  PIR.Process.le_foldReplies (L := List E → Prop) (absorb.chargedNode_monotone antitone)
    (leaf := fun value history => Post history value) (stop := fun _ _ => True)
    (fun residual reached => doomed reached residual)
    (fun value reached inside => closed reached (.done value) inside)
    (fun _ _ _ => trivial)
    (fun operation next reached inside => closed reached (.call operation next) inside)
    process history member

end Zkc.Transcript
