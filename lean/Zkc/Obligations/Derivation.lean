module

public import Zkc.Obligations.Charged
public import Zkc.Semantics.Boundary

public section

/-! Checked structural proofs over the actual open process. Query cuts carry
an abstract escape judgment; receive rules cover every recovered message.

This is a higher-order Lean proof object. Relative adequacy below does not
provide finite serialization or complete proof search. The reverse
construction from the charged reading may use classical choice.
-/

set_option autoImplicit false
namespace Zkc.Obligations
open Zkc.Transcript
variable {I : PIR.Signature} {E P : Type} {Raw : E → Type}

inductive Derivation (absorb : Interface I E P Raw) (escape : EscapeJudgment E Raw) :
    {A : Type} → (List E → A → Prop) → List E → PIR.Process I A → Type 1 where
  | done {A Post history} {value : A} (holds : Post history value) :
      Derivation absorb escape Post history (.done value)
  | halt {A Post history} (reason : PIR.Stop) :
      Derivation absorb escape (A := A) Post history (.halt reason)
  | receive {A Post history} {operation : I.Op} {event : P → E}
      {recover : E → Option (I.Reply operation)} {next : I.Reply operation → PIR.Process I A}
      (absorbed : absorb operation = .receive event recover)
      (continuations : ∀ message value, recover (event message) = some value →
        Derivation absorb escape Post (history ++ [event message]) (next value)) :
      Derivation absorb escape Post history (.call operation next)
  | send {A Post history} {operation : I.Op} {event : E} {value : I.Reply operation}
      {next : I.Reply operation → PIR.Process I A}
      (absorbed : absorb operation = .send event value)
      (continuation : Derivation absorb escape Post (history ++ [event]) (next value)) :
      Derivation absorb escape Post history (.call operation next)
  | query {A Post history} {operation : I.Op} {event : E}
      {decode : Raw event → Option (I.Reply operation)} {next : I.Reply operation → PIR.Process I A}
      (absorbed : absorb operation = .query event decode) (bad : Raw event → Prop)
      (bounded : escape history event bad)
      (continuations : ∀ raw value, decode raw = some value → ¬ bad raw →
        Derivation absorb escape Post (history ++ [event]) (next value)) :
      Derivation absorb escape Post history (.call operation next)
  | refuse {A Post history} {operation : I.Op} {next : I.Reply operation → PIR.Process I A}
      (absorbed : absorb operation = .refuse) :
      Derivation absorb escape Post history (.call operation next)

namespace Derivation
variable {absorb : Interface I E P Raw} {escape : EscapeJudgment E Raw}
  {A B : Type} {Post : List E → A → Prop} {Final : List E → B → Prop}
  {history : List E} {process : PIR.Process I A}

/-- Interpret an abstract escape policy by proving each of its local bounds. -/
def mapEscape {target : EscapeJudgment E Raw}
    (law : ∀ reached event bad, escape reached event bad → target reached event bad)
    {history : List E} {process : PIR.Process I A}
    (derivation : Derivation absorb escape Post history process) :
    Derivation absorb target Post history process :=
  match derivation with
  | .done holds => .done holds
  | .halt reason => .halt reason
  | .receive absorbed continuations => .receive absorbed fun message value recovered =>
      (continuations message value recovered).mapEscape law
  | .send absorbed continuation => .send absorbed (continuation.mapEscape law)
  | .query absorbed bad bounded continuations =>
      .query absorbed bad (law _ _ _ bounded) fun raw value decoded outside =>
        (continuations raw value decoded outside).mapEscape law
  | .refuse absorbed => .refuse absorbed

/-- The continuation receives the actual history and complete returned value. -/
def bind {history : List E} {process : PIR.Process I A}
    (first : Derivation absorb escape Post history process) (next : A → PIR.Process I B)
    (continuation : ∀ reached value, Post reached value →
      Derivation absorb escape Final reached (next value)) :
    Derivation absorb escape Final history (process.bind next) :=
  match first with
  | .done holds => continuation _ _ holds
  | .halt reason => .halt reason
  | .receive absorbed continuations =>
      .receive absorbed fun message value recovered =>
        (continuations message value recovered).bind next continuation
  | .send absorbed suffix => .send absorbed (suffix.bind next continuation)
  | .query absorbed bad bounded continuations =>
      .query absorbed bad bounded fun raw value decoded outside =>
        (continuations raw value decoded outside).bind next continuation
  | .refuse absorbed => .refuse absorbed

def consequence (derivation : Derivation absorb escape Post history process)
    {Weaker : List E → A → Prop} (implies : ∀ reached value, Post reached value → Weaker reached value) :
    Derivation absorb escape Weaker history process := by
  simpa only [PIR.Process.bind_done] using derivation.bind PIR.Process.done
    (fun reached value holds => .done (implies reached value holds))

/-- Exact whole-process transport preserves branches, stops and arbitrary replies. -/
def transport {actual : PIR.Process I A} (binding : actual = process)
    (derivation : Derivation absorb escape Post history process) :
    Derivation absorb escape Post history actual := binding.symm ▸ derivation

/-- Checked conditional branches contribute only their actual guard equations. -/
def branch (condition : Prop) [Decidable condition] {yes no : PIR.Process I A}
    (taken : condition → Derivation absorb escape Post history yes)
    (untaken : ¬ condition → Derivation absorb escape Post history no) :
    Derivation absorb escape Post history (if condition then yes else no) := by
  split
  · exact taken ‹condition›
  · exact untaken ‹¬ condition›

def guard (condition : Prop) [Decidable condition]
    (body : condition → Derivation absorb escape Post history process) :
    Derivation absorb escape Post history (if condition then process else .halt .reject) :=
  branch condition body (fun _ => .halt .reject)

/-- Framing needs a returned-state law. A captured name alone supplies none. -/
def frame (derivation : Derivation absorb escape Post history process)
    (Frame : List E → A → Prop) (preserved : ∀ reached value, Post reached value → Frame reached value) :
    Derivation absorb escape (fun reached value => Post reached value ∧ Frame reached value)
      history process :=
  derivation.consequence fun reached value holds => ⟨holds, preserved reached value holds⟩

/-- Conjoin an independently proved all-replies returned-state invariant. This
connects ordinary private frame preservation to a charged residual derivation. -/
noncomputable def frameReturns (interaction : PIR.Interaction I) (Frame : A → Prop)
    (head : Derivation absorb escape Post history process) (phase : interaction.Phase)
    (returns : PIR.Boundary.Returns interaction (fun value _ => Frame value) process phase) :
    Derivation absorb escape (fun reached value => Post reached value ∧ Frame value) history process := by
  induction head generalizing phase with
  | done holds => exact .done ⟨holds, returns⟩
  | halt reason => exact .halt reason
  | receive absorbed continuations ih =>
      exact .receive absorbed fun m value recovered => ih m value recovered _ (returns value)
  | send absorbed continuation ih => exact .send absorbed (ih _ (returns _))
  | query absorbed bad bounded continuations ih =>
      exact .query absorbed bad bounded fun raw value decoded outside =>
        ih raw value decoded outside _ (returns value)
  | refuse absorbed => exact .refuse absorbed

/-- The binding and the continuation seam belong to each checked call. -/
def call {actual component : PIR.Process I A} (binding : actual = component)
    (callee : Derivation absorb escape Post history component)
    (next : A → PIR.Process I B)
    (seam : ∀ reached value, Post reached value → Derivation absorb escape Final reached (next value)) :
    Derivation absorb escape Final history (actual.bind next) :=
  (callee.transport binding).bind next seam

/-- The zero case is explicit and never invokes a body-local assumption. -/
def repeatN (step : A → PIR.Process I A) (invariant : List E → Nat → A → Prop)
    (body : ∀ reached remaining value, invariant reached (remaining + 1) value →
      Derivation absorb escape (fun final => invariant final remaining) reached (step value)) :
    ∀ count reached value, invariant reached count value →
      Derivation absorb escape (fun final => invariant final 0) reached (PIR.repeatN count step value)
  | 0, _, _, holds => .done holds
  | count + 1, reached, value, holds =>
      (body reached count value holds).bind (PIR.repeatN count step)
        (fun final returned valid => repeatN step invariant body count final returned valid)

theorem charged (antitone : escape.Antitone)
    (derivation : Derivation absorb escape Post history process) :
    absorb.Charged escape Post process history := by
  induction derivation with
  | done holds => exact holds
  | halt reason => trivial
  | receive absorbed continuations ih =>
      rw [Interface.charged_call, absorbed]
      exact fun message value recovered => ih message value recovered
  | send absorbed continuation ih =>
      rw [Interface.charged_call, absorbed]
      exact ih
  | query absorbed bad bounded continuations ih =>
      rw [Interface.charged_call, absorbed]
      refine antitone _ _ _ bad ?_ bounded
      rintro raw ⟨value, decoded, outside⟩
      exact Classical.byContradiction fun inside => outside (ih raw value decoded inside)
  | refuse absorbed =>
      rw [Interface.charged_call, absorbed]
      trivial

/-- Relative completeness of the proof object for its reading. No escape law
is needed in this direction; the canonical exceptional set is used verbatim. -/
theorem of_charged : ∀ (process : PIR.Process I A) (history : List E),
    absorb.Charged escape Post process history → Nonempty (Derivation absorb escape Post history process)
  | .done _, _, holds => ⟨.done holds⟩
  | .halt reason, _, _ => ⟨.halt reason⟩
  | .call operation next, history, holds => by
      rw [Interface.charged_call] at holds
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · rw [absorbed] at holds
        exact ⟨.receive absorbed fun message value recovered =>
          Classical.choice (of_charged (next value) _ (holds message value recovered))⟩
      · rw [absorbed] at holds
        exact ⟨.send absorbed (Classical.choice (of_charged (next value) _ holds))⟩
      · rw [absorbed] at holds
        refine ⟨.query absorbed
          (fun raw => ∃ value, decode raw = some value ∧
            ¬ absorb.Charged escape Post (next value) (history ++ [event]))
          holds fun raw value decoded outside => Classical.choice (of_charged (next value) _ ?_)⟩
        exact Classical.byContradiction fun missing => outside ⟨value, decoded, missing⟩
      · exact ⟨.refuse absorbed⟩

theorem nonempty_iff_charged (antitone : escape.Antitone) :
    Nonempty (Derivation absorb escape Post history process) ↔
      absorb.Charged escape Post process history :=
  ⟨fun ⟨derivation⟩ => derivation.charged antitone, of_charged process history⟩

end Derivation
end Zkc.Obligations
