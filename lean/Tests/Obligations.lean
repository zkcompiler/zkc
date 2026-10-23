import Zkc.Obligations.Context
import Zkc.Obligations.TokenRules

set_option autoImplicit false

namespace Tests.Obligations
open Zkc.Obligations Zkc.Transcript

def noEscape : EscapeJudgment Unit (fun _ => Bool) := fun _ _ bad => ∀ raw, ¬ bad raw

theorem noEscape_antitone : noEscape.Antitone :=
  fun _ _ _ _ included bounded raw inside => bounded raw (included raw inside)

/- A genuine promise gap: safe need not mean Yes. -/
def gap : Token Unit := ⟨fun _ => False, fun _ => False, fun _ yes => yes.elim⟩

example : gap.Safe () ∧ ¬ gap.Yes () := ⟨fun no => no, fun yes => yes⟩

def positive : Token Nat := Token.exact (fun value => value > 0)

theorem dropped_no_refused :
    ¬ (Bundle.LiveSafe ([] : Bundle Nat) 0 → Bundle.LiveSafe [positive] 0) := by
  intro discard
  exact discard (Bundle.liveSafe_nil 0) positive (by simp) (by change ¬ (0 > 0); omega)

/- A callee overwrites a captured frame. A name cannot supply its law. -/
theorem wrong_frame_refused :
    ¬ Bundle.Backward [positive] [positive] (fun old new => old = 0 ∧ new = 1) := by
  intro claimed
  have oldSafe := claimed 0 1 ⟨rfl, rfl⟩ (by
    intro token member
    have same : token = positive := by simpa using member
    subst token
    exact positive.yes_safe 1 (by change 1 > 0; omega))
  exact oldSafe positive (by simp) (by change ¬ (0 > 0); omega)

/- Context transport cannot invent honesty for an unrestricted receive. -/
def unrestricted : Context Bool := ⟨fun _ => True⟩
def honest : Context Bool := ⟨fun value => value = true⟩

theorem honest_context_refused :
    ¬ ∃ morphism : Context.Morphism unrestricted honest, morphism.substitution = id := by
  rintro ⟨morphism, same⟩
  have impossible := morphism.valid false trivial
  rw [same] at impossible
  exact Bool.false_ne_true impossible

abbrev bitSignature : PIR.Signature := ⟨Unit, fun _ => Bool⟩
/- Events retain the actual attacker bit. -/
def attackerReceive : Interface bitSignature Bool Bool (fun _ => Bool) :=
  fun _ => .receive id some

def rejectEscape : EscapeJudgment Bool (fun _ => Bool) := fun _ _ _ => False
theorem rejectEscape_antitone : rejectEscape.Antitone := fun _ _ _ _ _ holds => holds.elim

def echo : PIR.Process bitSignature Bool := .call () fun value => .done value

theorem honest_receive_substitution_refused :
    ¬ Nonempty (Derivation attackerReceive rejectEscape (fun _ value => value = true) [] echo) := by
  rintro ⟨derivation⟩
  have reading := derivation.charged rejectEscape_antitone
  change ∀ message value : Bool, some message = some value → value = true at reading
  exact Bool.false_ne_true (reading false false rfl)

def queryBit : Interface bitSignature Unit Unit (fun _ => Bool) := fun _ => .query () some

theorem invalid_escape_refused :
    ¬ Nonempty (Derivation queryBit noEscape (fun _ value => value = false) [] echo) := by
  rintro ⟨derivation⟩
  have reading := derivation.charged noEscape_antitone
  change ∀ raw : Bool, ¬ ∃ value, some raw = some value ∧ value ≠ false at reading
  exact reading true ⟨true, rfl, by decide⟩

theorem accepting_discard_refused :
    ¬ Nonempty (Derivation queryBit noEscape (fun _ _ => False) []
      (PIR.Process.done true)) := by
  rintro ⟨derivation⟩
  exact derivation.charged noEscape_antitone

/- Zero rounds need no service or body law. -/
example {I : PIR.Signature} {E P A : Type} {Raw : E → Type}
    (absorb : Interface I E P Raw) (escape : EscapeJudgment E Raw)
    (Post : List E → A → Prop) (step : A → PIR.Process I A)
    (history : List E) (value : A) (initial : Post history value) :
    Derivation absorb escape Post history (PIR.repeatN 0 step value) := .done initial

/- The slice uses a call and a bounded loop with a retained frame and history. -/
abbrev sendSignature : PIR.Signature := ⟨Nat, fun _ => Unit⟩
def sendInterface : Interface sendSignature Nat Unit (fun _ => Unit) := fun event => .send event ()
def sendEscape : EscapeJudgment Nat (fun _ => Unit) := fun _ _ _ => False

/-- No can live entirely in the caller's frame. It survives an identity callee
even when the callee body has no live obligations of its own. -/
def framed_token_call (history : List Nat) :
    Derivation sendInterface sendEscape (fun _ value => Bundle.Doomed [positive] value) history
      ((PIR.Process.done 0 : PIR.Process sendSignature Nat).bind .done) := by
  apply Derivation.callTokens (before := []) (frameBefore := [positive])
    (after := []) (frameAfter := [positive]) rfl
    (fun _ old new => new = old) (fun _ _ _ _ _ => Bundle.liveSafe_nil _)
    (fun _ old new same safe => by subst new; exact safe) 0
    ⟨positive, by simp, by change ¬ (0 > 0); omega⟩ history (.done rfl)
  intro reached value bad
  exact .done bad

def increment (state : Nat × Nat) : PIR.Process sendSignature (Nat × Nat) :=
  .call state.1 fun _ => .done (state.1 + 1, state.2)

theorem wrong_callee_frame_refused :
    ¬ Nonempty (Derivation sendInterface sendEscape (fun _ result => result.2 = 0) []
      (PIR.Process.call 7 (fun _ => .done (1, 1)) : PIR.Process sendSignature (Nat × Nat))) := by
  rintro ⟨derivation⟩
  have reading := derivation.charged
    (show sendEscape.Antitone from fun _ _ _ _ _ impossible => impossible.elim)
  change (1 : Nat) = 0 at reading
  omega

def slice (allowed : Bool) (count : Nat) (state : Nat × Nat) : PIR.Process sendSignature (Nat × Nat) :=
  if allowed = true then (increment state).bind (PIR.repeatN count increment) else .halt .reject

def increment_derived (history : List Nat) (state : Nat × Nat) :
    Derivation sendInterface sendEscape
      (fun reached result => reached = history ++ [state.1] ∧ result = (state.1 + 1, state.2))
      history (increment state) :=
  .send rfl (.done ⟨rfl, rfl⟩)

def loop_derived (count : Nat) (history : List Nat) (state : Nat × Nat) :
    Derivation sendInterface sendEscape
      (fun reached result => result.1 = state.1 + count ∧ result.2 = state.2 ∧
        reached.length = history.length + count) history (PIR.repeatN count increment state) := by
  let invariant := fun (reached : List Nat) (remaining : Nat) (value : Nat × Nat) =>
    value.1 + remaining = state.1 + count ∧ value.2 = state.2 ∧
      reached.length + remaining = history.length + count
  have body : ∀ reached remaining value, invariant reached (remaining + 1) value →
      Derivation sendInterface sendEscape (fun final => invariant final remaining) reached
        (increment value) := by
    intro reached remaining value valid
    refine .send rfl (.done ?_)
    dsimp [invariant] at valid ⊢
    simp only [List.length_append, List.length_singleton]
    exact ⟨by omega, valid.2.1, by omega⟩
  exact (Derivation.repeatN increment invariant body count history state
    ⟨rfl, rfl, rfl⟩).consequence (fun reached value valid => by
      dsimp [invariant] at valid
      simpa only [Nat.add_zero] using valid)

/-- General rules assemble the slice, retaining the actual returned frame. -/
def slice_derived (allowed : Bool) (count : Nat) (history : List Nat) (state : Nat × Nat) :
    Derivation sendInterface sendEscape
      (fun reached result => result.1 = state.1 + count + 1 ∧ result.2 = state.2 ∧
        reached.length = history.length + count + 1) history (slice allowed count state) := by
  apply Derivation.guard (allowed = true)
  intro _
  apply Derivation.call rfl ((increment_derived history state).frame
    (fun _ result => result.2 = state.2) (fun _ _ returned => by rw [returned.2]))
  intro reached value returned
  rcases returned with ⟨⟨rfl, rfl⟩, _⟩
  exact (loop_derived count (history ++ [state.1]) (state.1 + 1, state.2)).consequence
    (fun final result valid => by
      simp only [List.length_append, List.length_singleton] at valid
      exact ⟨by omega, valid.2.1, by omega⟩)

example (history : List Nat) (state : Nat × Nat) :
    Nonempty (Derivation sendInterface sendEscape (fun _ _ => False) history (slice false 3 state)) :=
  ⟨.halt .reject⟩

/- Stops preserve actual prefix and poststate, but the reading cannot assert
successful acceptance. -/
example (history : List Nat) (state : Nat) :
    (PIR.Process.call 7 (fun _ => .halt .reject) : PIR.Process sendSignature Unit).run
      (fun event saved => ⟨.returned (), (saved.1 + 1, saved.2 ++ [event]), [event]⟩)
      (state, history) = ⟨.stopped .reject, (state + 1, history ++ [7]), [7]⟩ := rfl

example : ¬ Accepted (fun _ : Unit => True) (.stopped .reject) := fun accepted => accepted

/- Equal final outcomes alone lose the reached history and poststate. -/
example (state : Nat) :
    ((PIR.Process.call 7 (fun _ => .halt .reject) : PIR.Process sendSignature Unit).run
      (fun event saved => ⟨.returned (), saved + 1, [event]⟩) state).outcome =
    ((PIR.Process.halt .reject : PIR.Process sendSignature Unit).run
      (fun event saved => ⟨.returned (), saved + 1, [event]⟩) state).outcome := rfl

example : (PIR.Process.call 7 (fun _ => .halt .reject) : PIR.Process sendSignature Unit) ≠
    .halt .reject := by intro impossible; cases impossible

/- Opt-in normalization handles do notation and preserves associativity. -/
open scoped PIR.ProcessSimp in
example {I : PIR.Signature} {A B L : Type} (process : PIR.Process I A) (next : A → PIR.Process I B)
    (leaf : B → L) (stop : PIR.Stop → L) (node : (op : I.Op) → (I.Reply op → L) → L) :
    ((do let value ← process; next value) : PIR.Process I B).foldReplies leaf stop node =
      process.foldReplies (fun value => (next value).foldReplies leaf stop node) stop node := by
  simp

example {I : PIR.Signature} {A B C : Type} (process : PIR.Process I A) (next : A → PIR.Process I B)
    (last : B → PIR.Process I C) :
    ((process >>= next) >>= last) = (process >>= fun value => next value >>= last) := by simp

end Tests.Obligations

#print axioms Zkc.Obligations.Derivation.charged
#print axioms Zkc.Obligations.Derivation.nonempty_iff_charged
#print axioms Zkc.Obligations.Derivation.repeatTokens
#print axioms Tests.Obligations.slice_derived
