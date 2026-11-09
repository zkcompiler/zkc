module

public import Mathlib.Data.List.Basic

public section

/-! Promise tokens have disjoint Yes and No sides, with a permitted gap.
Presence of a token establishes neither side. Safety moves backwards through
deterministic transitions; by contraposition, No moves forwards.
-/

set_option autoImplicit false
namespace Zkc.Obligations
universe u v

structure Token (State : Type u) where
  Yes : State → Prop
  No : State → Prop
  disjoint : ∀ state, Yes state → No state → False

namespace Token
variable {S : Type u} {T : Type v}

@[expose] def exact (predicate : S → Prop) : Token S :=
  ⟨predicate, fun state => ¬ predicate state, fun _ yes no => no yes⟩

@[expose] def pullback (token : Token T) (substitution : S → T) : Token S :=
  ⟨token.Yes ∘ substitution, token.No ∘ substitution,
    fun state => token.disjoint (substitution state)⟩

@[expose] def Safe (token : Token S) (state : S) : Prop := ¬ token.No state

theorem yes_safe (token : Token S) (state : S) (yes : token.Yes state) : token.Safe state :=
  token.disjoint state yes

end Token

abbrev Bundle (State : Type u) := List (Token State)

namespace Bundle
variable {S : Type u} {T : Type v}

@[expose] def LiveSafe (tokens : Bundle S) (state : S) : Prop :=
  ∀ token ∈ tokens, token.Safe state

@[expose] def Doomed (tokens : Bundle S) (state : S) : Prop :=
  ∃ token ∈ tokens, token.No state

@[expose] def AllYes (tokens : Bundle S) (state : S) : Prop :=
  ∀ token ∈ tokens, token.Yes state

theorem liveSafe_iff_not_doomed (tokens : Bundle S) (state : S) :
    tokens.LiveSafe state ↔ ¬ tokens.Doomed state := by
  constructor
  · intro safe ⟨token, member, no⟩
    exact safe token member no
  · intro no token member bad
    exact no ⟨token, member, bad⟩

theorem allYes_liveSafe (tokens : Bundle S) (state : S) (yes : tokens.AllYes state) :
    tokens.LiveSafe state :=
  fun token member => token.yes_safe state (yes token member)

theorem liveSafe_nil (state : S) : LiveSafe ([] : Bundle S) state :=
  fun _ member => nomatch member

theorem liveSafe_append (left right : Bundle S) (state : S) :
    (left ++ right).LiveSafe state ↔ left.LiveSafe state ∧ right.LiveSafe state := by
  simp only [LiveSafe, List.mem_append, or_imp, forall_and]

/-- Captured and returned states are related explicitly; no frame is implicit. -/
@[expose] def Backward (before : Bundle S) (after : Bundle T) (step : S → T → Prop) : Prop :=
  ∀ old new, step old new → after.LiveSafe new → before.LiveSafe old

/-- Honest Yes transport is a separate obligation. -/
@[expose] def Honest (before : Bundle S) (after : Bundle T) (step : S → T → Prop) : Prop :=
  ∀ old new, step old new → before.AllYes old → after.AllYes new

theorem Backward.doomed {before : Bundle S} {after : Bundle T} {step : S → T → Prop}
    (law : Backward before after step) {old : S} {new : T} (taken : step old new)
    (doomed : before.Doomed old) : after.Doomed new := by
  classical
  by_contra safe
  exact (liveSafe_iff_not_doomed before old).mp
    (law old new taken ((liveSafe_iff_not_doomed after new).mpr safe)) doomed

theorem Backward.frame {before frameBefore : Bundle S} {after frameAfter : Bundle T}
    {step : S → T → Prop} (body : Backward before after step)
    (frame : Backward frameBefore frameAfter step) :
    Backward (before ++ frameBefore) (after ++ frameAfter) step := by
  intro old new taken safe
  obtain ⟨bodySafe, frameSafe⟩ := (liveSafe_append after frameAfter new).mp safe
  exact (liveSafe_append before frameBefore old).mpr
    ⟨body old new taken bodySafe, frame old new taken frameSafe⟩

/-- Accepting-path discard requires a proof of safety at the actual state. -/
theorem discard_iff (tokens : Bundle S) (state : S) :
    (LiveSafe ([] : Bundle S) state → tokens.LiveSafe state) ↔ tokens.LiveSafe state :=
  ⟨fun proof => proof (liveSafe_nil state), fun safe _ => safe⟩

end Bundle
end Zkc.Obligations
