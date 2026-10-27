module

public import Zkc.Construction.OriginalLaws
public import Zkc.Semantics.Yields

@[expose] public section

/-! Frame invariants of the nominal construction. Ordinary source actions
cannot change iteration frames, for any reply or failure. This supplies the
closing-frame obligation when folding a normalized original callback. -/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source
variable {carriers : Structured.Carriers} {A : Type}

private theorem receive_frames (routing : Routing) (state : State carriers)
    (ty : Structured.Ty) (site : String) (sender : Nat) :
    PIR.Yields (fun result => result.2.frames = state.frames) (receive routing state ty site sender) := by
  cases mode : routing.mode with
  | producer =>
      dsimp only [receive]
      simp only [mode]
      cases ty <;> try trivial
      dsimp only
      split
      · trivial
      · unfold queryField
        split
        · dsimp only [PIR.Process.bind, record, PIR.Yields]
          intros
          trivial
        · trivial
  | validator =>
      dsimp only [receive]
      simp only [mode]
      split
      · trivial
      · intro value
        dsimp only
        split
        · trivial
        · dsimp only [record, PIR.Process.bind, PIR.Yields]
          intros
          trivial

private theorem send_frames (routing : Routing) (state : State carriers)
    (ty : Structured.Ty) (site : String) (receiver : Nat) (value : carriers.Value ty) :
    PIR.Yields (fun result => result.2.frames = state.frames) (send routing state ty site receiver value) := by
  cases mode : routing.mode <;> simp only [send, mode]
  all_goals
    split
    · dsimp only [record, PIR.Yields]
      intros
      trivial
    · trivial

private theorem query_frames (routing : Routing) (state : State carriers)
    (site field : String) (handle : Nat) :
    PIR.Yields (fun result => result.2.frames = state.frames) (query routing state site field handle) := by
  unfold query
  split
  · unfold queryField
    split
    · intro _; trivial
    · trivial
  · split
    · split
      · intro _; trivial
      · trivial
    · trivial

/-- Ordinary participant operations preserve the complete frame stack. -/
theorem action_frames (routing : Routing)
    (operation : (Structured.participantInterfaceOn carriers).Op) (state : State carriers) :
    PIR.Yields (fun result => result.2.frames = state.frames) (operations routing (.action operation) state) := by
  cases operation with
  | receive =>
      cases profile : routing.context.profile with
      | fiatShamir _ => simpa only [operations, profile] using receive_frames routing state _ _ _
      | plain =>
          simp only [operations, profile, receivePlain]
          split
          · trivial
          · split
            · trivial
            · intro value; rfl
  | send =>
      cases profile : routing.context.profile with
      | fiatShamir _ => simpa only [operations, profile] using send_frames routing state _ _ _ _
      | plain =>
          simp only [operations, profile, sendPlain]
          split
          · intro value; rfl
          · trivial
  | query site field args =>
      cases args with
      | cons handle tail => cases tail; exact query_frames _ _ _ _ _

/-- A normalized source view with ordinary participant actions preserves frames
on every successful reply path. No condition excludes stopped executions. -/
theorem actions_frames (routing : Routing)
    (source : PIR.Process (Structured.participantInterfaceOn carriers) A) (state : State carriers) :
    PIR.Yields (fun result => result.2.frames = state.frames)
      (source.interpretState (fun operation current => operations routing (.action operation) current) state) := by
  induction source generalizing state with
  | done => rfl
  | halt => trivial
  | call operation next ih =>
      simp only [PIR.Process.interpretState]
      apply (action_frames routing operation state).bind
      intro result frames
      exact (ih result.1 result.2).mono fun value same => same.trans frames

/-- An ordinary-action source callback always closes the frame it entered.
A stopped callback executes no close, keeping its reached operation prefix. -/
theorem fold_within_actions (routing : Routing) (site : String) (index : Nat)
    (source : PIR.Process (Structured.participantInterfaceOn carriers) A) (state : State carriers) :
    fold routing (Structured.Occurrence.iterations.within site index
      (source.interpret Structured.Occurrence.actions)) state =
      (source.interpretState (fun operation current => operations routing (.action operation) current)
        { state with frames := state.frames ++ [⟨site, index⟩] }).bind
        (fun (value, final) => .done (value, { final with frames := state.frames })) := by
  rw [fold_within, fold_actions]
  apply (actions_frames routing source { state with frames := state.frames ++ [⟨site, index⟩] }).bind_congr
  intro result frames
  simp only [frames, List.getLast?_concat, ↓reduceIte, List.dropLast_concat]

end Zkc.Construction.Original
