import Zkc.Protocols.Sumcheck.Source

/-! Complete source admission, including the pure terminal consumer. -/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Admission

open PIR Zkc.Source
open AlgebraicRounds

variable {F : Type} [CommSemiring F] [DecidableEq F]

theorem rounds_formed (count : Nat) (accumulator : Source.Accumulator F) :
    Conforms interaction (Source.rounds count accumulator) (start count accumulator.claim) := by
  induction count generalizing accumulator with
  | zero => trivial
  | succ count ih =>
      refine ⟨trivial, ?_⟩
      intro message
      by_cases accepted : message.boundary = accumulator.claim
      · simp only [Conforms, interaction, start, if_pos accepted]
        exact ⟨trivial, fun _ => ih _⟩
      · simp only [Conforms, interaction, start, if_neg accepted]
        exact ⟨trivial, fun _ => trivial⟩

theorem rounds_returns (count : Nat) (accumulator : Source.Accumulator F) :
    Boundary.Returns interaction (fun _ phase => phase = .finished)
      (Source.rounds count accumulator) (start count accumulator.claim) := by
  induction count generalizing accumulator with
  | zero => rfl
  | succ count ih =>
      intro message
      by_cases accepted : message.boundary = accumulator.claim
      · simp only [Boundary.Returns, interaction, start, if_pos accepted]
        exact fun _ => ih _
      · simp [Boundary.Returns, interaction, accepted]

theorem rounds_bounded (count : Nat) (accumulator : Source.Accumulator F) :
    Within (2 * count) (Source.rounds count accumulator) := by
  induction count generalizing accumulator with
  | zero => trivial
  | succ count ih =>
      rw [show 2 * (count + 1) = (2 * count + 1) + 1 by omega]
      intro message
      by_cases accepted : message.boundary = accumulator.claim
      · simp only [if_pos accepted, Within]
        exact fun _ => ih _
      · simp [if_neg accepted, Within]

theorem source_formed {n : Nat} (count : Nat)
    (env : Environment (Source.Value F n) [.accumulator, .polynomial]) :
    Conforms interaction ((Source.program count).denote Source.meaning env)
      (start count (env .here).claim) := by
  rw [Source.program_denote]
  exact Boundary.conforms_bind interaction _ _ (fun _ phase => phase = .finished) _
    (rounds_formed count _) (rounds_returns count _) (fun _ _ _ => trivial)

theorem source_returns {n : Nat} (count : Nat)
    (env : Environment (Source.Value F n) [.accumulator, .polynomial]) :
    Boundary.Returns interaction (fun _ phase => phase = .finished)
      ((Source.program count).denote Source.meaning env) (start count (env .here).claim) := by
  rw [Source.program_denote]
  exact Boundary.returns_bind interaction _ _ (fun _ phase => phase = .finished) _ _
    (rounds_returns count _) (fun _ _ completed => completed)

theorem source_bounded {n : Nat} (count : Nat)
    (env : Environment (Source.Value F n) [.accumulator, .polynomial]) :
    Within (2 * count) ((Source.program count).denote Source.meaning env) := by
  rw [Source.program_denote]
  exact Boundary.within_bind _ _ (2 * count) 0 (rounds_bounded count _) (fun _ => trivial)

end Zkc.Protocols.Sumcheck.Admission
