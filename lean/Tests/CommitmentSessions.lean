import Zkc.Protocols.CommitmentSessions.Modular

set_option autoImplicit false

namespace Tests.CommitmentSessions
open Zkc.Protocols.CommitmentSessions Zkc.Protocols.CommitmentSessions.Modular

def inputs : SessionId → Input := fun sid => if sid then ⟨3,2,3⟩ else ⟨3,1,2⟩
def both : List Action := [⟨false,.commit⟩, ⟨true,.commit⟩]
def complete : List Action := both ++ [⟨false,.reveal⟩, ⟨true,.reveal⟩]

theorem two_builds_to_one :
    (run Zkc.Protocols.CommitmentSessions.Modular.provider inputs false both initial).builds = 2 ∧
    (run Zkc.Protocols.CommitmentSessions.Modular.provider inputs true both initial).builds = 1 := by decide

theorem cancel_before_demand :
    (run Zkc.Protocols.CommitmentSessions.Modular.provider inputs true [⟨false,.cancel⟩,⟨false,.commit⟩] initial).builds = 0 := by decide

theorem honest_open_control :
    (run Zkc.Protocols.CommitmentSessions.Modular.provider inputs true complete initial).sessions false = .done ∧
    (run Zkc.Protocols.CommitmentSessions.Modular.provider inputs true complete initial).sessions true = .done := by decide

theorem wrong_private_cache_control :
    (run Zkc.Protocols.CommitmentSessions.Modular.provider inputs true (both ++ [⟨true,.open 1 2⟩]) initial).sessions true = .failed := by decide

theorem reordered_global_distinguished :
    (run Zkc.Protocols.CommitmentSessions.Modular.provider inputs true both initial).trace ≠
    (run Zkc.Protocols.CommitmentSessions.Modular.provider inputs true both.reverse initial).trace := by decide

theorem reordered_roles_equal :
    role false (run Zkc.Protocols.CommitmentSessions.Modular.provider inputs true both initial).trace =
      role false (run Zkc.Protocols.CommitmentSessions.Modular.provider inputs true both.reverse initial).trace ∧
    role true (run Zkc.Protocols.CommitmentSessions.Modular.provider inputs true both initial).trace =
      role true (run Zkc.Protocols.CommitmentSessions.Modular.provider inputs true both.reverse initial).trace := by decide

theorem toy_group_collision :
    Zkc.Protocols.CommitmentSessions.Modular.provider.verify 3 0 1 2 = true ∧
    Zkc.Protocols.CommitmentSessions.Modular.provider.verify 3 0 2 4 = true := by decide

def eagerInitial : State (List Nat) :=
  {(initial : State (List Nat)) with cache := put (fun _ => none) 3 (table 3), builds := 1}

theorem eager_cancel_separator :
    (run Zkc.Protocols.CommitmentSessions.Modular.provider inputs true [⟨false,.cancel⟩] initial).trace =
      (run Zkc.Protocols.CommitmentSessions.Modular.provider inputs true [⟨false,.cancel⟩] eagerInitial).trace ∧
    (run Zkc.Protocols.CommitmentSessions.Modular.provider inputs true [⟨false,.cancel⟩] initial).builds ≠
      (run Zkc.Protocols.CommitmentSessions.Modular.provider inputs true [⟨false,.cancel⟩] eagerInitial).builds := by decide

/-- Uniform 49-point tape, with the unsafe variant discarding coordinate two. -/
def coinPairs (reuse : Bool) (m1 : Nat) : List (Nat × Nat) :=
  (List.range 7).flatMap fun r0 => (List.range 7).map fun r1 =>
    (3*r0 % 7, (m1 + 3*(if reuse then r0 else r1)) % 7)

def diagonalCount (reuse : Bool) : Nat :=
  ((coinPairs reuse 0).filter (fun p => p.1 == p.2)).length

theorem fresh_vs_reused_diagonal : diagonalCount false = 7 ∧ diagonalCount true = 49 := by decide

theorem fresh_support_same :
    (coinPairs false 0).contains (0,0) = true ∧ (coinPairs false 1).contains (0,0) = true := by decide

theorem reused_support_separator :
    (coinPairs true 0).contains (0,0) = true ∧ (coinPairs true 1).contains (0,0) = false := by decide

end Tests.CommitmentSessions
