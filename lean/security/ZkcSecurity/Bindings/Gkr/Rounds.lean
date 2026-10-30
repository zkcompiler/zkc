module

public import ZkcSecurity.Bindings.Gkr.Circuit
public import ZkcSecurity.Families.Sumcheck.Contract
public import Zkc.Protocols.Gkr.Source.VerifierProcess

public section
noncomputable section

/-! Four-table GKR restriction mathematics. These states and anchored point
invariants are independent of source layout, routing, and execution handlers. -/

namespace ZkcSecurity.Realizations.Gkr.Rounds
open Zkc.Polynomial Zkc.Polynomial.Multilinear Zkc.Construction
open Zkc.Source.Structured
open ZkcSecurity.Families.Sumcheck
open ZkcSecurity.Examples.Components
open ZkcExamples.Structured OracleComp OracleSpec

variable {F : Type} [Field F] [DecidableEq F]

structure State (F : Type) (n : Nat) where
  reference : GkrRoundsReference.State F n
  point : List F
  claim : F

@[expose] def advance {n : Nat} (state : State F (n + 1)) (m : F × F × F) (r : F) : State F n :=
  ⟨GkrRoundsReference.restrict state.reference r, state.point ++ [r],
    (Message.coefficientTriples F).evaluate m r⟩

@[expose] def project {n : Nat} (state : State F n) : List F × F := (state.point, state.claim)

@[expose] def value {n : Nat} (reference : GkrRoundsReference.State F n) (point : Fin n → F) : F :=
  Zkc.Protocols.AlgebraicRounds.Gate.value
    (extension n reference.add point) (extension n reference.mul point)
    (extension n reference.left point) (extension n reference.right point)

omit [DecidableEq F] in
theorem value_restrict {n : Nat} (reference : GkrRoundsReference.State F (n + 1))
    (r : F) (tail : List F) :
    value (GkrRoundsReference.restrict reference r) (coordinates n tail) =
      value reference (coordinates (n + 1) (r :: tail)) := by
  have coordinatesEq : coordinates (n + 1) (r :: tail) = Fin.cons r (coordinates n tail) := by
    funext i; refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  simp only [value, GkrRoundsReference.restrict, extension_fixFirst, coordinatesEq]

/-- A trace invariant records observations after all future restrictions, not
just the initial sum. It is independent of the messages and claim truth. -/
@[expose] def Anchored {dimension n : Nat} (root : GkrRoundsReference.State F dimension)
    (state : State F n) : Prop :=
  state.point.length + n = dimension ∧
    ∀ tail : List F, value state.reference (coordinates n tail) =
      value root (coordinates dimension (state.point ++ tail))

omit [DecidableEq F] in
theorem anchored_initial {dimension : Nat} (root : GkrRoundsReference.State F dimension) (claim : F) :
    Anchored root (⟨root, [], claim⟩ : State F dimension) := by
  exact ⟨by simp, fun _ => rfl⟩

omit [DecidableEq F] in
theorem anchored_advance {dimension n : Nat} (root : GkrRoundsReference.State F dimension)
    (state : State F (n + 1)) (anchored : Anchored root state) (m : F × F × F) (r : F) :
    Anchored root (advance state m r) := by
  refine ⟨?_, fun tail => ?_⟩
  · have sized := anchored.1
    simp only [advance, List.length_append, List.length_singleton]; omega
  · rw [show (advance state m r).reference = GkrRoundsReference.restrict state.reference r from rfl,
      value_restrict, anchored.2]
    simp only [advance, List.append_assoc, List.singleton_append]

@[expose] def Residual {dimension n : Nat} (root : GkrRoundsReference.State F dimension)
    (result : List F × F) : Prop :=
  ∃ state : State F n, Anchored root state ∧
    GkrRoundsReference.admissible state.reference ∧
    state.claim ≠ GkrRoundsReference.total state.reference ∧ project state = result

omit [DecidableEq F] in
theorem terminal {dimension : Nat} (root : GkrRoundsReference.State F dimension)
    (result : List F × F) (wrong : Residual (n := 0) root result) :
    result.1.length = dimension ∧ result.2 ≠ value root (coordinates dimension result.1) := by
  obtain ⟨state, anchored, _, wrong, rfl⟩ := wrong
  refine ⟨by simpa [project] using anchored.1, ?_⟩
  have observation := anchored.2 []
  simp only [List.append_nil] at observation
  have total : GkrRoundsReference.total state.reference = value state.reference (coordinates 0 []) := rfl
  exact fun same => wrong (same.trans (total.trans observation).symm)

end ZkcSecurity.Realizations.Gkr.Rounds
