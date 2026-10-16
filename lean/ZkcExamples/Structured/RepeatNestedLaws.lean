module

public import ZkcExamples.Structured.RepeatNestedViews
public import Zkc.Source.Structured.OpenLaws
public import Zkc.Source.Structured.RepeatLaws
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Abel

@[expose] public section

/-! Symbolic equations for the complete unchanged nested-repeat source.
The original inner count and field capture remain independent of both indices. -/
namespace ZkcExamples.Structured.RepeatNestedLaws
open Zkc.Source Zkc.Source.Structured RepeatNestedBodies RepeatNestedViews

set_option smartUnfolding false

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def inputs (outer inner : Option Nat) (x : Option F) :
    Values (Component (assignment F G)) [.index, .index, .field "bls12-381.fr"] :=
  .cons outer (.cons inner (.cons x .nil))

theorem run_body_view (context : ProtocolContext) (self : Nat)
    (outer inner : Option Nat) (x : Option F) :
    invokeProtocol (unit.protocolTable F G) runSignature context self (inputs outer inner x) =
      (runBody.denote
        (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context)
        (maskValues self (context.mapScopes runSignature.inputScopes)
          (inputs outer inner x)).get).bind
        (fun results => .done (maskValues self
          (context.mapScopes runSignature.outputScopes) results)) :=
  unit.protocol_body_view_as runDefinition run_member runSignature run_signature
    runBody run_raw context self (inputs outer inner x)

/-- Zero iterations do not demand the captured inner count or field. -/
theorem zero_outer (inner : Option Nat) (x : Option F) :
    program.participant F G 0 (inputs (some 0) inner x) = .done (.cons x .nil) := by
  change (invokeProtocol (unit.protocolTable F G) runSignature {} 0
    (inputs (some 0) inner x)).interpret forgetSites = _
  rw [run_body_view]
  rfl

/-- Missing outer count fails before any inner callback. -/
theorem missing_outer (inner : Option Nat) (x : Option F) :
    program.participant F G 0 (inputs none inner x) = .halt .incomplete := by
  change (invokeProtocol (unit.protocolTable F G) runSignature {} 0
    (inputs none inner x)).interpret forgetSites = _
  rw [run_body_view]
  rfl

/-- The missing-count observation retains the actual outer header. -/
theorem observed_missing_outer (inner : Option Nat) (x : Option F) :
    program.observed F G 0 (inputs none inner x) =
      .call (.mark "s3") (fun _ => .halt .incomplete) := by
  change invokeProtocol (unit.protocolTable F G) runSignature {} 0 (inputs none inner x) = _
  rw [run_body_view]
  rfl

set_option smartUnfolding true in
/-- Refusal applies to every excessive natural, without inspecting captured inputs. -/
theorem observed_excess_outer (count : Nat) (large : 3 < count)
    (inner : Option Nat) (x : Option F) :
    program.observed F G 0 (inputs (some count) inner x) =
      .call (.mark "s3") (fun _ => .halt .refused) := by
  change invokeProtocol (unit.protocolTable F G) runSignature {} 0
    (inputs (some count) inner x) = _
  rw [run_body_view]
  change ((PIR.Proc.call (I := observedInterface F G) (.mark "s3") (fun _ =>
    (denoteRepeat (F := F) (G := G)
      ⟨[.field "bls12-381.fr"], [.index, .field "bls12-381.fr"], [0], [[0]], 3⟩
      {} 0 (some count) (.cons x .nil) (.cons inner (.cons x .nil)) _).bind _)).bind _ :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) runSignature.outputs)) = _
  simp only [PIR.Proc.bind]
  rw [repeat_above_maximum
    ⟨[.field "bls12-381.fr"], [.index, .field "bls12-381.fr"], [0], [[0]], 3⟩ {} 0 _ _ _ count rfl large]
  rfl

/-- Arithmetic accumulation with an unchanged increment. -/
private def additions (count : Nat) (start increment : F) : F :=
  match count with
  | 0 => start
  | count + 1 => additions count (start + increment) increment

omit [DecidableEq F] in
private theorem additions_eq (count : Nat) (start increment : F) :
    additions count start increment = start + count • increment := by
  induction count generalizing start with
  | zero => simp [additions]
  | succ count ih =>
    rw [additions, ih, succ_nsmul]
    abel

private def nestedAdditions (outer inner : Nat) (start increment : F) : F :=
  match outer with
  | 0 => start
  | outer + 1 => nestedAdditions outer inner (additions inner start increment) increment

omit [DecidableEq F] in
private theorem nestedAdditions_eq (outer inner : Nat) (start increment : F) :
    nestedAdditions outer inner start increment = start + (outer * inner) • increment := by
  induction outer generalizing start with
  | zero => simp [nestedAdditions]
  | succ outer ih =>
    rw [nestedAdditions, ih, additions_eq, Nat.succ_mul, add_nsmul]
    abel

private theorem source_additions (n m : Nat) (outerBound : n ≤ 3) (innerBound : m ≤ 2) (x : F) :
    program.participant F G 0 (inputs (some n) (some m) (some x)) =
      .done (.cons (some (nestedAdditions n m x x)) .nil) := by
  change (invokeProtocol (unit.protocolTable F G) runSignature {} 0
    (inputs (some n) (some m) (some x))).interpret forgetSites = _
  rw [run_body_view]
  interval_cases n <;> interval_cases m <;> rfl

/-- The two independently supplied bounds count additions, not fresh states. -/
theorem repeated_addition (n m : Nat) (outerBound : n ≤ 3) (innerBound : m ≤ 2) (x : F) :
    program.participant F G 0 (inputs (some n) (some m) (some x)) =
      .done (.cons (some ((1 + n * m) • x)) .nil) := by
  rw [source_additions n m outerBound innerBound, nestedAdditions_eq]
  simp only [add_nsmul, one_nsmul]

/-- Each reached inner repeat with zero count preserves the current outer state. -/
theorem zero_inner (n : Nat) (bound : n ≤ 3) (x : Option F) :
    program.participant F G 0 (inputs (some n) (some 0) x) = .done (.cons x .nil) := by
  change (invokeProtocol (unit.protocolTable F G) runSignature {} 0
    (inputs (some n) (some 0) x)).interpret forgetSites = _
  rw [run_body_view]
  interval_cases n <;> rfl

theorem positive_missing_inner (x : Option F) :
    program.participant F G 0 (inputs (some 1) none x) = .halt .incomplete := by
  change (invokeProtocol (unit.protocolTable F G) runSignature {} 0
    (inputs (some 1) none x)).interpret forgetSites = _
  rw [run_body_view]
  rfl

end ZkcExamples.Structured.RepeatNestedLaws
