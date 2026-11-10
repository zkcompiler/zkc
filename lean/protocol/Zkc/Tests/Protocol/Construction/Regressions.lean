module

public import Zkc.Tools.Protocol.Readings

/-! Regression controls for the common constructor, on small model processes.

* A condition whose own condition contains an `if` is split on the condition the derived bound
  is built for.
* An equation for one constructor of an operation is not applied to a call of another
  constructor, even when both sides agree after unfolding the operation.
* A condition that its `Decidable` instance decides selects its branch without visiting the other,
  and takes that branch as written, so a named program in it keeps its law.
* A structural equation whose instantiation needs non-reducible unfolding of a value type is
  registered as a `@[spec]` equation; as a `construction_simp` lemma it does not fire.
-/

@[expose] public section
set_option experimental.vcgen true
open PIR Zkc.Transcript Std.WP ProtocolProof ZkcSecurity.Obligations.WeakestPrecondition

namespace ProtocolProofExamples.ConstructorRegressions

inductive VOp where
  | recv

abbrev VSig : Signature := ⟨VOp, fun _ => Nat⟩

/-- One receive of a number; nothing is refused. -/
def absorb : Interface VSig Nat Nat (fun _ => Unit) := fun _ => .receive id some

noncomputable abbrev logic : WPMonad (Process VSig) (Assert Nat) (StopAssert Nat) :=
  chargedMonad absorb exactEscape exactEscape_antitone

attribute [local instance] logic
attribute [local construction_simp] absorb

/-! ### Nested conditions -/

/-- The branch condition itself contains an `if`; the conditional follows a receive, so its
bound is derived. -/
def nested : Process VSig Nat :=
  Process.call VOp.recv .done >>= fun value =>
    if (if value = 0 then 1 else 2) = 1 then .done value else .halt .reject

theorem nested_returns_zero :
    ⦃fun _ => ⟨True⟩⦄ nested ⦃fun out _ => ⟨out = 0⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold nested
  construct_region
  intro message value _
  by_cases zero : value = 0 <;> simp [zero]

/-! ### Equation candidates of another constructor -/

inductive Calc where
  | constant (bit : Bool)
  | equal

/-- An operation meaning by cases; the `constant` case ignores the table and its operands. -/
def calculate (table : Nat → Bool) : Calc → Nat → Nat → Process VSig Bool
  | .constant bit, _, _ => .done bit
  | .equal, left, right => .done (decide (left = right && table left))

/-- The equation of the `constant` case. After unfolding `calculate`, its left side unifies with
an `equal` call while leaving `table` unassigned. -/
@[spec] theorem calculate_constant (table : Nat → Bool) (bit : Bool) (left right : Nat) :
    calculate table (.constant bit) left right = .done bit := rfl

/-- The equation of the `equal` case, at a lower priority so that the other candidate is met
first. -/
@[spec low] theorem calculate_equal (table : Nat → Bool) (left right : Nat) :
    calculate table .equal left right = .done (decide (left = right && table left)) := rfl

theorem equal_call (table : Nat → Bool) (left right : Nat) :
    ⦃fun _ => ⟨True⟩⦄ calculate table .equal left right
    ⦃fun out _ => ⟨out = decide (left = right && table left)⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  construct_region

/-! ### Decided conditions -/

/-- A constant that structural normalization does not unfold. -/
def threshold : Nat := 3

/-- A process with no specification: constructing it is a missing-rule failure. -/
opaque unknown : Process VSig Nat

/-- The condition is decided by its instance; the untaken branch has no rule. -/
def decided : Process VSig Nat :=
  Process.call VOp.recv .done >>= fun value =>
    if threshold = 3 then .done value else unknown

theorem decided_branch :
    ⦃fun _ => ⟨True⟩⦄ decided ⦃fun _ _ => ⟨True⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold decided
  construct_region

/-- Under this interface every node is a receive, so a triple with trivial assertions holds
for every process, including one whose body is not available. -/
theorem holds_trivially (process : Process VSig Nat) :
    ⦃fun _ => ⟨True⟩⦄ process ⦃fun _ _ => ⟨True⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  constructor
  intro history _
  induction process generalizing history with
  | done value => trivial
  | halt reason => trivial
  | call operation next step => exact fun _ value _ => step value _ trivial

/-- A named program over a process without a specification. Its law is the only way to
construct it: its body calls `unknown`. -/
def named : Process VSig Nat := unknown >>= fun value => .done value

@[spec] theorem named_law :
    ⦃fun _ => ⟨True⟩⦄ named ⦃fun _ _ => ⟨True⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ :=
  holds_trivially named

/-- The decided condition selects a named program. The branch is taken as written, so the law
of `named` applies; reducing the branch further would expose `unknown`. -/
def decidedNamed : Process VSig Nat :=
  Process.call VOp.recv .done >>= fun _ =>
    if threshold = 3 then named else .done 0

theorem decided_named_branch :
    ⦃fun _ => ⟨True⟩⦄ decidedNamed ⦃fun _ _ => ⟨True⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold decidedNamed
  construct_region

/-! ### Structural equations up to non-reducible unfolding -/

/-- A value carrier whose instances are not reducible. -/
def Carrier : Bool → Type
  | true => Nat
  | false => Unit

/-- Continue with a present value, stop on an absent one. -/
def present (value : Option (Carrier true)) (next : Nat → Process VSig Nat) : Process VSig Nat :=
  match value with
  | some found => next found
  | none => .halt .incomplete

/-- The present case, stated over `Nat`. A program spelling the value type as `Carrier true`
matches it only after unfolding `Carrier`. -/
theorem present_some (found : Nat) (next : Nat → Process VSig Nat) :
    present (@some Nat found) next = next found := rfl

def presentCall (found : Nat) : Process VSig Nat :=
  present (some found) fun value => .done (value + 1)

section SimpForm
attribute [local construction_simp] present_some

/-- As a structural simp lemma the equation does not fire, since simp matches up to reducible
unfolding; the constructor reports a missing rule. -/
example (found : Nat) :
    ⦃fun _ => ⟨True⟩⦄ presentCall found
    ⦃fun out _ => ⟨out = found + 1⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold presentCall
  fail_if_success construct_region
  exact ⟨fun _ _ => rfl⟩

end SimpForm

section SpecForm
attribute [local spec] present_some

/-- As a `@[spec]` equation it is applied at the program root with full unification. -/
theorem present_call (found : Nat) :
    ⦃fun _ => ⟨True⟩⦄ presentCall found
    ⦃fun out _ => ⟨out = found + 1⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold presentCall
  construct_region

end SpecForm

#print axioms nested_returns_zero
#print axioms equal_call
#print axioms decided_branch
#print axioms decided_named_branch
#print axioms present_call

end ProtocolProofExamples.ConstructorRegressions
