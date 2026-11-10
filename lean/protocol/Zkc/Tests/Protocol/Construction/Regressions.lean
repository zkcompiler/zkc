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
* Laws of one operation that differ in a premise that evaluation decides select one another; a
  premise that evaluation does not decide remains an obligation.
* A definition registered for evaluation is evaluated when its match is decided and stays as
  written otherwise.
* An instance parameter of a law that the program does not determine is found by instance
  synthesis.
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

/-! ### Premises decided by evaluation -/

/-- The numbers of a literal set. -/
def odd : Nat → Bool := fun index => index.testBit 0

/-- A receive for a member of a set, a constant for another number. -/
def gated (allowed : Nat → Bool) (index : Nat) : Process VSig Nat :=
  if allowed index then .call VOp.recv .done else .done 0

@[spec] theorem gated_member (allowed : Nat → Bool) (index : Nat) (member : allowed index = true) :
    gated allowed index = .call VOp.recv .done := by
  simp only [gated, member, ite_true]

@[spec] theorem gated_outside (allowed : Nat → Bool) (index : Nat)
    (outside : allowed index = false) : gated allowed index = .done 0 := by
  simp only [gated, outside, Bool.false_eq_true, ite_false]

/-- The membership of `2` is decided: the law for a member is refuted and the law for another
number applies. No premise remains. -/
theorem gated_closed :
    ⦃fun _ => ⟨True⟩⦄ gated odd 2 ⦃fun out _ => ⟨out = 0⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  construct_region

/-- The membership of `3` is decided the other way: the receive remains, and no premise. -/
theorem gated_open :
    ⦃fun history => ⟨history = []⟩⦄ gated odd 3
    ⦃fun out history => ⟨history = [out]⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  construct_region
  rintro rfl message value recovered
  obtain rfl : message = value := Option.some.inj recovered
  rfl

/-- A flag that returns when set. -/
def flagged (flag : Bool) : Process VSig Nat := if flag then .done 1 else .halt .reject

@[spec] theorem flagged_set (flag : Bool) (set : flag = true) : flagged flag = .done 1 := by
  simp only [flagged, set, ite_true]

/-- A symbolic flag is not decided: the premise of the law remains an obligation, which the
hypothesis closes. -/
theorem flagged_symbolic (flag : Bool) (set : flag = true) :
    ⦃fun _ => ⟨True⟩⦄ flagged flag ⦃fun out _ => ⟨out = 1⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  construct_region

/-! ### Definitions evaluated when their match is decided -/

/-- A transport along a flag: the value, or the unit value. -/
def keep : (present : Bool) → Nat → Carrier present
  | true, value => value
  | false, _ => ()

/-- Return a number held for a literal index. -/
def stored (index : Nat) : Process VSig (Carrier (odd index)) := .done (keep (odd index) 7)

/-- Without the registration the transport remains in the obligation: reflexivity closes it
only by unfolding the transport and the set. -/
example : ⦃fun _ => ⟨True⟩⦄ stored 3
    ⦃fun out _ => ⟨out = (7 : Nat)⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold stored
  construct_region
  fail_if_success with_reducible rfl
  rfl

section Evaluated
attribute [local construction_eval] keep

/-- With the registration the transport is evaluated: the obligation is an equation between
numerals. -/
theorem stored_value : ⦃fun _ => ⟨True⟩⦄ stored 3
    ⦃fun out _ => ⟨out = (7 : Nat)⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold stored
  construct_region
  with_reducible rfl

/-- Return a number held for a symbolic flag. -/
def storedFor (present : Bool) : Process VSig (Carrier present) := .done (keep present 7)

/-- A symbolic flag is not decided: the transport stays as written. -/
theorem stored_symbolic (present : Bool) : ⦃fun _ => ⟨True⟩⦄ storedFor present
    ⦃fun out _ => ⟨out = keep present 7⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  unfold storedFor
  construct_region

end Evaluated

/-! ### Instance parameters of a law -/

/-- A class that no program mentions. -/
class Budget where
  limit : Nat

/-- A named program whose law holds under an instance that the program does not determine. -/
def budgeted : Process VSig Nat := unknown >>= fun value => .done value

@[spec] theorem budgeted_law [Budget] :
    ⦃fun _ => ⟨True⟩⦄ budgeted ⦃fun _ _ => ⟨True⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ :=
  holds_trivially budgeted

/-- The instance of the law is the one in scope. -/
theorem budgeted_call [Budget] :
    ⦃fun _ => ⟨True⟩⦄ (Process.call VOp.recv .done >>= fun _ => budgeted)
    ⦃fun _ _ => ⟨True⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  construct_region

#print axioms nested_returns_zero
#print axioms equal_call
#print axioms decided_branch
#print axioms decided_named_branch
#print axioms present_call
#print axioms gated_closed
#print axioms gated_open
#print axioms flagged_symbolic
#print axioms stored_value
#print axioms budgeted_call

end ProtocolProofExamples.ConstructorRegressions
