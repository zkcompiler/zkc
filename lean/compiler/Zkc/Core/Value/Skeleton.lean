module

public import Zkc.Core.Value.Table
public import Zkc.Core.Program.Erase

@[expose] public section

/-!
The value form of a term: the table of its applications and its skeleton.

A term's instructions are of two kinds. A *value* is an operation that computes: equal
applications of it are one value, and where it is written does not matter in a program that
never stops `undefined`. Everything else is kept in order: an effect (an operation whose results
are new each time, or that can stop with a reason), a guard, and every form of control. A dialect
says which of its operations are values (`ValueRules`).

The value form of a term is the table of its applications (`Value/Table.lean`) together with its
*skeleton* (`Skel`): what is kept in order, with identifiers of the table in place of names. A
value has the identifier of the first application of its operation to its operands; a result of
an effect or of a form of control, and an input of a region, is a *leaf* with an identifier of
its own. The walk of the analysis builds both, and follows a skeleton that it is given
(`Facts/Walk.lean`).

An application is placed in the table with its operands in the order written, except that an
operation of two operands whose result does not depend on their order has the smaller
identifier first (`ValueRules.order`), so that `x + y` and `y + x` are one value. An effect keeps
its operands in the order written.

What following a skeleton asks a dialect to decide (`SkelRules`: its types, its performers, and
whether two operations are the same), which the rules of its elaboration give (`Rules.skel`: two
operations are the same when they are written alike), lawful when those rules are
(`Rules.skel_lawful`), and whether how often a loop runs follows how often a loop
of a skeleton runs (`Times.follows`, which then is the loop's count on the identifiers,
`Times.follows_eq`) are here too. The meaning of a skeleton is in `Value/Runs.lean`.
-/
namespace Zkc.Core

open FactCheck (idOf)

/-! ## Which operations are values -/

/-- What the value form reads of the operations of a dialect: which are values, how they are
written, where the table places them, and which commute. A dialect gives it as part of the one
description of its operations (`FactRules.values`, `Facts/OpFacts.lean`). -/
structure ValueRules (D : Dialect) (Raw : Type) where
  /-- The written form of an operation that is a value: equal applications of it are one
  value, and it has no effect and stops only `undefined`. Nothing for an operation that is kept
  in order: one whose results are new each time, or that can stop with a reason. -/
  written : ∀ {ins res : List D.Ty}, D.Op ins res → Option Raw
  /-- A number for a written operation, by which the table places its applications. -/
  place : Raw → Nat
  /-- Whether the result of a written operation of two operands does not depend on their order.
  Such an operation is placed in the table with its operands in one order, whichever way they
  were written. -/
  commutes : Raw → Bool

/-- The identifiers of the operands of a written operation in the order in which the table places
its applications: two operands of an operation that commutes with the smaller first, and every
other list as it is. -/
def ValueRules.order {D : Dialect} {Raw : Type} (rules : ValueRules D Raw) (raw : Raw) :
    List Nat → List Nat
  | [] => []
  | [only] => [only]
  | [first, second] =>
      if rules.commutes raw = true ∧ second < first then [second, first] else [first, second]
  | first :: second :: third :: others => first :: second :: third :: others

/-! ## The skeleton -/

/-- How often a loop of a skeleton runs: a written number of times, or as often as the value of
an identifier says. -/
inductive Count (D : Dialect) (w : D.Who) where
  | fixed (n : Nat)
  | value {t : D.Ty} (count : Nat) (ok : D.Count w t)

/-- The number of iterations, when it is written. -/
def Count.size {D : Dialect} {w : D.Who} : Count D w → Option Nat
  | .fixed n => some n
  | .value .. => none

/-! ## What following a skeleton asks of a dialect -/

section
variable {D : Dialect}

/-- What following a skeleton compares that a dialect must decide: its types, as elaboration
compares them (`TypeEquality`), who performs, and whether two operations are the same. -/
structure SkelRules (D : Dialect) extends TypeEquality D where
  sameWho : DecidableEq D.Who
  /-- Whether two operations on operands of the same types are the same operation. -/
  sameOp : ∀ {ins res res' : List D.Ty}, D.Op ins res → D.Op ins res' → Bool

/-- Operations that are found the same are the same. -/
def SkelRules.Lawful (checks : SkelRules D) : Prop :=
  ∀ {ins res res' : List D.Ty} (o : D.Op ins res) (o' : D.Op ins res'),
    checks.sameOp o o' = true → res = res' ∧ HEq o o'

/-- What following decides for a dialect, from the rules by which its regions are elaborated:
types as the rules compare them, who performs by equality, and two operations by their written
forms. -/
def Rules.skel {Raw Who : Type} [DecidableEq Raw] [DecidableEq D.Who] (rules : Rules D Raw Who) :
    SkelRules D where
  toTypeEquality := rules.toTypeEquality
  sameWho := inferInstance
  sameOp := fun o o' => decide (rules.printOp o = rules.printOp o')

/-- Following is lawful when elaboration's rules are: two operations written alike are read back
as one operation (`Rules.Lawful`). -/
theorem Rules.skel_lawful {Raw Who : Type} [DecidableEq Raw] [DecidableEq D.Who]
    {rules : Rules D Raw Who} (lawful : rules.Lawful) : rules.skel.Lawful := by
  intro ins res res' o o' found
  have both := lawful.op o
  rw [of_decide_eq_true found, lawful.op o'] at both
  exact Sigma.mk.inj (Except.ok.inj both).symm

/-- Whether how often a loop runs follows how often a loop of a skeleton runs: the same written
number, or a count of the same type, by the dialect's decision, on the same identifier. -/
def Times.follows (checks : SkelRules D) {w : D.Who} {Γ : Ctx D.Ty} (ids : Ctx Nat) :
    Times D w Γ → Count D w → Bool
  | .fixed n, .fixed n' => decide (n = n')
  | .value (t := t) count _, .value (t := t') id _ =>
      match checks.sameTy t t' with
      | isTrue _ => decide (idOf ids count.name = id)
      | isFalse _ => false
  | .fixed _, .value .. => false
  | .value .., .fixed _ => false

end

mutual
  /-- What a term keeps in order, on identifiers of a table. A result of an entry and an input
  of a region are leaves: `results` (or `inputs`, `input`) is the first of their identifiers,
  which are consecutive. -/
  inductive Skel (D : Dialect) : List D.Ty → Type where
    | ret {outs} (exit : List Nat) : Skel D outs
    | effect {outs ins res} (key : Key) (o : D.Op ins res) (operands : List Nat) (results : Nat)
        (rest : Skel D outs) : Skel D outs
    | guard {outs t} (key : Key) (w : D.Who) (condition : Nat) (ok : D.Condition w t)
        (why : Reason) (rest : Skel D outs) : Skel D outs
    | choose {outs mid t} (key : Key) (w : D.Who) (condition : Nat) (ok : D.Condition w t)
        (onTrue onFalse : Skel D mid) (results : Nat) (rest : Skel D outs) : Skel D outs
    | cases {outs mid t payloads} (key : Key) (w : D.Who) (subject : Nat)
        (ok : D.Alternatives w t payloads) (arms : SkelArms D mid payloads) (results : Nat)
        (rest : Skel D outs) : Skel D outs
    | loop {outs carried each} (key : Key) (w : D.Who) (times : Count D w) (initial : List Nat)
        (inputs : Nat) (body : Skel D (carried ++ each)) (results : Nat) (rest : Skel D outs) :
        Skel D outs
    | block {outs mid} (key : Key) (number : Nat) (body : Skel D mid) (results : Nat)
        (rest : Skel D outs) : Skel D outs
    | attempt {outs mid} (key : Key) (w : D.Who) (input : Nat) (body : Skel D mid)
        (results : Nat) (rest : Skel D outs) : Skel D outs
  /-- The arms of a case analysis of a skeleton, each with the leaf of its payload. -/
  inductive SkelArms (D : Dialect) : List D.Ty → List D.Ty → Type where
    | nil {mid} : SkelArms D mid []
    | cons {mid payload payloads} (input : Nat) (arm : Skel D mid)
        (rest : SkelArms D mid payloads) : SkelArms D mid (payload :: payloads)
end

/-! ## How often a loop runs, on identifiers -/

section
variable {D : Dialect}

/-- How often a loop runs, on the identifier of its count. -/
def Times.count {w : D.Who} {Γ : Ctx D.Ty} (ids : Ctx Nat) : Times D w Γ → Count D w
  | .fixed n => .fixed n
  | .value count ok => .value (idOf ids count.name) ok

/-- A count that a loop's count follows is the loop's count on the identifiers. -/
theorem Times.follows_eq (checks : SkelRules D) {w : D.Who} {Γ : Ctx D.Ty} (ids : Ctx Nat) :
    ∀ (times : Times D w Γ) (count : Count D w), times.follows checks ids count = true →
      count = times.count ids
  | .fixed n, .fixed n', same => by
      simp only [Times.follows, decide_eq_true_eq] at same
      subst same
      rfl
  | .value (t := t) c ok, .value (t := t') id ok', same => by
      simp only [Times.follows] at same
      split at same
      · next sameType _ =>
          subst sameType
          simp only [decide_eq_true_eq] at same
          subst same
          rfl
      · cases same
  | .fixed _, .value .., same => by cases same
  | .value .., .fixed _, same => by cases same

end

end Zkc.Core
