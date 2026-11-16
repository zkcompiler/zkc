module

public import Zkc.Core.Facts.Walk

@[expose] public section

/-!
The value form of a term: the table of its applications and its skeleton.

A term's instructions are of two kinds. A *value* is an operation that computes: equal
applications of it are one value, and where it is written does not matter in a program that
never stops `undefined`. Everything else is kept in order: an effect (an operation whose results
are new each time, or that can stop with a reason), a guard, and every form of control. A dialect
says which of its operations are values (`ValueRules`).

The value form of a term is the table of its applications, the one that the check of facts
builds (`Facts/State.lean`), together with its *skeleton* (`Skel`): what is kept in order, with
identifiers of the table in place of names. A value has the identifier of the first application
of its operation to its operands; a result of an effect or of a form of control, and an input of
a region, is a *leaf* with an identifier of its own. `Term.skeleton` builds both, in one walk.

An application is placed in the table with its operands in the order written, except that an
operation of two operands whose result does not depend on their order has the smaller
identifier first (`ValueRules.order`), so that `x + y` and `y + x` are one value. An effect keeps
its operands in the order written.

The meaning of a skeleton is in `Value/Runs.lean`; whether a second term follows the skeleton
of a first, in `Value/Follows.lean`.
-/

namespace Zkc.Core

open FactCheck (St share fresh idOf idsOf bindIds)

/-! ## Which operations are values -/

/-- What a dialect tells the value form of its operations. -/
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

/-! ## The skeleton of a term -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (rules : ValueRules D Raw)

/-- How often a loop runs, on the identifier of its count. -/
def Times.count {w : D.Who} {Γ : Ctx D.Ty} (ids : Ctx Nat) : Times D w Γ → Count D w
  | .fixed n => .fixed n
  | .value count ok => .value (idOf ids count.name) ok

mutual
  /-- The skeleton of a term and the table with its values, from the identifiers of the names in
  scope and a state. A value is shared in the table, with its operands in the order of
  `ValueRules.order`; every other result is a new leaf. -/
  def Term.skeleton : {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → Ctx Nat →
      St D.Ty Raw → Skel D outs × St D.Ty Raw
    | _, _, .ret exit, ids, st => (.ret (idsOf ids exit), st)
    | _, _, .op (res := res) key o operands results rest, ids, st =>
        match rules.written o with
        | some raw =>
            let made := share raw (rules.order raw (idsOf ids operands)) res.length st
            rest.skeleton (bindIds ids results made.1) made.2
        | none =>
            let made := fresh res.length st
            let after := rest.skeleton (bindIds ids results made.1) made.2
            (.effect key o (idsOf ids operands) st.next after.1, after.2)
    | _, _, .guard key w c ok why rest, ids, st =>
        let after := rest.skeleton ids st
        (.guard key w (idOf ids c.name) ok why after.1, after.2)
    | _, _, .choose (mid := mid) key w c ok _ onTrue onFalse results rest, ids, st =>
        let yes := onTrue.skeleton ids st
        let no := onFalse.skeleton ids yes.2
        let made := fresh mid.length no.2
        let after := rest.skeleton (bindIds ids results made.1) made.2
        (.choose key w (idOf ids c.name) ok yes.1 no.1 no.2.next after.1, after.2)
    | _, _, .cases (mid := mid) key w x ok _ arms results rest, ids, st =>
        let inside := arms.skeleton ids st
        let made := fresh mid.length inside.2
        let after := rest.skeleton (bindIds ids results made.1) made.2
        (.cases key w (idOf ids x.name) ok inside.1 inside.2.next after.1, after.2)
    | _, _, .loop (carried := carried) (each := each) key w times _ initial inputs body results
        rest, ids, st =>
        let bound := fresh (carried.length + 1) st
        let inside := body.skeleton (bindIds ids inputs bound.1) bound.2
        let made := fresh (carried.length + each.length) inside.2
        let after := rest.skeleton (bindIds ids results made.1) made.2
        (.loop key w (times.count ids) (idsOf ids initial) st.next inside.1 inside.2.next after.1,
          after.2)
    | _, _, .block (mid := mid) key number body results rest, ids, st =>
        let inside := body.skeleton ids st
        let made := fresh mid.length inside.2
        let after := rest.skeleton (bindIds ids results made.1) made.2
        (.block key number inside.1 inside.2.next after.1, after.2)
    | _, _, .attempt (mid := mid) key w _ inputs body results rest, ids, st =>
        let bound := fresh 1 st
        let inside := body.skeleton (bindIds ids inputs bound.1) bound.2
        let made := fresh mid.length inside.2
        let after := rest.skeleton (bindIds ids results made.1) made.2
        (.attempt key w st.next inside.1 inside.2.next after.1, after.2)
  /-- The skeletons of the arms of a case analysis. -/
  def Arms.skeleton : {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads →
      Ctx Nat → St D.Ty Raw → SkelArms D mid payloads × St D.Ty Raw
    | _, _, _, .nil, _, st => (.nil, st)
    | _, _, _, .cons inputs arm rest, ids, st =>
        let bound := fresh 1 st
        let inside := arm.skeleton (bindIds ids inputs bound.1) bound.2
        let others := rest.skeleton ids inside.2
        (.cons st.next inside.1 others.1, others.2)
end

end

end Zkc.Core
