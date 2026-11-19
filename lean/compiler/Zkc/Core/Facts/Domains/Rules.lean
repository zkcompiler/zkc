module

public import Zkc.Core.Facts.Domains.Interface
public import Zkc.Core.Meaning.ValidValues
public import Zkc.Core.Program.Erase
public import Zkc.Core.Process.Same

@[expose] public section

/-!
The seam of the analysis on the term in steps, part 4: what a dialect tells the analysis.

The rules of a dialect (`Rules`) say how an operation is written, whether it is shared, what
its written form requires and guarantees as assertions, which written operations an assertion
may use, and what the index of a loop is. What each domain is told about an operation is the
domain's own and is not here. The laws tie the rules to a semantics (`Rules.Lawful`). They cover
operations used in assertions, safety and guarantees under their requirements, and the numeric
reading of a loop index where the rules specify one. The knowledge domain supplies ranges and forms.
-/

namespace Zkc.Core.BodyAnalysis

/-- What a dialect tells the analysis of its operations. -/
structure Rules (D : Dialect) (Raw : Type) where
  /-- How an application of an operation reads: its written form, for every operation. -/
  written : ∀ {ins res : List D.Ty}, D.Op ins res → Raw
  /-- Whether equal applications of the operation are one value: no reply, no event, no stop
  other than `undefined`. An operation that is not shared is kept in order. -/
  shared : ∀ {ins res : List D.Ty}, D.Op ins res → Bool
  /-- Which operand has the same numeric and Boolean readings as result port zero. -/
  observedOperand : ∀ {ins res : List D.Ty}, D.Op ins res → Option Nat := fun _ => none
  /-- Whether the table places the two operands of a written operation in one order. -/
  commutes : Raw → Bool
  /-- A number for a written operation, by which the table places its applications. -/
  place : Raw → Nat
  /-- How many results a written operation gives. -/
  results : Raw → Nat
  /-- What an application must satisfy to be inside the operation's domain, about its operands;
  and what holds of its operands followed by its results when it is. -/
  contract : Raw → Contract Raw
  /-- Whether an assertion may apply the written operation: it is shared and requires
  nothing, so it gives results on all valid operands of its types. -/
  assertable : Raw → Bool
  /-- Admission and arity together let a dialect resolve a written operation once. -/
  assertionArity : Raw → Option Nat := fun op => if assertable op then some (results op) else none
  assertionArity_eq : ∀ op, assertionArity op =
    (if assertable op then some (results op) else none) := by intros; rfl
  /-- Whether the index of a loop that `who` performs reads as the number of the iteration. -/
  numbered : D.Who → Bool
  /-- Construct the index at a known iteration number. -/
  indexAt : D.Who → Nat → Option (Expr Raw)
  /-- Convert a count to the index type at this loop. Count and index can have different holders. -/
  indexFromCount : ∀ {w t}, D.Count w t → Option (Expr Raw)
  /-- Advance a value of the loop's index type. -/
  indexNext : D.Who → Option (Expr Raw)

section
variable {D : Dialect} {Raw : Type}

/-- The requirements of an operation hold of the values of its operands. -/
def Rules.Required (rules : Rules D Raw) (sem : Semantics D) (R : Reading sem.Dyn)
    (Run : Raw → List sem.Dyn → List sem.Dyn → Prop) (Valid : sem.Dyn → Prop)
    {ins res : List D.Ty} (o : D.Op ins res) (values : HList sem.Val ins) : Prop :=
  ∀ requirement, requirement ∈ (rules.contract (rules.written o)).requires →
    requirement.Holds (ValidRun sem Run Valid) R (sem.dyns values)

/-- The guarantees of an operation hold of the values of its operands followed by its results. -/
def Rules.Ensured (rules : Rules D Raw) (sem : Semantics D) (R : Reading sem.Dyn)
    (Run : Raw → List sem.Dyn → List sem.Dyn → Prop) (Valid : sem.Dyn → Prop)
    {ins res : List D.Ty} (o : D.Op ins res) (values : HList sem.Val ins)
    (results : HList sem.Val res) : Prop :=
  ∀ guarantee, guarantee ∈ (rules.contract (rules.written o)).ensures →
    guarantee.Holds (ValidRun sem Run Valid) R (sem.dyns values ++ sem.dyns results)

/-- Validity, arity and totality for the shared operations an assertion can evaluate. -/
structure Rules.AssertionLaws (rules : Rules D Raw) (sem : Semantics D) (R : Reading sem.Dyn)
    (Run : Raw → List sem.Dyn → List sem.Dyn → Prop) (Valid : sem.Dyn → Prop) : Prop where
  /-- A written operation gives valid results on valid operands, as many as the rules say. -/
  keeps : ∀ raw operands results, Run raw operands results → (∀ v, v ∈ operands → Valid v) →
    (∀ v, v ∈ results → Valid v) ∧ results.length = rules.results raw
  /-- A shared operation whose requirements hold on valid operands returns what its written form
  gives, and its guarantees hold of its operands and results. -/
  defined : ∀ {ins res : List D.Ty} (o : D.Op ins res), rules.shared o = true →
    ∀ (key : Key) (path : List Frame) (values : HList sem.Val ins),
      (∀ v, v ∈ sem.dyns values → Valid v) → rules.Required sem R Run Valid o values →
      ∃ results, sem.op key o path values = .done results ∧
        Run (rules.written o) (sem.dyns values) (sem.dyns results) ∧
        rules.Ensured sem R Run Valid o values results
  /-- An operation that an assertion may use is shared and requires nothing. -/
  assertable : ∀ {ins res : List D.Ty} (o : D.Op ins res),
    rules.assertable (rules.written o) = true →
    rules.shared o = true ∧ (rules.contract (rules.written o)).requires = []

/-- The laws that tie the rules of a dialect to a semantics. -/
structure Rules.Lawful (rules : Rules D Raw) (sem : Semantics D)
    (permitted : ∀ op, sem.S.Reply op → Prop) (R : Reading sem.Dyn)
    (Run : Raw → List sem.Dyn → List sem.Dyn → Prop) (Valid : sem.Dyn → Prop)
    (undefined : sem.H → Prop) : Prop extends rules.AssertionLaws sem R Run Valid where
  /-- A shared operation returns what its written form gives, or stops `undefined`. -/
  computes : ∀ {ins res : List D.Ty} (o : D.Op ins res), rules.shared o = true →
    ∀ (key : Key) (path : List Frame) (values : HList sem.Val ins),
      (∃ results, sem.op key o path values = .done results ∧
          Run (rules.written o) (sem.dyns values) (sem.dyns results)) ∨
        ∃ stop, sem.op key o path values = .halt stop ∧ undefined stop
  observedOperand : ∀ {ins res : List D.Ty} (o : D.Op ins res) {i}, rules.observedOperand o = some i →
    ∀ {key path} {args : HList sem.Val ins} {results : HList sem.Val res},
    (sem.op key o path args).CanReturn permitted results →
    ∀ {x y}, (sem.dyns args)[i]? = some x → (sem.dyns results)[0]? = some y →
      R.Agrees x y
  /-- A written form gives one list of results. -/
  functional : ∀ raw operands results results', Run raw operands results →
    Run raw operands results' → results = results'
  /-- A written form that commutes gives the same on its two operands exchanged. -/
  commutative : ∀ raw, rules.commutes raw = true → ∀ (first second : sem.Dyn) results,
    Run raw [first, second] results → Run raw [second, first] results
  /-- An operation kept in order whose requirements hold on valid operands, on permitted
  replies, never stops `undefined` and returns valid values, of which, with the operands,
  every guarantee of its written form holds. -/
  effect : ∀ {ins res : List D.Ty} (o : D.Op ins res), rules.shared o = false →
    ∀ (key : Key) (path : List Frame) (values : HList sem.Val ins),
      (∀ v, v ∈ sem.dyns values → Valid v) → rules.Required sem R Run Valid o values →
      (sem.op key o path values).Every permitted
        (fun results => (∀ v, v ∈ sem.dyns results → Valid v) ∧
          rules.Ensured sem R Run Valid o values results)
        (fun stop => ¬ undefined stop)
  /-- A valid condition reads as the truth value that the semantics takes it for. -/
  condition : ∀ {w : D.Who} {t : D.Ty} (ok : D.Condition w t) (v : sem.Val t), Valid ⟨t, v⟩ →
    R.bool ⟨t, v⟩ = some (sem.holds ok v)
  /-- A valid count reads as the number that the semantics takes it for. -/
  count : ∀ {w : D.Who} {t : D.Ty} (ok : D.Count w t) (v : sem.Val t), Valid ⟨t, v⟩ →
    R.nat ⟨t, v⟩ = some (sem.count ok v)
  /-- The payload of the alternative of a valid variant is valid. -/
  pick : ∀ {w : D.Who} {t : D.Ty} {payloads : List D.Ty} (ok : D.Alternatives w t payloads)
    (v : sem.Val t), Valid ⟨t, v⟩ → PickValid sem Valid (sem.pick ok v)
  /-- An index is valid, and reads as the number of its iteration where the rules say so. -/
  index : ∀ (w : D.Who) (i : Nat), Valid ⟨D.index w, sem.index w i⟩ ∧
    (rules.numbered w = true → R.nat ⟨D.index w, sem.index w i⟩ = some i)
  /-- A closed expression constructs the typed index of any known iteration. -/
  indexAt : ∀ w n e, rules.indexAt w n = some e →
    e.UsesOnly rules.assertable = true ∧
    e.Denotes (ValidRun sem Run Valid) [] ⟨D.index w, sem.index w n⟩
  /-- A count can already have the right type or need an explicit conversion. -/
  indexFromCount : ∀ {w t} (ok : D.Count w t) e, rules.indexFromCount ok = some e →
    e.UsesOnly rules.assertable = true ∧ ∀ v : sem.Val t, Valid ⟨t, v⟩ →
    e.Denotes (ValidRun sem Run Valid) [⟨t, v⟩] ⟨D.index w, sem.index w (sem.count ok v)⟩
  /-- Successor can compose existing operations, including addition and a literal one. -/
  indexNext : ∀ w e, rules.indexNext w = some e →
    e.UsesOnly rules.assertable = true ∧ ∀ i,
    e.Denotes (ValidRun sem Run Valid) [⟨D.index w, sem.index w i⟩] ⟨D.index w, sem.index w (i + 1)⟩
  /-- The collected values of valid values are valid, when they are as many as the size given,
  if one is given. -/
  collect : ∀ (size : Option Nat) (a : D.Ty) (vs : List (sem.Val a)),
    (∀ n, size = some n → vs.length = n) →
    (∀ v, v ∈ vs → Valid ⟨a, v⟩) → Valid ⟨D.collected size a, sem.collect size a vs⟩
  /-- The beginning of an attempt never stops `undefined` and gives a valid number. -/
  begin : ∀ (w : D.Who) (key : Key) (path : List Frame),
    (sem.begin w key path).Every permitted (fun n => Valid ⟨D.index w, n⟩)
      (fun stop => ¬ undefined stop)
  /-- The end of an attempt never stops `undefined`. -/
  settle : ∀ (w : D.Who) (key : Key) (path : List Frame),
    (sem.settle w key path).Every permitted (fun _ => True) (fun stop => ¬ undefined stop)
  /-- The stop of a guard is not `undefined`. -/
  stop : ∀ (w : D.Who) (why : Reason) (occurrence : Occurrence),
    ¬ undefined (sem.stop w why occurrence)

/-- A value is of a type: it is valid and carries that type. This is what a domain's laws take
as "typed", with the relation of written operations on valid values (`ValidRun`). -/
def TypedValue (sem : Semantics D) (Valid : sem.Dyn → Prop) (v : sem.Dyn) (τ : D.Ty) : Prop :=
  Valid v ∧ v.1 = τ

end

end Zkc.Core.BodyAnalysis
