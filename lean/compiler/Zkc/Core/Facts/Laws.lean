module

public import Zkc.Core.Facts.Valuation
public import Zkc.Core.Value.Runs

@[expose] public section

/-!
The laws that a dialect proves of its rules and its semantics (`FactRules.Lawful`): what the
soundness of the analysis (`Facts/Soundness.lean`, `Facts/SoundnessFollowing.lean`,
`Facts/Theorems.lean`) asks of a dialect. Each is a statement about the rules and the semantics
alone, with no term in it.

The facts of the table are about `ValidRun`: a written operation that gives results on valid
operands, and valid results. Every operation has requirements, those of its written form, and
they hold of its operands' values or not (`FactRules.Required`): a shared operation whose
requirements hold returns (`defined`), and what its written form guarantees then holds of its
operands followed by its results (`OpFacts.Lawful`, the law `ops`); an operation kept in order
whose requirements hold never stops `undefined` and returns valid values of which, with its
operands, every guarantee of its written form holds (`effect`); and the values that the
requirements of any operation name are there (`named`). The law `collect` asks that the
collected values be as many as the size given, since a sequence of a written size is valid only
of that length; the law `pick` that the payload of the alternative of a valid variant be valid
(`PickValid`).
-/

namespace Zkc.Core

open FactCheck

section
variable {D : Dialect} {Raw : Type}

/-- A written operation gives results on valid operands, and the results are valid: the relation
that the facts of the table are about. -/
def ValidRun (sem : Semantics D) (Run : Raw → List sem.Dyn → List sem.Dyn → Prop)
    (Valid : sem.Dyn → Prop) (raw : Raw) (operands results : List sem.Dyn) : Prop :=
  Run raw operands results ∧ (∀ v, v ∈ operands → Valid v) ∧ ∀ v, v ∈ results → Valid v

/-- The payload of the alternative of a variant is valid. -/
def PickValid (sem : Semantics D) (Valid : sem.Dyn → Prop) {payloads : List D.Ty}
    (p : Pick sem.Val payloads) : Prop :=
  p.All fun τ v => Valid ⟨τ, v⟩

/-- The requirements of an operation hold of the values of its operands. -/
def FactRules.Required (rules : FactRules D Raw) (sem : Semantics D) (R : Reading sem.Dyn)
    (Run : Raw → List sem.Dyn → List sem.Dyn → Prop) (Valid : sem.Dyn → Prop)
    {ins res : List D.Ty} (o : D.Op ins res) (values : HList sem.Val ins) : Prop :=
  ∀ requirement, requirement ∈ rules.ops.requires (rules.written o) →
    requirement.Holds (ValidRun sem Run Valid) R (sem.dyns values)

/-- The laws that tie the rules of a dialect to a semantics. Each is about the rules and the
semantics alone. -/
structure FactRules.Lawful (rules : FactRules D Raw) (sem : Semantics D)
    (permitted : ∀ op, sem.S.Reply op → Prop) (R : Reading sem.Dyn)
    (Run : Raw → List sem.Dyn → List sem.Dyn → Prop) (Valid : sem.Dyn → Prop)
    (undefined : sem.H → Prop) : Prop where
  /-- A value returns what its written form gives, or stops `undefined`; a written form gives
  one result; a written form that commutes gives the same on its operands exchanged. -/
  binding : rules.values.Binding sem Run undefined
  /-- What the rules say of the forms and the ranges of written operations is true. -/
  ops : OpFacts.Lawful rules.ops R (ValidRun sem Run Valid)
  /-- A written operation gives valid results on valid operands. -/
  keeps : ∀ raw operands results, Run raw operands results → (∀ v, v ∈ operands → Valid v) →
    ∀ v, v ∈ results → Valid v
  /-- The law `defined`: a shared operation whose requirements hold on valid operands
  returns. -/
  defined : ∀ {ins res : List D.Ty} (o : D.Op ins res), rules.shared o = true →
    ∀ (key : Key) (path : List Frame) (values : HList sem.Val ins),
      (∀ v, v ∈ sem.dyns values → Valid v) → rules.Required sem R Run Valid o values →
      ∃ results, sem.op key o path values = .done results
  /-- The law `named`: every value that a requirement of an operation names beyond its operands
  is there, on valid operands: one value, given by its written operation. For every
  operation. -/
  named : ∀ {ins res : List D.Ty} (o : D.Op ins res) (values : HList sem.Val ins),
    (∀ v, v ∈ sem.dyns values → Valid v) →
    ∀ requirement, requirement ∈ rules.ops.requires (rules.written o) → ∀ operand,
      operand ∈ requirement.operands → ∀ written positions, operand = .apply written positions →
        ∃ operands results, atPositions (sem.dyns values) positions = some operands ∧
          ValidRun sem Run Valid written operands results ∧ results.length = 1
  /-- The law `effect`: an operation kept in order whose requirements hold on valid operands, on
  permitted replies, never stops `undefined` and returns valid values, of which, with the
  operands, every guarantee of its written form holds. Outside its requirements it may stop
  `undefined`: the analysis has decided them where it is applied. -/
  effect : ∀ {ins res : List D.Ty} (o : D.Op ins res), rules.shared o = false →
    ∀ (key : Key) (path : List Frame) (values : HList sem.Val ins),
      (∀ v, v ∈ sem.dyns values → Valid v) → rules.Required sem R Run Valid o values →
      (sem.op key o path values).Every permitted
        (fun results => (∀ v, v ∈ sem.dyns results → Valid v) ∧
          ∀ guarantee, guarantee ∈ rules.ops.ensures (rules.written o) →
            guarantee.Holds (ValidRun sem Run Valid) R (sem.dyns values ++ sem.dyns results))
        (fun stop => ¬ undefined stop)
  /-- What a type says of a natural holds of its valid values. -/
  range : ∀ (τ : D.Ty) (r : Range) (v : sem.Val τ), rules.range τ = some r → Valid ⟨τ, v⟩ →
    ∃ n, R.nat ⟨τ, v⟩ = some n ∧ r.Has n
  /-- A type that has a valid value is not said to have none. -/
  noValue : ∀ (τ : D.Ty) (v : sem.Val τ), Valid ⟨τ, v⟩ → rules.noValue τ = false
  /-- A valid condition reads as the truth value that the semantics takes it for. -/
  condition : ∀ {w : D.Who} {t : D.Ty} (ok : D.Condition w t) (v : sem.Val t), Valid ⟨t, v⟩ →
    R.bool ⟨t, v⟩ = some (sem.holds ok v)
  /-- A valid count reads as the number that the semantics takes it for. -/
  count : ∀ {w : D.Who} {t : D.Ty} (ok : D.Count w t) (v : sem.Val t), Valid ⟨t, v⟩ →
    R.nat ⟨t, v⟩ = some (sem.count ok v)
  /-- The payload of the alternative of a valid variant is valid. -/
  pick : ∀ {w : D.Who} {t : D.Ty} {payloads : List D.Ty} (ok : D.Alternatives w t payloads)
    (v : sem.Val t), Valid ⟨t, v⟩ → PickValid sem Valid (sem.pick ok v)
  /-- An iteration number is valid and reads as itself. -/
  index : ∀ (w : D.Who) (i : Nat), Valid ⟨D.index w, sem.index w i⟩ ∧
    R.nat ⟨D.index w, sem.index w i⟩ = some i
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

end

end Zkc.Core
