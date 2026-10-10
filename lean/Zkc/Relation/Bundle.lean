import Zkc.Algebra.RingExpression
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Deterministic relation bundles: several tables with explicit presence and
height policies, column groups whose contents come from the configuration, the
public statement or the witness, closed ring expressions over public slots and
signed same-table reads, scoped assertions, and interaction records.

Read definedness is part of satisfaction: an undefined finite read on an active
row makes the relation false; it is never a default value. Field-weighted
balance and natural multiset equality are different predicates. Local balance
keys include their table, so separate tables never cancel each other. The
bundle has no protocol randomness; `Staged` is a separate challenge-indexed
predicate over the same data.

This model is single-sorted: every value lies in one commutative ring `F`.
The native carrier's typed fields, extension embeddings and canonical natural
decoding are related to it by an interpretation choice, not by a theorem here.
The definitions do not establish that a native parser, evaluator or protocol
implements them.
-/

set_option autoImplicit false

namespace Zkc.Relation.Bundle

inductive ReadModel where
  | finite
  | cyclic
  deriving DecidableEq

/-- Contiguous row sets. `interval` additionally requires `stop ≤ height`. -/
inductive Scope where
  | all
  | first
  | last
  | interior (left right : Nat)
  | interval (start stop : Nat)
  deriving DecidableEq

namespace Scope

def Active : Scope → Nat → Nat → Prop
  | .all, _, _ => True
  | .first, _, row => row = 0
  | .last, height, row => row + 1 = height
  | .interior left right, height, row => left ≤ row ∧ row + right < height
  | .interval start stop, _, row => start ≤ row ∧ row < stop

instance (scope : Scope) (height row : Nat) : Decidable (scope.Active height row) := by
  cases scope <;> unfold Active <;> infer_instance

def Defined : Scope → Nat → Prop
  | .interval _ stop, height => stop ≤ height
  | _, _ => True

instance (scope : Scope) (height : Nat) : Decidable (scope.Defined height) := by
  cases scope <;> unfold Defined <;> infer_instance

end Scope

/-- The party fixing a group's contents. `statement` is the native `public`
authority: values supplied by the verifier's public instance. -/
inductive Authority where
  | witness
  | config
  | statement
  deriving DecidableEq

inductive Input where
  | publicSlot (index : Nat)
  | read (group : Nat) (offset : Int) (column : Nat)
  deriving DecidableEq

abbrev Term (F : Type) := Algebra.RingExpression.Expr F Input

structure Group where
  authority : Authority
  width : Nat

/-- Who chooses a table height, and its admitted range. -/
inductive Height where
  | fixed (height : Nat)
  | config (min max : Nat) (powerOfTwo : Bool)
  | statement (min max : Nat) (powerOfTwo : Bool)

def Height.Admits : Height → Nat → Prop
  | .fixed height, n => n = height ∧ 0 < n
  | .config min max powerOfTwo, n | .statement min max powerOfTwo, n =>
      0 < n ∧ min ≤ n ∧ n ≤ max ∧ (powerOfTwo = true → ∃ k, n = 2 ^ k)

structure Assertion (F : Type) where
  scope : Scope
  expression : Term F

/-- Global contributions share one key per channel and tuple; `inTable key`
contributions balance only within their table and key. -/
inductive Locality where
  | global
  | inTable (key : Nat)
  deriving DecidableEq

def Locality.key (table : Nat) : Locality → Option (Nat × Nat)
  | .global => none
  | .inTable key => some (table, key)

inductive Side where
  | push
  | pull
  deriving DecidableEq

structure FieldInteraction (F : Type) where
  channel : Nat
  locality : Locality
  scope : Scope
  tuple : List (Term F)
  count : Term F

structure MultisetInteraction (F : Type) where
  channel : Nat
  locality : Locality
  scope : Scope
  side : Side
  tuple : List (Term F)
  multiplicity : Term F
  bound : Nat

structure Table (F : Type) where
  optional : Bool
  height : Height
  readModel : ReadModel
  groups : List Group
  assertions : List (Assertion F)
  fieldInteractions : List (FieldInteraction F)
  multisetInteractions : List (MultisetInteraction F)

/-! Supplied data. Cells are indexed by table, group, column and row. Each
party's function is consulted only for groups it has authority over. -/

structure Configuration (F : Type) where
  height : Nat → Nat
  cell : Nat → Nat → Nat → Nat → F

structure Statement (F : Type) where
  present : Nat → Bool
  height : Nat → Nat
  publicSlot : Nat → F
  cell : Nat → Nat → Nat → Nat → F

structure Witness (F : Type) where
  cell : Nat → Nat → Nat → Nat → F

structure Data (F : Type) where
  config : Configuration F
  statement : Statement F
  witness : Witness F

/-- Index of `row + offset`: finite reads must stay inside the table; cyclic
reads reduce modulo a positive height. -/
def resolve (model : ReadModel) (height row : Nat) (offset : Int) : Option Nat :=
  match model with
  | .finite =>
      if 0 ≤ (row : Int) + offset ∧ (row : Int) + offset < height then
        some ((row : Int) + offset).toNat
      else none
  | .cyclic =>
      if 0 < height then some (((row : Int) + offset) % (height : Int)).toNat else none

variable {F : Type}

namespace Table

def heightOf (table : Table F) (t : Nat) (data : Data F) : Nat :=
  match table.height with
  | .fixed height => height
  | .config .. => data.config.height t
  | .statement .. => data.statement.height t

/-- Cell contents from the party with authority over the group. -/
def cell [Zero F] (table : Table F) (t : Nat) (data : Data F)
    (group column row : Nat) : F :=
  match table.groups[group]? with
  | some ⟨.config, _⟩ => data.config.cell t group column row
  | some ⟨.statement, _⟩ => data.statement.cell t group column row
  | some ⟨.witness, _⟩ => data.witness.cell t group column row
  | none => 0

def defined (table : Table F) (height row : Nat) : Input → Bool
  | .publicSlot _ => true
  | .read group offset column =>
      (match table.groups[group]? with
        | some g => decide (column < g.width)
        | none => false) &&
      (resolve table.readModel height row offset).isSome

def valuation [Zero F] (table : Table F) (t : Nat) (data : Data F)
    (height row : Nat) : Input → F
  | .publicSlot index => data.statement.publicSlot index
  | .read group offset column =>
      match resolve table.readModel height row offset with
      | some index => table.cell t data group column index
      | none => 0

/-- Every syntactic input of the term is defined on the row. -/
def TermDefined (table : Table F) (height row : Nat) (e : Term F) : Prop :=
  ∀ x ∈ e.inputs, table.defined height row x = true

def activeRows (scope : Scope) (height : Nat) : List Nat :=
  (List.range height).filter fun row => decide (scope.Active height row)

def AssertionHolds [CommRing F] (table : Table F) (t : Nat) (data : Data F)
    (height : Nat) (a : Assertion F) : Prop :=
  a.scope.Defined height ∧
    ∀ row < height, a.scope.Active height row →
      table.TermDefined height row a.expression ∧
        a.expression.eval (table.valuation t data height row) = 0

/-- Every term of an interaction is defined on each active row. -/
def InteractionDefined (table : Table F) (height : Nat) (scope : Scope)
    (terms : List (Term F)) : Prop :=
  scope.Defined height ∧
    ∀ row < height, scope.Active height row → ∀ e ∈ terms, table.TermDefined height row e

def Admissible (table : Table F) (t : Nat) (data : Data F) : Prop :=
  (table.optional = false → data.statement.present t = true) ∧
    (data.statement.present t = true → table.height.Admits (table.heightOf t data))

def Holds [CommRing F] (table : Table F) (t : Nat) (data : Data F) : Prop :=
  (∀ a ∈ table.assertions, table.AssertionHolds t data (table.heightOf t data) a) ∧
    (∀ i ∈ table.fieldInteractions,
      table.InteractionDefined (table.heightOf t data) i.scope (i.count :: i.tuple)) ∧
    ∀ i ∈ table.multisetInteractions,
      table.InteractionDefined (table.heightOf t data) i.scope (i.multiplicity :: i.tuple)

end Table

/-- One row's field-weighted contribution. -/
structure Contribution (F : Type) where
  channel : Nat
  key : Option (Nat × Nat)
  tuple : List F
  count : F

/-- One row's multiset contribution; `value` denotes its canonical natural. -/
structure Multiplicity (F : Type) where
  channel : Nat
  key : Option (Nat × Nat)
  tuple : List F
  side : Side
  value : F
  bound : Nat

namespace Table

def fieldContributions [CommRing F] (table : Table F) (t : Nat) (data : Data F) :
    List (Contribution F) :=
  let height := table.heightOf t data
  table.fieldInteractions.flatMap fun i =>
    (activeRows i.scope height).map fun row =>
      let v := table.valuation t data height row
      ⟨i.channel, i.locality.key t, i.tuple.map (·.eval v), i.count.eval v⟩

def multiplicities [CommRing F] (table : Table F) (t : Nat) (data : Data F) :
    List (Multiplicity F) :=
  let height := table.heightOf t data
  table.multisetInteractions.flatMap fun i =>
    (activeRows i.scope height).map fun row =>
      let v := table.valuation t data height row
      ⟨i.channel, i.locality.key t, i.tuple.map (·.eval v), i.side,
        i.multiplicity.eval v, i.bound⟩

end Table

end Zkc.Relation.Bundle

namespace Zkc.Relation

/-- A deterministic multi-table relation; its table indices are positions. -/
structure Bundle (F : Type) where
  tables : List (Bundle.Table F)

end Zkc.Relation

namespace Zkc.Relation.Bundle

variable {F : Type}

/-- Contributions of present tables only; an absent table has no rows. -/
def fieldContributions [CommRing F] (b : Bundle F) (data : Data F) :
    List (Contribution F) :=
  b.tables.zipIdx.flatMap fun entry =>
    if data.statement.present entry.2 then entry.1.fieldContributions entry.2 data else []

def multiplicities [CommRing F] (b : Bundle F) (data : Data F) : List (Multiplicity F) :=
  b.tables.zipIdx.flatMap fun entry =>
    if data.statement.present entry.2 then entry.1.multiplicities entry.2 data else []

/-- Sum of the counts at one balance key. -/
def fieldSum [CommRing F] [DecidableEq F] (cs : List (Contribution F)) (channel : Nat)
    (key : Option (Nat × Nat)) (tuple : List F) : F :=
  ((cs.filter fun c => decide (c.channel = channel ∧ c.key = key ∧ c.tuple = tuple)).map
    (·.count)).sum

def FieldBalanced [CommRing F] [DecidableEq F] (cs : List (Contribution F)) : Prop :=
  ∀ channel key tuple, fieldSum cs channel key tuple = 0

/-- Natural total of one side at one balance key, through `natural`. -/
def naturalSum [DecidableEq F] (natural : F → Nat) (ms : List (Multiplicity F))
    (side : Side) (channel : Nat) (key : Option (Nat × Nat)) (tuple : List F) : Nat :=
  ((ms.filter fun m =>
      decide (m.side = side ∧ m.channel = channel ∧ m.key = key ∧ m.tuple = tuple)).map
    fun m => natural m.value).sum

/-- Every multiplicity denotes a natural within its bound, and push and pull
totals agree as naturals at every key. -/
def MultisetHolds [DecidableEq F] (natural : F → Nat) (ms : List (Multiplicity F)) : Prop :=
  (∀ m ∈ ms, natural m.value ≤ m.bound) ∧
    ∀ channel key tuple,
      naturalSum natural ms .push channel key tuple = naturalSum natural ms .pull channel key tuple

/-- Satisfaction. `natural` is the canonical natural representative of a
multiplicity value (for `ZMod n`, `ZMod.val`); it is not applied to field
counts. -/
def Holds [CommRing F] [DecidableEq F] (b : Bundle F) (natural : F → Nat)
    (data : Data F) : Prop :=
  (∀ t (table : Table F), b.tables[t]? = some table →
      table.Admissible t data ∧ (data.statement.present t = true → table.Holds t data)) ∧
    FieldBalanced (b.fieldContributions data) ∧
    MultisetHolds natural (b.multiplicities data)

/-! Balance laws. -/

/-- Keys with no contribution balance trivially, so balance is a finite check
over the keys that actually occur. -/
theorem fieldBalanced_iff [CommRing F] [DecidableEq F] (cs : List (Contribution F)) :
    FieldBalanced cs ↔ ∀ c ∈ cs, fieldSum cs c.channel c.key c.tuple = 0 := by
  constructor
  · intro h c _
    exact h _ _ _
  · intro h channel key tuple
    by_cases occurs : ∃ c ∈ cs, c.channel = channel ∧ c.key = key ∧ c.tuple = tuple
    · obtain ⟨c, mem, rfl, rfl, rfl⟩ := occurs
      exact h c mem
    · have empty : (cs.filter fun c =>
          decide (c.channel = channel ∧ c.key = key ∧ c.tuple = tuple)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro c mem
        simpa using fun a b d => occurs ⟨c, mem, a, b, d⟩
      unfold fieldSum
      rw [empty]
      rfl

theorem naturalSum_absent [DecidableEq F] (natural : F → Nat) (ms : List (Multiplicity F))
    (side : Side) (channel : Nat) (key : Option (Nat × Nat)) (tuple : List F)
    (none : ∀ m ∈ ms, ¬ (m.channel = channel ∧ m.key = key ∧ m.tuple = tuple)) :
    naturalSum natural ms side channel key tuple = 0 := by
  have empty : (ms.filter fun m =>
      decide (m.side = side ∧ m.channel = channel ∧ m.key = key ∧ m.tuple = tuple)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro m mem
    simpa using fun _ a b c => none m mem ⟨a, b, c⟩
  unfold naturalSum
  rw [empty]
  rfl

theorem multisetHolds_iff [DecidableEq F] (natural : F → Nat) (ms : List (Multiplicity F)) :
    MultisetHolds natural ms ↔
      (∀ m ∈ ms, natural m.value ≤ m.bound) ∧
        ∀ m ∈ ms, naturalSum natural ms .push m.channel m.key m.tuple =
          naturalSum natural ms .pull m.channel m.key m.tuple := by
  constructor
  · rintro ⟨bounds, balance⟩
    exact ⟨bounds, fun m _ => balance _ _ _⟩
  · rintro ⟨bounds, balance⟩
    refine ⟨bounds, fun channel key tuple => ?_⟩
    by_cases occurs : ∃ m ∈ ms, m.channel = channel ∧ m.key = key ∧ m.tuple = tuple
    · obtain ⟨m, mem, rfl, rfl, rfl⟩ := occurs
      exact balance m mem
    · have none : ∀ m ∈ ms, ¬ (m.channel = channel ∧ m.key = key ∧ m.tuple = tuple) :=
        fun m mem h => occurs ⟨m, mem, h⟩
      rw [naturalSum_absent natural ms _ _ _ _ none, naturalSum_absent natural ms _ _ _ _ none]

/-- Every contribution comes from a present table: an absent table has no
rows and contributes nothing. -/
theorem fieldContribution_origin [CommRing F] (b : Bundle F) (data : Data F)
    (c : Contribution F) (mem : c ∈ b.fieldContributions data) :
    ∃ t table, b.tables[t]? = some table ∧ data.statement.present t = true ∧
      c ∈ table.fieldContributions t data := by
  simp only [fieldContributions, List.mem_flatMap] at mem
  obtain ⟨⟨table, index⟩, entry, mem⟩ := mem
  have found : b.tables[index]? = some table := by
    rw [List.mem_zipIdx_iff_getElem?] at entry
    simpa using entry
  split at mem
  · exact ⟨index, table, found, by assumption, mem⟩
  · simp at mem

/-- A local key names the contributing table, so contributions of different
tables never share a local balance key. -/
theorem fieldContribution_local_key [CommRing F] (table : Table F) (t : Nat)
    (data : Data F) (c : Contribution F) (mem : c ∈ table.fieldContributions t data)
    (s key : Nat) (isLocal : c.key = some (s, key)) : s = t := by
  simp only [Table.fieldContributions, List.mem_flatMap, List.mem_map] at mem
  obtain ⟨i, _, row, _, rfl⟩ := mem
  cases hi : i.locality with
  | global => simp [hi, Locality.key] at isLocal
  | inTable k =>
      simp only [hi, Locality.key, Option.some.injEq, Prod.mk.injEq] at isLocal
      exact isLocal.1.symm

/-! Staged challenge-dependent programs. -/

/-- Inputs of a staged term. Phase `0` reads are the bundle's own groups;
challenges and claims belong to phases `1..`. -/
inductive StagedInput where
  | publicSlot (index : Nat)
  | read (phase group : Nat) (offset : Int) (column : Nat)
  | challenge (phase index : Nat)
  | claim (phase index : Nat)
  deriving DecidableEq

abbrev StagedTerm (F : Type) := Algebra.RingExpression.Expr F StagedInput

structure StagedAssertion (F : Type) where
  scope : Scope
  expression : StagedTerm F

structure StagedTable (F : Type) where
  groups : List Nat
  assertions : List (StagedAssertion F)

structure StagedPhase (F : Type) where
  challenges : Nat
  claims : Nat
  tables : List (StagedTable F)

structure Staged (F : Type) where
  phases : List (StagedPhase F)
  global : List (StagedTerm F)

/-- Actual challenge values, received claims and committed phase groups,
indexed by phase (from `1`), slot or table/group/column/row. -/
structure StagedData (F : Type) where
  challenge : Nat → Nat → F
  claim : Nat → Nat → F
  cell : Nat → Nat → Nat → Nat → Nat → F

namespace Staged

variable (b : Bundle F) (s : Staged F) (data : Data F) (staged : StagedData F)

/-- An input is available to phase `phase` only if it is not from a later
phase, and a read must be a defined same-table read of an existing group. -/
def defined (t phase height row : Nat) : StagedInput → Bool
  | .publicSlot _ => true
  | .read 0 group offset column =>
      match b.tables[t]? with
      | some table => table.defined height row (.read group offset column)
      | none => false
  | .read (p + 1) group offset column =>
      decide (p + 1 ≤ phase) &&
        (match s.phases[p]? >>= (·.tables[t]?) >>= (·.groups[group]?) with
          | some width => decide (column < width)
          | none => false) &&
        (match b.tables[t]? with
          | some table => (resolve table.readModel height row offset).isSome
          | none => false)
  | .challenge p index =>
      decide (0 < p ∧ p ≤ phase) &&
        (match s.phases[p - 1]? with
          | some ph => decide (index < ph.challenges)
          | none => false)
  | .claim p index =>
      decide (0 < p ∧ p ≤ phase) &&
        (match s.phases[p - 1]? with
          | some ph => decide (index < ph.claims)
          | none => false)

def valuation [Zero F] (t height row : Nat) : StagedInput → F
  | .publicSlot index => data.statement.publicSlot index
  | .read 0 group offset column =>
      match b.tables[t]? with
      | some table => table.valuation t data height row (.read group offset column)
      | none => 0
  | .read (p + 1) group offset column =>
      match b.tables[t]?.bind fun table => resolve table.readModel height row offset with
      | some index => staged.cell (p + 1) t group column index
      | none => 0
  | .challenge p index => staged.challenge p index
  | .claim p index => staged.claim p index

/-- The predicate of phase `phase` (from `1`) on present table `t`. -/
def PhaseTableHolds [CommRing F] (phase t : Nat) (height : Nat)
    (table : StagedTable F) : Prop :=
  ∀ a ∈ table.assertions, a.scope.Defined height ∧
    ∀ row < height, a.scope.Active height row →
      (∀ x ∈ a.expression.inputs, defined b s t phase height row x = true) ∧
        a.expression.eval (valuation b data staged t height row) = 0

/-- The challenge-indexed staged predicate. It contains no assertion or
interaction of the bundle itself, and it does not imply the bundle relation;
relating the two needs a separately stated reduction. -/
def Holds [CommRing F] : Prop :=
  (∀ t (table : Table F), b.tables[t]? = some table → table.Admissible t data) ∧
    (∀ p (phase : StagedPhase F), s.phases[p]? = some phase →
      ∀ t (table : Table F), b.tables[t]? = some table →
        data.statement.present t = true → ∀ (stagedTable : StagedTable F),
          phase.tables[t]? = some stagedTable →
          PhaseTableHolds b s data staged (p + 1) t (table.heightOf t data) stagedTable) ∧
    ∀ g ∈ s.global,
      (∀ x ∈ g.inputs, (match x with | .read .. => false | x => defined b s 0 s.phases.length 0 0 x) = true) ∧
        g.eval (valuation b data staged 0 0 0) = 0

/-- Two staged data that agree on every value available to phase `phase`
give the same phase predicate: later challenges, claims and groups cannot
influence an earlier phase. -/
theorem phaseTableHolds_local [CommRing F] (staged' : StagedData F)
    (phase t height : Nat) (table : StagedTable F)
    (challenges : ∀ p i, p ≤ phase → staged.challenge p i = staged'.challenge p i)
    (claims : ∀ p i, p ≤ phase → staged.claim p i = staged'.claim p i)
    (cells : ∀ p g c r, p ≤ phase → staged.cell p t g c r = staged'.cell p t g c r) :
    PhaseTableHolds b s data staged phase t height table ↔
      PhaseTableHolds b s data staged' phase t height table := by
  have agree : ∀ row, ∀ x, defined b s t phase height row x = true →
      valuation b data staged t height row x = valuation b data staged' t height row x := by
    intro row x available
    cases x with
    | publicSlot => rfl
    | read p group offset column =>
        cases p with
        | zero => rfl
        | succ p =>
            simp only [defined, Bool.and_eq_true, decide_eq_true_eq] at available
            simp only [valuation]
            split <;> simp [cells _ _ _ _ available.1.1]
    | challenge p index =>
        simp only [defined, Bool.and_eq_true, decide_eq_true_eq] at available
        exact challenges p index available.1.2
    | claim p index =>
        simp only [defined, Bool.and_eq_true, decide_eq_true_eq] at available
        exact claims p index available.1.2
  unfold PhaseTableHolds
  refine forall₂_congr fun a _ => and_congr_right fun _ => forall₂_congr fun row _ =>
    imp_congr_right fun _ => ?_
  constructor
  · rintro ⟨inputs, zero⟩
    refine ⟨inputs, ?_⟩
    rw [← Algebra.RingExpression.Expr.eval_local _ _ _
      fun x mem => agree row x (inputs x mem)]
    exact zero
  · rintro ⟨inputs, zero⟩
    refine ⟨inputs, ?_⟩
    rw [Algebra.RingExpression.Expr.eval_local _ _ _
      fun x mem => agree row x (inputs x mem)]
    exact zero

end Staged

end Zkc.Relation.Bundle
