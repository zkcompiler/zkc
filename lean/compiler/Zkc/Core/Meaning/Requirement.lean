module

public import Zkc.Core.Program.Requirement
public import Zkc.Core.Meaning.Fold

@[expose] public section

/-!
What a requirement says of values.

A requirement (`Program/Requirement.lean`) names values: operands of an application by their
positions, or the first result of a written operation applied to some of them. How a value
reads, as a natural or as a truth value, is a `Reading`; what a written operation gives on
operands is a relation `Run`. Both are given by the dialect. A requirement holds of the values of
an application's operands when the values that it names are there and it says of them what is
true (`Requirement.Holds`). Nothing here depends on an analysis: this is the language in which an
operation states its domain, and in which a definition states what it requires and what it
guarantees (`Summary`, `Program/Requirement.lean`).

A definition satisfies a summary when, on valid inputs of which every requirement holds, it never
stops undefined, and what it returns is valid and, with the inputs, satisfies every guarantee
(`Summary.Holds`). A requirement over no written operation, as the summary of a function is, is
read with no relation of written operations (`Empty.elim`); read as a requirement over the written
operations of a dialect (`Requirement.lift`), it holds of the same values whatever the relation
(`Requirement.holds_lift`), and so does such a summary (`Summary.holds_lift`).
-/

namespace Zkc.Core

/-- How a value reads: as a natural, as a truth value; nothing for a value that is not one. -/
structure Reading (Val : Type) where
  nat : Val → Option Nat
  bool : Val → Option Bool

section
variable {Val : Type} {Raw : Type}

/-- The value that an operand of a requirement names, among the operands' values. -/
def Operand.Denotes (Run : Raw → List Val → List Val → Prop) (args : List Val) :
    Operand Raw → Val → Prop
  | .arg position, v => args[position]? = some v
  | .apply written positions, v => ∃ operands rs, atPositions args positions = some operands ∧
      Run written operands rs ∧ rs.head? = some v

/-- The values that operands name, in order. -/
def DenotesAll (Run : Raw → List Val → List Val → Prop) (args : List Val) :
    List (Operand Raw) → List Val → Prop
  | [], [] => True
  | o :: os, v :: vs => Operand.Denotes Run args o v ∧ DenotesAll Run args os vs
  | _, _ => False

/-- The value that one operand names. -/
theorem DenotesAll.one {Run : Raw → List Val → List Val → Prop} {args : List Val}
    {o : Operand Raw} {vs : List Val} (h : DenotesAll Run args [o] vs) :
    ∃ v, vs = [v] ∧ o.Denotes Run args v := by
  match vs, h with
  | [v], ⟨d, _⟩ => exact ⟨v, rfl, d⟩

/-- The values that two operands name. -/
theorem DenotesAll.two {Run : Raw → List Val → List Val → Prop} {args : List Val}
    {o o' : Operand Raw} {vs : List Val} (h : DenotesAll Run args [o, o'] vs) :
    ∃ v v', vs = [v, v'] ∧ o.Denotes Run args v ∧ o'.Denotes Run args v' := by
  match vs, h with
  | [v, v'], ⟨d, d', _⟩ => exact ⟨v, v', rfl, d, d'⟩

/-- What a requirement says of the values it names: an order, a bound, a number, a truth
value. An order, a bound, a number and a difference are of naturals: the values that it names
read as naturals, and the numbers are so related. -/
def Requirement.Relation (R : Reading Val) : Requirement Raw → List Val → Prop
  | .le .., [a, b] => ∃ x y, R.nat a = some x ∧ R.nat b = some y ∧ x ≤ y
  | .lt .., [a, b] => ∃ x y, R.nat a = some x ∧ R.nat b = some y ∧ x < y
  | .atLeast _ n, [a] => ∃ x, R.nat a = some x ∧ n ≤ x
  | .below _ n, [a] => ∃ x, R.nat a = some x ∧ x < n
  | .exactly _ n, [a] => ∃ x, R.nat a = some x ∧ x = n
  | .difference _ _ n, [b, a] => ∃ x y, R.nat b = some x ∧ R.nat a = some y ∧ x - y = n
  | .holds _, [a] => R.bool a = some true
  | .bounded _, [a] => ∃ x, R.nat a = some x
  | _, _ => False

/-- A requirement holds of the operands' values: the values it names are there, and it says
of them what is true. -/
def Requirement.Holds (Run : Raw → List Val → List Val → Prop) (R : Reading Val)
    (args : List Val) (requirement : Requirement Raw) : Prop :=
  ∃ vs, DenotesAll Run args requirement.operands vs ∧ requirement.Relation R vs

/-- A lifted operand names the value that it names with no relation of written operations: an
operand by its position. -/
theorem Operand.denotes_lift {Run : Raw → List Val → List Val → Prop} {args : List Val} {v : Val} :
    ∀ operand : Operand Empty, (operand.lift (Raw := Raw)).Denotes Run args v ↔
      operand.Denotes Empty.elim args v
  | .arg _ => Iff.rfl
  | .apply written _ => nomatch written

/-- Lifted operands name the values that they name with no relation of written operations. -/
theorem DenotesAll.lift {Run : Raw → List Val → List Val → Prop} {args : List Val} :
    ∀ {operands : List (Operand Empty)} {vs : List Val},
      DenotesAll Run args (operands.map Operand.lift) vs ↔ DenotesAll Empty.elim args operands vs
  | [], [] => Iff.rfl
  | [], _ :: _ => Iff.rfl
  | _ :: _, [] => Iff.rfl
  | operand :: _, _ :: _ => and_congr (Operand.denotes_lift operand) DenotesAll.lift

/-- A lifted requirement says of values what it says. -/
theorem Requirement.relation_lift (R : Reading Val) (requirement : Requirement Empty)
    (vs : List Val) : (requirement.lift (Raw := Raw)).Relation R vs ↔ requirement.Relation R vs := by
  cases requirement <;>
    match vs with
    | [] | [_] | [_, _] | _ :: _ :: _ :: _ => exact Iff.rfl

/-- **A lifted requirement holds whatever the relation of written operations**: exactly when the
requirement holds with none. -/
theorem Requirement.holds_lift {Run : Raw → List Val → List Val → Prop} {R : Reading Val}
    {args : List Val} (requirement : Requirement Empty) :
    (requirement.lift (Raw := Raw)).Holds Run R args ↔ requirement.Holds Empty.elim R args := by
  unfold Requirement.Holds
  rw [Requirement.operands_lift]
  exact exists_congr fun vs => and_congr DenotesAll.lift (Requirement.relation_lift R requirement vs)

/-- Every lifted requirement of a list holds exactly when every requirement of the list holds with
no relation of written operations. -/
theorem Requirement.all_holds_lift {Run : Raw → List Val → List Val → Prop} {R : Reading Val}
    {args : List Val} (requirements : List (Requirement Empty)) :
    (∀ requirement, requirement ∈ requirements.map (Requirement.lift (Raw := Raw)) →
        requirement.Holds Run R args) ↔
      ∀ requirement, requirement ∈ requirements → requirement.Holds Empty.elim R args :=
  ⟨fun all requirement listed =>
      (Requirement.holds_lift requirement).mp (all _ (List.mem_map.mpr ⟨requirement, listed, rfl⟩)),
    fun all requirement listed => by
      obtain ⟨original, listed', rfl⟩ := List.mem_map.mp listed
      exact (Requirement.holds_lift original).mpr (all original listed')⟩

end

/-! ## What it is for a definition to satisfy a summary -/

/-- A definition satisfies a summary: on valid inputs of which every requirement holds, it
never stops undefined, and what it returns is valid and, with the inputs, satisfies every
guarantee. With no requirement and no guarantee this is what it is for the definition to be
assured (`Summary.holds_empty`, `Evidence/Summary.lean`). -/
def Summary.Holds {D : Dialect} {Raw : Type} (sem : Semantics D)
    (permitted : ∀ op, sem.S.Reply op → Prop) (R : Reading sem.Dyn)
    (Run : Raw → List sem.Dyn → List sem.Dyn → Prop) (Valid : sem.Dyn → Prop)
    (undefined : sem.H → Prop) (summary : Summary Raw) {ins outs : List D.Ty}
    (run : HList sem.Val ins → Process sem.S sem.H (HList sem.Val outs)) : Prop :=
  ∀ inputs : HList sem.Val ins, (∀ v, v ∈ sem.dyns inputs → Valid v) →
    (∀ requirement, requirement ∈ summary.requires →
      requirement.Holds Run R (sem.dyns inputs)) →
    (run inputs).Every permitted
      (fun returned => (∀ v, v ∈ sem.dyns returned → Valid v) ∧
        ∀ guarantee, guarantee ∈ summary.ensures →
          guarantee.Holds Run R (sem.dyns inputs ++ sem.dyns returned))
      (fun stop => ¬ undefined stop)

/-- **A lifted summary holds whatever the relation of written operations**: a definition
satisfies the summary of a function read as a summary over the written operations of a dialect, for
any relation, exactly when it satisfies the summary with no relation of written operations. -/
theorem Summary.holds_lift {D : Dialect} {Raw : Type} {sem : Semantics D}
    {permitted : ∀ op, sem.S.Reply op → Prop} {R : Reading sem.Dyn}
    {Run : Raw → List sem.Dyn → List sem.Dyn → Prop} {Valid : sem.Dyn → Prop}
    {undefined : sem.H → Prop} (summary : Summary Empty) {ins outs : List D.Ty}
    {run : HList sem.Val ins → Process sem.S sem.H (HList sem.Val outs)} :
    Summary.Holds sem permitted R Run Valid undefined (summary.lift (Raw := Raw)) run ↔
      Summary.Holds sem permitted R Empty.elim Valid undefined summary run := by
  constructor
  · intro holds values valid required
    exact Process.every_mono _ _
      (fun _ post => ⟨post.1, (Requirement.all_holds_lift summary.ensures).mp post.2⟩)
      (fun _ stop => stop)
      (holds values valid ((Requirement.all_holds_lift summary.requires).mpr required))
  · intro holds values valid required
    exact Process.every_mono _ _
      (fun _ post => ⟨post.1, (Requirement.all_holds_lift summary.ensures).mpr post.2⟩)
      (fun _ stop => stop)
      (holds values valid ((Requirement.all_holds_lift summary.requires).mp required))

end Zkc.Core
