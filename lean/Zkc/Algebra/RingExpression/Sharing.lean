import Zkc.Algebra.RingExpression

/-! Structural sharing of ring-expression arenas.

An arena lists nodes whose children are indices of earlier nodes, so one node
can stand for every identical subtree. A node map between two arenas that keeps
each node's label and sends children to the images of children, in order, makes
every node unfold to the same tree as its image. The tree laws of
`Zkc.Algebra.RingExpression` then apply to both arenas unchanged.

The subject is this untyped structural core over one ring. Field identities,
explicit embeddings, admission limits, the native checker and the native
decoder are not modelled here; no native correspondence is claimed.
-/

set_option autoImplicit false

namespace Zkc.Algebra.RingExpression

/-- One arena node; children are indices of earlier nodes. -/
inductive Node (R : Type*) (I : Type*) where
  | constant (value : R)
  | input (index : I)
  | add (left right : Nat)
  | mul (left right : Nat)
  | neg (operand : Nat)
  deriving DecidableEq

namespace Node

variable {R I : Type*}

/-- Send each child through a node map; the label is untouched. -/
def map (f : Nat → Nat) : Node R I → Node R I
  | .constant value => .constant value
  | .input index => .input index
  | .add left right => .add (f left) (f right)
  | .mul left right => .mul (f left) (f right)
  | .neg operand => .neg (f operand)

/-- Every child index is strictly below `i`. -/
def before (i : Nat) : Node R I → Bool
  | .constant _ | .input _ => true
  | .add left right | .mul left right => left < i && right < i
  | .neg operand => operand < i

/-- The operand indices, in operand order. -/
def children : Node R I → List Nat
  | .constant _ | .input _ => []
  | .add left right | .mul left right => [left, right]
  | .neg operand => [operand]

end Node

/-- Nodes in index order. -/
abbrev Arena (R : Type*) (I : Type*) := List (Node R I)

namespace Arena

variable {R I : Type*}

/-- Every edge points strictly backward. -/
def WellFormed (a : Arena R I) : Prop :=
  ∀ i (h : i < a.length), (a[i]).before i = true

/-- `f` sends every node of `a` to a node of `b` with the same label whose
children are the images of its children, in operand order. Nothing is
required of nodes of `b` outside the image. -/
def Hom (f : Nat → Nat) (a b : Arena R I) : Prop :=
  ∀ i (h : i < a.length), b[f i]? = some ((a[i]).map f)

instance (a : Arena R I) : Decidable a.WellFormed :=
  inferInstanceAs (Decidable (∀ i (h : i < a.length), (a[i]).before i = true))

instance [DecidableEq R] [DecidableEq I] (f : Nat → Nat) (a b : Arena R I) :
    Decidable (a.Hom f b) :=
  inferInstanceAs (Decidable (∀ i (h : i < a.length), b[f i]? = some ((a[i]).map f)))

/-- `live` selects nodes together with every node they reach: each operand of
a live node is live. -/
def Closed (live : Nat → Bool) (a : Arena R I) : Prop :=
  ∀ i (h : i < a.length), live i = true → ∀ j ∈ (a[i]).children, live j = true

/-- A label-preserving node map required on the live nodes only. Nodes outside
`live` need no image, so a target that drops them is admitted. -/
def HomOn (live : Nat → Bool) (f : Nat → Nat) (a b : Arena R I) : Prop :=
  ∀ i (h : i < a.length), live i = true → b[f i]? = some ((a[i]).map f)

instance (live : Nat → Bool) (a : Arena R I) : Decidable (a.Closed live) :=
  inferInstanceAs (Decidable (∀ i (h : i < a.length), live i = true →
    ∀ j ∈ (a[i]).children, live j = true))

instance [DecidableEq R] [DecidableEq I] (live : Nat → Bool) (f : Nat → Nat)
    (a b : Arena R I) : Decidable (a.HomOn live f b) :=
  inferInstanceAs (Decidable (∀ i (h : i < a.length), live i = true →
    b[f i]? = some ((a[i]).map f)))

theorem Hom.homOn {f : Nat → Nat} {a b : Arena R I} (hom : a.Hom f b) (live : Nat → Bool) :
    a.HomOn live f b := fun i h _ => hom i h

/-- Unfold node `i` into the tree model with the given fuel. A well-formed
arena resolves every node with any fuel above its index. -/
def unfold (a : Arena R I) : Nat → Nat → Option (Expr R I)
  | 0, _ => none
  | fuel + 1, i =>
    match a[i]? with
    | some (.constant value) => some (.constant value)
    | some (.input index) => some (.input index)
    | some (.add left right) => do
        return .add (← a.unfold fuel left) (← a.unfold fuel right)
    | some (.mul left right) => do
        return .mul (← a.unfold fuel left) (← a.unfold fuel right)
    | some (.neg operand) => do return .neg (← a.unfold fuel operand)
    | none => none

/-- Under a label-preserving node map, every node unfolds to the same tree as
its image, at every fuel. Only the source needs backward edges. -/
theorem unfold_hom {f : Nat → Nat} {a b : Arena R I} (wf : a.WellFormed)
    (hom : a.Hom f b) :
    ∀ fuel i, i < a.length → a.unfold fuel i = b.unfold fuel (f i) := by
  intro fuel
  induction fuel with
  | zero => intro i _; rfl
  | succ fuel ih =>
    intro i hi
    have hw := wf i hi
    have hb := hom i hi
    have ha : a[i]? = some a[i] := List.getElem?_eq_getElem hi
    generalize a[i] = n at hw hb ha
    cases n with
    | constant value => simp [unfold, ha, hb, Node.map]
    | input index => simp [unfold, ha, hb, Node.map]
    | add left right =>
      simp only [Node.before, Bool.and_eq_true, decide_eq_true_eq] at hw
      simp [unfold, ha, hb, Node.map, ih left (by omega), ih right (by omega)]
    | mul left right =>
      simp only [Node.before, Bool.and_eq_true, decide_eq_true_eq] at hw
      simp [unfold, ha, hb, Node.map, ih left (by omega), ih right (by omega)]
    | neg operand =>
      simp only [Node.before, decide_eq_true_eq] at hw
      simp [unfold, ha, hb, Node.map, ih operand (by omega)]

/-- Dead-node elimination. Under a node map that is label preserving on a
closed live set, every live node unfolds to the same tree as its image; the
nodes outside the set, which no live node reaches, do not take part. -/
theorem unfold_homOn {live : Nat → Bool} {f : Nat → Nat} {a b : Arena R I}
    (wf : a.WellFormed) (closed : a.Closed live) (hom : a.HomOn live f b) :
    ∀ fuel i, i < a.length → live i = true → a.unfold fuel i = b.unfold fuel (f i) := by
  intro fuel
  induction fuel with
  | zero => intro i _ _; rfl
  | succ fuel ih =>
    intro i hi hl
    have hw := wf i hi
    have hb := hom i hi hl
    have hc := closed i hi hl
    have ha : a[i]? = some a[i] := List.getElem?_eq_getElem hi
    generalize a[i] = n at hw hb ha hc
    cases n with
    | constant value => simp [unfold, ha, hb, Node.map]
    | input index => simp [unfold, ha, hb, Node.map]
    | add left right =>
      simp only [Node.before, Bool.and_eq_true, decide_eq_true_eq] at hw
      simp only [Node.children, List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
        false_imp_iff, implies_true, and_true] at hc
      simp [unfold, ha, hb, Node.map, ih left (by omega) hc.1, ih right (by omega) hc.2]
    | mul left right =>
      simp only [Node.before, Bool.and_eq_true, decide_eq_true_eq] at hw
      simp only [Node.children, List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
        false_imp_iff, implies_true, and_true] at hc
      simp [unfold, ha, hb, Node.map, ih left (by omega) hc.1, ih right (by omega) hc.2]
    | neg operand =>
      simp only [Node.before, decide_eq_true_eq] at hw
      simp only [Node.children, List.mem_singleton, forall_eq] at hc
      simp [unfold, ha, hb, Node.map, ih operand (by omega) hc]

/-- Live ordered outputs, including repeated positions, unfold to the trees of
their images under a map defined on the live nodes only. -/
theorem outputs_homOn {live : Nat → Bool} {f : Nat → Nat} {a b : Arena R I}
    (wf : a.WellFormed) (closed : a.Closed live) (hom : a.HomOn live f b)
    (fuel : Nat) (outputs : List Nat)
    (bound : ∀ o ∈ outputs, o < a.length ∧ live o = true) :
    outputs.map (a.unfold fuel) = (outputs.map f).map (b.unfold fuel) := by
  rw [List.map_map]
  exact List.map_congr_left fun o ho =>
    unfold_homOn wf closed hom fuel o (bound o ho).1 (bound o ho).2

/-- In a well-formed arena the fuel does not matter once it exceeds the index:
every node has one tree. -/
theorem unfold_stable {a : Arena R I} (wf : a.WellFormed) :
    ∀ fuel i, i < fuel → a.unfold fuel i = a.unfold (i + 1) i := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    intro i hi
    obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    by_cases hin : i < a.length
    · have hw := wf i hin
      have ha : a[i]? = some a[i] := List.getElem?_eq_getElem hin
      generalize a[i] = n at hw ha
      cases n with
      | constant value => simp [unfold, ha]
      | input index => simp [unfold, ha]
      | add left right =>
        simp only [Node.before, Bool.and_eq_true, decide_eq_true_eq] at hw
        simp [unfold, ha, ih fuel (by omega) left (by omega),
          ih fuel (by omega) right (by omega), ih i (by omega) left (by omega),
          ih i (by omega) right (by omega)]
      | mul left right =>
        simp only [Node.before, Bool.and_eq_true, decide_eq_true_eq] at hw
        simp [unfold, ha, ih fuel (by omega) left (by omega),
          ih fuel (by omega) right (by omega), ih i (by omega) left (by omega),
          ih i (by omega) right (by omega)]
      | neg operand =>
        simp only [Node.before, decide_eq_true_eq] at hw
        simp [unfold, ha, ih fuel (by omega) operand (by omega),
          ih i (by omega) operand (by omega)]
    · have ha : a[i]? = none := List.getElem?_eq_none (by omega)
      simp [unfold, ha]

/-- A well-formed arena resolves every node with fuel above its index. -/
theorem unfold_isSome {a : Arena R I} (wf : a.WellFormed) :
    ∀ fuel i, i < fuel → i < a.length → (a.unfold fuel i).isSome = true := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    intro i hi hin
    obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    have hw := wf i hin
    have ha : a[i]? = some a[i] := List.getElem?_eq_getElem hin
    generalize a[i] = n at hw ha
    cases n with
    | constant value => simp [unfold, ha]
    | input index => simp [unfold, ha]
    | add left right =>
      simp only [Node.before, Bool.and_eq_true, decide_eq_true_eq] at hw
      have hl := ih fuel (by omega) left (by omega) (by omega)
      have hr := ih fuel (by omega) right (by omega) (by omega)
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hl
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hr
      simp [unfold, ha, hx, hy]
    | mul left right =>
      simp only [Node.before, Bool.and_eq_true, decide_eq_true_eq] at hw
      have hl := ih fuel (by omega) left (by omega) (by omega)
      have hr := ih fuel (by omega) right (by omega) (by omega)
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hl
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hr
      simp [unfold, ha, hx, hy]
    | neg operand =>
      simp only [Node.before, decide_eq_true_eq] at hw
      have ho := ih fuel (by omega) operand (by omega) (by omega)
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ho
      simp [unfold, ha, hx]

/-- Ordered outputs, including repeated positions, unfold to the same trees
as their images. -/
theorem outputs_hom {f : Nat → Nat} {a b : Arena R I} (wf : a.WellFormed)
    (hom : a.Hom f b) (fuel : Nat) (outputs : List Nat)
    (bound : ∀ o ∈ outputs, o < a.length) :
    outputs.map (a.unfold fuel) = (outputs.map f).map (b.unfold fuel) := by
  rw [List.map_map]
  exact List.map_congr_left fun o ho => unfold_hom wf hom fuel o (bound o ho)

/-- The tree laws transfer: evaluation under any assignment agrees between a
node and its image. Degrees and input lists transfer the same way. -/
theorem eval_unfold_hom [CommRing R] {f : Nat → Nat} {a b : Arena R I}
    (wf : a.WellFormed) (hom : a.Hom f b) (fuel i : Nat) (hi : i < a.length)
    (assignment : I → R) :
    (a.unfold fuel i).map (Expr.eval assignment) =
      (b.unfold fuel (f i)).map (Expr.eval assignment) := by
  rw [unfold_hom wf hom fuel i hi]

theorem degree_unfold_hom {f : Nat → Nat} {a b : Arena R I}
    (wf : a.WellFormed) (hom : a.Hom f b) (fuel i : Nat) (hi : i < a.length)
    (inputDegree : I → Nat) :
    (a.unfold fuel i).map (Expr.degree inputDegree) =
      (b.unfold fuel (f i)).map (Expr.degree inputDegree) := by
  rw [unfold_hom wf hom fuel i hi]

end Arena
end Zkc.Algebra.RingExpression
