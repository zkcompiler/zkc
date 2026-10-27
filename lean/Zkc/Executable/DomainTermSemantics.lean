module

public import Zkc.Executable.DomainNormalizationCheck
public import Zkc.Executable.DomainSchema

@[expose] public section

/-! Nominal interpretation and scope invariants for the hash-consed term DAG.
Only nodes recurse here; instruction execution remains Domain.evaluate. -/
set_option autoImplicit false
namespace Zkc.Executable.CanonicalNormalization
open Zkc.Construction Zkc.Source
abbrev Value (F G : Type) := Domain.Value (Structured.uniformCarriers F G)
abbrev HasSort {F G : Type} (value : Value F G) (sort : ValueSort) : Prop := value.sort = sort
variable {F G : Type}

structure Valuation (F G : Type) where
  outer : Nat → Option (Value F G)
  index : Option (Value F G)
  carried : List (Value F G)
  results : List (List (Value F G))

def Leaf.value (valuation : Valuation F G) : Leaf → Option (Value F G)
  | .outer key => valuation.outer key
  | .index => valuation.index
  | .carried position => valuation.carried[position]?
  | .result anchor position => (valuation.results[anchor]?).bind (·[position]?)

/-- Values of a list of terms at their sorts. -/
@[reducible] def SortedValues (values : List (Value F G)) (sorts : List ValueSort) : Prop :=
  values.length = sorts.length ∧
    ∀ (index : Nat) (value : Value F G) (sort : ValueSort), values[index]? = some value →
      sorts[index]? = some sort → HasSort value sort

section Eval
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The value of a term: a leaf's value, or its node applied to its operands'
values. Operands must be earlier ids. -/
def Terms.eval (terms : Terms) (valuation : Valuation F G) (id : Nat) : Option (Value F G) :=
  match terms[id]? with
  | some (.leaf found, _) => found.value valuation
  | some (.calculate calculation operands, _) =>
      match operands.mapM (fun operand => if _h : operand < id then terms.eval valuation operand else none) with
      | some arguments =>
          match Domain.calculate (Structured.ringModel F G) calculation arguments with
          | .returned [value] => some value
          | _ => none
      | none => none
  | some (.indicesEmpty, _) => some (.indices [])
  | some (.indicesAppend coordinates index, _) =>
      if _h : coordinates < id ∧ index < id then
        match terms.eval valuation coordinates, terms.eval valuation index with
        | some (.indices path), some (.data (.index index')) => some (.indices (path ++ [index']))
        | _, _ => none
      else none
  | none => none
termination_by id
decreasing_by all_goals (first | assumption | omega)


/-- Every operand of a node, ids of earlier nodes. -/
def Node.operands : Node → List Nat
  | .calculate _ operands => operands
  | .indicesAppend coordinates index => [coordinates, index]
  | _ => []

/-- Every node's operands are earlier ids. -/
@[reducible] def Terms.Formed (terms : Terms) : Prop :=
  ∀ (id : Nat) (node : Node) (sort : ValueSort), terms[id]? = some (node, sort) →
    ∀ operand ∈ node.operands, operand < id

/-- The table refers to results of anchors before `anchor` only. -/
@[reducible] def Terms.Before (terms : Terms) (anchor : Nat) : Prop :=
  ∀ (id leafAnchor position : Nat) (sort : ValueSort),
    terms[id]? = some (Node.leaf (.result leafAnchor position), sort) → leafAnchor < anchor

/-- Every term that has a value has its sort. -/
@[reducible] def Terms.Sorted (terms : Terms) (valuation : Valuation F G) : Prop :=
  ∀ (id : Nat) (node : Node) (sort : ValueSort) (value : Value F G), terms[id]? = some (node, sort) →
    terms.eval valuation id = some value → HasSort value sort

/-- Positions of an environment denote their ids' terms. -/
@[reducible] def Denotes (terms : Terms) (valuation : Valuation F G) (ids : List Nat) (env : List (Value F G)) : Prop :=
  ids.length = env.length ∧
    ∀ (position id : Nat), ids[position]? = some id → terms.eval valuation id = env[position]?

/-- Every id is an id of the table. -/
@[reducible] def Bounded (terms : Terms) (ids : List Nat) : Prop := ∀ id ∈ ids, id < terms.length

theorem Terms.eval_unfold (terms : Terms) (valuation : Valuation F G) (id : Nat) :
    terms.eval valuation id =
      match terms[id]? with
      | some (.leaf found, _) => found.value valuation
      | some (.calculate calculation operands, _) =>
          match operands.mapM (fun operand => if _h : operand < id then terms.eval valuation operand else none) with
          | some arguments =>
              match Domain.calculate (Structured.ringModel F G) calculation arguments with
              | .returned [value] => some value
              | _ => none
          | none => none
      | some (.indicesEmpty, _) => some (.indices [])
      | some (.indicesAppend coordinates index, _) =>
          if _h : coordinates < id ∧ index < id then
            match terms.eval valuation coordinates, terms.eval valuation index with
            | some (.indices path), some (.data (.index index')) =>
                some (.indices (path ++ [index']))
            | _, _ => none
          else none
      | none => none := by
  rw [Terms.eval]

/-- Evaluation agrees on two tables and two valuations that agree up to `bound`
on entries and on the values of the leaves there. -/
theorem Terms.eval_congr (terms terms' : Terms) (valuation valuation' : Valuation F G) (bound : Nat)
    (entries : ∀ id, id < bound → terms'[id]? = terms[id]?)
    (leaves : ∀ id leaf sort, id < bound → terms[id]? = some (.leaf leaf, sort) →
      leaf.value valuation' = leaf.value valuation) :
    ∀ id, id < bound → terms'.eval valuation' id = terms.eval valuation id := by
  intro id
  induction id using Nat.strong_induction_on with
  | _ id ih =>
    intro within
    rw [Terms.eval_unfold terms', Terms.eval_unfold terms, entries id within]
    cases entry : terms[id]? with
    | none => rfl
    | some found =>
        obtain ⟨node, sort⟩ := found
        cases node with
        | leaf leaf => exact leaves id leaf sort within entry
        | calculate calculation operands =>
            have same : (fun operand => if _h : operand < id then terms'.eval valuation' operand else none) =
                (fun operand => if _h : operand < id then terms.eval valuation operand else none) := by
              funext operand
              by_cases below : operand < id
              · simp only [below, dite_true]
                exact ih operand below (by omega)
              · simp only [below, dite_false]
            simp only [same]
        | indicesEmpty => rfl
        | indicesAppend coordinates index =>
            simp only
            by_cases below : coordinates < id ∧ index < id
            · simp only [below, and_self, dite_true]
              rw [ih coordinates below.1 (by omega), ih index below.2 (by omega)]
            · simp only [below, dite_false]

/-- Extending a table keeps the values of its ids. -/
theorem Terms.eval_append (terms more : Terms) (valuation : Valuation F G) (id : Nat)
    (within : id < terms.length) : (terms ++ more).eval valuation id = terms.eval valuation id :=
  Terms.eval_congr terms (terms ++ more) valuation valuation terms.length
    (fun _ within => List.getElem?_append_left within) (fun _ _ _ _ _ => rfl) id within

/-- Recording the results of a new anchor keeps the values of terms that refer
to earlier anchors only. -/
theorem Terms.eval_results (terms : Terms) (valuation : Valuation F G) (results : List (Value F G))
    (before : terms.Before valuation.results.length) (id : Nat) :
    terms.eval { valuation with results := valuation.results ++ [results] } id = terms.eval valuation id := by
  by_cases within : id < terms.length
  · refine Terms.eval_congr terms terms valuation _ terms.length (fun _ _ => rfl) ?_ id within
    intro id' leaf sort _ found
    cases leaf with
    | result anchor position =>
        have earlier := before id' anchor position sort found
        simp [Leaf.value, List.getElem?_append_left earlier]
    | _ => rfl
  · rw [Terms.eval_unfold, Terms.eval_unfold, List.getElem?_eq_none (by omega)]

/-! ## Interning -/

theorem findIdx?_some {α : Type} {xs : List α} {p : α → Bool} {i : Nat} (found : xs.findIdx? p = some i) :
    ∃ within : i < xs.length, p xs[i] = true := by
  obtain ⟨within, holds, -⟩ := List.findIdx?_eq_some_iff_getElem.mp found
  exact ⟨within, holds⟩

/-- Interning finds an equal entry or appends the entry. -/
theorem Terms.intern_cases (terms : Terms) (entry : Node × ValueSort) :
    (∃ id, id < terms.length ∧ terms[id]? = some entry ∧ terms.intern entry = (terms, id)) ∨
      terms.intern entry = (terms ++ [entry], terms.length) := by
  unfold Terms.intern
  split
  · rename_i id found
    obtain ⟨within, holds⟩ := findIdx?_some found
    simp only [Bool.and_eq_true, beq_iff_eq] at holds
    obtain ⟨same, sorts⟩ := holds
    have nodes := (Node.same_iff _ _).mp same
    refine .inl ⟨id, within, ?_, rfl⟩
    rw [List.getElem?_eq_getElem within]
    obtain ⟨node, sort⟩ := entry
    simp only at nodes sorts
    rw [← nodes, ← sorts]
  · exact .inr rfl

/-- An interned entry is at its id, and the table only grows. -/
theorem Terms.intern_spec (terms : Terms) (entry : Node × ValueSort) :
    (terms.intern entry).2 < (terms.intern entry).1.length ∧
      (terms.intern entry).1[(terms.intern entry).2]? = some entry ∧
      ∃ more, (terms.intern entry).1 = terms ++ more := by
  rcases Terms.intern_cases terms entry with ⟨id, within, found, interned⟩ | interned
  · rw [interned]
    exact ⟨within, found, [], by simp⟩
  · rw [interned]
    exact ⟨by simp, by simp, [entry], rfl⟩

/-- Leaves for consecutive positions: each at its id, with its sort. -/
theorem Terms.leaves_spec (leaf : Nat → Leaf) :
    ∀ (sorts : List ValueSort) (terms : Terms) (first : Nat),
      (∃ more, (terms.leaves leaf sorts first).1 = terms ++ more) ∧
        (terms.leaves leaf sorts first).2.length = sorts.length ∧
        Bounded (terms.leaves leaf sorts first).1 (terms.leaves leaf sorts first).2 ∧
        ∀ (position id : Nat) (sort : ValueSort), (terms.leaves leaf sorts first).2[position]? = some id →
          sorts[position]? = some sort →
            (terms.leaves leaf sorts first).1[id]? = some (.leaf (leaf (first + position)), sort)
  | [], terms, first => ⟨⟨[], by simp [Terms.leaves]⟩, rfl, by simp [Terms.leaves, Bounded], by simp [Terms.leaves]⟩
  | sort :: sorts, terms, first => by
      obtain ⟨within, found, more, grown⟩ := Terms.intern_spec terms (.leaf (leaf first), sort)
      obtain ⟨⟨more', grown'⟩, lengths, bounded, entries⟩ :=
        Terms.leaves_spec leaf sorts (terms.intern (.leaf (leaf first), sort)).1 (first + 1)
      simp only [Terms.leaves]
      refine ⟨⟨more ++ more', by rw [grown', grown, List.append_assoc]⟩, by simp [lengths], ?_, ?_⟩
      · intro id member
        rcases List.mem_cons.mp member with rfl | member
        · rw [grown']
          simp only [List.length_append]
          omega
        · exact bounded id member
      · intro position id sort' idFound sortFound
        cases position with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at idFound sortFound
            subst idFound sortFound
            rw [grown', List.getElem?_append_left within, found]
            simp
        | succ position =>
            simp only [List.getElem?_cons_succ] at idFound sortFound
            rw [entries position id sort' idFound sortFound]
            simp only [show first + 1 + position = first + (position + 1) by omega]


/-! ## Totality of movable calculations -/

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem Bounded.append {terms more : Terms} {ids : List Nat} (bounded : Bounded terms ids) :
    Bounded (terms ++ more) ids := fun id member =>
  Nat.lt_of_lt_of_le (bounded id member) (by simp)

theorem Denotes.append {terms more : Terms} {valuation : Valuation F G} {ids : List Nat}
    {env : List (Value F G)} (denotes : Denotes terms valuation ids env) (bounded : Bounded terms ids) :
    Denotes (terms ++ more) valuation ids env := by
  refine ⟨denotes.1, fun position id found => ?_⟩
  exact (Terms.eval_append terms more valuation id (bounded id (List.mem_of_getElem? found))).trans
    (denotes.2 position id found)

/-- The operands an instruction reads have the values of the ids their
positions hold. -/
theorem Denotes.read_some {terms : Terms} {valuation : Valuation F G} {ids : List Nat}
    {env : List (Value F G)} (denotes : Denotes terms valuation ids env) :
    ∀ {operands : List Nat} {operandIds' : List Nat}, operandIds ids operands = some operandIds' →
      ∃ arguments, Domain.read env operands = some arguments ∧
        operandIds'.mapM (terms.eval valuation) = some arguments
  | [], operandIds', found => by
      simp only [operandIds, List.mapM_nil, Option.pure_def, Option.some.injEq] at found
      subst found
      exact ⟨[], rfl, rfl⟩
  | operand :: operands, operandIds', found => by
      simp only [operandIds, List.mapM_cons] at found
      cases first : ids[operand]? with
      | none => simp [first] at found
      | some id =>
          cases rest : operands.mapM (ids[·]?) with
          | none => simp [first, rest] at found
          | some ids' =>
              simp only [first, rest, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq] at found
              subst found
              obtain ⟨arguments, readEq, evalEq⟩ := denotes.read_some (operands := operands) (operandIds' := ids') rest
              have within : operand < env.length := by
                rw [← denotes.1]
                exact (List.getElem?_eq_some_iff.mp first).1
              have valueEq := denotes.2 operand id first
              rw [List.getElem?_eq_getElem within] at valueEq
              refine ⟨env[operand] :: arguments, ?_, ?_⟩
              · simp only [Domain.read, List.mapM_cons, List.getElem?_eq_getElem within] at readEq ⊢
                simp [readEq]
              · simp [List.mapM_cons, valueEq, evalEq]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem operandIds_bounded {terms : Terms} {ids : List Nat} (bounded : Bounded terms ids) :
    ∀ {operands : List Nat} {operandIds' : List Nat}, operandIds ids operands = some operandIds' →
      ∀ id ∈ operandIds', id < terms.length
  | [], operandIds', found => by
      simp only [operandIds, List.mapM_nil, Option.pure_def, Option.some.injEq] at found
      subst found
      simp
  | operand :: operands, operandIds', found => by
      simp only [operandIds, List.mapM_cons] at found
      cases first : ids[operand]? with
      | none => simp [first] at found
      | some id =>
          cases rest : operands.mapM (ids[·]?) with
          | none => simp [first, rest] at found
          | some ids' =>
              simp only [first, rest, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq] at found
              subst found
              intro id' member
              rcases List.mem_cons.mp member with rfl | member
              · exact bounded id' (List.mem_of_getElem? first)
              · exact operandIds_bounded bounded (operands := operands) rest id' member

/-- Values of ids at their sorts are values at those sorts. -/
theorem sorted_values {terms : Terms} {valuation : Valuation F G} (sorted : terms.Sorted valuation) :
    ∀ {ids : List Nat} {values : List (Value F G)} {sorts : List ValueSort},
      ids.mapM (terms.eval valuation) = some values → ids.map terms.sort? = sorts.map some →
        SortedValues values sorts
  | [], values, sorts, found, sortsEq => by
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at found
      subst found
      cases sorts with
      | nil => exact ⟨rfl, by simp⟩
      | cons => simp at sortsEq
  | id :: ids, values, sorts, found, sortsEq => by
      simp only [List.mapM_cons] at found
      cases first : terms.eval valuation id with
      | none => simp [first] at found
      | some value =>
          cases rest : ids.mapM (terms.eval valuation) with
          | none => simp [first, rest] at found
          | some values' =>
              simp only [first, rest, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq] at found
              subst found
              cases sorts with
              | nil => simp at sortsEq
              | cons sort sorts' =>
                  simp only [List.map_cons, List.cons.injEq] at sortsEq
                  obtain ⟨sortEq, sortsEq'⟩ := sortsEq
                  obtain ⟨lengths, tail⟩ := sorted_values sorted rest sortsEq'
                  refine ⟨by simp [lengths], ?_⟩
                  intro index v s found' sortFound
                  cases index with
                  | zero =>
                      simp only [List.getElem?_cons_zero, Option.some.injEq] at found' sortFound
                      subst found' sortFound
                      unfold Terms.sort? at sortEq
                      cases entry : terms[id]? with
                      | none => simp [entry] at sortEq
                      | some entry' =>
                          obtain ⟨node, s'⟩ := entry'
                          simp only [entry, Option.map_some, Option.some.injEq] at sortEq
                          subst sortEq
                          exact sorted id node s' value entry first
                  | succ index =>
                      simp only [List.getElem?_cons_succ] at found' sortFound
                      exact tail index v s found' sortFound

/-- The value of a node from its operands' values. -/
def Node.value (terms : Terms) (valuation : Valuation F G) : Node → Option (Value F G)
  | .leaf found => found.value valuation
  | .calculate calculation operands =>
      match operands.mapM (terms.eval valuation) with
      | some arguments =>
          match Domain.calculate (Structured.ringModel F G) calculation arguments with
          | .returned [value] => some value
          | _ => none
      | none => none
  | .indicesEmpty => some (.indices [])
  | .indicesAppend coordinates index =>
      match terms.eval valuation coordinates, terms.eval valuation index with
      | some (.indices path), some (.data (.index index')) => some (.indices (path ++ [index']))
      | _, _ => none

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem mapM_congr' {α β : Type} {f g : α → Option β} :
    ∀ (xs : List α), (∀ x ∈ xs, f x = g x) → xs.mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, same => by
      simp only [List.mapM_cons, same x (List.mem_cons_self ..),
        mapM_congr' xs (fun y member => same y (List.mem_cons_of_mem _ member))]

theorem mapM_below (terms : Terms) (valuation : Valuation F G) (id : Nat) :
    ∀ (operands : List Nat), (∀ operand ∈ operands, operand < id) →
      operands.mapM (fun operand => if _h : operand < id then terms.eval valuation operand else none) =
        operands.mapM (terms.eval valuation)
  | [], _ => rfl
  | operand :: operands, below => by
      have first := below operand (List.mem_cons_self ..)
      simp only [List.mapM_cons, first, dite_true,
        mapM_below terms valuation id operands (fun o member => below o (List.mem_cons_of_mem _ member))]

/-- A node whose operands are earlier ids evaluates as its node does. -/
theorem eval_node {terms : Terms} {valuation : Valuation F G} {id : Nat} {node : Node} {sort : ValueSort}
    (entry : terms[id]? = some (node, sort)) (below : ∀ operand ∈ node.operands, operand < id) :
    terms.eval valuation id = node.value terms valuation := by
  rw [Terms.eval_unfold, entry]
  cases node with
  | leaf leaf => rfl
  | calculate calculation operands =>
      simp only [Node.value]
      rw [mapM_below terms valuation id operands below]
  | indicesEmpty => rfl
  | indicesAppend coordinates index =>
      have both : coordinates < id ∧ index < id :=
        ⟨below coordinates (by simp [Node.operands]), below index (by simp [Node.operands])⟩
      simp only [Node.value, both, and_self, dite_true]

theorem Node.value_append {terms more : Terms} {valuation : Valuation F G} {node : Node}
    (below : ∀ operand ∈ node.operands, operand < terms.length) :
    node.value (terms ++ more) valuation = node.value terms valuation := by
  cases node with
  | leaf => rfl
  | calculate calculation operands =>
      have same : operands.mapM ((terms ++ more).eval valuation) = operands.mapM (terms.eval valuation) :=
        mapM_congr' operands fun operand member => Terms.eval_append terms more valuation operand (below operand member)
      simp only [Node.value, same]
  | indicesEmpty => rfl
  | indicesAppend coordinates index =>
      simp only [Node.value]
      rw [Terms.eval_append terms more valuation coordinates (below coordinates (by simp [Node.operands])),
        Terms.eval_append terms more valuation index (below index (by simp [Node.operands]))]

/-- Interning a node over earlier ids: its id evaluates as the node does, and
the table stays formed. -/
theorem intern_eval {terms : Terms} {node : Node} {sort : ValueSort} {valuation : Valuation F G}
    (formed : terms.Formed) (below : ∀ operand ∈ node.operands, operand < terms.length) :
    (terms.intern (node, sort)).1.eval valuation (terms.intern (node, sort)).2 = node.value terms valuation ∧
      (terms.intern (node, sort)).1.Formed ∧ (∃ more, (terms.intern (node, sort)).1 = terms ++ more) ∧
      (terms.intern (node, sort)).2 < (terms.intern (node, sort)).1.length ∧
      (terms.intern (node, sort)).1[(terms.intern (node, sort)).2]? = some (node, sort) := by
  rcases Terms.intern_cases terms (node, sort) with ⟨id, within, found, interned⟩ | interned
  · rw [interned]
    exact ⟨eval_node found (formed id node sort found), formed, ⟨[], by simp⟩, within, found⟩
  · rw [interned]
    dsimp only
    have entry : (terms ++ [(node, sort)])[terms.length]? = some (node, sort) := by simp
    refine ⟨?_, ?_, ⟨[(node, sort)], rfl⟩, by simp, entry⟩
    · rw [eval_node entry below, Node.value_append below]
    · intro id' node' sort' found' operand member
      by_cases old : id' < terms.length
      · rw [List.getElem?_append_left old] at found'
        exact formed id' node' sort' found' operand member
      · rw [List.getElem?_append_right (by omega)] at found'
        have small : id' - terms.length < 1 := (List.getElem?_eq_some_iff.mp found').1
        have same : id' = terms.length := by omega
        subst same
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found'
        obtain ⟨rfl, rfl⟩ := found'
        exact below operand member

theorem intern_sorted {terms : Terms} {node : Node} {sort : ValueSort} {valuation : Valuation F G}
    (sorted : terms.Sorted valuation)
    (below : ∀ operand ∈ node.operands, operand < terms.length)
    (hasSort : ∀ value, node.value terms valuation = some value → HasSort value sort) :
    (terms.intern (node, sort)).1.Sorted valuation := by
  rcases Terms.intern_cases terms (node, sort) with ⟨id, within, found, interned⟩ | interned
  · rw [interned]
    exact sorted
  · rw [interned]
    dsimp only
    intro id' node' sort' value found' evaluated
    by_cases old : id' < terms.length
    · rw [List.getElem?_append_left old] at found'
      rw [Terms.eval_append terms _ valuation id' old] at evaluated
      exact sorted id' node' sort' value found' evaluated
    · rw [List.getElem?_append_right (by omega)] at found'
      have small : id' - terms.length < 1 := (List.getElem?_eq_some_iff.mp found').1
      have same : id' = terms.length := by omega
      subst same
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found'
      obtain ⟨rfl, rfl⟩ := found'
      have entry : (terms ++ [(node, sort)])[terms.length]? = some (node, sort) := by simp
      rw [eval_node entry below, Node.value_append below] at evaluated
      exact hasSort value evaluated

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem intern_before {terms : Terms} {node : Node} {sort : ValueSort} {anchor : Nat}
    (before : terms.Before anchor)
    (leafBefore : ∀ leafAnchor position, node = .leaf (.result leafAnchor position) → leafAnchor < anchor) :
    (terms.intern (node, sort)).1.Before anchor := by
  rcases Terms.intern_cases terms (node, sort) with ⟨id, within, found, interned⟩ | interned
  · rw [interned]
    exact before
  · rw [interned]
    dsimp only
    intro id' leafAnchor position sort' found'
    by_cases old : id' < terms.length
    · rw [List.getElem?_append_left old] at found'
      exact before id' leafAnchor position sort' found'
    · rw [List.getElem?_append_right (by omega)] at found'
      have small : id' - terms.length < 1 := (List.getElem?_eq_some_iff.mp found').1
      have same : id' = terms.length := by omega
      subst same
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found'
      exact leafBefore leafAnchor position found'.1

/-! ## Movable instructions -/

theorem Denotes.push {terms : Terms} {valuation : Valuation F G} {ids : List Nat} {env : List (Value F G)}
    (denotes : Denotes terms valuation ids env) {id : Nat} {value : Value F G}
    (evaluated : terms.eval valuation id = some value) :
    Denotes terms valuation (ids ++ [id]) (env ++ [value]) := by
  refine ⟨by simp [denotes.1], fun position id' found => ?_⟩
  by_cases old : position < ids.length
  · rw [List.getElem?_append_left old] at found
    rw [List.getElem?_append_left (by rw [← denotes.1]; exact old)]
    exact denotes.2 position id' found
  · rw [List.getElem?_append_right (by omega)] at found
    have small : position - ids.length < 1 := (List.getElem?_eq_some_iff.mp found).1
    have same : position = ids.length := by omega
    subst same
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at found
    subst found
    rw [denotes.1, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    simpa using evaluated

/-! ## New entries -/

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Every entry `leaves` adds is a leaf for one of its positions, at that
position's sort. -/
theorem Terms.leaves_new (leaf : Nat → Leaf) :
    ∀ (sorts : List ValueSort) (terms : Terms) (first id : Nat) (entry : Node × ValueSort),
      terms.length ≤ id → (terms.leaves leaf sorts first).1[id]? = some entry →
        ∃ position sort, sorts[position]? = some sort ∧ entry = (.leaf (leaf (first + position)), sort)
  | [], terms, first, id, entry, beyond, found => by
      simp only [Terms.leaves] at found
      exact absurd (List.getElem?_eq_some_iff.mp found).1 (by omega)
  | sort :: sorts, terms, first, id, entry, beyond, found => by
      simp only [Terms.leaves] at found
      have shift : ∀ position, first + 1 + position = first + (position + 1) := fun _ => by omega
      rcases Terms.intern_cases terms (.leaf (leaf first), sort) with ⟨id', -, -, interned⟩ | interned
      · rw [interned] at found
        obtain ⟨position, sort', sortFound, rfl⟩ := Terms.leaves_new leaf sorts terms (first + 1) id entry beyond found
        exact ⟨position + 1, sort', by simpa using sortFound, by rw [shift]⟩
      · rw [interned] at found
        by_cases fresh : id = terms.length
        · subst fresh
          obtain ⟨⟨more, grown⟩, -, -, -⟩ :=
            Terms.leaves_spec leaf sorts (terms ++ [(.leaf (leaf first), sort)]) (first + 1)
          rw [grown, List.getElem?_append_left (by simp)] at found
          simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
            Option.some.injEq] at found
          exact ⟨0, sort, rfl, by rw [← found]; rfl⟩
        · obtain ⟨position, sort', sortFound, rfl⟩ :=
            Terms.leaves_new leaf sorts _ (first + 1) id entry (by simp; omega) found
          exact ⟨position + 1, sort', by simpa using sortFound, by rw [shift]⟩

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- A property of every entry survives interning an entry that has it. -/
theorem intern_all {terms : Terms} {entry : Node × ValueSort} (property : Node × ValueSort → Prop)
    (all : ∀ found ∈ terms, property found) (holds : property entry) :
    ∀ found ∈ (terms.intern entry).1, property found := by
  rcases Terms.intern_cases terms entry with ⟨id, -, -, interned⟩ | interned
  · rw [interned]; exact all
  · rw [interned]
    intro found member
    rcases List.mem_append.mp member with member | member
    · exact all found member
    · simp only [List.mem_singleton] at member
      subst member
      exact holds

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem leaves_all (leaf : Nat → Leaf) (property : Node × ValueSort → Prop) :
    ∀ (sorts : List ValueSort) (terms : Terms) (first : Nat),
      (∀ found ∈ terms, property found) →
      (∀ (position : Nat) (sort : ValueSort), sorts[position]? = some sort →
        property (.leaf (leaf (first + position)), sort)) →
      ∀ found ∈ (terms.leaves leaf sorts first).1, property found
  | [], terms, first, all, _ => by simpa [Terms.leaves] using all
  | sort :: sorts, terms, first, all, holds => by
      simp only [Terms.leaves]
      apply leaves_all leaf property sorts _ (first + 1)
      · exact intern_all property all (by simpa using holds 0 sort rfl)
      · intro position sort' found
        have := holds (position + 1) sort' (by simpa using found)
        rwa [show first + 1 + position = first + (position + 1) by omega]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- What the outer leaves of a loop body establish: the table grows by outer
leaves, one id per enclosing id, each at the enclosing id's sort. -/
theorem outers_spec (enclosing : Terms) :
    ∀ (ids : List Nat) (terms terms' : Terms) (ids' : List Nat), terms.outers enclosing ids = some (terms', ids') →
      (∃ more, terms' = terms ++ more) ∧ ids'.length = ids.length ∧ Bounded terms' ids' ∧
        (∀ (position id id' : Nat), ids[position]? = some id → ids'[position]? = some id' →
          ∃ sort, enclosing.sort? id = some sort ∧ terms'[id']? = some (.leaf (.outer id), sort)) ∧
        (∀ (property : Node × ValueSort → Prop), (∀ found ∈ terms, property found) →
          (∀ (id : Nat) (sort : ValueSort), enclosing.sort? id = some sort → property (.leaf (.outer id), sort)) →
          ∀ found ∈ terms', property found)
  | [], terms, terms', ids', found => by
      simp only [Terms.outers, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl⟩ := found
      exact ⟨⟨[], by simp⟩, rfl, by simp [Bounded], by simp, fun _ all _ => all⟩
  | id :: ids, terms, terms', ids', found => by
      simp only [Terms.outers] at found
      cases sortFound : enclosing.sort? id with
      | none => simp [sortFound] at found
      | some sort =>
          simp only [sortFound] at found
          obtain ⟨within, entry, more, grown⟩ := Terms.intern_spec terms (.leaf (.outer id), sort)
          cases rest : (terms.intern (.leaf (.outer id), sort)).1.outers enclosing ids with
          | none => simp [rest] at found
          | some result =>
              obtain ⟨terms₁, ids₁⟩ := result
              simp only [rest, Option.some.injEq, Prod.mk.injEq] at found
              obtain ⟨rfl, rfl⟩ := found
              obtain ⟨⟨more', grown'⟩, lengths, bounded, entries, all⟩ :=
                outers_spec enclosing ids _ terms₁ ids₁ rest
              refine ⟨⟨more ++ more', by rw [grown', grown, List.append_assoc]⟩, by simp [lengths], ?_, ?_, ?_⟩
              · intro id' member
                rcases List.mem_cons.mp member with rfl | member
                · rw [grown']; simp only [List.length_append]; omega
                · exact bounded id' member
              · intro position id' id'' idFound idFound'
                cases position with
                | zero =>
                    simp only [List.getElem?_cons_zero, Option.some.injEq] at idFound idFound'
                    subst idFound idFound'
                    exact ⟨sort, sortFound, by rw [grown', List.getElem?_append_left within, entry]⟩
                | succ position =>
                    simp only [List.getElem?_cons_succ] at idFound idFound'
                    exact entries position id' id'' idFound idFound'
              · intro property allBefore leafHolds
                exact all property (intern_all property allBefore (leafHolds id sort sortFound)) leafHolds

/-! ## The invariant between both programs -/

/-- The simulation invariant between both programs' environments and one
table at anchor ordinal `anchor`. -/
structure Holds (terms : Terms) (valuation : Valuation F G) (anchor : Nat) (exportedIds : List Nat)
    (exportedEnv : List (Value F G)) (readingIds : List Nat) (readingEnv : List (Value F G)) : Prop where
  exported : Denotes terms valuation exportedIds exportedEnv
  reading : Denotes terms valuation readingIds readingEnv
  exportedBounded : Bounded terms exportedIds
  readingBounded : Bounded terms readingIds
  formed : terms.Formed
  sorted : terms.Sorted valuation
  before : terms.Before anchor
  results : valuation.results.length = anchor

theorem Denotes.append_lists {terms : Terms} {valuation : Valuation F G} {ids ids' : List Nat}
    {env env' : List (Value F G)} (first : Denotes terms valuation ids env)
    (second : Denotes terms valuation ids' env') : Denotes terms valuation (ids ++ ids') (env ++ env') := by
  refine ⟨by simp [first.1, second.1], fun position id found => ?_⟩
  by_cases old : position < ids.length
  · rw [List.getElem?_append_left old] at found
    rw [List.getElem?_append_left (by rw [← first.1]; exact old)]
    exact first.2 position id found
  · rw [List.getElem?_append_right (by omega)] at found
    rw [List.getElem?_append_right (by rw [← first.1]; omega), ← first.1]
    exact second.2 _ id found

theorem Denotes.transfer {terms terms' : Terms} {valuation valuation' : Valuation F G} {ids : List Nat}
    {env : List (Value F G)} (denotes : Denotes terms valuation ids env) (bounded : Bounded terms ids)
    (same : ∀ id, id < terms.length → terms'.eval valuation' id = terms.eval valuation id) :
    Denotes terms' valuation' ids env :=
  ⟨denotes.1, fun position id found => by
    rw [same id (bounded id (List.mem_of_getElem? found))]
    exact denotes.2 position id found⟩

/-- Recording an anchor's results as leaves keeps the invariant, at the next
anchor ordinal. -/
theorem Holds.record {terms : Terms} {valuation : Valuation F G} {anchor : Nat}
    {exportedIds readingIds : List Nat} {exportedEnv readingEnv : List (Value F G)}
    (holds : Holds terms valuation anchor exportedIds exportedEnv readingIds readingEnv)
    {sorts : List ValueSort} {appended : List (Value F G)} (sortedAppended : SortedValues appended sorts) :
    Holds (terms.leaves (.result anchor) sorts 0).1 { valuation with results := valuation.results ++ [appended] }
      (anchor + 1) (exportedIds ++ (terms.leaves (.result anchor) sorts 0).2) (exportedEnv ++ appended)
      (readingIds ++ (terms.leaves (.result anchor) sorts 0).2) (readingEnv ++ appended) := by
  obtain ⟨⟨more, grown⟩, lengths, bounded, entries⟩ := Terms.leaves_spec (.result anchor) sorts terms 0
  have fresh := Terms.leaves_new (.result anchor) sorts terms 0
  generalize terms.leaves (.result anchor) sorts 0 = leaved at grown lengths bounded entries fresh ⊢
  obtain ⟨terms', resultIds⟩ := leaved
  simp only at grown lengths bounded entries fresh ⊢
  subst grown
  have old : ∀ id, id < terms.length →
      (terms ++ more).eval { valuation with results := valuation.results ++ [appended] } id =
        terms.eval valuation id := by
    intro id within
    rw [Terms.eval_append terms more _ id within]
    exact Terms.eval_results terms valuation appended (by rw [holds.results]; exact holds.before) id
  have anchorEq : (valuation.results ++ [appended])[anchor]? = some appended := by
    rw [List.getElem?_append_right (by rw [holds.results]), holds.results, Nat.sub_self]; rfl
  have newValues : ∀ position sort, sorts[position]? = some sort →
      Leaf.value { valuation with results := valuation.results ++ [appended] } (.result anchor (0 + position)) =
        appended[position]? := by
    intro position sort _
    simp only [Leaf.value, Nat.zero_add, anchorEq, Option.bind_some]
  have new : Denotes (terms ++ more) { valuation with results := valuation.results ++ [appended] } resultIds
      appended := by
    refine ⟨by rw [lengths, sortedAppended.1], fun position id found => ?_⟩
    have within : position < sorts.length := by
      rw [← lengths]; exact (List.getElem?_eq_some_iff.mp found).1
    have sortFound : sorts[position]? = some sorts[position] := List.getElem?_eq_getElem within
    have entry := entries position id sorts[position] found sortFound
    rw [eval_node entry (by simp [Node.operands])]
    exact newValues position _ sortFound
  have bounded' : ∀ ids, Bounded terms ids → Bounded (terms ++ more) ids := fun _ b => b.append
  refine ⟨(holds.exported.transfer holds.exportedBounded old).append_lists new,
    (holds.reading.transfer holds.readingBounded old).append_lists new, ?_, ?_, ?_, ?_, ?_, by simp [holds.results]⟩
  · intro id member
    rcases List.mem_append.mp member with member | member
    · exact bounded' _ holds.exportedBounded id member
    · exact bounded id member
  · intro id member
    rcases List.mem_append.mp member with member | member
    · exact bounded' _ holds.readingBounded id member
    · exact bounded id member
  · intro id node sort found operand member
    by_cases inside : id < terms.length
    · rw [List.getElem?_append_left inside] at found
      exact holds.formed id node sort found operand member
    · obtain ⟨position, sort', -, equal⟩ := fresh id (node, sort) (by omega) found
      simp only [Prod.mk.injEq] at equal
      rw [equal.1] at member
      simp [Node.operands] at member
  · intro id node sort value found evaluated
    by_cases inside : id < terms.length
    · rw [List.getElem?_append_left inside] at found
      rw [old id inside] at evaluated
      exact holds.sorted id node sort value found evaluated
    · obtain ⟨position, sort', sortFound, equal⟩ := fresh id (node, sort) (by omega) found
      simp only [Prod.mk.injEq] at equal
      obtain ⟨rfl, rfl⟩ := equal
      rw [eval_node found (by simp [Node.operands]), Node.value, newValues position sort sortFound] at evaluated
      exact sortedAppended.2 position value sort evaluated sortFound
  · intro id leafAnchor position sort found
    by_cases inside : id < terms.length
    · rw [List.getElem?_append_left inside] at found
      have := holds.before id leafAnchor position sort found
      omega
    · obtain ⟨position', sort', -, equal⟩ := fresh id _ (by omega) found
      simp only [Prod.mk.injEq, Node.leaf.injEq, Leaf.result.injEq] at equal
      omega

/-! ## A loop body's first terms -/

/-- The entries a loop body's table starts with: leaves for the enclosing
values at their sorts, the index and the carried values at their sorts. -/
def BodyEntry (enclosing : Terms) (sorts : List ValueSort) (entry : Node × ValueSort) : Prop :=
  (∃ id sort, enclosing.sort? id = some sort ∧ entry = (.leaf (.outer id), sort)) ∨
    entry = (.leaf .index, .data .index) ∨
    (∃ position sort, sorts[position]? = some sort ∧ entry = (.leaf (.carried position), sort))

/-- A loop body's first terms denote the enclosing values, the index and the
carried values; they are leaves and have their sorts. -/
theorem Holds.body {terms : Terms} {valuation : Valuation F G} {anchor : Nat}
    {exportedIds readingIds : List Nat} {exportedEnv readingEnv : List (Value F G)}
    (holds : Holds terms valuation anchor exportedIds exportedEnv readingIds readingEnv)
    {body₁ : Terms} {outerIds : List Nat} (outersE : Terms.outers [] terms exportedIds = some (body₁, outerIds))
    {body₂ : Terms} {outerIds' : List Nat} (outersR : body₁.outers terms readingIds = some (body₂, outerIds'))
    {body₃ : Terms} {indexId : Nat} (indexed : body₂.intern (.leaf .index, .data .index) = (body₃, indexId))
    {sorts : List ValueSort} {body₄ : Terms} {carriedIds : List Nat}
    (carriedLeaves : body₃.leaves .carried sorts 0 = (body₄, carriedIds))
    {index : Nat} {carried : List (Value F G)} (carriedSorted : SortedValues carried sorts) :
    Holds body₄ ⟨fun id => terms.eval valuation id, some (.data (.index index)), carried, []⟩ 0
      (outerIds ++ indexId :: carriedIds) (exportedEnv ++ .data (.index index) :: carried)
      (outerIds' ++ indexId :: carriedIds) (readingEnv ++ .data (.index index) :: carried) := by
  set valuation' : Valuation F G := ⟨fun id => terms.eval valuation id, some (.data (.index index)), carried, []⟩
  obtain ⟨⟨more₁, grown₁⟩, lengths₁, bounded₁, entries₁, all₁⟩ := outers_spec terms exportedIds [] body₁ outerIds outersE
  obtain ⟨⟨more₂, grown₂⟩, lengths₂, bounded₂, entries₂, all₂⟩ :=
    outers_spec terms readingIds body₁ body₂ outerIds' outersR
  obtain ⟨withinIndex, entryIndex, more₃, grown₃⟩ := Terms.intern_spec body₂ (.leaf .index, .data .index)
  rw [indexed] at withinIndex entryIndex grown₃
  simp only at withinIndex entryIndex grown₃
  obtain ⟨⟨more₄, grown₄⟩, lengths₄, bounded₄, entries₄⟩ := Terms.leaves_spec .carried sorts body₃ 0
  rw [carriedLeaves] at grown₄ lengths₄ bounded₄ entries₄
  simp only at grown₄ lengths₄ bounded₄ entries₄
  -- Every entry is a leaf of the body's first kinds.
  have good : ∀ found ∈ body₄, BodyEntry terms sorts found := by
    have first : ∀ found ∈ body₁, BodyEntry terms sorts found :=
      all₁ _ (by simp) (fun id sort found => .inl ⟨id, sort, found, rfl⟩)
    have second : ∀ found ∈ body₂, BodyEntry terms sorts found :=
      all₂ _ first (fun id sort found => .inl ⟨id, sort, found, rfl⟩)
    have third : ∀ found ∈ body₃, BodyEntry terms sorts found := by
      have := intern_all (BodyEntry terms sorts) second (.inr (.inl rfl)) (entry := (.leaf .index, .data .index))
      rwa [indexed] at this
    have := leaves_all .carried (BodyEntry terms sorts) sorts body₃ 0 third
      (fun position sort found => .inr (.inr ⟨position, sort, found, by simp⟩))
    rwa [carriedLeaves] at this
  have entryOf : ∀ (id : Nat) (entry : Node × ValueSort), body₄[id]? = some entry → BodyEntry terms sorts entry :=
    fun id entry found => good entry (List.mem_of_getElem? found)
  -- Earlier entries persist.
  have keep₁ : ∀ (id : Nat) (entry : Node × ValueSort), body₁[id]? = some entry → body₄[id]? = some entry := by
    intro id entry found
    have inside := (List.getElem?_eq_some_iff.mp found).1
    rw [grown₄, grown₃, grown₂, List.getElem?_append_left (by simp; omega),
      List.getElem?_append_left (by simp; omega), List.getElem?_append_left inside, found]
  have keep₂ : ∀ (id : Nat) (entry : Node × ValueSort), body₂[id]? = some entry → body₄[id]? = some entry := by
    intro id entry found
    have inside := (List.getElem?_eq_some_iff.mp found).1
    rw [grown₄, grown₃, List.getElem?_append_left (by simp; omega), List.getElem?_append_left inside, found]
  have keep₃ : ∀ (id : Nat) (entry : Node × ValueSort), body₃[id]? = some entry → body₄[id]? = some entry := by
    intro id entry found
    have inside := (List.getElem?_eq_some_iff.mp found).1
    rw [grown₄, List.getElem?_append_left inside, found]
  have leafValue : ∀ (id : Nat) (leaf : Leaf) (sort : ValueSort), body₄[id]? = some (.leaf leaf, sort) →
      body₄.eval valuation' id = leaf.value valuation' := fun id leaf sort found =>
    eval_node found (by simp [Node.operands])
  -- The enclosing values.
  have outer : ∀ (ids ids' : List Nat) (env : List (Value F G)),
      Denotes terms valuation ids env → ids'.length = ids.length →
      (∀ (position id id' : Nat), ids[position]? = some id → ids'[position]? = some id' →
        ∃ sort, terms.sort? id = some sort ∧ body₄[id']? = some (.leaf (.outer id), sort)) →
      Denotes body₄ valuation' ids' env := by
    intro ids ids' env denotes lengths entries
    refine ⟨by rw [lengths, denotes.1], fun position id' found' => ?_⟩
    have inside : position < ids.length := by rw [← lengths]; exact (List.getElem?_eq_some_iff.mp found').1
    obtain ⟨sort, -, entry⟩ := entries position ids[position] id' (List.getElem?_eq_getElem inside) found'
    rw [leafValue id' _ sort entry]
    exact denotes.2 position ids[position] (List.getElem?_eq_getElem inside)
  have rest : Denotes body₄ valuation' (indexId :: carriedIds) (.data (.index index) :: carried) := by
    refine ⟨by simp [lengths₄, carriedSorted.1], fun position id found => ?_⟩
    cases position with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        rw [leafValue indexId .index (.data .index) (keep₃ indexId _ entryIndex)]
        rfl
    | succ position =>
        simp only [List.getElem?_cons_succ] at found ⊢
        have inside : position < sorts.length := by
          rw [← lengths₄]; exact (List.getElem?_eq_some_iff.mp found).1
        rw [leafValue id (.carried (0 + position)) sorts[position]
          (entries₄ position id sorts[position] found (List.getElem?_eq_getElem inside))]
        simp [Leaf.value, valuation']
  refine ⟨(outer exportedIds outerIds exportedEnv holds.exported lengths₁ fun position id id' found found' => by
      obtain ⟨sort, sortFound, entry⟩ := entries₁ position id id' found found'
      exact ⟨sort, sortFound, keep₁ id' _ entry⟩).append_lists rest,
    (outer readingIds outerIds' readingEnv holds.reading lengths₂ fun position id id' found found' => by
      obtain ⟨sort, sortFound, entry⟩ := entries₂ position id id' found found'
      exact ⟨sort, sortFound, keep₂ id' _ entry⟩).append_lists rest, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro id member
    rcases List.mem_append.mp member with member | member
    · have := bounded₁ id member
      rw [grown₄, grown₃, grown₂]; simp only [List.length_append]; omega
    · rcases List.mem_cons.mp member with rfl | member
      · rw [grown₄]; simp only [List.length_append]; omega
      · exact bounded₄ id member
  · intro id member
    rcases List.mem_append.mp member with member | member
    · have := bounded₂ id member
      rw [grown₄, grown₃]; simp only [List.length_append]; omega
    · rcases List.mem_cons.mp member with rfl | member
      · rw [grown₄]; simp only [List.length_append]; omega
      · exact bounded₄ id member
  · intro id node sort found operand member
    rcases entryOf id _ found with ⟨_, _, _, equal⟩ | equal | ⟨_, _, _, equal⟩ <;>
      simp only [Prod.mk.injEq] at equal <;> rw [equal.1] at member <;> simp [Node.operands] at member
  · intro id node sort value found evaluated
    rcases entryOf id _ found with ⟨id', sort', sortFound, equal⟩ | equal | ⟨position, sort', sortFound, equal⟩ <;>
      simp only [Prod.mk.injEq] at equal <;> obtain ⟨rfl, rfl⟩ := equal <;>
      rw [leafValue id _ _ found] at evaluated
    · simp only [Leaf.value, valuation'] at evaluated
      unfold Terms.sort? at sortFound
      cases entry : terms[id']? with
      | none => simp [entry] at sortFound
      | some entry' =>
          obtain ⟨node', sort''⟩ := entry'
          simp only [entry, Option.map_some, Option.some.injEq] at sortFound
          subst sortFound
          exact holds.sorted id' node' _ value entry evaluated
    · simp only [Leaf.value, valuation', Option.some.injEq] at evaluated
      subst evaluated
      rfl
    · simp only [Leaf.value, valuation'] at evaluated
      exact carriedSorted.2 position value _ evaluated sortFound
  · intro id leafAnchor position sort found
    rcases entryOf id _ found with ⟨_, _, _, equal⟩ | equal | ⟨_, _, _, equal⟩ <;> simp at equal

/-! ## Bookkeeping -/

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem advance_suffix {anchor : Nat} :
    ∀ {program : List Instruction} {terms : Terms} {ids : List Nat} {terms' : Terms} {ids' : List Nat}
      {rest : List Instruction}, advance anchor terms ids program = .ok (terms', ids', rest) →
      ∃ skipped, program = skipped ++ rest
  | [], _, _, _, _, _, advanced => by
      simp only [advance, Except.ok.injEq, Prod.mk.injEq] at advanced
      obtain ⟨-, -, rfl⟩ := advanced
      exact ⟨[], rfl⟩
  | instruction :: program, terms, ids, terms', ids', rest, advanced => by
      simp only [advance] at advanced
      split at advanced
      · cases termed : terms.term ids anchor instruction with
        | error refusal => simp [termed] at advanced
        | ok result =>
            simp only [termed] at advanced
            obtain ⟨skipped, rfl⟩ := advance_suffix advanced
            exact ⟨instruction :: skipped, rfl⟩
      · simp only [Except.ok.injEq, Prod.mk.injEq] at advanced
        obtain ⟨-, -, rfl⟩ := advanced
        exact ⟨[], rfl⟩

end Eval
end Zkc.Executable.CanonicalNormalization
