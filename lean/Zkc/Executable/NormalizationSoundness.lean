module

public import Zkc.Executable.Completeness

@[expose] public section

/-! Soundness of checked normalization.

A scope's terms denote values under a `Valuation` of their leaves: the
enclosing scope's values, the loop index and carried values, and the results of
the anchors run so far. `Terms.eval` evaluates an id. The simulation invariant
`Holds` ties both programs' environments to the table: every position denotes
its id's term, every term that has a value has its sort, and the table refers to
the results of earlier anchors only.

* `normalize_ideal`: the movable instructions at the head of a program extend
  its environment by the values of their terms. They never stop, because a
  movable calculation is total on operands of its declared sorts.
* `idealStep_local`: an anchor reads its environment only through its operands
  and only appends results, so equal operand values give equal steps.
* `sound_at`: if both programs' scopes are accepted, their ideal meanings agree
  in every monad, for every challenge function, whenever their continuations
  agree on environments the invariant relates (`ScopeSound`). Loop bodies are
  scopes of their own, iteration by iteration.
* `checkNormalized_sound`: on inputs of the declared sorts, with helpers that
  return values of their declared result sorts, accepted programs have equal
  ideal meanings.
* `checkNormalized_flow`: every term a value of either program depends on is
  held by that program at the value's position or earlier.
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction Zkc.Source

variable {F G : Type}

/-! ## Values of terms -/

/-- Values of a scope's leaves: the enclosing scope's values (at the top, the
inputs), the loop index, the carried values and the results of the anchors run
so far, by ordinal. -/
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

/-- The coordinates an occurrence-coordinate value holds. -/
def coordinatesOf : Value F G → List Nat
  | .indices coordinates => coordinates
  | _ => []

/-- The index an index value holds. -/
def indexOf : Value F G → Option Nat
  | .index value => some value
  | _ => none

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
          match Zkc.Construction.calculate calculation arguments with
          | .returned [value] => some value
          | _ => none
      | none => none
  | some (.indicesEmpty, _) => some (.indices [])
  | some (.indicesAppend coordinates index, _) =>
      if _h : coordinates < id ∧ index < id then
        match terms.eval valuation coordinates, terms.eval valuation index with
        | some coordinates', some index' => some (.indices (coordinatesOf coordinates' ++ (indexOf index').toList))
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
              match Zkc.Construction.calculate calculation arguments with
              | .returned [value] => some value
              | _ => none
          | none => none
      | some (.indicesEmpty, _) => some (.indices [])
      | some (.indicesAppend coordinates index, _) =>
          if _h : coordinates < id ∧ index < id then
            match terms.eval valuation coordinates, terms.eval valuation index with
            | some coordinates', some index' =>
                some (.indices (coordinatesOf coordinates' ++ (indexOf index').toList))
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
/-- Arguments at data sorts decode at their types. -/
theorem decodeValues_sorted :
    ∀ (tys : List Structured.Ty) (arguments : List (Value F G)),
      SortedValues arguments (tys.map .data) → tys.all dataType = true →
        ∃ values, decodeValues tys arguments = some values
  | [], [], _, _ => ⟨.nil, rfl⟩
  | [], _ :: _, sorted, _ => by simp [SortedValues] at sorted
  | _ :: _, [], sorted, _ => by simp [SortedValues] at sorted
  | ty :: tys, argument :: arguments, sorted, data => by
      simp only [List.all_cons, Bool.and_eq_true] at data
      obtain ⟨lengths, sorts⟩ := sorted
      obtain ⟨decoded, encoded⟩ := sorts 0 argument (.data ty) rfl rfl
      obtain ⟨values, decodes⟩ := decodeValues_sorted tys arguments
        ⟨by simpa using lengths, fun index value sort found sortFound =>
          sorts (index + 1) value sort found sortFound⟩ data.2
      refine ⟨.cons decoded values, ?_⟩
      simp only [decodeValues, ← encoded, Value.decode_encode data.1, decodes]
      rfl

/-- A total calculation returns on arguments of its declared sorts. -/
theorem calculate_total (calculation : Calculation) (total : calculation.total = true)
    (arguments : List (Value F G)) (sorted : SortedValues arguments (calculation.op.arguments.map .data))
    (data : calculation.op.arguments.all dataType = true) :
    ∃ value, Zkc.Construction.calculate calculation arguments = .returned [value] := by
  obtain ⟨values, decodes⟩ := decodeValues_sorted _ arguments sorted data
  have evaluates : ∃ results, calculation.evaluate values = .returned results := by
    cases calculation <;> simp [Calculation.total] at total <;>
      rcases values with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩ <;> exact ⟨_, rfl⟩
  obtain ⟨results, evaluated⟩ := evaluates
  have length := encodeValues_length results
  rw [Calculation.single] at length
  rcases encoded : encodeValues results with _ | ⟨value, _ | ⟨_, _⟩⟩ <;> rw [encoded] at length <;>
    simp at length
  refine ⟨value, ?_⟩
  simp only [Zkc.Construction.calculate, decodes, evaluated, encoded]

/-! ## Movable instructions -/

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
      ∃ arguments, Construction.read env operands = some arguments ∧
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
              · simp only [Construction.read, List.mapM_cons, List.getElem?_eq_getElem within] at readEq ⊢
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
          match Zkc.Construction.calculate calculation arguments with
          | .returned [value] => some value
          | _ => none
      | none => none
  | .indicesEmpty => some (.indices [])
  | .indicesAppend coordinates index =>
      match terms.eval valuation coordinates, terms.eval valuation index with
      | some coordinates', some index' => some (.indices (coordinatesOf coordinates' ++ (indexOf index').toList))
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

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem indicesAt_of {env : List (Value F G)} {position : Nat} {value : Value F G}
    (found : env[position]? = some value) : indicesAt env position = coordinatesOf value := by
  simp only [indicesAt, found]
  cases value <;> rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem indexAt_of {env : List (Value F G)} {position : Nat} {value : Value F G}
    (found : env[position]? = some value) : indexAt env position = indexOf value := by
  simp only [indexAt, found]
  cases value <;> rfl

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

/-- What recording a movable instruction's term establishes: the table grows,
the new term has a value, and the instruction's ideal step appends exactly that
value. -/
theorem term_spec {terms : Terms} {ids : List Nat} {anchor : Nat} {instruction : Instruction}
    {terms' : Terms} {id : Nat} (movable : Instruction.movable instruction = true)
    (term : terms.term ids anchor instruction = .ok (terms', id))
    {valuation : Valuation F G} {env : List (Value F G)} (denotes : Denotes terms valuation ids env)
    (bounded : Bounded terms ids) (formed : terms.Formed) (sorted : terms.Sorted valuation) :
    ∃ value, (∃ more, terms' = terms ++ more) ∧ id < terms'.length ∧ terms'.Formed ∧
      terms'.Sorted valuation ∧ (∀ anchor', terms.Before anchor' → terms'.Before anchor') ∧
      terms'.eval valuation id = some value ∧
      ∀ {m : Type → Type} [Monad m] (context : Context) (challenge : History F G → m F)
        (helpers : Structured.Evaluation.Meanings F G Structured.closedInterface) {R : Type}
        (proof : Proof F G) (next : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
        idealStep context challenge helpers instruction env proof next = next (env ++ [value]) proof := by
  rcases (movable_iff instruction).mp movable with
    ⟨calculation, operands, results, rfl, total⟩ | ⟨results, rfl⟩ | ⟨coordinates, index, results, rfl⟩
  · simp only [Terms.term] at term
    cases found : operandIds ids operands with
    | none => simp [found] at term
    | some operandIds' =>
        cases resultsEq : calculation.op.results with
        | nil => simp [found, resultsEq] at term
        | cons result more =>
            cases more with
            | cons => simp [found, resultsEq] at term
            | nil =>
                simp only [found, resultsEq] at term
                split at term
                · rename_i checks
                  obtain ⟨sortsEq, data⟩ := checks
                  simp only [Except.ok.injEq] at term
                  obtain ⟨rfl, rfl⟩ : (terms.intern (.calculate calculation operandIds', .data result)).1 = terms' ∧
                      (terms.intern (.calculate calculation operandIds', .data result)).2 = id := by
                    rw [term]; exact ⟨rfl, rfl⟩
                  obtain ⟨arguments, readEq, argumentsEq⟩ := denotes.read_some found
                  have below := operandIds_bounded bounded found
                  have argumentsSorted := sorted_values sorted argumentsEq
                    (sorts := calculation.op.arguments.map .data) (by rw [sortsEq, List.map_map])
                  obtain ⟨value, computed⟩ := calculate_total calculation total arguments argumentsSorted data
                  have valueEq : (Node.calculate calculation operandIds').value terms valuation = some value := by
                    simp only [Node.value, argumentsEq, computed]
                  obtain ⟨evaluates, formed', grown, within, -⟩ :=
                    intern_eval (node := .calculate calculation operandIds') (sort := .data result)
                      (valuation := valuation) formed below
                  refine ⟨value, grown, within, formed', ?_, ?_, by rw [evaluates, valueEq], ?_⟩
                  · refine intern_sorted (node := .calculate calculation operandIds') sorted below ?_
                    intro value' found'
                    rw [valueEq, Option.some.injEq] at found'
                    subst found'
                    exact calculate_sorted computed 0 value (.data result) rfl (by rw [resultsEq]; rfl)
                  · intro anchor' before
                    exact intern_before before (fun _ _ equal => by cases equal)
                  · intro m _ context challenge helpers R proof next
                    simp only [idealStep, readEq, computed]
                · cases term
  · simp only [Terms.term, Except.ok.injEq] at term
    obtain ⟨rfl, rfl⟩ : (terms.intern (.indicesEmpty, .indices)).1 = terms' ∧
        (terms.intern (.indicesEmpty, .indices)).2 = id := by
      rw [term]; exact ⟨rfl, rfl⟩
    have below : ∀ operand ∈ Node.indicesEmpty.operands, operand < terms.length := by simp [Node.operands]
    obtain ⟨evaluates, formed', grown, within, -⟩ :=
      intern_eval (sort := .indices) (valuation := valuation) formed below
    refine ⟨.indices [], grown, within, formed', ?_, ?_, by rw [evaluates]; rfl, ?_⟩
    · refine intern_sorted sorted below ?_
      intro value found'
      simp only [Node.value, Option.some.injEq] at found'
      subst found'
      trivial
    · intro anchor' before
      exact intern_before before (fun _ _ equal => by cases equal)
    · intro m _ context challenge helpers R proof next
      rfl
  · simp only [Terms.term] at term
    cases coordinatesFound : ids[coordinates]? with
    | none => simp [coordinatesFound] at term
    | some coordinatesId =>
        cases indexFound : ids[index]? with
        | none => simp [coordinatesFound, indexFound] at term
        | some indexId =>
            simp only [coordinatesFound, indexFound, Except.ok.injEq] at term
            obtain ⟨rfl, rfl⟩ : (terms.intern (.indicesAppend coordinatesId indexId, .indices)).1 = terms' ∧
                (terms.intern (.indicesAppend coordinatesId indexId, .indices)).2 = id := by
              rw [term]; exact ⟨rfl, rfl⟩
            have below : ∀ operand ∈ (Node.indicesAppend coordinatesId indexId).operands,
                operand < terms.length := by
              simp only [Node.operands, List.mem_cons, List.not_mem_nil, or_false]
              rintro operand (rfl | rfl)
              · exact bounded _ (List.mem_of_getElem? coordinatesFound)
              · exact bounded _ (List.mem_of_getElem? indexFound)
            have coordinatesWithin : coordinates < env.length := by
              rw [← denotes.1]; exact (List.getElem?_eq_some_iff.mp coordinatesFound).1
            have indexWithin : index < env.length := by
              rw [← denotes.1]; exact (List.getElem?_eq_some_iff.mp indexFound).1
            have coordinatesValue := denotes.2 coordinates coordinatesId coordinatesFound
            have indexValue := denotes.2 index indexId indexFound
            rw [List.getElem?_eq_getElem coordinatesWithin] at coordinatesValue
            rw [List.getElem?_eq_getElem indexWithin] at indexValue
            obtain ⟨evaluates, formed', grown, within, -⟩ :=
              intern_eval (sort := .indices) (valuation := valuation) formed below
            refine ⟨.indices (coordinatesOf env[coordinates] ++ (indexOf env[index]).toList), grown, within,
              formed', ?_, ?_, ?_, ?_⟩
            · refine intern_sorted sorted below ?_
              intro value found'
              simp only [Node.value, coordinatesValue, indexValue, Option.some.injEq] at found'
              subst found'
              trivial
            · intro anchor' before
              exact intern_before before (fun _ _ equal => by cases equal)
            · rw [evaluates]
              simp only [Node.value, coordinatesValue, indexValue]
            · intro m _ context challenge helpers R proof next
              simp only [idealStep, indicesAt_of (List.getElem?_eq_getElem coordinatesWithin),
                indexAt_of (List.getElem?_eq_getElem indexWithin)]

/-- The movable instructions at the head of a program extend its environment by
the values of their terms: they never stop and need no challenge. -/
theorem normalize_ideal {anchor : Nat} :
    ∀ {program : List Instruction} {terms : Terms} {ids : List Nat} {terms' : Terms} {ids' : List Nat}
      {rest : List Instruction}, advance anchor terms ids program = .ok (terms', ids', rest) →
      ∀ {valuation : Valuation F G} {env : List (Value F G)}, Denotes terms valuation ids env →
        Bounded terms ids → terms.Formed → terms.Sorted valuation →
        ∃ env', (∃ more, terms' = terms ++ more) ∧ Denotes terms' valuation ids' env' ∧ Bounded terms' ids' ∧
          terms'.Formed ∧ terms'.Sorted valuation ∧ (∀ anchor', terms.Before anchor' → terms'.Before anchor') ∧
          ∀ {m : Type → Type} [Monad m] (context : Context) (challenge : History F G → m F)
            (helpers : Structured.Evaluation.Meanings F G Structured.closedInterface) {R : Type}
            (proof : Proof F G) (next : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
            idealK context challenge helpers program env proof next =
              idealK context challenge helpers rest env' proof next
  | [], terms, ids, terms', ids', rest, advanced, valuation, env, denotes, bounded, formed, sorted => by
      simp only [advance, Except.ok.injEq, Prod.mk.injEq] at advanced
      obtain ⟨rfl, rfl, rfl⟩ := advanced
      exact ⟨env, ⟨[], by simp⟩, denotes, bounded, formed, sorted, fun _ before => before,
        by intros; rfl⟩
  | instruction :: program, terms, ids, terms', ids', rest, advanced, valuation, env, denotes, bounded, formed,
      sorted => by
      simp only [advance] at advanced
      split at advanced
      · rename_i movable
        cases termed : terms.term ids anchor instruction with
        | error refusal => simp [termed] at advanced
        | ok result =>
            obtain ⟨terms₁, id⟩ := result
            simp only [termed] at advanced
            obtain ⟨value, ⟨more, grown⟩, within, formed₁, sorted₁, before₁, evaluated, step⟩ :=
              term_spec movable termed denotes bounded formed sorted
            have denotes₁ : Denotes terms₁ valuation (ids ++ [id]) (env ++ [value]) := by
              rw [grown]
              exact (denotes.append bounded).push (by rw [← grown]; exact evaluated)
            have bounded₁ : Bounded terms₁ (ids ++ [id]) := by
              intro id' member
              rcases List.mem_append.mp member with member | member
              · rw [grown]; exact (bounded.append) id' member
              · simp only [List.mem_singleton] at member
                subst member
                exact within
            obtain ⟨env', ⟨more', grown'⟩, denotes', bounded', formed', sorted', before', run⟩ :=
              normalize_ideal advanced denotes₁ bounded₁ formed₁ sorted₁
            refine ⟨env', ⟨more ++ more', by rw [grown', grown, List.append_assoc]⟩, denotes', bounded', formed',
              sorted', fun anchor' before => before' anchor' (before₁ anchor' before), ?_⟩
            intro m _ context challenge helpers R proof next
            simp only [idealK]
            rw [step context challenge helpers proof]
            exact run context challenge helpers proof next
      · simp only [Except.ok.injEq, Prod.mk.injEq] at advanced
        obtain ⟨rfl, rfl, rfl⟩ := advanced
        exact ⟨env, ⟨[], by simp⟩, denotes, bounded, formed, sorted, fun _ before => before,
          by intros; rfl⟩

/-! ## Anchors read their operands only -/

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem read_positions (arguments : List (Value F G)) :
    Construction.read arguments (List.range' 0 arguments.length) = some arguments := by
  simpa [Construction.read] using read_range' ([] : List (Value F G)) arguments

section Local
variable {m : Type → Type} [Monad m] (context : Context) (challenge : History F G → m F)
  (helpers : Structured.Evaluation.Meanings F G Structured.closedInterface)

/-- An anchor reads its environment only through its operands and only appends
its results: renumbered over its operand values it takes the same step. -/
theorem idealStep_local {R : Type} {operation : Operation} {operands : List Nat} {results : List ValueSort}
    {body : List Instruction} {env arguments : List (Value F G)} {proof : Proof F G}
    {next : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)}
    (notLoop : ∀ site maximum yielded, operation ≠ .loop site maximum yielded)
    (found : Construction.read env operands = some arguments) :
    idealStep context challenge helpers ⟨operation, operands, results, body⟩ env proof next =
      idealStep context challenge helpers ⟨operation, List.range' 0 arguments.length, results, []⟩ arguments proof
        (fun env' unread => next (env ++ env'.drop arguments.length) unread) := by
  have lengths : operands.length = arguments.length := length_of_mapM_some found
  have values : ∀ position reference, operands[position]? = some reference →
      env[reference]? = arguments[position]? := fun position reference entry =>
    (value_at found entry).symm
  cases operation with
  | loop site maximum yielded => exact absurd rfl (notLoop site maximum yielded)
  | calculate calculation =>
      simp only [idealStep, found, read_positions]
      cases Zkc.Construction.calculate calculation arguments <;> simp
  | call name =>
      simp only [idealStep, found, read_positions]
      cases callHelper helpers name arguments <;> simp
  | _ =>
      rcases operands with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
        rcases arguments with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, more⟩⟩⟩⟩ <;>
        (try simp at lengths)
      · rfl
      · have va : env[a]? = some x := by simpa using values 0 a rfl
        show _ = idealStep context challenge helpers ⟨_, [0], _, []⟩ [x] proof _
        simp [idealStep, va]
      · have va : env[a]? = some x := by simpa using values 0 a rfl
        have vb : env[b]? = some y := by simpa using values 1 b rfl
        show _ = idealStep context challenge helpers ⟨_, [0, 1], _, []⟩ [x, y] proof _
        simp [idealStep, transcriptAt, indicesAt, indexAt, va, vb]
      · have va : env[a]? = some x := by simpa using values 0 a rfl
        have vb : env[b]? = some y := by simpa using values 1 b rfl
        have vc : env[c]? = some z := by simpa using values 2 c rfl
        show _ = idealStep context challenge helpers ⟨_, [0, 1, 2], _, []⟩ [x, y, z] proof _
        simp [idealStep, transcriptAt, dataAt, va, vb]
      · rfl

/-- A helper returns values of the declared result sorts. -/
def HelperSorted (table : Structured.Evaluation.Meanings F G Structured.closedInterface) (name : String)
    (declared : List ValueSort) : Prop :=
  ∀ (arguments values : List (Value F G)), callHelper table name arguments = .returned values →
    values.length = declared.length → SortedValues values declared

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem stopped_always {α : Type} (stop : PIR.Stop) (unread : Proof F G) :
    (pure (.stopped stop, unread) : Always (PIR.Outcome α × Proof F G)) (fun _ => True) := trivial

/-- A continuing anchor appends values of the sorts its operation fixes; a
helper call's are of its declared result sorts when the helper returns those. -/
theorem anchor_continues {operation : Operation} {results : List ValueSort} {arguments : List (Value F G)}
    {proof : Proof F G} (notLoop : ∀ site maximum yielded, operation ≠ .loop site maximum yielded)
    (called : ∀ name, operation = .call name → HelperSorted helpers name results) :
    Continues context helpers ⟨operation, List.range' 0 arguments.length, results, []⟩ arguments proof
      fun env' _ => ∃ appended, env' = arguments ++ appended ∧
        SortedValues appended (Instruction.resultSorts ⟨operation, [], results, []⟩) := by
  cases operation with
  | localService => exact stopped_always _ _
  | loop site maximum yielded => exact absurd rfl (notLoop site maximum yielded)
  | calculate calculation =>
      refine Continues.calculate context helpers ?_
      intro arguments' values found computed
      rw [read_positions] at found
      cases found
      refine ⟨values, rfl, ?_, ?_⟩
      · rw [calculate_length calculation computed]
        simp [Instruction.resultSorts]
      · exact calculate_sorted computed
  | call name =>
      refine Continues.call context helpers ?_
      intro arguments' values found computed lengths
      rw [read_positions] at found
      cases found
      exact ⟨values, rfl, called name rfl arguments values computed lengths⟩
  | receive site schema peer ty =>
      rcases arguments with _ | ⟨x, more⟩
      · show Continues context helpers ⟨_, [], _, []⟩ [] proof _
        cases scalar : scalarType ty with
        | none => unfold Continues; simp only [idealStep, scalar]; exact stopped_always _ _
        | some common =>
            refine Continues.receive context helpers scalar ?_
            intro payload rest _ typed
            refine ⟨[.data payload], rfl, rfl, ?_⟩
            intro index value sort found sortFound
            match index, found, sortFound with
            | 0, found, sortFound =>
                simp only [List.getElem?_cons_zero, Option.some.injEq, Instruction.resultSorts] at found sortFound
                subst found sortFound
                have same := scalarType_payload (typed ▸ scalar)
                rw [same]
                exact payload_sorted payload
      · exact stopped_always _ _
  | observe suite template =>
      rcases arguments with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, rest⟩⟩⟩⟩
      all_goals try exact stopped_always _ _
      show Continues context helpers ⟨_, [0, 1, 2], _, []⟩ [x, y, z] proof _
      refine Continues.observe context helpers ?_
      intro history origin payload _ _ _
      refine ⟨[.transcript (history ++ [.message origin payload])], rfl, rfl, ?_⟩
      intro index value sort found sortFound
      match index, found, sortFound with
      | 0, found, sortFound =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Instruction.resultSorts] at found sortFound
          subst found sortFound
          trivial
  | challenge suite field template =>
      rcases arguments with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
      all_goals try exact stopped_always _ _
      show Continues context helpers ⟨_, [0, 1], _, []⟩ [x, y] proof _
      refine Continues.challenge context helpers ?_
      intro history origin answer _ _
      refine ⟨[.data (.field field answer), .transcript (history ++ [.challenge origin])], rfl, rfl, ?_⟩
      intro index value sort found sortFound
      match index, found, sortFound with
      | 0, found, sortFound =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Instruction.resultSorts] at found sortFound
          subst found sortFound
          exact ⟨answer, rfl⟩
      | 1, found, sortFound =>
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
            Instruction.resultSorts] at found sortFound
          subst found sortFound
          trivial
  | guard site =>
      rcases arguments with _ | ⟨x, _ | ⟨y, rest⟩⟩
      all_goals try exact stopped_always _ _
      show Continues context helpers ⟨_, [0], _, []⟩ [x] proof _
      refine Continues.guard context helpers ?_
      intro _
      exact ⟨[], by simp, rfl, by simp⟩
  | indicesEmpty =>
      rcases arguments with _ | ⟨x, more⟩
      · refine Continues.indicesEmpty context helpers ?_
        exact ⟨[.indices []], rfl, rfl, fun index value sort found sortFound => by
          match index, found, sortFound with
          | 0, found, sortFound =>
              simp only [List.getElem?_cons_zero, Option.some.injEq, Instruction.resultSorts] at found sortFound
              subst found sortFound
              trivial⟩
      · exact stopped_always _ _
  | indicesAppend =>
      rcases arguments with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
      all_goals try exact stopped_always _ _
      show Continues context helpers ⟨_, [0, 1], _, []⟩ [x, y] proof _
      refine Continues.indicesAppend context helpers ?_
      intro appended
      exact ⟨[.indices appended], rfl, rfl, fun index value sort found sortFound => by
        match index, found, sortFound with
        | 0, found, sortFound =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, Instruction.resultSorts] at found sortFound
            subst found sortFound
            trivial⟩
  | send => exact stopped_always _ _
  | unsupported => exact stopped_always _ _

end Local


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
    Holds body₄ ⟨fun id => terms.eval valuation id, some (.index index), carried, []⟩ 0
      (outerIds ++ indexId :: carriedIds) (exportedEnv ++ .index index :: carried)
      (outerIds' ++ indexId :: carriedIds) (readingEnv ++ .index index :: carried) := by
  set valuation' : Valuation F G := ⟨fun id => terms.eval valuation id, some (.index index), carried, []⟩
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
  have rest : Denotes body₄ valuation' (indexId :: carriedIds) (.index index :: carried) := by
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
      exact ⟨index, rfl⟩
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

theorem Instruction.callList_append :
    ∀ (first second : List Instruction),
      Instruction.callList (first ++ second) = Instruction.callList first ++ Instruction.callList second
  | [], second => by simp [Instruction.callList]
  | instruction :: first, second => by
      simp [Instruction.callList, Instruction.callList_append first second]

/-! ## Accepted scopes -/

section Sound
variable {m : Type → Type} [Monad m] (context : Context) (challenge : History F G → m F)
  (helpers : Structured.Evaluation.Meanings F G Structured.closedInterface)

/-- Accepted scopes have equal ideal meanings, whenever their continuations
agree on environments the invariant relates at the end. -/
def ScopeSound (fuel : Nat) : Prop :=
  ∀ (terms : Terms) (exportedIds : List Nat) (exported : List Instruction) (readingIds : List Nat)
    (reading : List Instruction) (anchor : Nat) (terms' : Terms) (exportedIds' readingIds' : List Nat),
    checkScope fuel terms exportedIds exported readingIds reading anchor = .ok (terms', exportedIds', readingIds') →
    (∀ call ∈ Instruction.callList exported, HelperSorted helpers call.1 call.2) →
    ∀ (valuation : Valuation F G) (exportedEnv readingEnv : List (Value F G)) (proof : Proof F G) (R : Type)
      (next next' : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      Holds terms valuation anchor exportedIds exportedEnv readingIds readingEnv →
      (∀ (valuation' : Valuation F G) (anchor' : Nat) (exportedEnv' readingEnv' : List (Value F G))
        (unread : Proof F G),
        Holds terms' valuation' anchor' exportedIds' exportedEnv' readingIds' readingEnv' →
          next exportedEnv' unread = next' readingEnv' unread) →
      idealK context challenge helpers exported exportedEnv proof next =
        idealK context challenge helpers reading readingEnv proof next'

/-- Accepted anchors take equal steps, whenever their continuations agree on
the same appended results. -/
def AnchorSound (fuel : Nat) : Prop :=
  ∀ (terms : Terms) (exportedIds : List Nat) (first : Instruction) (readingIds : List Nat) (first' : Instruction)
    (anchor : Nat) (terms' : Terms) (resultIds : List Nat),
    checkAnchor fuel terms exportedIds first readingIds first' anchor = .ok (terms', resultIds) →
    (∀ call ∈ Instruction.callsOf first, HelperSorted helpers call.1 call.2) →
    ∀ (valuation : Valuation F G) (exportedEnv readingEnv : List (Value F G)) (proof : Proof F G) (R : Type)
      (next next' : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      Holds terms valuation anchor exportedIds exportedEnv readingIds readingEnv →
      (∀ (results : List (Value F G)) (unread : Proof F G),
        Holds terms' { valuation with results := valuation.results ++ [results] } (anchor + 1)
          (exportedIds ++ resultIds) (exportedEnv ++ results) (readingIds ++ resultIds) (readingEnv ++ results) →
          next (exportedEnv ++ results) unread = next' (readingEnv ++ results) unread) →
      idealStep context challenge helpers first exportedEnv proof next =
        idealStep context challenge helpers first' readingEnv proof next'

/-- An empty fuel accepts nothing. -/
theorem sound_zero : ScopeSound context challenge helpers 0 ∧ AnchorSound context challenge helpers 0 := by
  constructor
  · intro _ _ _ _ _ _ _ _ _ checked
    simp [checkScope] at checked
  · intro _ _ _ _ _ _ _ _ checked
    simp [checkAnchor] at checked

/-- A scope is sound when its anchors and the scopes after them are. -/
theorem scopeSound_succ (fuel : Nat) (scope : ScopeSound context challenge helpers fuel)
    (anchors : AnchorSound context challenge helpers fuel) : ScopeSound context challenge helpers (fuel + 1) := by
  intro terms exportedIds exported readingIds reading anchor terms' exportedIds' readingIds' checked calls
    valuation exportedEnv readingEnv proof R next next' holds finishes
  simp only [checkScope] at checked
  cases advancedE : advance anchor terms exportedIds exported with
  | error refusal => simp [advancedE] at checked
  | ok resultE =>
    obtain ⟨terms₁, exportedIds₁, exported₁⟩ := resultE
    simp only [advancedE] at checked
    cases advancedR : advance anchor terms₁ readingIds reading with
    | error refusal => simp [advancedR] at checked
    | ok resultR =>
      obtain ⟨terms₂, readingIds₁, reading₁⟩ := resultR
      simp only [advancedR] at checked
      obtain ⟨exportedEnv₁, ⟨moreE, grownE⟩, denotesE, boundedE, formed₁, sorted₁, before₁, runE⟩ :=
        normalize_ideal advancedE holds.exported holds.exportedBounded holds.formed holds.sorted
      have readingDenotes₁ : Denotes terms₁ valuation readingIds readingEnv := by
        rw [grownE]; exact holds.reading.append holds.readingBounded
      have readingBounded₁ : Bounded terms₁ readingIds := by rw [grownE]; exact holds.readingBounded.append
      obtain ⟨readingEnv₁, ⟨moreR, grownR⟩, denotesR, boundedR, formed₂, sorted₂, before₂, runR⟩ :=
        normalize_ideal advancedR readingDenotes₁ readingBounded₁ formed₁ sorted₁
      have holds₂ : Holds terms₂ valuation anchor exportedIds₁ exportedEnv₁ readingIds₁ readingEnv₁ :=
        ⟨by rw [grownR]; exact denotesE.append boundedE, denotesR, by rw [grownR]; exact boundedE.append, boundedR,
          formed₂, sorted₂, before₂ anchor (before₁ anchor holds.before), holds.results⟩
      rw [runE context challenge helpers proof next, runR context challenge helpers proof next']
      obtain ⟨skipped, rfl⟩ := advance_suffix advancedE
      cases exported₁ with
      | nil =>
          cases reading₁ with
          | nil =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at checked
              obtain ⟨rfl, rfl, rfl⟩ := checked
              exact finishes valuation anchor exportedEnv₁ readingEnv₁ proof holds₂
          | cons => simp at checked
      | cons first exportedRest =>
          cases reading₁ with
          | nil => simp at checked
          | cons first' readingRest =>
              simp only at checked
              cases anchored : checkAnchor fuel terms₂ exportedIds₁ first readingIds₁ first' anchor with
              | error refusal => simp [anchored] at checked
              | ok resultA =>
                  obtain ⟨terms₃, resultIds⟩ := resultA
                  simp only [anchored] at checked
                  have callsOf : ∀ call ∈ Instruction.callList (skipped ++ first :: exportedRest),
                      HelperSorted helpers call.1 call.2 := calls
                  simp only [Instruction.callList_append, Instruction.callList, List.mem_append] at callsOf
                  simp only [idealK]
                  refine anchors terms₂ exportedIds₁ first readingIds₁ first' anchor terms₃ resultIds anchored
                    (fun call member => callsOf call (.inr (.inl member))) valuation exportedEnv₁ readingEnv₁
                    proof R _ _ holds₂ ?_
                  intro results unread holds₃
                  exact scope terms₃ _ exportedRest _ readingRest (anchor + 1) terms' exportedIds' readingIds'
                    checked (fun call member => callsOf call (.inr (.inr member))) _ _ _ unread R next next' holds₃
                    finishes

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem mapM_map_some {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → xs.map f = ys.map some
  | [], ys, found => by
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at found
      subst found
      rfl
  | x :: xs, ys, found => by
      simp only [List.mapM_cons] at found
      cases first : f x with
      | none => simp [first] at found
      | some y =>
          cases rest : xs.mapM f with
          | none => simp [first, rest] at found
          | some ys' =>
              simp only [first, rest, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq] at found
              subst found
              simp [first, mapM_map_some rest]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem read_cons_some {env : List (Value F G)} {operand : Nat} {operands : List Nat}
    {arguments : List (Value F G)} (found : Construction.read env (operand :: operands) = some arguments) :
    ∃ value rest, arguments = value :: rest ∧ env[operand]? = some value ∧
      Construction.read env operands = some rest := by
  simp only [Construction.read, List.mapM_cons] at found
  cases first : env[operand]? with
  | none => simp [first] at found
  | some value =>
      cases others : operands.mapM (fun reference => env[reference]?) with
      | none => simp [first, others] at found
      | some rest =>
          simp only [first, others, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at found
          exact ⟨value, rest, found.symm, rfl, others⟩

/-- An accepted pair of loops takes equal steps: the same count and initial
values, and bodies whose checked scope agrees iteration by iteration. -/
theorem loop_step (fuel : Nat) (scope : ScopeSound context challenge helpers fuel)
    {terms : Terms} {valuation : Valuation F G} {anchor : Nat} {exportedIds readingIds : List Nat}
    {exportedEnv readingEnv : List (Value F G)}
    (holds : Holds terms valuation anchor exportedIds exportedEnv readingIds readingEnv)
    {loop loop' : LoopParts}
    (calls : ∀ call ∈ Instruction.callsOf ⟨.loop loop.site loop.maximum loop.yielded, loop.count :: loop.initial,
      loop.results, loop.body⟩, HelperSorted helpers call.1 call.2)
    (maximumEq : loop.maximum = loop'.maximum) {counted : Nat} {carried : List Nat}
    (foundE : operandIds exportedIds (loop.count :: loop.initial) = some (counted :: carried))
    (foundR : operandIds readingIds (loop'.count :: loop'.initial) = some (counted :: carried))
    {sorts : List ValueSort} (sortsFound : carried.mapM terms.sort? = some sorts)
    {body₁ : Terms} {outerIds : List Nat} (outersE : Terms.outers [] terms exportedIds = some (body₁, outerIds))
    {body₂ : Terms} {outerIds' : List Nat} (outersR : body₁.outers terms readingIds = some (body₂, outerIds'))
    {body₃ : Terms} {indexId : Nat} (indexed : body₂.intern (.leaf .index, .data .index) = (body₃, indexId))
    {body₄ : Terms} {carriedIds : List Nat} (carriedLeaves : body₃.leaves .carried sorts 0 = (body₄, carriedIds))
    {body₅ : Terms} {bodyIds bodyIds' : List Nat}
    (bodyChecked : checkScope fuel body₄ (outerIds ++ indexId :: carriedIds) loop.body
      (outerIds' ++ indexId :: carriedIds) loop'.body 0 = .ok (body₅, bodyIds, bodyIds'))
    {yieldedIds : List Nat} (yieldedE : operandIds bodyIds loop.yielded = some yieldedIds)
    (yieldedR : operandIds bodyIds' loop'.yielded = some yieldedIds)
    (yieldedSorts : yieldedIds.map body₅.sort? = sorts.map some)
    {terms' : Terms} {resultIds : List Nat} (checked : terms.leaves (.result anchor) sorts 0 = (terms', resultIds))
    {proof : Proof F G} {R : Type} {next next' : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)}
    (continues : ∀ (results : List (Value F G)) (unread : Proof F G),
      Holds terms' { valuation with results := valuation.results ++ [results] } (anchor + 1)
        (exportedIds ++ resultIds) (exportedEnv ++ results) (readingIds ++ resultIds) (readingEnv ++ results) →
        next (exportedEnv ++ results) unread = next' (readingEnv ++ results) unread) :
    idealStep context challenge helpers ⟨.loop loop.site loop.maximum loop.yielded, loop.count :: loop.initial,
        loop.results, loop.body⟩ exportedEnv proof next =
      idealStep context challenge helpers ⟨.loop loop'.site loop'.maximum loop'.yielded,
        loop'.count :: loop'.initial, loop'.results, loop'.body⟩ readingEnv proof next' := by
  obtain ⟨argumentsE, readE, evalE⟩ := holds.exported.read_some foundE
  obtain ⟨argumentsR, readR, evalR⟩ := holds.reading.read_some foundR
  rw [evalE, Option.some.injEq] at evalR
  subst evalR
  obtain ⟨value, values, rfl, countE, initialE⟩ := read_cons_some readE
  obtain ⟨value', values', equal, countR, initialR⟩ := read_cons_some readR
  simp only [List.cons.injEq] at equal
  obtain ⟨rfl, rfl⟩ := equal
  have carriedEval : carried.mapM (terms.eval valuation) = some values := by
    simp only [List.mapM_cons] at evalE
    cases first : terms.eval valuation counted with
    | none => simp [first] at evalE
    | some value'' =>
        cases rest : carried.mapM (terms.eval valuation) with
        | none => simp [first, rest] at evalE
        | some values'' =>
            simp only [first, rest, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
              List.cons.injEq] at evalE
            rw [evalE.2]
  have valuesSorted : SortedValues values sorts := sorted_values holds.sorted carriedEval (mapM_map_some sortsFound)
  have bodyCalls : ∀ call ∈ Instruction.callList loop.body, HelperSorted helpers call.1 call.2 := by
    intro call member
    exact calls call (by simpa [Instruction.callsOf] using member)
  -- The iterations agree as their bodies and yields do.
  have iterations : ∀ (items : List Nat) (current : List (Value F G)) (unread : Proof F G),
      SortedValues current sorts →
      iterateM (fun start unread' continuation => idealK context challenge helpers loop.body start unread' continuation)
          exportedEnv loop.yielded items current unread (fun final unread' => next (exportedEnv ++ final) unread') =
        iterateM (fun start unread' continuation =>
            idealK context challenge helpers loop'.body start unread' continuation)
          readingEnv loop'.yielded items current unread (fun final unread' => next' (readingEnv ++ final) unread') := by
    intro items
    induction items with
    | nil =>
        intro current unread sortedCurrent
        have recorded := holds.record sortedCurrent
        rw [checked] at recorded
        exact continues current unread recorded
    | cons index items ih =>
        intro current unread sortedCurrent
        simp only [iterateM]
        refine scope body₄ _ loop.body _ loop'.body 0 body₅ bodyIds bodyIds' bodyChecked bodyCalls _ _ _ unread R _ _
          (holds.body outersE outersR indexed carriedLeaves (index := index) sortedCurrent) ?_
        intro valuation' anchor' finalE finalR unread' finalHolds
        obtain ⟨yieldedValues, readFinalE, evalFinalE⟩ := finalHolds.exported.read_some yieldedE
        obtain ⟨yieldedValues', readFinalR, evalFinalR⟩ := finalHolds.reading.read_some yieldedR
        rw [evalFinalE, Option.some.injEq] at evalFinalR
        subst evalFinalR
        simp only [readFinalE, readFinalR]
        exact ih yieldedValues unread' (sorted_values finalHolds.sorted evalFinalE yieldedSorts)
  simp only [idealStep, indexAt_of countE, indexAt_of countR, initialE, initialR, ← maximumEq]
  cases indexOf value with
  | none => rfl
  | some bound =>
      simp only
      by_cases bounded : bound ≤ loop.maximum
      · simp only [bounded, ite_true]
        exact iterations _ values proof valuesSorted
      · simp only [bounded, ite_false]

/-- Accepted anchors take equal steps: a plain anchor reads equal operand
values, a loop iterates bodies that agree iteration by iteration. -/
theorem anchorSound_succ (fuel : Nat) (scope : ScopeSound context challenge helpers fuel) :
    AnchorSound context challenge helpers (fuel + 1) := by
  intro terms exportedIds first readingIds first' anchor terms' resultIds checked calls
    valuation exportedEnv readingEnv proof R next next' holds continues
  simp only [checkAnchor] at checked
  cases loopE : Instruction.loopParts first with
  | none =>
      cases loopR : Instruction.loopParts first' with
      | some _ => simp [loopE, loopR] at checked
      | none =>
          simp only [loopE, loopR] at checked
          cases loopy : (loopOperation first.operation || loopOperation first'.operation)
          · simp only [loopy, Bool.false_eq_true, ite_false] at checked
            by_cases same : first.operation = first'.operation ∧ first.results = first'.results
            · simp only [same, and_self, ite_true] at checked
              obtain ⟨operationEq, resultsEq⟩ := same
              cases foundE : operandIds exportedIds first.operands with
              | none => simp [foundE] at checked
              | some operands =>
                  cases foundR : operandIds readingIds first'.operands with
                  | none => simp [foundE, foundR] at checked
                  | some operands' =>
                      simp only [foundE, foundR] at checked
                      by_cases equal : operands = operands'
                      · subst equal
                        simp only [ite_true, Except.ok.injEq] at checked
                        obtain ⟨argumentsE, readE, evalE⟩ := holds.exported.read_some foundE
                        obtain ⟨argumentsR, readR, evalR⟩ := holds.reading.read_some foundR
                        rw [evalE, Option.some.injEq] at evalR
                        subst evalR
                        rcases first with ⟨operation, operandsE, results, bodyE⟩
                        rcases first' with ⟨operation', operandsR, results', bodyR⟩
                        simp only at operationEq resultsEq readE readR checked loopy
                        subst operationEq resultsEq
                        have notLoop : ∀ site maximum yielded, operation ≠ .loop site maximum yielded := by
                          intro site maximum yielded equal
                          subst equal
                          simp [loopOperation] at loopy
                        have called : ∀ name, operation = .call name → HelperSorted helpers name results := by
                          intro name equal
                          subst equal
                          exact calls (name, results) (by simp [Instruction.callsOf])
                        rw [idealStep_local context challenge helpers notLoop readE,
                          idealStep_local context challenge helpers notLoop readR]
                        refine idealStep_congr context helpers challenge _ _ _ _ _ _
                          (anchor_continues context helpers notLoop called) ?_
                        rintro env' unread ⟨appended, rfl, sortedAppended⟩
                        simp only [List.drop_left]
                        have recorded := holds.record sortedAppended (sorts := Instruction.resultSorts
                          ⟨operation, [], results, []⟩)
                        have sortsEq : Instruction.resultSorts ⟨operation, [], results, []⟩ =
                            Instruction.resultSorts ⟨operation, operandsE, results, bodyE⟩ := by
                          cases operation <;> rfl
                        rw [sortsEq, checked] at recorded
                        exact continues appended unread recorded
                      · simp only [equal, ite_false] at checked
                        cases checked
            · simp only [same, ite_false] at checked
              cases checked
          · simp only [loopy, ite_true] at checked
            cases checked
  | some loop =>
      cases loopR : Instruction.loopParts first' with
      | none => simp [loopE, loopR] at checked
      | some loop' =>
          simp only [loopE, loopR] at checked
          have firstEq := Instruction.loopParts_some loopE
          have firstEq' := Instruction.loopParts_some loopR
          subst firstEq firstEq'
          by_cases header : loop.site = loop'.site ∧ loop.maximum = loop'.maximum ∧
              loop.yielded.length = loop'.yielded.length ∧ loop.results = loop'.results
          · simp only [header, and_self, ite_true] at checked
            obtain ⟨-, maximumEq, -, -⟩ := header
            cases foundE : operandIds exportedIds (loop.count :: loop.initial) with
            | none => simp [foundE] at checked
            | some operandsE =>
                cases operandsE with
                | nil => simp [foundE] at checked
                | cons counted carried =>
                    cases foundR : operandIds readingIds (loop'.count :: loop'.initial) with
                    | none => simp [foundE, foundR] at checked
                    | some operandsR =>
                        simp only [foundE, foundR] at checked
                        by_cases equal : counted :: carried = operandsR
                        · subst equal
                          simp only [ite_true] at checked
                          cases sortsFound : carried.mapM terms.sort? with
                          | none => simp [sortsFound] at checked
                          | some sorts =>
                              simp only [sortsFound] at checked
                              cases outersE : Terms.outers [] terms exportedIds with
                              | none => simp [outersE] at checked
                              | some resultO =>
                                  obtain ⟨body₁, outerIds⟩ := resultO
                                  simp only [outersE] at checked
                                  cases outersR : body₁.outers terms readingIds with
                                  | none => simp [outersR] at checked
                                  | some resultO' =>
                                      obtain ⟨body₂, outerIds'⟩ := resultO'
                                      simp only [outersR] at checked
                                      generalize indexed : body₂.intern (.leaf .index, .data .index) = indexResult
                                        at checked
                                      obtain ⟨body₃, indexId⟩ := indexResult
                                      generalize carriedLeaves : body₃.leaves .carried sorts 0 = carriedResult
                                        at checked
                                      obtain ⟨body₄, carriedIds⟩ := carriedResult
                                      simp only at checked
                                      cases bodyChecked : checkScope fuel body₄ (outerIds ++ indexId :: carriedIds)
                                          loop.body (outerIds' ++ indexId :: carriedIds) loop'.body 0 with
                                      | error refusal => simp [bodyChecked] at checked
                                      | ok bodyResult =>
                                          obtain ⟨body₅, bodyIds, bodyIds'⟩ := bodyResult
                                          simp only [bodyChecked] at checked
                                          cases yieldedE : operandIds bodyIds loop.yielded with
                                          | none => simp [yieldedE] at checked
                                          | some yieldedIds =>
                                              cases yieldedR : operandIds bodyIds' loop'.yielded with
                                              | none => simp [yieldedE, yieldedR] at checked
                                              | some yieldedIds' =>
                                                  simp only [yieldedE, yieldedR] at checked
                                                  by_cases yieldedOk : yieldedIds = yieldedIds' ∧
                                                      yieldedIds.map body₅.sort? = sorts.map some
                                                  · obtain ⟨yieldedSame, yieldedSorts⟩ := yieldedOk
                                                    subst yieldedSame
                                                    simp [yieldedSorts] at checked
                                                    exact loop_step context challenge helpers fuel scope holds calls
                                                      maximumEq foundE foundR sortsFound outersE outersR indexed
                                                      carriedLeaves bodyChecked yieldedE yieldedR yieldedSorts checked
                                                      continues
                                                  · simp only [yieldedOk, ite_false] at checked
                                                    cases checked
                        · simp only [equal, ite_false] at checked
                          cases checked
          · simp only [header, ite_false] at checked
            cases checked

/-- Accepted scopes and anchors are sound at every fuel. -/
theorem sound_at : ∀ fuel, ScopeSound context challenge helpers fuel ∧ AnchorSound context challenge helpers fuel
  | 0 => sound_zero context challenge helpers
  | fuel + 1 =>
      ⟨scopeSound_succ context challenge helpers fuel (sound_at fuel).1 (sound_at fuel).2,
        anchorSound_succ context challenge helpers fuel (sound_at fuel).1⟩

/-- The normalization check is sound: on inputs of the declared sorts, with
helpers that return values of their declared result sorts, accepted programs
have equal ideal meanings, in every monad and for every challenge function.
Equal outcomes, stop reasons and unread proofs follow, and so does the same
sequence of challenge calls with the same histories. -/
theorem checkNormalized_sound {inputs : List ValueSort} {exported : List Instruction}
    {exportedReturned : List Nat} {reading : List Instruction} {readingReturned : List Nat}
    {result : Terms × List Nat × List Nat}
    (accepted : checkNormalized inputs exported exportedReturned reading readingReturned = .ok result)
    (helpersSorted : ∀ call ∈ Instruction.callList exported, HelperSorted helpers call.1 call.2)
    (env : List (Value F G)) (sorted : SortedValues env inputs) (proof : Proof F G) :
    ideal context challenge helpers readingReturned reading env proof =
      ideal context challenge helpers exportedReturned exported env proof := by
  unfold checkNormalized at accepted
  obtain ⟨⟨more, grown⟩, lengths, bounded, entries⟩ := Terms.leaves_spec .outer inputs [] 0
  have fresh := Terms.leaves_new .outer inputs [] 0
  generalize Terms.leaves [] .outer inputs 0 = initial at accepted grown lengths bounded entries fresh
  obtain ⟨terms, initialIds⟩ := initial
  simp only [List.nil_append] at accepted grown lengths bounded entries fresh
  subst grown
  cases checked : checkScope (Instruction.sizeList exported + Instruction.sizeList reading + 1) terms initialIds
      exported initialIds reading 0 with
  | error refusal => simp [checked] at accepted
  | ok final =>
      obtain ⟨terms', exportedIds, readingIds⟩ := final
      simp only [checked] at accepted
      cases returnedE : operandIds exportedIds exportedReturned with
      | none => simp [returnedE] at accepted
      | some returned =>
          cases returnedR : operandIds readingIds readingReturned with
          | none => simp [returnedE, returnedR] at accepted
          | some returned' =>
              simp only [returnedE, returnedR] at accepted
              by_cases same : returned = returned'
              · subst same
                set valuation : Valuation F G := ⟨fun position => env[position]?, none, [], []⟩
                have leafValue : ∀ (id : Nat) (entry : Node × ValueSort), terms[id]? = some entry →
                    ∃ position sort, inputs[position]? = some sort ∧ entry = (.leaf (.outer position), sort) ∧
                      terms.eval valuation id = env[position]? := by
                  intro id entry found
                  obtain ⟨position, sort, sortFound, rfl⟩ := fresh id entry (Nat.zero_le _) found
                  refine ⟨position, sort, sortFound, by simp, ?_⟩
                  rw [eval_node found (by simp [Node.operands])]
                  simp [Node.value, Leaf.value, valuation]
                have denotes : Denotes terms valuation initialIds env := by
                  refine ⟨by rw [lengths, sorted.1], fun position id found => ?_⟩
                  have inside : position < inputs.length := by
                    rw [← lengths]; exact (List.getElem?_eq_some_iff.mp found).1
                  have entry := entries position id inputs[position] found (List.getElem?_eq_getElem inside)
                  obtain ⟨position', sort, -, equal, value⟩ := leafValue id _ entry
                  simp only [Prod.mk.injEq, Node.leaf.injEq, Leaf.outer.injEq, Nat.zero_add] at equal
                  rw [value, ← equal.1]
                have holds : Holds terms valuation 0 initialIds env initialIds env := by
                  refine ⟨denotes, denotes, bounded, bounded, ?_, ?_, ?_, rfl⟩
                  · intro id node sort found operand member
                    obtain ⟨position, sort', -, equal, -⟩ := leafValue id _ found
                    simp only [Prod.mk.injEq] at equal
                    rw [equal.1] at member
                    simp [Node.operands] at member
                  · intro id node sort value found evaluated
                    obtain ⟨position, sort', sortFound, equal, valueEq⟩ := leafValue id _ found
                    simp only [Prod.mk.injEq] at equal
                    obtain ⟨-, rfl⟩ := equal
                    rw [valueEq] at evaluated
                    exact sorted.2 position value sort evaluated sortFound
                  · intro id leafAnchor position sort found
                    obtain ⟨position', sort', -, equal, -⟩ := leafValue id _ found
                    simp at equal
                symm
                unfold ideal
                refine (sound_at context challenge helpers _).1 terms initialIds exported initialIds reading 0 terms'
                  exportedIds readingIds checked helpersSorted valuation env env proof _ _ _ holds ?_
                intro valuation' anchor' exportedEnv readingEnv unread finalHolds
                obtain ⟨valuesE, readE, evalE⟩ := finalHolds.exported.read_some returnedE
                obtain ⟨valuesR, readR, evalR⟩ := finalHolds.reading.read_some returnedR
                rw [evalE, Option.some.injEq] at evalR
                subst evalR
                simp only [finish, readE, readR]
              · simp [same] at accepted

end Sound

/-! ## Dependency discipline -/

/-- Every pure value held at a position is computed from values held at earlier
positions: the operands of the term at each position are held at earlier
positions. -/
@[reducible] def Flows (terms : Terms) (ids : List Nat) : Prop :=
  ∀ (position id : Nat) (node : Node) (sort : ValueSort), ids[position]? = some id →
    terms[id]? = some (node, sort) → ∀ operand ∈ node.operands, ∃ earlier < position, ids[earlier]? = some operand

/-- The term `id` is computed, directly or through other terms, from the term
`target`. -/
inductive Depends (terms : Terms) : Nat → Nat → Prop
  | refl (id : Nat) : Depends terms id id
  | step {id operand target : Nat} {node : Node} {sort : ValueSort} :
      terms[id]? = some (node, sort) → operand ∈ node.operands → Depends terms operand target →
        Depends terms id target

/-- Under the discipline, every term a held value depends on is held at that
position or earlier. -/
theorem Flows.depends {terms : Terms} {ids : List Nat} (flows : Flows terms ids) {id target : Nat}
    (depends : Depends terms id target) :
    ∀ {position : Nat}, ids[position]? = some id → ∃ earlier ≤ position, ids[earlier]? = some target := by
  induction depends with
  | refl id => exact fun {position} found => ⟨position, Nat.le_refl _, found⟩
  | step entry member _ continues =>
      intro position found
      obtain ⟨earlier, lt, earlierFound⟩ := flows position _ _ _ found entry _ member
      obtain ⟨earliest, le, earliestFound⟩ := continues earlierFound
      exact ⟨earliest, by omega, earliestFound⟩

theorem Flows.grow {terms more : Terms} {ids : List Nat} (flows : Flows terms ids) (bounded : Bounded terms ids) :
    Flows (terms ++ more) ids := by
  intro position id node sort found entry
  have within := bounded id (List.mem_of_getElem? found)
  rw [List.getElem?_append_left within] at entry
  exact flows position id node sort found entry

theorem Flows.push {terms : Terms} {ids : List Nat} {id : Nat} (flows : Flows terms ids)
    (held : ∀ (node : Node) (sort : ValueSort), terms[id]? = some (node, sort) → ∀ operand ∈ node.operands,
      ∃ earlier < ids.length, ids[earlier]? = some operand) :
    Flows terms (ids ++ [id]) := by
  intro position id' node sort found entry operand member
  by_cases old : position < ids.length
  · rw [List.getElem?_append_left old] at found
    obtain ⟨earlier, lt, earlierFound⟩ := flows position id' node sort found entry operand member
    exact ⟨earlier, lt, by rw [List.getElem?_append_left (by omega)]; exact earlierFound⟩
  · rw [List.getElem?_append_right (by omega)] at found
    have small : position - ids.length < 1 := (List.getElem?_eq_some_iff.mp found).1
    have same : position = ids.length := by omega
    subst same
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at found
    subst found
    obtain ⟨earlier, lt, earlierFound⟩ := held node sort entry operand member
    exact ⟨earlier, lt, by rw [List.getElem?_append_left lt]; exact earlierFound⟩

theorem Flows.append_leaves {terms : Terms} :
    ∀ {ids results : List Nat}, Flows terms ids →
      (∀ id ∈ results, ∀ (node : Node) (sort : ValueSort), terms[id]? = some (node, sort) → node.operands = []) →
      Flows terms (ids ++ results)
  | ids, [], flows, _ => by simpa using flows
  | ids, id :: results, flows, leaves => by
      have pushed : Flows terms (ids ++ [id]) := flows.push fun node sort entry operand member => by
        rw [leaves id List.mem_cons_self node sort entry] at member
        cases member
      have appended := Flows.append_leaves (ids := ids ++ [id]) (results := results) pushed
        (fun id' member => leaves id' (List.mem_cons_of_mem _ member))
      simpa using appended

theorem operandIds_held {ids : List Nat} :
    ∀ {operands operandIds' : List Nat}, operandIds ids operands = some operandIds' →
      ∀ id ∈ operandIds', ∃ position < ids.length, ids[position]? = some id
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
              · exact ⟨operand, (List.getElem?_eq_some_iff.mp first).1, first⟩
              · exact operandIds_held (operands := operands) rest id' member

/-- A recorded term's operands are held at positions before it. -/
theorem term_flow {terms : Terms} {ids : List Nat} {anchor : Nat} {instruction : Instruction}
    {terms' : Terms} {id : Nat} (movable : Instruction.movable instruction = true)
    (term : terms.term ids anchor instruction = .ok (terms', id)) :
    (∃ more, terms' = terms ++ more) ∧ id < terms'.length ∧
      ∀ (node : Node) (sort : ValueSort), terms'[id]? = some (node, sort) → ∀ operand ∈ node.operands,
        ∃ earlier < ids.length, ids[earlier]? = some operand := by
  rcases (movable_iff instruction).mp movable with
    ⟨calculation, operands, results, rfl, -⟩ | ⟨results, rfl⟩ | ⟨coordinates, index, results, rfl⟩
  · simp only [Terms.term] at term
    cases found : operandIds ids operands with
    | none => simp [found] at term
    | some operandIds' =>
        cases resultsEq : calculation.op.results with
        | nil => simp [found, resultsEq] at term
        | cons result more =>
            cases more with
            | cons => simp [found, resultsEq] at term
            | nil =>
                simp only [found, resultsEq] at term
                split at term
                · simp only [Except.ok.injEq] at term
                  obtain ⟨rfl, rfl⟩ : (terms.intern (.calculate calculation operandIds', .data result)).1 = terms' ∧
                      (terms.intern (.calculate calculation operandIds', .data result)).2 = id := by
                    rw [term]; exact ⟨rfl, rfl⟩
                  obtain ⟨within, entry, grown⟩ :=
                    Terms.intern_spec terms (.calculate calculation operandIds', .data result)
                  refine ⟨grown, within, fun node sort found' operand member => ?_⟩
                  rw [entry, Option.some.injEq, Prod.mk.injEq] at found'
                  obtain ⟨rfl, -⟩ := found'
                  exact operandIds_held found operand member
                · cases term
  · simp only [Terms.term, Except.ok.injEq] at term
    obtain ⟨rfl, rfl⟩ : (terms.intern (.indicesEmpty, .indices)).1 = terms' ∧
        (terms.intern (.indicesEmpty, .indices)).2 = id := by
      rw [term]; exact ⟨rfl, rfl⟩
    obtain ⟨within, entry, grown⟩ := Terms.intern_spec terms (.indicesEmpty, .indices)
    refine ⟨grown, within, fun node sort found' operand member => ?_⟩
    rw [entry, Option.some.injEq, Prod.mk.injEq] at found'
    obtain ⟨rfl, -⟩ := found'
    simp [Node.operands] at member
  · simp only [Terms.term] at term
    cases coordinatesFound : ids[coordinates]? with
    | none => simp [coordinatesFound] at term
    | some coordinatesId =>
        cases indexFound : ids[index]? with
        | none => simp [coordinatesFound, indexFound] at term
        | some indexId =>
            simp only [coordinatesFound, indexFound, Except.ok.injEq] at term
            obtain ⟨rfl, rfl⟩ : (terms.intern (.indicesAppend coordinatesId indexId, .indices)).1 = terms' ∧
                (terms.intern (.indicesAppend coordinatesId indexId, .indices)).2 = id := by
              rw [term]; exact ⟨rfl, rfl⟩
            obtain ⟨within, entry, grown⟩ := Terms.intern_spec terms (.indicesAppend coordinatesId indexId, .indices)
            refine ⟨grown, within, fun node sort found' operand member => ?_⟩
            rw [entry, Option.some.injEq, Prod.mk.injEq] at found'
            obtain ⟨rfl, -⟩ := found'
            simp only [Node.operands, List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl
            · exact ⟨coordinates, (List.getElem?_eq_some_iff.mp coordinatesFound).1, coordinatesFound⟩
            · exact ⟨index, (List.getElem?_eq_some_iff.mp indexFound).1, indexFound⟩

theorem advance_flow {anchor : Nat} :
    ∀ {program : List Instruction} {terms : Terms} {ids : List Nat} {terms' : Terms} {ids' : List Nat}
      {rest : List Instruction}, advance anchor terms ids program = .ok (terms', ids', rest) →
      Bounded terms ids → Flows terms ids →
        (∃ more, terms' = terms ++ more) ∧ Bounded terms' ids' ∧ Flows terms' ids'
  | [], terms, ids, terms', ids', rest, advanced, bounded, flows => by
      simp only [advance, Except.ok.injEq, Prod.mk.injEq] at advanced
      obtain ⟨rfl, rfl, rfl⟩ := advanced
      exact ⟨⟨[], by simp⟩, bounded, flows⟩
  | instruction :: program, terms, ids, terms', ids', rest, advanced, bounded, flows => by
      simp only [advance] at advanced
      split at advanced
      · rename_i movable
        cases termed : terms.term ids anchor instruction with
        | error refusal => simp [termed] at advanced
        | ok result =>
            obtain ⟨terms₁, id⟩ := result
            simp only [termed] at advanced
            obtain ⟨⟨more, grown⟩, within, held⟩ := term_flow movable termed
            have bounded₁ : Bounded terms₁ (ids ++ [id]) := by
              intro id' member
              rcases List.mem_append.mp member with member | member
              · rw [grown]; exact bounded.append id' member
              · simp only [List.mem_singleton] at member
                subst member
                exact within
            have flows₀ : Flows terms₁ ids := by rw [grown]; exact flows.grow bounded
            obtain ⟨⟨more', grown'⟩, bounded', flows'⟩ := advance_flow advanced bounded₁ (flows₀.push held)
            exact ⟨⟨more ++ more', by rw [grown', grown, List.append_assoc]⟩, bounded', flows'⟩
      · simp only [Except.ok.injEq, Prod.mk.injEq] at advanced
        obtain ⟨rfl, rfl, rfl⟩ := advanced
        exact ⟨⟨[], by simp⟩, bounded, flows⟩

/-- An accepted anchor's results are fresh leaves of the scope's table. -/
theorem checkAnchor_leaves {fuel : Nat} {terms : Terms} {exportedIds : List Nat} {first : Instruction}
    {readingIds : List Nat} {first' : Instruction} {anchor : Nat} {terms' : Terms} {resultIds : List Nat}
    (checked : checkAnchor fuel terms exportedIds first readingIds first' anchor = .ok (terms', resultIds)) :
    ∃ sorts, terms.leaves (.result anchor) sorts 0 = (terms', resultIds) := by
  cases fuel with
  | zero => simp [checkAnchor] at checked
  | succ fuel =>
      simp only [checkAnchor] at checked
      repeat' split at checked
      all_goals first
        | exact ⟨_, Except.ok.inj checked⟩
        | cases checked

/-- Both programs' positions keep the discipline through an accepted scope. -/
theorem checkScope_flow : ∀ (fuel : Nat) {terms : Terms} {exportedIds : List Nat} {exported : List Instruction}
    {readingIds : List Nat} {reading : List Instruction} {anchor : Nat} {terms' : Terms}
    {exportedIds' readingIds' : List Nat},
    checkScope fuel terms exportedIds exported readingIds reading anchor = .ok (terms', exportedIds', readingIds') →
    Bounded terms exportedIds → Bounded terms readingIds → Flows terms exportedIds → Flows terms readingIds →
      Flows terms' exportedIds' ∧ Flows terms' readingIds'
  | 0, _, _, _, _, _, _, _, _, _, checked, _, _, _, _ => by simp [checkScope] at checked
  | fuel + 1, terms, exportedIds, exported, readingIds, reading, anchor, terms', exportedIds', readingIds', checked,
      boundedE₀, boundedR₀, flowsE₀, flowsR₀ => by
      simp only [checkScope] at checked
      cases advancedE : advance anchor terms exportedIds exported with
      | error refusal => simp [advancedE] at checked
      | ok resultE =>
        obtain ⟨terms₁, exportedIds₁, exported₁⟩ := resultE
        simp only [advancedE] at checked
        cases advancedR : advance anchor terms₁ readingIds reading with
        | error refusal => simp [advancedR] at checked
        | ok resultR =>
          obtain ⟨terms₂, readingIds₁, reading₁⟩ := resultR
          simp only [advancedR] at checked
          obtain ⟨⟨moreE, grownE⟩, boundedE₁, flowsE₁⟩ := advance_flow advancedE boundedE₀ flowsE₀
          have boundedR₁ : Bounded terms₁ readingIds := by rw [grownE]; exact boundedR₀.append
          have flowsR₁ : Flows terms₁ readingIds := by rw [grownE]; exact flowsR₀.grow boundedR₀
          obtain ⟨⟨moreR, grownR⟩, boundedR₂, flowsR₂⟩ := advance_flow advancedR boundedR₁ flowsR₁
          have boundedE₂ : Bounded terms₂ exportedIds₁ := by rw [grownR]; exact boundedE₁.append
          have flowsE₂ : Flows terms₂ exportedIds₁ := by rw [grownR]; exact flowsE₁.grow boundedE₁
          cases exported₁ with
          | nil =>
              cases reading₁ with
              | nil =>
                  simp only [Except.ok.injEq, Prod.mk.injEq] at checked
                  obtain ⟨rfl, rfl, rfl⟩ := checked
                  exact ⟨flowsE₂, flowsR₂⟩
              | cons => simp at checked
          | cons first exportedRest =>
              cases reading₁ with
              | nil => simp at checked
              | cons first' readingRest =>
                  simp only at checked
                  cases anchored : checkAnchor fuel terms₂ exportedIds₁ first readingIds₁ first' anchor with
                  | error refusal => simp [anchored] at checked
                  | ok resultA =>
                      obtain ⟨terms₃, resultIds⟩ := resultA
                      simp only [anchored] at checked
                      obtain ⟨sorts, leaves⟩ := checkAnchor_leaves anchored
                      have spec := Terms.leaves_spec (.result anchor) sorts terms₂ 0
                      simp only [leaves] at spec
                      obtain ⟨⟨more, grown⟩, lengths, boundedResults, entries⟩ := spec
                      have leafResults : ∀ id ∈ resultIds, ∀ (node : Node) (sort : ValueSort),
                          terms₃[id]? = some (node, sort) → node.operands = [] := by
                        intro id member node sort found
                        obtain ⟨position, positionFound⟩ := List.mem_iff_getElem?.mp member
                        have inside : position < sorts.length := by
                          rw [← lengths]; exact (List.getElem?_eq_some_iff.mp positionFound).1
                        have entry := entries position id sorts[position] positionFound
                          (List.getElem?_eq_getElem inside)
                        rw [entry, Option.some.injEq, Prod.mk.injEq] at found
                        rw [← found.1]
                        rfl
                      have extend : ∀ {ids : List Nat}, Bounded terms₂ ids → Flows terms₂ ids →
                          Bounded terms₃ (ids ++ resultIds) ∧ Flows terms₃ (ids ++ resultIds) := by
                        intro ids bounded flows
                        refine ⟨fun id member => ?_, ?_⟩
                        · rcases List.mem_append.mp member with member | member
                          · rw [grown]; exact bounded.append id member
                          · exact boundedResults id member
                        · have grownFlows : Flows terms₃ ids := by rw [grown]; exact flows.grow bounded
                          exact grownFlows.append_leaves leafResults
                      obtain ⟨boundedE₃, flowsE₃⟩ := extend boundedE₂ flowsE₂
                      obtain ⟨boundedR₃, flowsR₃⟩ := extend boundedR₂ flowsR₂
                      exact checkScope_flow fuel checked boundedE₃ boundedR₃ flowsE₃ flowsR₃

/-- The dependency discipline of accepted programs. In the final table, every
term a value of either program depends on is held by that program at the
value's position or earlier. So a pure value the reading first computes after
an anchor is none of the terms that anchor's operands depend on: moving a value
past its consumer is refused. -/
theorem checkNormalized_flow {inputs : List ValueSort} {exported : List Instruction}
    {exportedReturned : List Nat} {reading : List Instruction} {readingReturned : List Nat} {terms : Terms}
    {exportedIds readingIds : List Nat}
    (accepted : checkNormalized inputs exported exportedReturned reading readingReturned =
      .ok (terms, exportedIds, readingIds)) :
    (∀ (position id target : Nat), readingIds[position]? = some id → Depends terms id target →
      ∃ earlier ≤ position, readingIds[earlier]? = some target) ∧
    (∀ (position id target : Nat), exportedIds[position]? = some id → Depends terms id target →
      ∃ earlier ≤ position, exportedIds[earlier]? = some target) := by
  unfold checkNormalized at accepted
  obtain ⟨⟨more, grown⟩, lengths, bounded, entries⟩ := Terms.leaves_spec .outer inputs [] 0
  generalize Terms.leaves [] .outer inputs 0 = initial at accepted grown lengths bounded entries
  obtain ⟨initialTerms, initialIds⟩ := initial
  simp only [List.nil_append] at accepted grown lengths bounded entries
  subst grown
  have flows : Flows initialTerms initialIds := by
    have appended := Flows.append_leaves (terms := initialTerms) (ids := []) (results := initialIds)
      (fun _ _ _ _ found => by simp at found) (by
        intro id member node sort found
        obtain ⟨position, positionFound⟩ := List.mem_iff_getElem?.mp member
        have inside : position < inputs.length := by
          rw [← lengths]; exact (List.getElem?_eq_some_iff.mp positionFound).1
        have entry := entries position id inputs[position] positionFound (List.getElem?_eq_getElem inside)
        rw [entry, Option.some.injEq, Prod.mk.injEq] at found
        rw [← found.1]
        rfl)
    simpa using appended
  cases checked : checkScope (Instruction.sizeList exported + Instruction.sizeList reading + 1) initialTerms initialIds
      exported initialIds reading 0 with
  | error refusal => simp [checked] at accepted
  | ok final =>
      obtain ⟨terms', exportedIds', readingIds'⟩ := final
      simp only [checked] at accepted
      obtain ⟨flowsE, flowsR⟩ := checkScope_flow _ checked bounded bounded flows flows
      have same : terms' = terms ∧ exportedIds' = exportedIds ∧ readingIds' = readingIds := by
        split at accepted
        · split at accepted
          · simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
            exact accepted
          · cases accepted
        · cases accepted
      obtain ⟨rfl, rfl, rfl⟩ := same
      exact ⟨fun position id target found depends => flowsR.depends depends found,
        fun position id target found depends => flowsE.depends depends found⟩

/-! ## The lowering rule -/

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Inputs the executable admits, followed by the host's transcript, have the
validator's declared input sorts. -/
theorem admits_sorted {validator : Validator} {data : List (Value F G)} (admitted : validator.admits data = true)
    (history : History F G) :
    SortedValues (data ++ [.transcript history]) (validator.inputs.map (·.2.sort)) := by
  obtain ⟨suite, sorts, sortsEq, dataSorts⟩ := admits_sorts validator admitted
  have lengths : sorts.length = data.length := by simpa using congrArg List.length dataSorts
  rw [sortsEq]
  refine ⟨by simp [lengths], fun index value sort found sortFound => ?_⟩
  rcases Nat.lt_or_ge index data.length with lt | ge
  · rw [List.getElem?_append_left lt] at found
    rw [List.getElem?_append_left (by omega)] at sortFound
    have reported : dataSort? value = some sort := by
      have := congrArg (·[index]?) dataSorts
      simp only [List.getElem?_map, sortFound, found, Option.map_some] at this
      exact (Option.some.inj this).symm
    exact dataSort_sorted reported
  · rw [List.getElem?_append_right ge] at found
    rw [List.getElem?_append_right (by omega), lengths] at sortFound
    cases offset : index - data.length with
    | zero =>
        simp [offset] at found sortFound
        subst found sortFound
        trivial
    | succ k => simp [offset] at found

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- A helper of a closed table returns values of its declared output types. -/
theorem helperSorted_of_outputs {table : Structured.Evaluation.Meanings F G Structured.closedInterface}
    {name : String} {declared : List ValueSort}
    (outputs : ∀ entry, table.find? (fun entry => entry.helper.name == name) = some entry →
      entry.helper.outputs.map .data = declared) :
    HelperSorted table name declared := by
  intro arguments values called lengths
  unfold callHelper at called
  cases found : table.find? (fun entry => entry.helper.name == name) with
  | none => simp [found] at called
  | some entry =>
      simp only [found] at called
      cases decoded : decodeValues entry.helper.inputs arguments with
      | none => simp [decoded] at called
      | some decodedValues =>
          simp only [decoded] at called
          cases invoked : closedOutcome (entry.invoke decodedValues) with
          | stopped => simp [invoked] at called
          | returned results =>
              simp only [invoked, PIR.Outcome.returned.injEq] at called
              subst called
              rw [← outputs entry found]
              exact ⟨by simp [encodeValues_length], encodeValues_sorted results⟩

/-- What the per-compile rule establishes when it accepts: the reading, the
agreeing interface, and equal ideal meanings of the reading and the constructed
validator, on inputs of its sorts, with helpers that return values of their
declared result sorts. -/
theorem checkLowering_sound {vocabulary : Vocabulary} {participant : Participant} {validator : Validator}
    {L : Lowered} (accepted : checkLowering vocabulary participant validator = .ok L) :
    validator.read vocabulary (Instruction.helpers participant.instructions) = .ok L ∧
      (∀ {m : Type → Type} [Monad m] (context : Context) (challenge : History F G → m F)
        (helpers : Structured.Evaluation.Meanings F G Structured.closedInterface),
        (∀ call ∈ Instruction.callList participant.instructions, HelperSorted helpers call.1 call.2) →
        ∀ (env : List (Value F G)), SortedValues env participant.inputs → ∀ (proof : Proof F G),
          ideal context challenge helpers L.returned (Code.instructions L.code) env proof =
            ideal context challenge helpers participant.returned participant.instructions env proof) ∧
      validator.inputs.map (·.2.sort) = participant.inputs ∧
      validator.results.map (·.sort) = participant.outputs ∧ validator.symbol = participant.symbol ∧
      validator.entry = participant.policy.entry ∧ validator.role = participant.policy.validator := by
  obtain ⟨reading, same, inputs, outputs, symbol, entry, role⟩ := checkLowering_spec accepted
  refine ⟨reading, ?_, inputs, outputs, symbol, entry, role⟩
  intro m _ context challenge helpers helpersSorted env sorted proof
  rcases same with ⟨code, returned⟩ | ⟨normalized, checked⟩
  · rw [code, returned]
  · exact checkNormalized_sound context challenge helpers checked helpersSorted env sorted proof

/-- Host validation prunes, at every budget and with every framing header, the
ideal acceptance of the constructed validator on the decoded proof. -/
theorem validate_prunes_export {m : Type → Type} [Monad m] [LawfulMonad m] (vocabulary : Vocabulary)
    (validator : Validator) (context : Context) (challenge : History F G → m F)
    (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat) {participant : Participant}
    {L : Lowered} (accepted : checkLowering vocabulary participant validator = .ok L)
    (prepared : ∀ name ∈ Instruction.helpers participant.instructions, Prepared vocabulary validator table name)
    (helpersSorted : ∀ call ∈ Instruction.callList participant.instructions, HelperSorted table call.1 call.2)
    (binding : List UInt8) (acceptance : Nat) (data : List (Value F G)) (history : History F G)
    (bytes : List UInt8) (admitted : validator.admits data = true) :
    Prunes (fun accepted => accepted = false)
      (validate vocabulary validator context challenge decode budget binding acceptance data history bytes)
      ((fun result => Accepts acceptance (idealObservation result)) <$>
        ideal context challenge table participant.returned participant.instructions (data ++ [.transcript history])
          (decodeProof decode (Plan.types data L.plan) (bytes.drop 40))) := by
  obtain ⟨reading, same, inputs, -⟩ := checkLowering_sound (F := F) (G := G) accepted
  have pruned := validate_prunes vocabulary validator context challenge table decode budget _ prepared reading
    binding acceptance data history bytes admitted
  have sorted := admits_sorted admitted history
  rw [inputs] at sorted
  rwa [same context challenge table helpersSorted _ sorted] at pruned

end Eval

end Zkc.Executable
