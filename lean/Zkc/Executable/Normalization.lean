module

public import Zkc.Executable.Refusal
public import Zkc.Construction.Scalar

@[expose] public section

/-! Checked normalization of pure total calculations.

The compiler may reschedule pure arithmetic: the constructed export computes a
value where the source does, while the program computes it in a calculation
call placed before its first consumer. The lowering rule then compares the two
programs not instruction by instruction but by their normal forms.

* An instruction is *movable* when it is a calculation that never stops on
  operands of its declared sorts, or occurrence-coordinate construction
  (`Instruction.movable`, `movable_iff`). Every other instruction is an
  *anchor*: receives, transcript operations, guards, helper calls, loops,
  calculations that can stop and anything unsupported.
* A movable instruction denotes a pure term over the inputs, the results of
  earlier anchors and the enclosing loop's index and carried values. Terms are
  kept in one hash-consed table per scope (`Terms`), so that equal terms of
  either program have the same id.
* `checkScope` walks both programs anchor by anchor against one table. Before
  each anchor it records the movable instructions of either program as terms;
  the two anchors must have the same operation and declared results, and their
  operands must denote the same terms. A loop's body is a scope of its own,
  checked the same way, whose yields must denote the same terms at the carried
  sorts. `checkNormalized` adds the returned terms.

Accepted are operand renumbering, every schedule of pure computations that
respects their dependencies, sharing of equal terms and dropping or adding terms
that reach no anchor. Refused are a changed anchor sequence, an operand that
denotes another term, an ill-sorted calculation and work moved into or out of a
loop body, since a body's terms live in its own table.

`checkNormalized_sound` states that accepted programs have equal ideal
meanings, in every monad and for every challenge function, on inputs of the
declared sorts, when every called helper returns values of its declared result
sorts. `checkNormalized_flow` states the dependency discipline: every term an
anchor's operands depend on is computed by the program before that anchor.
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction Zkc.Source

/-! ## What may move -/

/-- Instructions normalization may reschedule: calculations that never stop on
operands of their declared sorts, and occurrence-coordinate construction. -/
def Instruction.movable : Instruction → Bool
  | ⟨.calculate calculation, _, _, []⟩ => calculation.total
  | ⟨.indicesEmpty, [], _, []⟩ => true
  | ⟨.indicesAppend, [_, _], _, []⟩ => true
  | _ => false

/-- The movable instructions are exactly total calculations and well-formed
occurrence-coordinate construction; no other instruction form is movable. -/
theorem movable_iff (instruction : Instruction) :
    Instruction.movable instruction = true ↔
      (∃ calculation operands results, instruction = ⟨.calculate calculation, operands, results, []⟩ ∧
        calculation.total = true) ∨
      (∃ results, instruction = ⟨.indicesEmpty, [], results, []⟩) ∨
      (∃ coordinates index results, instruction = ⟨.indicesAppend, [coordinates, index], results, []⟩) := by
  constructor
  · intro movable
    rcases instruction with ⟨operation, operands, results, body⟩
    cases body with
    | cons _ _ => cases operation <;> simp [Instruction.movable] at movable
    | nil =>
        cases operation with
        | calculate calculation =>
            exact .inl ⟨calculation, operands, results, rfl, by simpa [Instruction.movable] using movable⟩
        | indicesEmpty =>
            cases operands with
            | nil => exact .inr (.inl ⟨results, rfl⟩)
            | cons _ _ => simp [Instruction.movable] at movable
        | indicesAppend =>
            rcases operands with _ | ⟨coordinates, _ | ⟨index, _ | ⟨_, _⟩⟩⟩
            · simp [Instruction.movable] at movable
            · simp [Instruction.movable] at movable
            · exact .inr (.inr ⟨coordinates, index, results, rfl⟩)
            · simp [Instruction.movable] at movable
        | _ => simp [Instruction.movable] at movable
  · rintro (⟨calculation, operands, results, rfl, total⟩ | ⟨results, rfl⟩ | ⟨coordinates, index, results, rfl⟩)
    · simpa [Instruction.movable] using total
    · rfl
    · rfl

/-- Every calculation has exactly one result. -/
theorem Calculation.single (calculation : Calculation) : calculation.op.results.length = 1 := by
  cases calculation <;> rfl

/-! ## Terms -/

/-- A leaf of a scope's terms: a value of the enclosing scope (at the top, an
input position), the loop index, a carried value, or a result of an earlier
anchor. -/
inductive Leaf where
  | outer (key : Nat)
  | index
  | carried (position : Nat)
  | result (anchor position : Nat)
  deriving DecidableEq, Repr

/-- A node of a scope's terms. Operands are ids of earlier nodes. -/
inductive Node where
  | leaf (leaf : Leaf)
  | calculate (calculation : Calculation) (operands : List Nat)
  | indicesEmpty
  | indicesAppend (coordinates index : Nat)
  deriving DecidableEq, Repr

/-- Compare two nodes, operand ids before calculations, whose domain strings
are compared only when the operands agree. -/
def Node.same : Node → Node → Bool
  | .leaf found, .leaf found' => found == found'
  | .calculate calculation operands, .calculate calculation' operands' =>
      operands == operands' && calculation == calculation'
  | .indicesEmpty, .indicesEmpty => true
  | .indicesAppend coordinates index, .indicesAppend coordinates' index' =>
      coordinates == coordinates' && index == index'
  | _, _ => false

theorem Node.same_iff (node node' : Node) : node.same node' = true ↔ node = node' := by
  cases node <;> cases node' <;> simp [Node.same, and_comm]

/-- A scope's hash-consed table of pure terms: the node and the sort of every
id, in allocation order. -/
abbrev Terms := List (Node × ValueSort)

/-- The id of an entry, allocated when absent. -/
def Terms.intern (terms : Terms) (entry : Node × ValueSort) : Terms × Nat :=
  match terms.findIdx? (fun found => found.1.same entry.1 && found.2 == entry.2) with
  | some id => (terms, id)
  | none => (terms ++ [entry], terms.length)

/-- The sort of an id. -/
def Terms.sort? (terms : Terms) (id : Nat) : Option ValueSort := (terms[id]?).map (·.2)

/-- The ids of leaves for consecutive positions, from `first`, at the given
sorts. -/
def Terms.leaves (terms : Terms) (leaf : Nat → Leaf) : List ValueSort → Nat → Terms × List Nat
  | [], _ => (terms, [])
  | sort :: sorts, first =>
      match terms.intern (.leaf (leaf first), sort) with
      | (terms', id) =>
          match terms'.leaves leaf sorts (first + 1) with
          | (terms'', ids) => (terms'', id :: ids)

/-- The ids of the enclosing scope's values as leaves of a loop body. -/
def Terms.outers (terms : Terms) (enclosing : Terms) : List Nat → Option (Terms × List Nat)
  | [] => some (terms, [])
  | id :: ids =>
      match enclosing.sort? id with
      | some sort =>
          match terms.intern (.leaf (.outer id), sort) with
          | (terms', id') =>
              match terms'.outers enclosing ids with
              | some (terms'', ids') => some (terms'', id' :: ids')
              | none => none
      | none => none

/-- The ids the given positions hold. -/
def operandIds (ids : List Nat) (operands : List Nat) : Option (List Nat) := operands.mapM (ids[·]?)

/-- Record a movable instruction's term: its operands' ids, checked against the
calculation's signature. -/
def Terms.term (terms : Terms) (ids : List Nat) (anchor : Nat) :
    Instruction → Except Refusal (Terms × Nat)
  | ⟨.calculate calculation, operands, _, _⟩ =>
      match operandIds ids operands, calculation.op.results with
      | some operands', [result] =>
          if operands'.map terms.sort? = calculation.op.arguments.map (some ∘ .data) ∧
              calculation.op.arguments.all dataType then
            .ok (terms.intern (.calculate calculation operands', .data result))
          else .error (.sort anchor)
      | _, _ => .error (.sort anchor)
  | ⟨.indicesEmpty, _, _, _⟩ => .ok (terms.intern (.indicesEmpty, .indices))
  | ⟨.indicesAppend, [coordinates, index], _, _⟩ =>
      match ids[coordinates]?, ids[index]? with
      | some coordinates', some index' => .ok (terms.intern (.indicesAppend coordinates' index', .indices))
      | _, _ => .error (.sort anchor)
  | _ => .error (.sort anchor)

/-- Record the movable instructions at the head of a program, up to its next
anchor. -/
def advance (anchor : Nat) : Terms → List Nat → List Instruction →
    Except Refusal (Terms × List Nat × List Instruction)
  | terms, ids, [] => .ok (terms, ids, [])
  | terms, ids, instruction :: rest =>
      if Instruction.movable instruction then
        match terms.term ids anchor instruction with
        | .ok (terms', id) => advance anchor terms' (ids ++ [id]) rest
        | .error refusal => .error refusal
      else .ok (terms, ids, instruction :: rest)

/-- The sorts of the values an anchor appends when it continues. -/
def Instruction.resultSorts : Instruction → List ValueSort
  | ⟨.receive _ _ _ ty, _, _, _⟩ => [.data ty]
  | ⟨.observe suite _, _, _, _⟩ => [.transcript suite]
  | ⟨.challenge suite field _, _, _, _⟩ => [.data (.field field), .transcript suite]
  | ⟨.calculate calculation, _, _, _⟩ => calculation.op.results.map .data
  | ⟨.indicesEmpty, _, _, _⟩ => [.indices]
  | ⟨.indicesAppend, _, _, _⟩ => [.indices]
  | ⟨.call _, _, results, _⟩ => results
  | _ => []

/-- Whether an operation is a loop. -/
def loopOperation : Operation → Bool
  | .loop _ _ _ => true
  | _ => false

/-- The parts of a loop instruction with a count operand. -/
structure LoopParts where
  site : String
  maximum : Nat
  yielded : List Nat
  count : Nat
  initial : List Nat
  results : List ValueSort
  body : List Instruction

/-- The parts of a loop instruction with a count operand, if it is one. -/
def Instruction.loopParts : Instruction → Option LoopParts
  | ⟨.loop site maximum yielded, count :: initial, results, body⟩ =>
      some ⟨site, maximum, yielded, count, initial, results, body⟩
  | _ => none

theorem Instruction.loopParts_some {instruction : Instruction} {loop : LoopParts}
    (found : Instruction.loopParts instruction = some loop) :
    instruction = ⟨.loop loop.site loop.maximum loop.yielded, loop.count :: loop.initial, loop.results,
      loop.body⟩ := by
  rcases instruction with ⟨operation, operands, results, body⟩
  cases operation <;> rcases operands with _ | ⟨count, initial⟩ <;> simp [Instruction.loopParts] at found
  subst found
  rfl

/-- The position of the first difference of two lists. -/
def firstDifferenceOf : List Nat → List Nat → Nat
  | first :: rest, other :: others => if first = other then firstDifferenceOf rest others + 1 else 0
  | _, _ => 0

mutual
/-- Check one scope of both programs, anchor by anchor, against one table:
before each anchor the movable instructions of either program are recorded as
terms; the anchors must agree. Returns the table and the ids of both programs'
positions at the end. -/
def checkScope : Nat → Terms → List Nat → List Instruction → List Nat → List Instruction → Nat →
    Except Refusal (Terms × List Nat × List Nat)
  | 0, _, _, _, _, _, _ => .error (.unsupported "normalization-depth")
  | fuel + 1, terms, exportedIds, exported, readingIds, reading, anchor =>
      match advance anchor terms exportedIds exported with
      | .error refusal => .error refusal
      | .ok (terms₁, exportedIds₁, exported₁) =>
          match advance anchor terms₁ readingIds reading with
          | .error refusal => .error refusal
          | .ok (terms₂, readingIds₁, reading₁) =>
              match exported₁, reading₁ with
              | [], [] => .ok (terms₂, exportedIds₁, readingIds₁)
              | first :: exportedRest, first' :: readingRest =>
                  match checkAnchor fuel terms₂ exportedIds₁ first readingIds₁ first' anchor with
                  | .error refusal => .error refusal
                  | .ok (terms₃, results) =>
                      checkScope fuel terms₃ (exportedIds₁ ++ results) exportedRest (readingIds₁ ++ results)
                        readingRest (anchor + 1)
              | _, _ => .error (.anchor anchor)

/-- Check one pair of anchors: the same operation and declared results, and
operands denoting the same terms; a loop's bodies are checked as a scope of
their own. Returns the ids of the anchor's results. -/
def checkAnchor : Nat → Terms → List Nat → Instruction → List Nat → Instruction → Nat →
    Except Refusal (Terms × List Nat)
  | 0, _, _, _, _, _, _ => .error (.unsupported "normalization-depth")
  | fuel + 1, terms, exportedIds, first, readingIds, first', anchor =>
      match Instruction.loopParts first, Instruction.loopParts first' with
      | some loop, some loop' =>
          if loop.site = loop'.site ∧ loop.maximum = loop'.maximum ∧ loop.yielded.length = loop'.yielded.length ∧
              loop.results = loop'.results then
            match operandIds exportedIds (loop.count :: loop.initial),
                operandIds readingIds (loop'.count :: loop'.initial) with
            | some (counted :: carried), some operands' =>
                if counted :: carried = operands' then
                  match carried.mapM terms.sort? with
                  | some sorts =>
                      match Terms.outers [] terms exportedIds with
                      | some (body₁, outerIds) =>
                          match body₁.outers terms readingIds with
                          | some (body₂, outerIds') =>
                              match body₂.intern (.leaf .index, .data .index) with
                              | (body₃, indexId) =>
                                  match body₃.leaves .carried sorts 0 with
                                  | (body₄, carriedIds) =>
                                      match checkScope fuel body₄ (outerIds ++ indexId :: carriedIds) loop.body
                                          (outerIds' ++ indexId :: carriedIds) loop'.body 0 with
                                      | .error refusal => .error refusal
                                      | .ok (body₅, bodyIds, bodyIds') =>
                                          match operandIds bodyIds loop.yielded, operandIds bodyIds' loop'.yielded with
                                          | some yieldedIds, some yieldedIds' =>
                                              if yieldedIds = yieldedIds' ∧
                                                  yieldedIds.map body₅.sort? = sorts.map some then
                                                .ok (terms.leaves (.result anchor) sorts 0)
                                              else .error (.yielded anchor)
                                          | _, _ => .error (.yielded anchor)
                          | none => .error (.anchor anchor)
                      | none => .error (.anchor anchor)
                  | none => .error (.anchor anchor)
                else .error (.anchorOperand anchor (firstDifferenceOf (counted :: carried) operands'))
            | _, _ => .error (.anchorOperand anchor 0)
          else .error (.anchor anchor)
      | none, none =>
          if loopOperation first.operation || loopOperation first'.operation then .error (.anchor anchor)
          else if first.operation = first'.operation ∧ first.results = first'.results then
            match operandIds exportedIds first.operands, operandIds readingIds first'.operands with
            | some operands, some operands' =>
                if operands = operands' then .ok (terms.leaves (.result anchor) (Instruction.resultSorts first) 0)
                else .error (.anchorOperand anchor (firstDifferenceOf operands operands'))
            | _, _ => .error (.anchorOperand anchor 0)
          else .error (.anchor anchor)
      | _, _ => .error (.anchor anchor)
end

mutual
/-- The helper calls of instructions, with their declared result sorts, those of
loop bodies included. -/
def Instruction.callList : List Instruction → List (String × List ValueSort)
  | [] => []
  | instruction :: rest => Instruction.callsOf instruction ++ Instruction.callList rest

def Instruction.callsOf : Instruction → List (String × List ValueSort)
  | ⟨.call name, _, results, _⟩ => [(name, results)]
  | ⟨.loop _ _ _, _, _, body⟩ => Instruction.callList body
  | _ => []
end

mutual
/-- The number of instructions, those of loop bodies included. -/
def Instruction.sizeList : List Instruction → Nat
  | [] => 0
  | instruction :: rest => Instruction.sizeOne instruction + Instruction.sizeList rest

def Instruction.sizeOne : Instruction → Nat
  | ⟨_, _, _, body⟩ => 1 + Instruction.sizeList body
end

/-- The normalization check: both programs, on inputs of the given sorts, have
the same anchors in the same order with operands denoting the same terms, and
return the same terms. Returns the table and the ids of both programs' final
positions, which relate their positions by the terms they hold. -/
def checkNormalized (inputs : List ValueSort) (exported : List Instruction) (exportedReturned : List Nat)
    (reading : List Instruction) (readingReturned : List Nat) : Except Refusal (Terms × List Nat × List Nat) :=
  match Terms.leaves [] .outer inputs 0 with
  | (terms, ids) =>
      match checkScope (Instruction.sizeList exported + Instruction.sizeList reading + 1) terms ids exported ids
          reading 0 with
      | .error refusal => .error refusal
      | .ok (terms', exportedIds, readingIds) =>
          match operandIds exportedIds exportedReturned, operandIds readingIds readingReturned with
          | some returned, some returned' =>
              if returned = returned' then .ok (terms', exportedIds, readingIds)
              else .error (.returned (firstDifferenceOf returned returned'))
          | _, _ => .error (.returned 0)

end Zkc.Executable
