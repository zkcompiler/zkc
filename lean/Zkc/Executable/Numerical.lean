module

public import Zkc.Algebra.RingExpression.Basic

@[expose] public section

/-! The physical plan payload of a native numerical call.

The compiler-generated `numerical.map`, `numerical.sum` and `numerical.product`
operations execute one pure field expression over a row domain
(`docs/spec/runtime/numerical.md`). Each binding names its field and an operand
mask of `0` (a scalar) and `1` (a vector) positions; each operation carries a
physical plan as its single text parameter
(`docs/spec/runtime/numerical-plans.md`):

    ["zkc.numerical-plan/0", expression, lanes, slots, locations]

where `expression` is the nested `zkc.ring/0` arena
(`docs/spec/domains/ring-expressions.md`).

`decode` reads that text into a `Zkc.Algebra.RingExpression.Expr` whose
constants are natural literals and whose inputs are operand slots. It accepts
exactly the plans the runtime's program admission accepts for a call over a
field with the given characteristic and operand mask, and refuses every other
payload with a named reason (`Refusal`):

- the plan has at most 16384 bytes of UTF-8 and its expression at most 4096;
- it is the canonical encoding of a plan: the compact array form with canonical
  natural numbers and no escapes, since the runtime refuses a payload that
  differs from the canonical encoding of what it parses; a bare arena is not a
  plan;
- every declared input and every constant of the expression is in the call's
  field, a constant is a canonical decimal below the characteristic, and an
  embedding is refused;
- an input node names a declared input, and every operand points strictly
  backward;
- there are exactly as many declared inputs as mask positions and exactly one
  output, and the output reaches every node;
- `lanes` is from 1 through 256, `slots` from 1 through the node count, and
  `locations` names one slot below `slots` for every node, using every slot;
- the slot schedule is valid (`scheduled`).

The arena's other formation limits (65 536 nodes and inputs, 4096 outputs and
depth 1024) cannot be reached within 4096 bytes. `mask?` reads the mask
argument: at most 1023 positions, each `0` or `1`. These are the static checks
of program admission. The runtime's bound on a call's rows (`rowLimit`) is a
capacity limit of the native call, as the element limit of every vector a native
kernel produces is; the executable meaning does not stop on it.

The plan's lanes and slot locations are a storage proposal. A valid plan
computes the expression it carries at every row, so its meaning is that
expression's; the schedule check refuses a proposal that would read a slot
another node has overwritten.

The tree an arena denotes repeats a shared node at each of its uses; it has the
meaning of the arena, which evaluates each node once.
-/

set_option autoImplicit false

namespace Zkc.Executable.Numerical
open Zkc.Algebra.RingExpression

/-- How a numerical call combines the expression's values at its rows: the
vector of them, their sum or their product. -/
inductive Reduction where
  | map
  | sum
  | product
  deriving DecidableEq, Repr

/-- The largest plan, in bytes. -/
def planLimit : Nat := 16384

/-- The largest expression of a plan, in bytes. -/
def bodyLimit : Nat := 4096

/-- The most rows a native call evaluates at once. -/
def laneLimit : Nat := 256

/-- The most nodes of an arena, and so the most storage slots of a plan. -/
def nodeLimit : Nat := 65536

/-- The most operand slots of one call. -/
def slotLimit : Nat := 1023

/-- The runtime's largest row count of one call: a native capacity limit,
which the executable meaning does not model. -/
def rowLimit : Nat := 1048576

/-- Why a plan payload is refused. -/
inductive Refusal where
  /-- The plan has more than 16384 bytes, or its expression more than 4096. -/
  | bytes
  /-- The payload is not the canonical encoding of a plan. -/
  | syntax
  /-- A declared input or a constant is not in the call's field. -/
  | field
  /-- A constant is not a canonical decimal below the characteristic. -/
  | literal
  /-- An input node names no declared input. -/
  | input
  /-- An operand or the output does not name an earlier node. -/
  | edge
  /-- The expression embeds a field into another. -/
  | embedding
  /-- The declared inputs are not the mask's positions. -/
  | slots
  /-- The expression does not have exactly one output. -/
  | outputs
  /-- A node does not contribute to the output. -/
  | unreachable
  /-- The lanes, slot count or locations are out of range, or a slot is unused. -/
  | shape
  /-- A node reads a slot that does not hold its operand, overwrites a value
  needed across chunks, or the output's slot does not keep the output. -/
  | schedule
  deriving DecidableEq, Repr

/-! ## Lexical form -/

/-- Tokens of the compact array form. -/
inductive Token where
  | left
  | right
  | comma
  | text (characters : List Char)
  | natural (value : Nat)
  deriving DecidableEq, Repr

/-- The value of a list of decimal digits. -/
def digitValue (digits : List Char) : Nat :=
  digits.foldl (fun value digit => 10 * value + (digit.toNat - '0'.toNat)) 0

/-- A canonical decimal: one or more digits, without a leading zero. -/
def canonicalDigits (digits : List Char) : Bool :=
  !digits.isEmpty && digits.all Char.isDigit && (digits.length == 1 || digits.head? != some '0')

/-- The characters of a string token up to its closing quote, and what follows
it. A backslash is refused: canonical payloads have no escapes. -/
def stringBody : List Char → Option (List Char × List Char)
  | [] => none
  | character :: rest =>
      if character = '"' then some ([], rest)
      else if character = '\\' then none
      else (stringBody rest).map fun (body, after) => (character :: body, after)

/-- Tokens of the compact form, with no whitespace; `fuel` bounds the number of
tokens. -/
def lexWith : Nat → List Char → Except Refusal (List Token)
  | _, [] => pure []
  | 0, _ :: _ => throw .syntax
  | fuel + 1, character :: rest =>
      if character = '[' then (Token.left :: ·) <$> lexWith fuel rest
      else if character = ']' then (Token.right :: ·) <$> lexWith fuel rest
      else if character = ',' then (Token.comma :: ·) <$> lexWith fuel rest
      else if character = '"' then
        match stringBody rest with
        | some (body, after) => (Token.text body :: ·) <$> lexWith fuel after
        | none => throw .syntax
      else if character.isDigit then
        let (digits, after) := (character :: rest).span Char.isDigit
        if canonicalDigits digits then (Token.natural (digitValue digits) :: ·) <$> lexWith fuel after
        else throw .syntax
      else throw .syntax

def lex (characters : List Char) : Except Refusal (List Token) :=
  lexWith characters.length characters

/-- The UTF-8 length of a text. -/
def byteLength (characters : List Char) : Nat :=
  characters.foldl (fun total character => total + character.utf8Size) 0

/-- Decimal digit counting with a structural bound. This stays transparent to
public kernel clients; `Nat.toDigits` uses a hidden implementation. -/
def digitCountWith : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, value => if value < 10 then 1 else 1 + digitCountWith fuel (value / 10)

/-- The number of decimal digits, including the one digit of zero. Each
recursive step strictly reduces a value of at least ten, so `value + 1`
is a sufficient structural bound. -/
def digitCount (value : Nat) : Nat := digitCountWith (value + 1) value

/-- The UTF-8 length of the canonical text the tokens were read from: the
compact form has no whitespace and no escapes. -/
def tokenBytes : List Token → Nat
  | [] => 0
  | .text characters :: rest => byteLength characters + 2 + tokenBytes rest
  | .natural value :: rest => digitCount value + tokenBytes rest
  | _ :: rest => 1 + tokenBytes rest

/-! ## The arena -/

/-- A node of the arena as written: its kind, field, literal and operand
indices, before they are checked. -/
inductive Node where
  | constant (field literal : List Char)
  | input (slot : Nat)
  | add (left right : Nat)
  | mul (left right : Nat)
  | neg (operand : Nat)
  | embed (field : List Char) (operand : Nat)
  deriving DecidableEq, Repr

/-- The nodes a node reads. -/
def Node.operands : Node → List Nat
  | .add left right | .mul left right => [left, right]
  | .neg operand | .embed _ operand => [operand]
  | .constant _ _ | .input _ => []

/-- One node: `["constant", field, literal]`, `["input", slot]`,
`["add", a, b]`, `["mul", a, b]`, `["neg", a]` or `["embed", field, a]`. -/
def node : List Token → Except Refusal (Node × List Token)
  | .left :: .text tag :: .comma :: .text field :: .comma :: .text literal :: .right :: rest =>
      if tag = "constant".toList then pure (.constant field literal, rest) else throw .syntax
  | .left :: .text tag :: .comma :: .text field :: .comma :: .natural operand :: .right :: rest =>
      if tag = "embed".toList then pure (.embed field operand, rest) else throw .syntax
  | .left :: .text tag :: .comma :: .natural first :: .comma :: .natural second :: .right :: rest =>
      if tag = "add".toList then pure (.add first second, rest)
      else if tag = "mul".toList then pure (.mul first second, rest)
      else throw .syntax
  | .left :: .text tag :: .comma :: .natural operand :: .right :: rest =>
      if tag = "input".toList then pure (.input operand, rest)
      else if tag = "neg".toList then pure (.neg operand, rest)
      else throw .syntax
  | _ => throw .syntax

def textItem : List Token → Except Refusal (List Char × List Token)
  | .text characters :: rest => pure (characters, rest)
  | _ => throw .syntax

def naturalItem : List Token → Except Refusal (Nat × List Token)
  | .natural value :: rest => pure (value, rest)
  | _ => throw .syntax

/-- Comma-separated items up to the closing bracket; `fuel` bounds their
number. -/
def items {α : Type} (item : List Token → Except Refusal (α × List Token)) :
    Nat → List Token → Except Refusal (List α × List Token)
  | 0, _ => throw .syntax
  | fuel + 1, tokens => do
      let (first, rest) ← item tokens
      match rest with
      | .comma :: more =>
          let (others, after) ← items item fuel more
          pure (first :: others, after)
      | .right :: after => pure ([first], after)
      | _ => throw .syntax

/-- A bracketed, possibly empty, list of items. -/
def array {α : Type} (item : List Token → Except Refusal (α × List Token)) (fuel : Nat) :
    List Token → Except Refusal (List α × List Token)
  | .left :: .right :: rest => pure ([], rest)
  | .left :: rest => items item fuel rest
  | _ => throw .syntax

def comma : List Token → Except Refusal (List Token)
  | .comma :: rest => pure rest
  | _ => throw .syntax

/-- The arena `["zkc.ring/0", inputs, nodes, outputs]` at the front of the
tokens: the declared input fields, the nodes, the outputs and what follows. -/
def arena (tokens : List Token) :
    Except Refusal ((List (List Char) × List Node × List Nat) × List Token) :=
  match tokens with
  | .left :: .text tag :: .comma :: rest => do
      unless tag = "zkc.ring/0".toList do throw .syntax
      let (inputs, rest) ← array textItem tokens.length rest
      let (nodes, rest) ← array node tokens.length (← comma rest)
      let (outputs, rest) ← array naturalItem tokens.length (← comma rest)
      match rest with
      | .right :: after => pure ((inputs, nodes, outputs), after)
      | _ => throw .syntax
  | _ => throw .syntax

/-- The plan `["zkc.numerical-plan/0", expression, lanes, slots, locations]`:
the expression's arena and its encoded size, the lanes, the slot count and the
locations. -/
def plan (tokens : List Token) :
    Except Refusal ((List (List Char) × List Node × List Nat) × Nat × Nat × Nat × List Nat) :=
  match tokens with
  | .left :: .text tag :: .comma :: rest => do
      unless tag = "zkc.numerical-plan/0".toList do throw .syntax
      let (expression, after) ← arena rest
      let size := tokenBytes (rest.take (rest.length - after.length))
      let (lanes, after) ← naturalItem (← comma after)
      let (slots, after) ← naturalItem (← comma after)
      let (locations, after) ← array naturalItem tokens.length (← comma after)
      match after with
      | [.right] => pure (expression, size, lanes, slots, locations)
      | _ => throw .syntax
  | _ => throw .syntax

/-! ## The expression -/

/-- The trees of the arena's nodes, in order, after those already read: each
constant in the call's field with a canonical literal below the characteristic,
each input naming a declared input, each operand an earlier node, and no
embedding. -/
def build (field : List Char) (characteristic inputs : Nat) :
    List Node → List (Expr Nat Nat) → Except Refusal (List (Expr Nat Nat))
  | [], built => pure built
  | node :: rest, built => do
      let tree ← match node with
        | .constant constantField literal =>
            if constantField ≠ field then throw .field
            else if canonicalDigits literal ∧ digitValue literal < characteristic then
              pure (.constant (digitValue literal))
            else throw .literal
        | .input slot => if slot < inputs then pure (.input slot) else throw .input
        | .add first second =>
            match built[first]?, built[second]? with
            | some left, some right => pure (.add left right)
            | _, _ => throw .edge
        | .mul first second =>
            match built[first]?, built[second]? with
            | some left, some right => pure (.mul left right)
            | _, _ => throw .edge
        | .neg operand =>
            match built[operand]? with
            | some tree => pure (.neg tree)
            | none => throw .edge
        | .embed _ _ => throw .embedding
      build field characteristic inputs rest (built ++ [tree])

/-- The nodes the output reaches: walking the arena from its last node, a
reached node reaches its operands. -/
def reached (nodes : List Node) (output : Nat) : List Bool :=
  nodes.zipIdx.foldr
    (fun (node, index) marks =>
      if marks.getD index false then node.operands.foldl (fun marks operand => marks.set operand true) marks
      else marks)
    ((List.range nodes.length).map (· == output))

/-! ## The slot schedule -/

/-- Whether each node varies with the row: an input whose mask position is a
vector, or a node with a varying operand. Constants are invariant. -/
def varying (mask : List Bool) (nodes : List Node) : List Bool :=
  nodes.foldl (fun marks node =>
    marks ++ [match node with
      | .input slot => mask.getD slot false
      | _ => node.operands.any (marks.getD · false)]) []

/-- Whether each node's value is needed across chunks: the output when it is
invariant, and every invariant operand of a varying node. -/
def persistent (nodes : List Node) (varies : List Bool) (output : Nat) : List Bool :=
  nodes.zipIdx.foldl (fun marks (node, index) =>
    if varies.getD index false then
      node.operands.foldl (fun marks operand =>
        if varies.getD operand false then marks else marks.set operand true) marks
    else marks)
    ((List.range nodes.length).map fun index => index == output && !varies.getD index false)

/-- Whether each operand of a node is the owner of its slot. -/
def readsOwners (locations : List Nat) (contents : List (Option Nat)) (node : Node) : Bool :=
  node.operands.all fun operand => contents.getD (locations.getD operand 0) none == some operand

/-- Whether a slot's owner may be overwritten: an empty slot, or a value not
needed across chunks. -/
def replaceable (persists : List Bool) : Option Nat → Bool
  | some owner => !persists.getD owner false
  | none => true

/-- The owners of the slots after one phase: the selected nodes run in arena
order, and each must find its operands in their slots and may not overwrite a
persistent value. `none` when a node fails either condition. -/
def phase (locations : List Nat) (persists : List Bool) (selected : List Bool) :
    List (Node × Nat) → List (Option Nat) → Option (List (Option Nat))
  | [], contents => some contents
  | (node, index) :: rest, contents =>
      if selected.getD index false then
        if readsOwners locations contents node && replaceable persists (contents.getD (locations.getD index 0) none) then
          phase locations persists selected rest (contents.set (locations.getD index 0) (some index))
        else none
      else phase locations persists selected rest contents

/-- The slot owners with every varying value forgotten: what a later chunk may
rely on from an earlier one. -/
def forget (varies : List Bool) (contents : List (Option Nat)) : List (Option Nat) :=
  contents.map fun owner => owner.bind fun index => if varies.getD index false then none else some index

/-- A slot schedule the plan contract admits. Invariant nodes run once, then the
varying nodes run for each chunk. Every read finds its operand, no write
replaces a persistent value, and the output keeps its slot after the first
chunk; the varying phase run again from what persists between chunks reaches
the same owners, so every later chunk does too. -/
structure Schedule where
  nodes : List Node
  mask : List Bool
  output : Nat
  slots : Nat
  locations : List Nat
  first : List (Option Nat)
  chunk : List (Option Nat)
  invariantPhase : phase locations (persistent nodes (varying mask nodes) output)
    ((varying mask nodes).map (!·)) nodes.zipIdx (List.replicate slots none) = some first
  varyingPhase : phase locations (persistent nodes (varying mask nodes) output)
    (varying mask nodes) nodes.zipIdx first = some chunk
  repeatedPhase : phase locations (persistent nodes (varying mask nodes) output)
    (varying mask nodes) nodes.zipIdx (forget (varying mask nodes) chunk) = some chunk
  outputKept : chunk.getD (locations.getD output 0) none = some output

/-- The schedule of a plan, when the plan contract admits it. -/
def schedule (mask : List Bool) (nodes : List Node) (slots output : Nat) (locations : List Nat) :
    Option Schedule :=
  match first : phase locations (persistent nodes (varying mask nodes) output)
      ((varying mask nodes).map (!·)) nodes.zipIdx (List.replicate slots none) with
  | none => none
  | some contents =>
      match chunk : phase locations (persistent nodes (varying mask nodes) output)
          (varying mask nodes) nodes.zipIdx contents with
      | none => none
      | some after =>
          if repeated : phase locations (persistent nodes (varying mask nodes) output)
              (varying mask nodes) nodes.zipIdx (forget (varying mask nodes) after) = some after then
            if kept : after.getD (locations.getD output 0) none = some output then
              some ⟨nodes, mask, output, slots, locations, contents, after, first, chunk, repeated, kept⟩
            else none
          else none

/-! ## Schedule correctness

The values are abstract: `step` computes one node from its operands' values,
so this is the slot bookkeeping of a plan, not a second expression semantics.
A value is any type, for example one row's field element or a chunk's lanes. -/

/-- One phase executed on values: each selected node, in arena order, reads its
operands from their slots and writes its result to its own slot. A read of an
empty slot fails. -/
def execute {α : Type} (step : Node → List α → α) (locations : List Nat) (selected : List Bool) :
    List (Node × Nat) → List (Option α) → Option (List (Option α))
  | [], contents => some contents
  | (node, index) :: rest, contents =>
      if selected.getD index false then
        (node.operands.mapM fun operand => contents.getD (locations.getD operand 0) none).bind fun operands =>
          execute step locations selected rest (contents.set (locations.getD index 0) (some (step node operands)))
      else execute step locations selected rest contents

/-- Concrete slots hold the values of their symbolic owners. -/
def Holds {α : Type} (value : Nat → α) (concrete : List (Option α)) (owners : List (Option Nat)) : Prop :=
  ∀ slot index, owners.getD slot none = some index → concrete.getD slot none = some (value index)

theorem holds_set {α : Type} {value : Nat → α} {concrete : List (Option α)} {owners : List (Option Nat)}
    (holds : Holds value concrete owners) (length : concrete.length = owners.length) (slot index : Nat) :
    Holds value (concrete.set slot (some (value index))) (owners.set slot (some index)) := by
  intro target owner found
  rw [List.getD_eq_getElem?_getD, List.getElem?_set] at found ⊢
  by_cases same : slot = target
  · subst same
    by_cases inside : slot < owners.length
    · have : owner = index := by simpa [inside] using found.symm
      subst this
      simp [length, inside]
    · simp [inside] at found
  · simp only [same, ite_false] at found ⊢
    exact holds target owner (by rw [List.getD_eq_getElem?_getD]; exact found)

theorem mapM_reads {α : Type} (read : Nat → Option α) (value : Nat → α) :
    ∀ operands : List Nat, (∀ operand ∈ operands, read operand = some (value operand)) →
      operands.mapM read = some (operands.map value)
  | [], _ => rfl
  | operand :: rest, found => by
      rw [List.mapM_cons, found operand List.mem_cons_self,
        mapM_reads read value rest fun other member => found other (List.mem_cons_of_mem _ member)]
      rfl

/-- Every read of an admitted phase sees its operand's value, and afterwards
every slot holds the value of its owner. -/
theorem execute_phase {α : Type} (step : Node → List α → α) (value : Nat → α) (locations : List Nat)
    (persists selected : List Bool) :
    ∀ (nodes : List (Node × Nat)) (owners after : List (Option Nat)) (concrete : List (Option α)),
      (∀ node index, (node, index) ∈ nodes → selected.getD index false = true →
        value index = step node (node.operands.map value)) →
      phase locations persists selected nodes owners = some after →
      Holds value concrete owners → concrete.length = owners.length →
      ∃ result, execute step locations selected nodes concrete = some result ∧
        Holds value result after ∧ result.length = after.length
  | [], owners, after, concrete, _, admitted, holds, length => by
      simp only [phase, Option.some.injEq] at admitted
      subst admitted
      exact ⟨concrete, rfl, holds, length⟩
  | (node, index) :: rest, owners, after, concrete, equations, admitted, holds, length => by
      have tail : ∀ node index, (node, index) ∈ rest → selected.getD index false = true →
          value index = step node (node.operands.map value) :=
        fun node index member => equations node index (List.mem_cons_of_mem _ member)
      cases chosen : selected.getD index false with
      | false =>
        simp only [phase, chosen, Bool.false_eq_true, ite_false] at admitted
        obtain ⟨result, executed, holdsResult, lengthResult⟩ :=
          execute_phase step value locations persists selected rest owners after concrete tail admitted holds length
        exact ⟨result, by simp only [execute, chosen, Bool.false_eq_true, ite_false]; exact executed,
          holdsResult, lengthResult⟩
      | true =>
        simp only [phase, chosen, ite_true] at admitted
        cases ok : (readsOwners locations owners node &&
            replaceable persists (owners.getD (locations.getD index 0) none)) with
        | false => simp only [ok, Bool.false_eq_true, ite_false, reduceCtorEq] at admitted
        | true =>
          simp only [ok, ite_true] at admitted
          simp only [Bool.and_eq_true, readsOwners, List.all_eq_true, beq_iff_eq] at ok
          have reads : (node.operands.mapM fun operand => concrete.getD (locations.getD operand 0) none) =
              some (node.operands.map value) :=
            mapM_reads _ value _ fun operand member => holds _ operand (ok.1 operand member)
          obtain ⟨result, executed, holdsResult, lengthResult⟩ := execute_phase step value locations persists
            selected rest _ after _ tail admitted
            (holds_set holds length (locations.getD index 0) index)
            (by simp only [List.length_set, length])
          refine ⟨result, ?_, holdsResult, lengthResult⟩
          simp only [execute, chosen, ite_true, reads, Option.bind_some]
          rw [← equations node index List.mem_cons_self chosen]
          exact executed

/-- Execution of a schedule over chunks: the invariant phase and the first
chunk, then one varying phase for each further chunk. `steps k` computes nodes
from chunk `k`'s operands; an empty domain runs neither phase. -/
def Schedule.run {α : Type} (schedule : Schedule) (steps : Nat → Node → List α → α) :
    Nat → Option (List (Option α))
  | 0 =>
      (execute (steps 0) schedule.locations ((varying schedule.mask schedule.nodes).map (!·))
        schedule.nodes.zipIdx (List.replicate schedule.slots none)).bind fun start =>
      execute (steps 0) schedule.locations (varying schedule.mask schedule.nodes) schedule.nodes.zipIdx start
  | chunk + 1 =>
      (schedule.run steps chunk).bind fun before =>
      execute (steps (chunk + 1)) schedule.locations (varying schedule.mask schedule.nodes)
        schedule.nodes.zipIdx before

/-- An admitted schedule computes the plan's values. Let `values k` be the
nodes' values in chunk `k`: each node's value is its step applied to its
operands' values, and an invariant node has one value in every chunk. Then
every chunk runs, each read sees its operand's value, persistent invariant
values survive every later chunk, and the output's slot holds the output's
value of the last chunk run. -/
theorem Schedule.run_correct {α : Type} (schedule : Schedule) (steps : Nat → Node → List α → α)
    (values : Nat → Nat → α)
    (equations : ∀ chunk node index, (node, index) ∈ schedule.nodes.zipIdx →
      values chunk index = steps chunk node (node.operands.map (values chunk)))
    (invariant : ∀ chunk index, (varying schedule.mask schedule.nodes).getD index false = false →
      values chunk index = values 0 index) :
    ∀ chunk, ∃ result, schedule.run steps chunk = some result ∧
      Holds (values chunk) result schedule.chunk ∧ result.length = schedule.chunk.length ∧
      result.getD (schedule.locations.getD schedule.output 0) none = some (values chunk schedule.output)
  | 0 => by
      have empty : Holds (values 0) (List.replicate schedule.slots none) (List.replicate schedule.slots none) := by
        intro slot index found
        simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate] at found
        split at found <;> cases found
      obtain ⟨start, started, holdsStart, lengthStart⟩ := execute_phase (steps 0) (values 0)
        schedule.locations _ _ _ _ _ _ (fun node index member _ => equations 0 node index member)
        schedule.invariantPhase empty (by simp only [List.length_replicate])
      obtain ⟨result, ran, holdsResult, lengthResult⟩ := execute_phase (steps 0) (values 0)
        schedule.locations _ _ _ _ _ _ (fun node index member _ => equations 0 node index member)
        schedule.varyingPhase holdsStart lengthStart
      exact ⟨result, by simp only [Schedule.run, started, Option.bind_some, ran], holdsResult, lengthResult,
        holdsResult _ _ schedule.outputKept⟩
  | chunk + 1 => by
      obtain ⟨before, ran, holdsBefore, lengthBefore, _⟩ :=
        Schedule.run_correct schedule steps values equations invariant chunk
      -- Only invariant owners persist between chunks, and their values do not change.
      have persisted : Holds (values (chunk + 1)) before
          (forget (varying schedule.mask schedule.nodes) schedule.chunk) := by
        intro slot index found
        rw [forget, List.getD_eq_getElem?_getD, List.getElem?_map] at found
        rcases owner : schedule.chunk[slot]? with _ | held
        · simp [owner] at found
        · rcases held with _ | held
          · simp [owner] at found
          · cases fixed : (varying schedule.mask schedule.nodes).getD held false
            · have read := fixed
              rw [List.getD_eq_getElem?_getD] at read
              have same : held = index := by simpa [owner, read] using found
              subst same
              have holdsSlot := holdsBefore slot held (by rw [List.getD_eq_getElem?_getD, owner]; rfl)
              rw [invariant (chunk + 1) held fixed, ← invariant chunk held fixed]
              exact holdsSlot
            · have read := fixed
              rw [List.getD_eq_getElem?_getD] at read
              simp [owner, read] at found
      obtain ⟨result, executed, holdsResult, lengthResult⟩ := execute_phase (steps (chunk + 1))
        (values (chunk + 1)) schedule.locations _ _ _ _ _ _
        (fun node index member _ => equations (chunk + 1) node index member) schedule.repeatedPhase persisted
        (by simp only [forget, List.length_map, lengthBefore])
      exact ⟨result, by simp only [Schedule.run, ran, Option.bind_some]; exact executed, holdsResult,
        lengthResult, holdsResult _ _ schedule.outputKept⟩

/-! ## The plan -/

/-- A checked plan: its expression and the admitted schedule of its arena. -/
structure Plan where
  expression : Expr Nat Nat
  lanes : Nat
  schedule : Schedule

/-- The plan of a numerical call over the field `field`, of the given
characteristic and operand mask, read from its text parameter. -/
def plan? (field : String) (characteristic : Nat) (mask : List Bool) (body : String) :
    Except Refusal Plan := do
  let characters := body.toList
  if planLimit < byteLength characters then throw .bytes
  let ((inputs, nodes, outputs), size, lanes, slots, locations) ← plan (← lex characters)
  if bodyLimit < size then throw .bytes
  unless 1 ≤ lanes ∧ lanes ≤ laneLimit ∧ 1 ≤ slots ∧ slots ≤ nodeLimit do throw .shape
  unless inputs.all (· = field.toList) do throw .field
  let built ← build field.toList characteristic inputs.length nodes []
  unless inputs.length = mask.length do throw .slots
  let output ← match outputs with
    | [output] => pure output
    | _ => throw .outputs
  let tree ← match built[output]? with
    | some tree => if (reached nodes output).all id then pure tree else throw .unreachable
    | none => throw .edge
  unless slots ≤ nodes.length ∧ locations.length = nodes.length ∧ locations.all (· < slots) ∧
      (List.range slots).all (locations.contains ·) do throw .shape
  match schedule mask nodes slots output locations with
  | some admitted => pure ⟨tree, lanes, admitted⟩
  | none => throw .schedule

/-- The expression a numerical call carries in its plan parameter. -/
def decode (field : String) (characteristic : Nat) (mask : List Bool) (body : String) :
    Except Refusal (Expr Nat Nat) :=
  (plan? field characteristic mask body).map (·.expression)

/-- The operand mask of a numerical binding: at most 1023 positions, `false`
for a scalar and `true` for a vector. -/
def mask? (text : String) : Option (List Bool) :=
  let characters := text.toList
  if characters.length ≤ slotLimit then
    characters.mapM fun character =>
      if character = '0' then some false else if character = '1' then some true else none
  else none

end Zkc.Executable.Numerical
