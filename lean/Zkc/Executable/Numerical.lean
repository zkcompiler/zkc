module

public import Zkc.Algebra.RingExpression.Basic

@[expose] public section

/-! The expression payload of a native numerical call.

The compiler-generated `numerical.map`, `numerical.sum` and `numerical.product`
operations execute one pure field expression over a row domain
(`docs/spec/runtime/numerical.md`). Each binding names its field and an operand
mask of `0` (a scalar) and `1` (a vector) positions; each operation carries the
expression as its single text parameter, a `zkc.ring/0` arena
(`docs/spec/domains/ring-expressions.md`).

`decode` reads that text into a `Zkc.Algebra.RingExpression.Expr` whose
constants are natural literals and whose inputs are operand slots. It accepts
exactly the payloads the runtime's program admission accepts for a call over a
field with the given characteristic and number of slots, and refuses every other
payload with a named reason (`Refusal`):

- the body has at most 4096 bytes of UTF-8;
- it is the canonical encoding of an arena: the compact array form with
  canonical natural numbers and no escapes, `["zkc.ring/0", inputs, nodes,
  outputs]`, since the runtime refuses a body that differs from the canonical
  encoding of what it parses;
- every declared input and every constant is in the call's field, a constant
  is a canonical decimal below the characteristic, and an embedding is refused;
- an input node names a declared input, and every operand points strictly
  backward;
- there are exactly as many declared inputs as mask positions and exactly one
  output, and the output reaches every node.

The arena's other formation limits (65 536 nodes and inputs, 4096 outputs and
depth 1024) cannot be reached within 4096 bytes. `mask?` reads the mask
argument: at most 1023 positions, each `0` or `1`. These are the static checks
of program admission. The runtime's bound on a call's rows (`rowLimit`) is a
capacity limit of the native call, as the element limit of every vector a native
kernel produces is; the executable meaning does not stop on it.

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

/-- The largest expression body, in bytes. -/
def bodyLimit : Nat := 4096

/-- The most operand slots of one call. -/
def slotLimit : Nat := 1023

/-- The runtime's largest row count of one call: a native capacity limit,
which the executable meaning does not model. -/
def rowLimit : Nat := 1048576

/-- Why an expression payload is refused. -/
inductive Refusal where
  /-- The body has more than 4096 bytes. -/
  | bytes
  /-- The body is not the canonical encoding of an arena. -/
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

/-- The arena `["zkc.ring/0", inputs, nodes, outputs]`: the declared input
fields, the nodes and the outputs. -/
def arena (tokens : List Token) : Except Refusal (List (List Char) × List Node × List Nat) :=
  match tokens with
  | .left :: .text tag :: .comma :: rest => do
      unless tag = "zkc.ring/0".toList do throw .syntax
      let (inputs, rest) ← array textItem tokens.length rest
      let (nodes, rest) ← array node tokens.length (← comma rest)
      let (outputs, rest) ← array naturalItem tokens.length (← comma rest)
      match rest with
      | [.right] => pure (inputs, nodes, outputs)
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

/-- The UTF-8 length of a text. -/
def byteLength (characters : List Char) : Nat :=
  characters.foldl (fun total character => total + character.utf8Size) 0

/-- The expression a numerical call over the field `field`, of the given
characteristic, with `slots` operand slots carries as its text parameter. -/
def decode (field : String) (characteristic slots : Nat) (body : String) :
    Except Refusal (Expr Nat Nat) := do
  let characters := body.toList
  if bodyLimit < byteLength characters then throw .bytes
  let (inputs, nodes, outputs) ← arena (← lex characters)
  unless inputs.all (· = field.toList) do throw .field
  let built ← build field.toList characteristic inputs.length nodes []
  unless inputs.length = slots do throw .slots
  let output ← match outputs with
    | [output] => pure output
    | _ => throw .outputs
  match built[output]? with
  | some tree =>
      if (reached nodes output).all id then pure tree else throw .unreachable
  | none => throw .edge

/-- The operand mask of a numerical binding: at most 1023 positions, `false`
for a scalar and `true` for a vector. -/
def mask? (text : String) : Option (List Bool) :=
  let characters := text.toList
  if characters.length ≤ slotLimit then
    characters.mapM fun character =>
      if character = '0' then some false else if character = '1' then some true else none
  else none

end Zkc.Executable.Numerical
