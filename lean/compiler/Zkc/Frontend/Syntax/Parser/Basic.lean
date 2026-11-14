module

public import Zkc.Frontend.Syntax.Tree
public import Zkc.Frontend.Syntax.Spans
public import Zkc.Frontend.Syntax.Lexer

@[expose] public section

set_option autoImplicit false

/-!
# Parser state and token helpers

The parser is recursive descent over the token array, with the lookahead that §5.0 states. Its
state is the position in the array, the end of the last token consumed (the end of a node's
span), and whether a static term is being read (GR5).
-/

namespace Zkc.Frontend.Syntax.Parser

structure State where
  tokens : Array Token
  texts : Array String
  file : String
  index : Nat
  lastLine : Nat
  lastColumn : Nat
  lastByte : Nat
  /-- greater than zero while a static term is read (GR5) -/
  staticDepth : Nat

abbrev ParseM := EStateM SyntaxError State

def tokenAt (state : State) (offset : Nat) : Token :=
  let i := state.index + offset
  if h : i < state.tokens.size then state.tokens[i] else state.tokens.back!

def textAt (state : State) (offset : Nat) : String :=
  let i := state.index + offset
  if h : i < state.texts.size then state.texts[i] else ""

@[inline] def peek : ParseM Token := do return tokenAt (← get) 0

@[inline] def peekKind (offset : Nat := 0) : ParseM TokenKind := do
  return (tokenAt (← get) offset).kind

@[inline] def peekText (offset : Nat := 0) : ParseM String := do return textAt (← get) offset

/-- Whether the token at `offset` is the identifier `word`: a contextual word in its position. -/
def atWord (word : String) (offset : Nat := 0) : ParseM Bool := do
  let state ← get
  return (tokenAt state offset).kind == .identifier && textAt state offset == word

def isLayout (kind : TokenKind) : Bool :=
  kind == .newline ∨ kind == .indent ∨ kind == .dedent ∨ kind == .endOfFile

/-- Consumes the current token. -/
def advance : ParseM Token := do
  let state ← get
  let token := tokenAt state 0
  if isLayout token.kind then
    set { state with index := state.index + 1 }
  else
    set { state with
      index := state.index + 1, lastLine := token.line.toNat
      lastColumn := token.stopColumn.toNat, lastByte := token.stopByte.toNat }
  return token

def tokenStart (token : Token) : Position :=
  { line := token.line.toNat, column := token.column.toNat, byte := token.startByte.toNat }

/-- The span from the start of `start` to the end of the last token consumed. -/
def spanFrom (start : Token) : ParseM Span := do
  let state ← get
  return Span.make state.file (tokenStart start)
    { line := state.lastLine, column := state.lastColumn, byte := state.lastByte }

def tokenSpan (file : String) (token : Token) : Span :=
  Span.make file (tokenStart token)
    { line := token.line.toNat, column := token.stopColumn.toNat, byte := token.stopByte.toNat }

def failAt {α : Type} (token : Token) (rule message : String) : ParseM α := do
  throw { rule, message, span := tokenSpan (← get).file token }

def fail {α : Type} (rule message : String) : ParseM α := do
  failAt (← peek) rule message

/-- How a token is named in a message. -/
def describe (offset : Nat := 0) : ParseM String := do
  let state ← get
  let token := tokenAt state offset
  match token.kind with
  | .identifier | .number => return textAt state offset
  | .string | .byteString | .hexString => return token.kind.spelling
  | kind => return kind.spelling

/-- A token that no production admits (`GR`). -/
def unexpected {α : Type} (expected : String) : ParseM α := do
  fail "GR" s!"expected {expected}, found `{← describe}`"

def expect (kind : TokenKind) : ParseM Token := do
  if (← peekKind) == kind then advance
  else
    let expected := match kind with
      | .newline => "the end of the line"
      | .indent => "an indented suite"
      | .dedent => "the end of the suite"
      | .identifier => "a name"
      | .string => "a string"
      | _ => s!"`{kind.spelling}`"
    unexpected expected

def accept (kind : TokenKind) : ParseM Bool := do
  if (← peekKind) == kind then
    discard advance
    return true
  return false

/-- Consumes the contextual word `word`. -/
def expectWord (word : String) : ParseM Token := do
  if ← atWord word then advance else unexpected s!"`{word}`"

/-- `Name`; a reserved word where a name is expected is refused by LX9. -/
def parseName : ParseM Name := do
  let token ← peek
  if token.kind == .identifier then
    let text ← peekText
    discard advance
    return { span := tokenSpan (← get).file token, text }
  else if token.kind.isReservedWord then
    fail "LX9" s!"`{token.kind.spelling}` is a reserved word"
  else
    unexpected "a name"

/-- Runs `action`; on a refusal, restores the state and gives `none`. -/
def attempt {α : Type} (action : ParseM α) : ParseM (Option α) := do
  let saved ← get
  try
    let value ← action
    return some value
  catch _ =>
    set saved
    return none

/-- The index of the token that closes the bracket opened at `offset`, if any. -/
def matchingClose (offset : Nat) : ParseM (Option Nat) := do
  let state ← get
  let mut depth := 0
  let mut i := state.index + offset
  while i < state.tokens.size do
    let kind := state.tokens[i]!.kind
    if kind == .leftParen ∨ kind == .leftBracket ∨ kind == .leftBrace ∨ kind == .innerOpen
        ∨ kind == .staticOpen then
      depth := depth + 1
    else if kind == .rightParen ∨ kind == .rightBracket ∨ kind == .rightBrace
        ∨ kind == .innerClose ∨ kind == .staticClose then
      depth := depth - 1
      if depth == 0 then return some (i - state.index)
    else if kind == .endOfFile then return none
    i := i + 1
  return none

/-- Whether the tokens at `offset` and `offset + 1` are `=` and `>` written together, the
spelling `=>` of a function literal (GR6). -/
def atFatArrow (offset : Nat) : ParseM Bool := do
  let state ← get
  let first := tokenAt state offset
  let second := tokenAt state (offset + 1)
  return first.kind == .equals ∧ (second.kind == .greater ∨ second.kind == .staticClose)
    ∧ first.stopByte == second.startByte

def inStatic : ParseM Bool := do return (← get).staticDepth > 0

/-- Reads `action` as a static term (GR5). -/
def withStatic {α : Type} (action : ParseM α) : ParseM α := do
  modify fun state => { state with staticDepth := state.staticDepth + 1 }
  let result ← action
  modify fun state => { state with staticDepth := state.staticDepth - 1 }
  return result

/-- Reads `action` outside any static term. -/
def withoutStatic {α : Type} (action : ParseM α) : ParseM α := do
  let depth := (← get).staticDepth
  modify fun state => { state with staticDepth := 0 }
  let result ← action
  modify fun state => { state with staticDepth := depth }
  return result

/-- A comma-separated list up to `close`, which may end with one more `,` (§5). The list is not
empty unless `allowEmpty`. `close` is not consumed. -/
def commaList {α : Type} (close : TokenKind) (item : ParseM α) (allowEmpty := false) :
    ParseM (Array α) := do
  let mut items := #[]
  if allowEmpty ∧ (← peekKind) == close then return items
  items := items.push (← item)
  while (← peekKind) == .comma do
    discard advance
    if (← peekKind) == close then break
    items := items.push (← item)
  return items

/-- `Suite(X) ::= NEWLINE INDENT X { X } DEDENT` -/
def suite {α : Type} (item : ParseM α) : ParseM (Array α) := do
  discard (expect .newline)
  discard (expect .indent)
  let mut items := #[← item]
  while (← peekKind) != .dedent do
    items := items.push (← item)
  discard advance
  return items

end Zkc.Frontend.Syntax.Parser
