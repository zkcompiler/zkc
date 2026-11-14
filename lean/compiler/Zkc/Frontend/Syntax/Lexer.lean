module

public import Zkc.Frontend.Syntax.Token
public import Zkc.Frontend.Syntax.Error
public import Zkc.Frontend.Syntax.Unicode

@[expose] public section

set_option autoImplicit false

/-!
# The lexer (§3.1)

A hand-written procedure over the bytes of a UTF-8 source. It produces the tokens of §3.2 with
`newline`, `indent` and `dedent` as LX2 and LX4 define them, and the comments, which are not
tokens and are kept for the formatter. The first refusal ends the run.
-/

namespace Zkc.Frontend.Syntax

/-- The tokens and comments of a file. The text of an identifier, a number, a string or a byte
string is kept with its token in `texts`, at the index of the token. -/
structure Lexed where
  tokens : Array Token
  texts : Array String
  comments : Array Comment
  deriving Inhabited

namespace Lexer

/-- An open bracket: its kind and its token. -/
structure OpenBracket where
  kind : TokenKind
  token : Token
  deriving Inhabited

structure State where
  source : ByteArray
  file : String
  pos : Nat
  line : Nat
  /-- the column of `pos`, counted in characters from 1 -/
  column : Nat
  tokens : Array Token
  texts : Array String
  comments : Array Comment
  brackets : Array OpenBracket
  indents : Array Nat
  sawLogicalLine : Bool

abbrev LexM := EStateM SyntaxError State

def pointSpan (file : String) (line column byte : Nat) : Span :=
  Span.make file ⟨line, column, byte⟩ ⟨line, column, byte⟩

def failAt {α : Type} (rule message : String) (line column byte : Nat) : LexM α := do
  let state ← get
  throw { rule, message, span := pointSpan state.file line column byte }

def failHere {α : Type} (rule message : String) : LexM α := do
  let state ← get
  failAt rule message state.line state.column state.pos

@[inline] def byteAt (source : ByteArray) (index : Nat) : UInt8 :=
  if h : index < source.size then source[index]'h else 0

/-- The length of a UTF-8 sequence from its first byte; 0 for a byte that cannot start one. -/
@[inline] def sequenceLength (first : UInt8) : Nat :=
  if first < 0x80 then 1
  else if first < 0xC2 then 0
  else if first < 0xE0 then 2
  else if first < 0xF0 then 3
  else if first < 0xF5 then 4
  else 0

/-- Decodes the character at `index` of a text known to be valid UTF-8: its code point and its
length in bytes. -/
def decodeAt (source : ByteArray) (index : Nat) : UInt32 × Nat :=
  let b0 := byteAt source index
  let cont (k : Nat) : UInt32 := (byteAt source (index + k) &&& 0x3F).toUInt32
  match sequenceLength b0 with
  | 1 => (b0.toUInt32, 1)
  | 2 => (((b0 &&& 0x1F).toUInt32 <<< 6) ||| cont 1, 2)
  | 3 => (((b0 &&& 0x0F).toUInt32 <<< 12) ||| (cont 1 <<< 6) ||| cont 2, 3)
  | 4 => (((b0 &&& 0x07).toUInt32 <<< 18) ||| (cont 1 <<< 12) ||| (cont 2 <<< 6) ||| cont 3, 4)
  | _ => (b0.toUInt32, 1)

/-- Decodes and validates the character at `index`; `none` when the bytes are not UTF-8. -/
def decodeChecked (source : ByteArray) (index : Nat) : Option (UInt32 × Nat) :=
  let b0 := byteAt source index
  let length := sequenceLength b0
  if length == 0 ∨ index + length > source.size then none
  else
    let isContinuation (k : Nat) := k ≥ length ∨ (byteAt source (index + k) &&& 0xC0) == 0x80
    if isContinuation 1 ∧ isContinuation 2 ∧ isContinuation 3 then
      let (code, width) := decodeAt source index
      let minimum : UInt32 := match length with | 2 => 0x80 | 3 => 0x800 | 4 => 0x10000 | _ => 0
      if code < minimum ∨ (0xD800 ≤ code ∧ code ≤ 0xDFFF) ∨ code > 0x10FFFF then none
      else some (code, width)
    else none

/-- LX1 refuses a text that is not UTF-8; the reference gives no wording for it. -/
def textError (file message : String) (line column byte : Nat) : SyntaxError :=
  { rule := "LX1", message, span := pointSpan file line column byte }

/-- One pass over the text for LX1. The result is the first character after which the full test
of Normalization Form C is needed, if any. A tail-recursive loop, so that its state is not boxed. -/
partial def scanText (source : ByteArray) (file : String) (index line column : Nat)
    (lastClass : UInt8) (suspect : Option (Nat × Nat × Nat)) :
    Except SyntaxError (Option (Nat × Nat × Nat)) :=
  if index ≥ source.size then .ok suspect
  else
    let b := byteAt source index
    if b == 0x0A then scanText source file (index + 1) (line + 1) 1 0 suspect
    else if b == 0x0D then
      if byteAt source (index + 1) != 0x0A then
        .error (textError file "a lone carriage return is not a line end" line column index)
      else scanText source file (index + 1) line (column + 1) 0 suspect
    else if b < 0x80 then scanText source file (index + 1) line (column + 1) 0 suspect
    else
      match decodeChecked source index with
      | none => .error (textError file "the file is not UTF-8 text" line column index)
      | some (code, width) =>
        if code < 0x300 then scanText source file (index + width) line (column + 1) 0 suspect
        else if Unicode.inRanges Unicode.notInNfcRanges code then
          .error (textError file "the file is not in Normalization Form C" line column index)
        else
          let cls := Unicode.combiningClass code
          let needsTest := (cls != 0 ∧ lastClass > cls) ∨ Unicode.mayCompose code
          let suspect := if suspect.isNone ∧ needsTest then some (line, column, index) else suspect
          scanText source file (index + width) line (column + 1) cls suspect

/-- LX1: the text is UTF-8, every carriage return ends a line with the line feed after it, and
the text is in Normalization Form C. -/
def checkText (source : ByteArray) (file : String) : Except SyntaxError Unit := do
  match ← scanText source file 0 1 1 0 none with
  | none => pure ()
  | some (suspectLine, suspectColumn, suspectByte) =>
    let mut codes : Array UInt32 := #[]
    let mut position := 0
    while position < source.size do
      let (code, width) := decodeAt source position
      codes := codes.push code
      position := position + width
    unless Unicode.isNfc codes do
      throw (textError file "the file is not in Normalization Form C" suspectLine suspectColumn
        suspectByte)

/-- The source and the current position. The state itself is never held across an update, so
that the arrays it holds are updated in place. -/
structure Cursor where
  source : ByteArray
  pos : Nat
  line : Nat
  column : Nat

def here : LexM Cursor := do
  let state ← get
  return ⟨state.source, state.pos, state.line, state.column⟩

/-- Records a token, and moves the position to `nextPos` and `nextColumn`. -/
def emitTo (kind : TokenKind) (startByte stopByte line column stopColumn : Nat) (text : String)
    (nextPos nextColumn : Nat) : LexM Unit :=
  modify fun state =>
    { state with
      tokens := state.tokens.push
        { kind, startByte := startByte.toUInt32, stopByte := stopByte.toUInt32
          line := line.toUInt32, column := column.toUInt32, stopColumn := stopColumn.toUInt32 }
      texts := state.texts.push text
      pos := nextPos, column := nextColumn }

/-- A token of no width at the current position. -/
def emitLayout (kind : TokenKind) : LexM Unit := do
  let ⟨_, pos, line, column⟩ ← here
  emitTo kind pos pos line column column "" pos column

/-- A token of `width` ASCII characters at the current position; the position moves past it. -/
def emitAscii (kind : TokenKind) (width : Nat) : LexM Unit := do
  let ⟨_, pos, line, column⟩ ← here
  emitTo kind pos (pos + width) line column (column + width) "" (pos + width) (column + width)

def isLineEnd (source : ByteArray) (index : Nat) : Bool :=
  index ≥ source.size ∨ byteAt source index == 0x0A
    ∨ (byteAt source index == 0x0D ∧ byteAt source (index + 1) == 0x0A)

def isDigit (b : UInt8) : Bool := 0x30 ≤ b ∧ b ≤ 0x39

/-- The code point at `index`, or 0 at the end. -/
def codeAt (source : ByteArray) (index : Nat) : UInt32 × Nat :=
  if index < source.size then decodeAt source index else (0, 0)

def mathematicalToken (code : UInt32) : Option TokenKind :=
  match code with
  | 0x2211 => some .sumSign
  | 0x220F => some .productSign
  | 0x2200 => some .forAllSign
  | 0x2203 => some .existsSign
  | 0x2208 => some .elementSign
  | 0x27EA => some .innerOpen
  | 0x27EB => some .innerClose
  | _ => none

def isOpening (kind : TokenKind) : Bool :=
  kind == .leftParen ∨ kind == .leftBracket ∨ kind == .leftBrace ∨ kind == .innerOpen
    ∨ kind == .staticOpen

def openingOf : TokenKind → TokenKind
  | .rightParen => .leftParen
  | .rightBracket => .leftBracket
  | .rightBrace => .leftBrace
  | .innerClose => .innerOpen
  | _ => .staticOpen

def lessMessage : String :=
  "write `a < b` for a comparison; `<` touching a name opens static arguments"

def bracketFailure {α : Type} (bracket : OpenBracket) (message : String) : LexM α :=
  if bracket.kind == .staticOpen then
    failAt "LX5" lessMessage bracket.token.line.toNat bracket.token.column.toNat
      bracket.token.startByte.toNat
  else
    failAt "LX6" message bracket.token.line.toNat bracket.token.column.toNat
      bracket.token.startByte.toNat

/-- Records an opening bracket, or matches a closing one with the innermost open bracket. A
bracket closed by another kind, or never closed, is refused by LX6 with the wording of the tools
(Appendix A), or by LX5 when the open bracket is a static one. -/
def trackBracket (kind : TokenKind) : LexM Unit := do
  let (token, innermost?) := (fun state : State => (state.tokens.back!, state.brackets.back?)) (← get)
  if isOpening kind then
    modify fun state => { state with brackets := state.brackets.push { kind, token } }
  else if kind == .rightParen ∨ kind == .rightBracket ∨ kind == .rightBrace ∨ kind == .innerClose
      ∨ kind == .staticClose then
    match innermost? with
    | some innermost =>
      if innermost.kind == openingOf kind then
        modify fun state => { state with brackets := state.brackets.pop }
      else if innermost.kind == .staticOpen then
        bracketFailure innermost ""
      else
        failAt "LX6" s!"unbalanced `{kind.spelling}`" token.line.toNat token.column.toNat
          token.startByte.toNat
    | none =>
      failAt "LX6" s!"unbalanced `{kind.spelling}`" token.line.toNat token.column.toNat
        token.startByte.toNat

/-- LX5: a lone `<` opens static arguments when it touches the identifier or reserved word
before it, or follows the word `section`. -/
def lessOpensStatic (state : State) : Bool :=
  match state.tokens.back? with
  | some previous =>
    previous.kind == .kwSection
      ∨ ((previous.kind == .identifier ∨ previous.kind.isReservedWord)
        ∧ previous.stopByte.toNat == state.pos)
  | none => false

def innermostIsStatic (state : State) : Bool :=
  match state.brackets.back? with
  | some innermost => innermost.kind == .staticOpen
  | none => false

def hexDigits (value : Nat) : String :=
  let digits := Nat.toDigits 16 value
  String.ofList ((List.replicate (4 - min 4 digits.length) '0') ++ digits.map Char.toUpper)

/-- Punctuation and operators, by longest match (LX5). -/
def lexPunctuation : LexM Unit := do
  let ⟨source, pos, _, _⟩ ← here
  let opensStatic := lessOpensStatic (← get)
  let closesStatic := innermostIsStatic (← get)
  let b := byteAt source pos
  let next := byteAt source (pos + 1)
  let one (kind : TokenKind) : LexM Unit := do emitAscii kind 1; trackBracket kind
  match b with
  | 0x28 => one .leftParen
  | 0x29 => one .rightParen
  | 0x5B => one .leftBracket
  | 0x5D => one .rightBracket
  | 0x7B => one .leftBrace
  | 0x7D => one .rightBrace
  | 0x2C => emitAscii .comma 1
  | 0x3B => emitAscii .semicolon 1
  | 0x40 => emitAscii .at 1
  | 0x23 => emitAscii .hash 1
  | 0x2A => emitAscii .star 1
  | 0x2F => emitAscii .slash 1
  | 0x25 => emitAscii .percent 1
  | 0x5E => emitAscii .caret 1
  | 0x3A =>
    if next == 0x3A then emitAscii .colonColon 2
    else if next == 0x3D then emitAscii .colonEquals 2
    else emitAscii .colon 1
  | 0x2E => if next == 0x2E then emitAscii .dotDot 2 else emitAscii .dot 1
  | 0x3D => if next == 0x3D then emitAscii .equalEqual 2 else emitAscii .equals 1
  | 0x21 =>
    if next == 0x3D then emitAscii .notEqual 2
    else failHere "LX6" "unexpected character '!'"
  | 0x2D => if next == 0x3E then emitAscii .rightArrow 2 else emitAscii .minus 1
  | 0x2B => if next == 0x2B then emitAscii .plusPlus 2 else emitAscii .plus 1
  | 0x3C =>
    if next == 0x3D then emitAscii .lessEqual 2
    else if next == 0x2D then emitAscii .leftArrow 2
    else if opensStatic then one .staticOpen
    else emitAscii .less 1
  | 0x3E =>
    if closesStatic then one .staticClose
    else if next == 0x3D then emitAscii .greaterEqual 2
    else emitAscii .greater 1
  | _ =>
    let shown := if b < 0x20 ∨ b == 0x7F then s!"U+{hexDigits b.toNat}"
      else s!"'{Char.ofNat b.toNat}'"
    failHere "LX6" s!"unexpected character {shown}"

/-- A string or byte string from its opening quote (LX7). `prefixWidth` is 0 for a string, 1 for
`b"`, 3 for `hex"`. -/
def lexString (kind : TokenKind) (prefixWidth : Nat) : LexM Unit := do
  let ⟨source, pos, line, column⟩ ← here
  let contentStart := pos + prefixWidth + 1
  let mut index := contentStart
  while !isLineEnd source index && byteAt source index != 0x22 do
    index := index + 1
  if isLineEnd source index then
    failHere "LX7" "a string ends on its line"
  -- the characters, all ASCII when valid, so that bytes and columns agree
  for position in [contentStart:index] do
    let c := byteAt source position
    -- a tab in a string is refused by LX3, which says where a tab stands, before LX7
    if c == 0x09 then
      failAt "LX3" "a tab stands only in a comment" line (column + position - pos) position
    if c < 0x20 ∨ c > 0x7E ∨ c == 0x5C then
      failHere "LX7" "a string holds printable ASCII without \" and \\"
  let content := String.fromUTF8! (source.extract contentStart index)
  if kind == .hexString then
    let isHex (c : Char) := c.isDigit ∨ ('a' ≤ c ∧ c ≤ 'f') ∨ ('A' ≤ c ∧ c ≤ 'F')
    if content.length % 2 != 0 ∨ !content.all isHex then
      failHere "LX7" "hex\"...\" holds an even number of hexadecimal digits"
  let width := index + 1 - pos
  emitTo kind pos (index + 1) line column (column + width) content (index + 1) (column + width)

/-- A number: decimal digits without a leading zero, not touching a name (LX8). -/
def lexNumber : LexM Unit := do
  let ⟨source, pos, line, column⟩ ← here
  let mut index := pos
  while isDigit (byteAt source index) do
    index := index + 1
  let text := String.fromUTF8! (source.extract pos index)
  if text.length > 1 ∧ text.front == '0' then
    failHere "LX8" "a number has no leading zero"
  let (code, _) := codeAt source index
  if index < source.size ∧ (Unicode.isXidContinue code) then
    let touching := (String.singleton (Char.ofNat code.toNat))
    failHere "LX8" s!"`{text}{touching}…`: numbers are decimal and a name does not touch a number"
  let width := index - pos
  emitTo .number pos index line column (column + width) text index (column + width)

/-- An identifier or a reserved word (LX6, LX9), or `_` alone. -/
def lexIdentifier : LexM Unit := do
  let ⟨source, pos, line, column⟩ ← here
  let mut index := pos
  let mut characters := 0
  let (_, firstWidth) := decodeAt source index
  index := index + firstWidth
  characters := 1
  while index < source.size do
    let (code, width) := decodeAt source index
    if code < 0x80 ∨ !Unicode.isMathematicalSymbol code then
      if Unicode.isXidContinue code then
        index := index + width
        characters := characters + 1
      else break
    else break
  if index - pos > 128 then
    failHere "LX6" "an identifier has at most 128 bytes"
  let text := String.fromUTF8! (source.extract pos index)
  -- the reserved words are lower-case ASCII words of at most nine letters
  let first := byteAt source pos
  let kind :=
    if text == "_" then TokenKind.underscore
    else if index - pos ≤ 9 ∧ 0x61 ≤ first ∧ first ≤ 0x7A then
      (reservedWordTable.get? text).getD .identifier
    else .identifier
  emitTo kind pos index line column (column + characters)
    (if kind == .identifier then text else "") index (column + characters)

/-- A character that is not ASCII, outside strings and comments. -/
def lexNonAscii : LexM Unit := do
  let ⟨source, pos, line, column⟩ ← here
  let (code, width) := decodeAt source pos
  match mathematicalToken code with
  | some kind =>
    emitTo kind pos (pos + width) line column (column + 1) "" (pos + width) (column + 1)
    trackBracket kind
  | none =>
    let shown := String.singleton (Char.ofNat code.toNat)
    if Unicode.isMathematicalSymbol code then
      failHere "LX10" s!"`{shown}` is not in the table of mathematical forms (∑ ∏ ∀ ∃ ∈ ⟪ ⟫)"
    else if Unicode.isXidStart code then lexIdentifier
    else failHere "LX6" s!"unexpected character {shown}"

/-- Records the comment that starts at the current position and moves to the end of the line. -/
def lexComment (ownLine : Bool) : LexM Unit := do
  let ⟨source, pos, line, column⟩ ← here
  let mut index := pos
  while !isLineEnd source index do
    index := index + 1
  let text := String.fromUTF8! (source.extract pos index)
  modify fun state => { state with
    comments := state.comments.push { text, line, column, startByte := pos, ownLine }
    pos := index, column := column + text.length }

/-- The tokens of the rest of the current line. -/
partial def lexLineTokens : LexM Unit := do
  let ⟨source, start, _, _⟩ ← here
  let mut pos := start
  while byteAt source pos == 0x20 do
    pos := pos + 1
  if pos != start then
    let skipped := pos - start
    modify fun state => { state with pos, column := state.column + skipped }
  if isLineEnd source pos then return
  let b := byteAt source pos
  if b == 0x20 then
    pure ()
  else if b == 0x09 then
    failHere "LX3" "a tab stands only in a comment"
  else if b == 0x2F ∧ byteAt source (pos + 1) == 0x2F then
    lexComment false
  else if b == 0x22 then
    lexString .string 0
  else if b == 0x62 ∧ byteAt source (pos + 1) == 0x22 then
    lexString .byteString 1
  else if b == 0x68 ∧ byteAt source (pos + 1) == 0x65 ∧ byteAt source (pos + 2) == 0x78
      ∧ byteAt source (pos + 3) == 0x22 then
    lexString .hexString 3
  else if isDigit b then
    lexNumber
  else if (0x41 ≤ b ∧ b ≤ 0x5A) ∨ (0x61 ≤ b ∧ b ≤ 0x7A) ∨ b == 0x5F then
    lexIdentifier
  else if b ≥ 0x80 then
    lexNonAscii
  else
    lexPunctuation
  lexLineTokens

/-- LX4: the indentation of a new logical line. -/
def startLogicalLine (width : Nat) : LexM Unit := do
  let (sawLogicalLine, top) := (fun state : State => (state.sawLogicalLine, state.indents.back!)) (← get)
  if !sawLogicalLine then
    if width != 0 then failHere "LX4" "the first line starts at column 0"
    modify fun state => { state with sawLogicalLine := true }
    return
  if width > top then
    if width != top + 4 then
      failHere "LX4" s!"a suite is indented by four spaces, not {width - top}"
    emitLayout .indent
    modify fun state => { state with indents := state.indents.push width }
  else
    let mut current := top
    while width < current do
      modify fun state => { state with indents := state.indents.pop }
      emitLayout .dedent
      current := (← get).indents.back!
    if width != current then
      failHere "LX4" "dedentation must match an enclosing suite"

/-- Moves past the end of the current line. -/
def endLine : LexM Unit := do
  let ⟨source, pos, _, _⟩ ← here
  let width := if byteAt source pos == 0x0D then 2 else 1
  modify fun state =>
    { state with pos := min source.size (pos + width), line := state.line + 1, column := 1 }

/-- One physical line. -/
def lexLine : LexM Unit := do
  let ⟨source, lineStart, _, _⟩ ← here
  let mut index := lineStart
  while byteAt source index == 0x20 ∧ index < source.size do
    index := index + 1
  let spaces := index - lineStart
  modify fun state => { state with pos := index, column := 1 + spaces }
  if isLineEnd source index then
    -- LX2: a blank line produces no token
    endLine
    return
  if byteAt source index == 0x2F ∧ byteAt source (index + 1) == 0x2F then
    lexComment true
    endLine
    return
  if byteAt source index == 0x09 then
    failHere "LX3" "a tab is not indentation"
  let opensLogicalLine := (← get).brackets.isEmpty
  if opensLogicalLine then startLogicalLine spaces
  lexLineTokens
  if (← get).brackets.isEmpty then emitLayout .newline
  endLine

partial def lexLines : LexM Unit := do
  if (← get).pos < (← get).source.size then
    lexLine
    lexLines

/-- The end of the file: every bracket is closed (LX2, LX5) and every suite is closed (LX4). -/
def finish : LexM Unit := do
  if let some innermost := (← get).brackets.back? then
    bracketFailure innermost s!"`{innermost.kind.spelling}` is never closed"
  for _ in [1:(← get).indents.size] do
    emitLayout .dedent
  emitLayout .endOfFile

end Lexer

/-- The lexer: the tokens and comments of a source, or the first refusal of §3.1. -/
def lex (file : String) (source : ByteArray) : Except SyntaxError Lexed := do
  Lexer.checkText source file
  let initial : Lexer.State :=
    { source, file, pos := 0, line := 1, column := 1
      tokens := Array.mkEmpty (source.size / 3), texts := Array.mkEmpty (source.size / 3)
      comments := #[], brackets := #[], indents := #[0], sawLogicalLine := false }
  match (do Lexer.lexLines; Lexer.finish).run initial with
  | .ok _ state => pure { tokens := state.tokens, texts := state.texts, comments := state.comments }
  | .error error _ => throw error

end Zkc.Frontend.Syntax
