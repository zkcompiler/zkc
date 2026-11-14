module

public import Std.Data.HashMap

@[expose] public section

set_option autoImplicit false

namespace Zkc.Frontend.Syntax

/-- The tokens of §3.2, the reserved words of §3.3, and the layout tokens of §3.1.
A reserved word is its own kind; a contextual word (§3.4) is an `identifier`. The `<` that opens
static arguments and the `>` that closes them (LX5) are kinds of their own, so that the parser
never decides between a bracket and a comparison. -/
inductive TokenKind where
  -- names and literals
  | identifier | number | string | byteString | hexString
  -- reserved words (§3.3), in the order of the reference
  | kwModule | kwUse | kwPub | kwAs | kwSection | kwInterface | kwType | kwStruct | kwEnum | kwDef
  | kwProtocol | kwRelation | kwScheme | kwGoal | kwSpec | kwRoles | kwWhere | kwMut | kwGuard
  | kwIf | kwThen | kwElse | kwMatch | kwCase | kwFor | kwIn | kwReturn | kwSend | kwDraw
  | kwSample | kwQuery | kwOpen | kwAttempt | kwAnd | kwOr | kwNot | kwTrue | kwFalse | kwBool
  | kwNat | kwIndex | kwNonzero | kwRational | kwPrimitive | kwAsset | kwExternal | kwSites
  -- punctuation
  | leftParen | rightParen | leftBracket | rightBracket | leftBrace | rightBrace
  | comma | colon | semicolon | dot | dotDot | colonColon | at | hash | underscore
  | equals | colonEquals | leftArrow | rightArrow
  | staticOpen | staticClose
  -- operators
  | plus | minus | star | slash | percent | caret | plusPlus
  | equalEqual | notEqual | less | lessEqual | greater | greaterEqual
  -- mathematical forms
  | sumSign | productSign | forAllSign | existsSign | elementSign | innerOpen | innerClose
  -- layout
  | newline | indent | dedent | endOfFile
  deriving Inhabited, BEq, Repr, DecidableEq

/-- The reserved words, with their kinds. -/
def reservedWords : Array (String × TokenKind) := #[
  ("module", .kwModule), ("use", .kwUse), ("pub", .kwPub), ("as", .kwAs),
  ("section", .kwSection), ("interface", .kwInterface), ("type", .kwType),
  ("struct", .kwStruct), ("enum", .kwEnum), ("def", .kwDef), ("protocol", .kwProtocol),
  ("relation", .kwRelation), ("scheme", .kwScheme), ("goal", .kwGoal), ("spec", .kwSpec),
  ("roles", .kwRoles), ("where", .kwWhere), ("mut", .kwMut), ("guard", .kwGuard),
  ("if", .kwIf), ("then", .kwThen), ("else", .kwElse), ("match", .kwMatch), ("case", .kwCase),
  ("for", .kwFor), ("in", .kwIn), ("return", .kwReturn), ("send", .kwSend), ("draw", .kwDraw),
  ("sample", .kwSample), ("query", .kwQuery), ("open", .kwOpen), ("attempt", .kwAttempt),
  ("and", .kwAnd), ("or", .kwOr), ("not", .kwNot), ("true", .kwTrue), ("false", .kwFalse),
  ("bool", .kwBool), ("nat", .kwNat), ("index", .kwIndex), ("nonzero", .kwNonzero),
  ("rational", .kwRational), ("primitive", .kwPrimitive), ("asset", .kwAsset),
  ("external", .kwExternal), ("sites", .kwSites)]

def reservedWordTable : Std.HashMap String TokenKind :=
  reservedWords.foldl (fun table (word, kind) => table.insert word kind) {}

namespace TokenKind

def isReservedWord (kind : TokenKind) : Bool :=
  reservedWords.any (·.2 == kind)

/-- The spelling of a token kind that has one, for messages. -/
def spelling : TokenKind → String
  | .identifier => "a name" | .number => "a number" | .string => "a string"
  | .byteString => "a byte string" | .hexString => "a byte string"
  | .leftParen => "(" | .rightParen => ")" | .leftBracket => "[" | .rightBracket => "]"
  | .leftBrace => "{" | .rightBrace => "}" | .comma => "," | .colon => ":"
  | .semicolon => ";" | .dot => "." | .dotDot => ".." | .colonColon => "::" | .at => "@"
  | .hash => "#" | .underscore => "_" | .equals => "=" | .colonEquals => ":="
  | .leftArrow => "<-" | .rightArrow => "->" | .staticOpen => "<" | .staticClose => ">"
  | .plus => "+" | .minus => "-" | .star => "*" | .slash => "/" | .percent => "%"
  | .caret => "^" | .plusPlus => "++" | .equalEqual => "==" | .notEqual => "!="
  | .less => "<" | .lessEqual => "<=" | .greater => ">" | .greaterEqual => ">="
  | .sumSign => "∑" | .productSign => "∏" | .forAllSign => "∀" | .existsSign => "∃"
  | .elementSign => "∈" | .innerOpen => "⟪" | .innerClose => "⟫"
  | .newline => "the end of the line" | .indent => "an indented line"
  | .dedent => "the end of the suite" | .endOfFile => "the end of the file"
  | kind => match reservedWords.find? (·.2 == kind) with
    | some (word, _) => word
    | none => "a token"

end TokenKind

/-- A token: its kind and where it is. A token never spans lines; `newline`, `indent`, `dedent`
and `endOfFile` have no width. -/
structure Token where
  kind : TokenKind
  startByte : UInt32
  stopByte : UInt32
  line : UInt32
  column : UInt32
  stopColumn : UInt32
  deriving Inhabited

/-- A comment, with its text from `//` to the end of the line. `ownLine` is true when only spaces
stand before it on its line. -/
structure Comment where
  text : String
  line : Nat
  column : Nat
  startByte : Nat
  ownLine : Bool
  deriving Inhabited, Repr

end Zkc.Frontend.Syntax
