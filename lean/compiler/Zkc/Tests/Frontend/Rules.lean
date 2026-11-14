import Zkc.Tests.Frontend.Harness
import Zkc.Tests.Frontend.RuleCases

/-!
# The rules of §3 and §5, one by one

The programs of `RuleCases`, the contextual words of §3.4, the tests that need raw bytes, the
shapes that precedence gives, the two spellings of each mathematical form, and the canonical
printer (FM1, FM2, FM3).
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend.Syntax

/-- Checks one block against `accept`, `refuse R` or `refuse R line:column`. -/
def checkExpectation (label expect : String) (result : Except SyntaxError (Array SourceFile)) :
    TestM Unit := do
  let words := (expect.splitOn " ").filter (· != "")
  match words, result with
  | "accept" :: _, .ok files =>
    pass
    for index in [0:files.size] do checkPrinter s!"{label}.{index}" files[index]!
  | "accept" :: _, .error error => failure s!"{label}: expected to parse; {error.render}"
  | "refuse" :: rule :: rest, .error error =>
    if error.rule != rule then
      failure s!"{label}: expected a refusal by {rule}; {error.render}"
    else match rest with
      | [position] =>
        expectTrue (position == s!"{error.line}:{error.column}")
          s!"{label}: refused by {rule} at {error.line}:{error.column}, expected at {position}"
      | _ => pass
  | "refuse" :: rule :: _, .ok _ => failure s!"{label}: parses; expected a refusal by {rule}"
  | _, _ => failure s!"{label}: unreadable expectation `{expect}`"

def ruleCaseSuite : TestM Unit := do
  let blocks := readBlocks ruleCases
  for block in blocks do
    checkExpectation block.id block.expect (parseBlock block)
  note s!"{blocks.size} programs for the rules of §3 and §5"

def contextualWordSuite : TestM Unit := do
  for word in contextualWords do
    checkExpectation s!"contextual word `{word}`" "accept"
      ((#[·]) <$> parseString word (contextualWordProgram word))
  note s!"{contextualWords.size} contextual words used as names"

def bytesOf (text : String) : ByteArray := text.toUTF8

def checkBytes (label expect : String) (source : ByteArray) : TestM Unit :=
  checkExpectation label expect ((#[·]) <$> parse label source)

/-- The rules that need bytes which a text block cannot hold. -/
def byteSuite : TestM Unit := do
  let program (body : String) : String := "module t\ntype T = primitive(\"x\")\n" ++ body
  -- LX1: line ends, UTF-8 and Normalization Form C
  checkBytes "LX1 CR LF" "accept" (bytesOf "module t\r\ntype T = primitive(\"x\")\r\n")
  checkBytes "LX1 lone CR" "refuse LX1 1:9" (bytesOf "module t\rtype T = primitive(\"x\")\n")
  checkBytes "LX1 precomposed" "accept" (bytesOf (program "// café\n"))
  checkBytes "LX1 decomposed" "refuse LX1 3:8" (bytesOf (program "// café\n"))
  checkBytes "LX1 reordered marks" "refuse LX1 3:8" (bytesOf (program "// cafẹ́\n"))
  checkBytes "LX1 normalized marks" "accept" (bytesOf (program "// cafẹ́\n"))
  checkBytes "LX1 Hangul jamo" "refuse LX1 3:5" (bytesOf (program "// 가\n"))
  checkBytes "LX1 Hangul syllable" "accept" (bytesOf (program "// 가\n"))
  checkBytes "LX1 singleton" "refuse LX1 3:4" (bytesOf (program "// Å\n"))
  checkBytes "LX1 not UTF-8" "refuse LX1 3:4"
    ((bytesOf (program "// ")).push 0xFF |>.push 0x0A)
  checkBytes "LX1 overlong" "refuse LX1 3:4"
    (((bytesOf (program "// ")).push 0xC0).push 0x80 |>.push 0x0A)
  -- LX2, LX4: the end of the file ends the last line and closes every suite
  checkBytes "LX4 no final line end" "accept"
    (bytesOf "module t\ndef f(a: nat) -> nat:\n    b = a\n    return b")
  checkBytes "LX2 spaces only" "accept" (bytesOf "module t\n    \ndef f() -> nat: 1\n        \n")
  -- LX3: tabs
  checkBytes "LX3 tab in a comment" "accept" (bytesOf (program "// a\ttab\n"))
  checkBytes "LX3 tab indentation" "refuse LX3 3:1"
    (bytesOf "module t\ndef f(a: nat) -> nat:\n\treturn a\n")
  checkBytes "LX3 tab between tokens" "refuse LX3 2:5" (bytesOf "module t\ntype\tT = primitive(\"x\")\n")
  checkBytes "LX3 tab in a string" "refuse LX3 2:22" (bytesOf "module t\ntype T = primitive(\"a\tb\")\n")
  -- LX6: the length of an identifier
  let name128 := "".pushn 'a' 128
  checkBytes "LX6 128 bytes" "accept" (bytesOf s!"module t\ndef {name128}() -> nat: 1\n")
  checkBytes "LX6 129 bytes" "refuse LX6 2:5" (bytesOf s!"module t\ndef {name128}b() -> nat: 1\n")
  checkBytes "LX6 control character" "refuse LX6 2:5" (bytesOf "module t\ndef \u0001() -> nat: 1\n")
  note "byte-level tests of LX1, LX2, LX3, LX4, LX6"

/-- The expression of the body of `def f`, for the tests of precedence. -/
def bodyExpression (text : String) : Option Expr :=
  match parseString "expression" s!"module t\ndef f() -> nat: {text}\n" with
  | .ok { tree := { items := #[.«def» { binding := .body (.expression _ value), .. }], .. }, .. } =>
    some value
  | _ => none

/-- The shape of an expression: its operators with explicit grouping, the parentheses of the
source as `paren`. -/
partial def shape : Expr → String
  | .ifExpr _ c a b => s!"(if {shape c} {shape a} {shape b})"
  | .orExpr _ a b => s!"(or {shape a} {shape b})"
  | .andExpr _ a b => s!"(and {shape a} {shape b})"
  | .notExpr _ a => s!"(not {shape a})"
  | .compare _ op a b =>
    let text := match op with
      | .equal => "==" | .notEqual => "!=" | .less => "<" | .lessEqual => "<="
      | .greater => ">" | .greaterEqual => ">="
    s!"({text} {shape a} {shape b})"
  | .sum _ op a b =>
    s!"({match op with | .add => "+" | .subtract => "-" | .concatenate => "++"} {shape a} {shape b})"
  | .product _ op a b =>
    s!"({match op with | .multiply => "*" | .divide => "/" | .remainder => "%"} {shape a} {shape b})"
  | .unary _ a => s!"(neg {shape a})"
  | .power _ a b => s!"(^ {shape a} {shape b})"
  | .paren _ a => s!"(paren {shape a})"
  | .number n => toString n.value
  | .path _ p => match p.plainName? with | some n => n.text | none => "path"
  | .call _ p _ => s!"(call {match p.plainName? with | some n => n.text | none => "path"})"
  | .binderForm .. => "binder"
  | _ => "other"

def precedenceSuite : TestM Unit := do
  let cases : List (String × String) := [
    ("-x^2", "(neg (^ x 2))"),
    ("2^-128", "(^ 2 (neg 128))"),
    ("a^b^c", "(^ a (^ b c))"),
    ("a - b - c", "(- (- a b) c)"),
    ("a + b * c", "(+ a (* b c))"),
    ("a * b % c / d", "(/ (% (* a b) c) d)"),
    ("a ++ b + c", "(+ (++ a b) c)"),
    ("not a == b", "(not (== a b))"),
    ("not not a", "(not (not a))"),
    ("a or b and c", "(or a (and b c))"),
    ("a and b or c", "(or (and a b) c)"),
    ("a < b and c >= d", "(and (< a b) (>= c d))"),
    ("-a * b", "(* (neg a) b)"),
    ("(a + b) * c", "(* (paren (+ a b)) c)"),
    ("if a then b else c + 1", "(if a b (+ c 1))"),
    ("x == ∑ v ∈ xs, v + 1", "(== x binder)")]
  for (text, expected) in cases do
    match bodyExpression text with
    | some value =>
      expectTrue (shape value == expected) s!"`{text}` has the shape {shape value}, not {expected}"
    | none => failure s!"`{text}` does not parse as an expression"
  note s!"{cases.length} expressions whose shape precedence decides"

/-- The two spellings of each mathematical form give the same node, which records the spelling;
the printer keeps the spelling (FM3). -/
def spellingSuite : TestM Unit := do
  let pairs : List (String × String) := [
    ("∑ x ∈ xs, x * 2", "sum([x * 2 for x in xs])"),
    ("∏ x ∈ 0..n, x + 1", "product([x + 1 for x in 0..n])"),
    ("∀ (x, y) ∈ pairs, x == y", "all([x == y for (x, y) in pairs])"),
    ("∃ x ∈ xs, x == 0", "any([x == 0 for x in xs])"),
    ("⟪xs, ys⟫", "inner(xs, ys)")]
  for (symbol, named) in pairs do
    let source (text : String) := s!"module t\ndef f() -> bool: {text}\n"
    match parseString "symbol" (source symbol), parseString "named" (source named) with
    | .ok a, .ok b =>
      let dumpA := (treeText a.tree).replace " symbol" " named"
      expectTrue (dumpA == treeText b.tree) s!"`{symbol}` and `{named}` give different nodes"
      expectTrue (((treeText a.tree).splitOn " symbol").length > 1) s!"`{symbol}`: no spelling"
      expectTrue ((formatSourceFile a).contains '∑' || (formatSourceFile a).contains '∏'
        || (formatSourceFile a).contains '∀' || (formatSourceFile a).contains '∃'
        || (formatSourceFile a).contains '⟪') s!"`{symbol}`: the formatter changed the spelling"
      expectTrue (((formatSourceFile b).splitOn named).length == 2)
        s!"`{named}`: the formatter changed the spelling"
    | _, _ => failure s!"`{symbol}` or `{named}` does not parse"
  -- a call of `sum` on a collection, or with a condition, is a call
  for text in ["sum(xs)", "sum([x for x in xs if x == 0])", "inner(xs)", "zkc::sum([x for x in xs])"] do
    match bodyExpression text with
    | some (.call ..) => pass
    | _ => failure s!"`{text}` is not a call"
  note s!"{pairs.length} mathematical forms in both spellings"

/-- The canonical text of `source`, or the refusal. -/
def formatted (source : String) : String :=
  match parseString "format" source with
  | .ok parsed => formatSourceFile parsed
  | .error error => error.render

def checkFormat (label source expected : String) : TestM Unit := do
  let result := formatted source
  expectTrue (result == expected) s!"{label}: the canonical text is\n{result}\nnot\n{expected}"

def printerSuite : TestM Unit := do
  -- FM2: `#[site(x)]` on the binder `x` is removed; on another binder it is kept
  checkFormat "site attribute on its binder"
    "module t\nprotocol X roles(P, V)(a: nat @P):\n    #[site(x)]\n    x <- send a to V\n    #[site(y)]\n    (z, w) <- send (a, a) to V\n"
    "module t\n\nprotocol X roles(P, V)(a: nat @P):\n    x <- send a to V\n    #[site(y)]\n    (z, w) <- send (a, a) to V\n"
  -- FM2: a role mapped to its namesake is removed, and the map when it is empty
  checkFormat "role map"
    "module t\nprotocol C roles(P, R)():\n    x <- send 1 from P to R\nprotocol X roles(P, V)():\n    y <- C() @(P = P, R = V)\n    z <- C() @(P = P, R = R)\n"
    "module t\n\nprotocol C roles(P, R)():\n    x <- send 1 from P to R\n\nprotocol X roles(P, V)():\n    y <- C() @(R = V)\n    z <- C()\n"
  -- FM2: `else reject`, `-> ()`; FM1: one role without parentheses, roles in roster order
  checkFormat "annotations"
    "module t\ndef f() -> ():\n    guard 1 < 2 else reject\n    return ()\nprotocol X roles(P, V)(a: nat @(V, P), b: nat @(P)):\n    x @(P, V) = a + b\n    guard @(V) a == b else abort\n"
    "module t\n\ndef f():\n    guard 1 < 2\n    return ()\n\nprotocol X roles(P, V)(a: nat @(P, V), b: nat @P):\n    x @(P, V) = a + b\n    guard @V a == b else abort\n"
  -- FM1: a body of `return e` alone is an expression body
  checkFormat "expression body" "module t\ndef f() -> nat:\n    return 1\n"
    "module t\n\ndef f() -> nat:\n    1\n"
  -- FM1: one blank line between top-level items, consecutive `use` items as in the source
  checkFormat "blank lines"
    "module t\nuse a::b\nuse a::c\n\n\nuse a::d\ndef f() -> nat: 1\n// about g\n\ndef g() -> nat:\n    x = 1\n\n\n    return x\n"
    "module t\n\nuse a::b\nuse a::c\n\nuse a::d\n\ndef f() -> nat: 1\n\n// about g\n\ndef g() -> nat:\n    x = 1\n\n    return x\n"
  -- FM1: a logical line of 100 characters stays; one of 101 is broken after its commas
  let line100 := "def f(a: nat, b: nat) -> nat: " ++ "".pushn 'x' 64 ++ "(a, b)"
  checkFormat "100 characters" s!"module t\n{line100}\n" s!"module t\n\n{line100}\n"
  let line101 := "def f(a: nat, b: nat) -> nat: " ++ "".pushn 'x' 65 ++ "(a, b)"
  checkFormat "101 characters" s!"module t\n{line101}\n"
    s!"module t\n\ndef f(\n    a: nat,\n    b: nat\n) -> nat: {"".pushn 'x' 65}(a, b)\n"
  -- FM1: a line without a bracket that holds a comma stays long
  let long := "def f(a: nat) -> nat: " ++ String.intercalate " + " (List.replicate 30 "a")
  checkFormat "no place to break" s!"module t\n{long}\n" s!"module t\n\n{long}\n"
  -- comments stay, before the construct that follows them
  checkFormat "comments"
    "// head\nmodule t\n// before f\ndef f() -> nat: 1 // after f\n    // end of f\n// end of file\n"
    "// head\nmodule t\n\n// before f\ndef f() -> nat: 1\n// after f\n// end of f\n// end of file\n"
  note "printer: FM1 layout, FM2 annotations, comments"

end Zkc.Tests.Frontend
