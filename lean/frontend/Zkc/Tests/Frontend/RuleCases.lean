/-!
# Test programs for the rules of §3 and §5

In the block format of the conformance tests. `expect` is `accept`, or `refuse <rule>`, or
`refuse <rule> <line>:<column>` when the position is checked too. Tests that need bytes a text
block cannot hold (a carriage return, a tab, an invalid byte) are in `Rules.lean`.
-/

namespace Zkc.Tests.Frontend

def ruleCases : String := r##"
=== LX2-continuation | accept | LX2: a logical line continues inside brackets, at any indentation
module t
def f(
  a: nat,
          b: nat
) -> nat: a + (
b)

=== LX2-blank-lines | accept | LX2: blank lines and comment lines at any column, in and out of brackets
module t

  // a comment at column 3
def f(a: nat) -> nat:

    b = a
 // a comment at column 2 inside the suite
      // and at column 7
    return [
        // inside a bracket
        b
    ][0]

=== LX2-operator-at-end | refuse LX2 2:26 | LX2: a logical line does not continue after an operator
module t
def f(a: nat) -> nat: a *
    2

=== LX2-inner-product | accept | LX2: ⟪ ⟫ is a bracket
module t
type F = primitive("bls12-381.fr")
def f(a: [F; 2], b: [F; 2]) -> F: ⟪a,
    b⟫

=== LX2-static-bracket | accept | LX2: a static bracket is a bracket
module t
section <
    F: Field,
    n: nat
> where (1 <= n):
    def zero() -> F: 0

=== LX4-dedent-two | accept | LX4: one line closes two suites
module t
def f(a: nat) -> nat:
    mut b = a
    for i in 0..a:
        if i < 2:
            b := b + i
    return b

=== LX4-dedent-three | accept | LX4: one line closes three suites, and a comment between them is not a line
module t
protocol X roles(P, V)(a: nat @P):
    for i in 0..a:
        if i < 2:
            match i:
                case 0:
                    x <- send i from P to V
                        // a comment deeper than any suite
                case _:
                    ()
  // a comment at an odd column
    y <- send a to V

=== LX4-two-spaces | refuse LX4 3:3 | LX4: a suite is indented by four spaces
module t
def f(a: nat) -> nat:
  return a

=== LX4-dedent-mismatch | refuse LX4 4:3 | LX4: dedentation must match an enclosing suite
module t
def f(a: nat) -> nat:
    b = a
  return b

=== LX4-first-line | refuse LX4 1:5 | LX4: the first logical line has indentation 0
    module t

=== LX4-indent-after-header | refuse GR 2:5 | LX4: an indented line after the header opens a suite that no production admits
module t
    def f() -> nat: 1

=== LX5-spaced | accept | LX5: a comparison has a space before `<`; `a<=b` is `a <= b`
module t
def f(a: nat, b: nat) -> bool: a < b and a<=b and b>=a and a > b

=== LX5-arrow | accept | LX5: `a<-1` contains `<-`, by longest match
module t
type F = primitive("bls12-381.fr")
protocol X roles(P, V)(a: F @P):
    y<-send a to V

=== LX5-closing-equals | accept | LX5: inside a static bracket `>=` is not formed, so `T<n>= e` closes the bracket
module t
type Small<n: nat>= index<n>

=== LX5-section | accept | LX5: `<` after the word `section` opens static parameters
module t
section <F: Field>:
    def zero() -> F: 0

=== LX5-touching | refuse LX5 2:41 | LX5: `<` touching a name opens static arguments
module t
def f(a: nat, b: nat, c: nat) -> bool: a<b and c > b

=== LX5-spaced-static | refuse LX5 2:16 | LX5: `index <4>` with a space is a comparison
module t
def f(x: index <4>) -> nat: x

=== LX6-unicode | accept | LX6: identifiers of XID characters
module t
def f(α: nat, βeta_2: nat, 名前: nat) -> nat: α + βeta_2 + 名前

=== LX6-underscore | accept | LX6: `_x` is a name and `_` the wildcard
module t
def f(_x: nat) -> nat:
    (_, y) = (_x, _x)
    return y

=== LX6-character | refuse LX6 2:23 | LX6: a character that is no token
module t
def f(a: nat) -> nat: $a

=== LX6-unbalanced | refuse LX6 2:24 | LX6: a closing bracket without an opening one
module t
def f(a: nat) -> nat: a)

=== LX6-never-closed | refuse LX6 2:23 | LX6: a bracket that is never closed
module t
def f(a: nat) -> nat: (a

=== LX6-mismatched | refuse LX6 2:25 | LX6: a bracket closed by another kind
module t
def f(a: nat) -> nat: [a)

=== LX7-comment-in-string | accept | LX7: `//` inside a string is text
module t
type T = primitive("a//b")

=== LX7-byte-strings | accept | LX7: b"…" and hex"…" with digits of either case
module t
def f() -> [byte; 3]: b"a/b"
def g() -> [byte; 2]: hex"0aFF"

=== LX7-unterminated | refuse LX7 2:20 | LX7: a string ends on its line
module t
type T = primitive("abc

=== LX7-backslash | refuse LX7 | LX7: a string has no escape
module t
type T = primitive("a\"b")

=== LX7-hex-digit | refuse LX7 | LX7: hex"…" holds hexadecimal digits
module t
def f() -> [byte; 1]: hex"0g"

=== LX7-non-ascii | refuse LX7 | LX7: a string holds printable ASCII
module t
type T = primitive("é")

=== LX8-large | accept | LX8: a number has no largest value
module t
def f() -> nat: 1234567890123456789012345678901234567890 + 0

=== LX8-leading-zero | refuse LX8 2:17 | LX8: a number has no leading zero
module t
def f() -> nat: 007

=== LX8-touching | refuse LX8 2:17 | LX8: a name does not touch a number
module t
def f() -> nat: 12abc

=== LX9-prelude-names | accept | LX9: `byte`, `length` and the sorts are names, not reserved words
module t
def f(length: nat, byte: nat, Field: nat) -> nat: length + byte + Field

=== LX9-reserved | refuse LX9 2:5 | LX9: a reserved word is not a name
module t
def type(x: nat) -> nat: x

=== LX10-forms | accept | LX10: the forms of the table
module t
type F = primitive("bls12-381.fr")
def f(xs: [F; 4], ys: [F; 4]) -> bool:
    s = ∑ x ∈ xs, x
    p = ∏ x ∈ xs, x
    q = ⟪xs, ys⟫
    return (∀ x ∈ xs, x == 0) or (∃ i ∈ 0..4, xs[i] == ys[i]) or s == p + q

=== LX10-other-symbol | refuse LX10 2:34 | LX10: `≤` is not in the table
module t
def f(a: nat, b: nat) -> bool: a ≤ b

=== LX10-partial | refuse LX10 2:23 | LX10: `∂` is not in the table
module t
def f(a: nat) -> nat: ∂a

=== GR-forms | accept | GR: one program with every declaration head
module t
use zkc::option::{Option, Some,}
pub use zkc::algebra as algebra
type F = primitive("bls12-381.fr")
pub spec type Poly = external("Zkc.Polynomial")
pub linear struct Ticket<T>:
    pub value: T
    point: [T]
enum Side:
    Left
    Right(nat, bool)
interface Empty
pub interface Carrier<n: nat> where (1 <= n):
    type T: Group + linear
    nat Size
    module Inner: Carrier<1>
    partial def get(xs: [T], i: nat) -> T
    spec def describe(x: T) -> bool
    protocol Ask roles(P, V)(x: T @P) -> y: T @V
    law size_positive(): 1 <= Size
module Leaf: Carrier<1> = primitive("test.leaf", n = 1)
module Data: Assets = asset(numbers)
#[kernel("test.add")]
pub def add(a: nat, b: nat) -> nat where (1 <= 2): a + b
pub entry def run(a: nat) -> nat: a
spec def holds(a: nat) -> bool = external("Zkc.Test.holds")
def row(a: nat) -> nat = primitive("test.row")
pub oracle def doubled<n: nat>(word: Oracle<W>): Rows<F, n> where (1 <= n):
    at i: 2 * word[i]
pub spec protocol Ideal roles(P)(spec secret: nat, x: nat @P private) -> (a: nat @P, b: nat @(P)):
    return (x, x)
relation R(a: nat; w: nat): a == w
spec for Ideal:
    requires holds(x)
    ensures named: a == b
    invariant a == a at i
    reduces @P R(x; x) to true
    proves @P label: R(x; x)
    through R(x; x) at i
    knowledge R(x) by extract or Other(x) by recover
    zero_knowledge honest: by simulate using coins, programming, trapdoor
    zero_knowledge by external("Zkc.Test.simulate")
    charge sites.challenge.inner <= 1 / 2^128
scheme S = Ideal<F>:
    construction derived(zkc::suites::Merlin)
    prover P
    offline D
    ideal Q, R
    context label: [byte; 4]
    commit sites.trace with Kzg(prover_key = sites.setup, verifier_key = sites.setup.vk)
    commit F with Kzg
    pin sites.setup = zkc::hash::Sha256: hex"00ff"
    grind 16 bits at sites.challenge, sites.other
    retry 8 from sites.tries
    samples derived by zkc::suites::Uniform
    layout zkc::layout::canonical:
        carry sites.challenge
        recover sites.response by recompute
    layout zkc::layout::canonical
goal G = zkc::goals::Soundness(S, statement = fixed, claims = (a, b), spec e = 3) <= 2^-64
nat N = 4

=== GR-unexpected | refuse GR 2:16 | GR: a token that no production admits
module t
def f() -> nat 1

=== GR-chain | refuse GR 2:46 | GR: comparisons do not chain
module t
def f(a: nat, b: nat, c: nat) -> bool: a < b < c

=== GR1-expression-body | accept | GR1: a body that is one expression in a suite
module t
def f(a: nat) -> nat:
    a + 1

=== GR1-if-expression | accept | GR1: after `if Expr`, `then` makes an expression
module t
def f(a: nat) -> nat:
    if a < 1 then 0 else a

=== GR1-record-pattern | accept | GR1: a record pattern at the start of a body is a statement
module t
struct Pair<T>:
    pub left: T
    pub right: T
def f(p: Pair<nat>) -> nat:
    Pair{left, right = r} = p
    (a, _): (nat, nat) = (left, r)
    return a

=== GR1-application | accept | GR1: in a protocol body a call alone on its line is an application
module t
protocol C roles(P, V)():
    x <- send 1 from P to V
protocol X roles(P, V)():
    C()
    C() @(P = P, V = V)
    #[site(again)]
    C()

=== GR1-protocol-expression | refuse GR1 4:5 | GR1: an expression is not a statement
module t
protocol X roles(P, V)(a: nat @P):
    b @P = a
    a + b

=== GR1-body-expression | refuse GR1 4:5 | GR1: a body is one expression, or statements and `return`
module t
def f(a: nat) -> nat:
    b = a
    b + 1

=== GR1-not-pattern | refuse GR1 3:5 | GR1: this is not a pattern
module t
def f(a: (nat, nat)) -> nat:
    a.0 = 1
    return a.1

=== GR1-wildcard | refuse GR1 3:9 | GR1: `_` is a pattern, not an expression
module t
def f(a: nat) -> nat:
    b = _
    return b

=== GR1-law-statements | refuse GR1 | §5.11: the body of a law is one expression
module t
law l(a: nat):
    b = a
    return b == a

=== GR1-relation-statements | refuse GR1 | §5.12: the body of a relation is one expression
module t
relation R(a: nat):
    b = a
    return b == a

=== GR1-missing-return | refuse FN4 | GR1: statements end with `return`
module t
def f(a: nat) -> nat:
    b = a
    c = b

=== GR1-return-not-last | refuse CT5 | `return` is the last line of a body
module t
def f(a: nat) -> nat:
    return a
    b = a

=== GR1-refutable | refuse TY13 3:5 | GR1, TY13: a pattern outside `case` is irrefutable
module t
def f(x: nat) -> nat:
    (1, y) = (x, x)
    return y

=== GR2-parenthesized | accept | GR2: an `if` expression in parentheses
module t
protocol X roles(P, V)(c: bool @P, a: bool @P):
    guard @P (if c then a else true)
def g(c: bool) -> nat: 1 + (if c then 1 else 2)
def h(c: bool) -> nat: [if c then 1 else 2 for i in 0..2][0]

=== GR2-operand | refuse GR2 2:28 | GR2: an `if` expression that is an operand is parenthesized
module t
def g(c: bool) -> nat: 1 + if c then 1 else 2

=== GR2-guard | refuse GR2 3:14 | GR2: the condition of a guard
module t
protocol X roles(P, V)(c: bool @P, a: bool @P):
    guard @P if c then a else reject

=== GR3-update | accept | GR3: `:=` updates a `mut` name
module t
def f(a: nat) -> nat:
    mut b = a
    b := b + 1
    return b

=== GR3-element | refuse GR3 4:10 | GR3: `:=` updates a name, not an element
module t
def f(a: [nat; 2]) -> [nat; 2]:
    mut b = a
    b[0] := 1
    return b

=== GR3-field | refuse GR3 5:13 | GR3: `:=` updates a name, not a field
module t
struct Box:
    value: nat
def f(a: Box) -> Box:
    a.value := 1
    return a

=== GR4-member-def | accept | GR4: member definitions and definitions in an implementing module
module t
interface I:
    def zero() -> nat
    def add(a: nat, b: nat) -> nat
    def one(a: nat) -> nat
    spec def describe(a: nat) -> bool
module M: I:
    def zero(): 0
    def add(a, b): a + b
    def one(a): a
    def helper() -> nat: 0
    def double(x: nat) -> nat: 2 * x
    spec def describe(a) = external("Zkc.Test.describe")
    #[kernel("test.add")]
    def plus(a, b): a + b
    module Inner = zkc::option
    nat Width = 4

=== GR4-typed-member | refuse GR 5:17 | GR4: after `def Name (` a name and `,` make a member definition, whose parameters have no type
module t
interface I:
    def add(a: nat, b: nat) -> nat
module M: I:
    def add(a, b: nat): a + b

=== GR5-static-terms | accept | GR5: a static argument is a type, a natural or a module, read by one production
module t
type F = primitive("bls12-381.fr")
struct Pair<A, B>:
    pub left: A
    pub right: B
type T1 = Pair<[F; 4], (F, nat)>
type T2 = Pair<index<4>, nonzero<F>>
type T3 = Pair<(a: F, b: bool), rational>
type T4 = Pair<_, [[F; 2]; 3]>
def f<n: nat>(x: [F; 2 * n + 1]) -> Pair<nat, [F; n]> where (n <= 4, 2^n: nat):
    Pair{left = 0, right = x[0..n]}

=== GR5-named-outside | refuse GR 2:32 | GR5: a named component stands only in a static term
module t
def f() -> (a: nat, b: nat): (a: 1, b: 2)

=== GR6-names | accept | GR6: `fn`, `distribution` and `affine` are names
module t
def fn_of(distribution: nat, affine: nat) -> nat:
    fn = distribution + affine
    return fn

=== GR6-function-type | refuse GR6 2:14 | GR6: a function type has no production
module t
def apply(f: fn(nat) -> nat) -> nat: 0

=== GR6-function-literal | refuse GR6 2:30 | GR6: a function literal has no production
module t
def total(xs: [nat]) -> nat: fn(x) => x

=== GR6-distribution | refuse GR6 2:1 | GR6: `distribution` has no production
module t
distribution D: nat = decode

=== GR6-affine | refuse GR6 2:1 | GR6: `affine` has no production
module t
affine struct Once:
    value: nat

=== added-spec-parameter | accept | `spec` in a static parameter list
module t
def f<spec e: nat>(x: nat) -> nat: x
section <F: Field, spec e: nat>:
    pub relation NearZero(; xs: [F; 4]): (∑ i ∈ 0..4, if xs[i] == 0 then 0 else 1) <= e

=== added-spec-parameter-refused | refuse SP11 2:7 | `spec` marks a natural
module t
def f<spec T>(x: nat) -> nat: x

=== added-spec-argument | accept | a specification argument among the static arguments of an application
module t
protocol C<n: nat, spec e: nat> roles(P, V)():
    x <- send 1 from P to V
protocol X roles(P, V)():
    y <- C<4, spec e = 3>()
    z <- C<n = 4, spec e = 2 + 1>() @(P = P)

=== added-spec-argument-refused | refuse SP11 5:24 | a specification argument stands after the other static arguments
module t
protocol C<n: nat, spec e: nat> roles(P, V)():
    x <- send 1 from P to V
protocol X roles(P, V)():
    y <- C<spec e = 3, 4>()

=== added-spec-goal | accept | `spec` in a goal
module t
goal G = zkc::goals::Soundness(S, statement = fixed, spec e = 3)

=== added-spec-goal-refused | refuse GR | a specification argument of a goal has a value
module t
goal G = zkc::goals::Soundness(S, spec e)

=== added-where-law | accept | a `where` on a law
module t
law bounded<n: nat>(x: index<n>) where (1 <= n): x < n

=== added-where-law-refused | refuse GR | the `where` of a law stands before its body
module t
law bounded<n: nat>(x: index<n>): x < n where (1 <= n)

=== added-where-relation | accept | a `where` on a relation
module t
relation Sorted<n: nat>(xs: [nat; n]) where (1 <= n): ∀ i ∈ 0..n - 1, xs[i] <= xs[i + 1]

=== added-where-relation-refused | refuse GR | the `where` of a relation stands before its body
module t
relation Sorted<n: nat>(xs: [nat; n]): ∀ i ∈ 0..n - 1, xs[i] <= xs[i + 1] where (1 <= n)

=== added-law-items | accept | a `law` at module level, in a section and in a nested module
module t
nat Limbs = 4
law limbs_cover(): 8 * Limbs == 32
section <n: nat>:
    law small(x: index<n>): x < n
module inner:
    def two() -> nat: 2
    law two_is_two(): two() == 2

=== added-law-refused | refuse GR | `law` without a parameter list is a name
module t
law limbs_cover: 1 == 1

=== added-static-names | accept | a static name at module and section level and in a module
module t
nat N = 4
pub nat M = N * 2
section <F: Field>:
    nat K = 3
module inner:
    pub nat Width = 8

=== added-static-name-refused | refuse GR | a static name has a size
module t
nat N

=== added-module-without-bound | accept | a module with a body and no bound
module t
module inner<k: nat>:
    pub def size() -> nat: 2^k
def f() -> nat: inner<3>::size()

=== added-module-refused | refuse GR | a module has a suite or a binding
module t
module inner<k: nat>

=== added-relation-external | accept | a relation bound to the formal library
module t
relation Close(word: [nat; 4]) = external("Zkc.Test.close")

=== added-relation-asset | refuse NL9 2:25 | a relation is not bound to an asset
module t
relation Data(x: nat) = asset(numbers)

=== spelling-forms | accept | both spellings of every mathematical form
module t
type F = primitive("bls12-381.fr")
def f(xs: [F; 4], ys: [F; 4]) -> bool:
    a = (∑ x ∈ xs, x) + sum([x for x in xs])
    b = (∏ x ∈ 0..4, xs[x]) * product([xs[x] for x in 0..4])
    c = (∀ x ∈ xs, x == 0) and all([x == 0 for x in xs])
    d = (∃ x ∈ xs, x == 0) or any([x == 0 for x in xs])
    return a + b == ⟪xs, ys⟫ + inner(xs, ys) and c and d

=== operators | accept | every operator, with its precedence
module t
def f(a: nat, b: nat, c: bool, xs: [nat; 4]) -> bool:
    x = -a^2 + a * b / 2 % 3 - (a ++ b)
    y = 2^-128
    return not a == b or c and a != b and a < b or a <= b and a > b or a >= b
"##

/-- The contextual words of §3.4. Each is used as a name where a name stands. -/
def contextualWords : Array String := #[
  "entry", "oracle", "linear", "partial", "law", "Self", "from", "to", "at", "deferred",
  "collect", "with", "private", "site", "kernel", "reject", "abort", "refused", "exhausted",
  "requires", "ensures", "invariant", "reduces", "proves", "through", "knowledge",
  "zero_knowledge", "charge", "by", "using", "coins", "programming", "trapdoor", "prover_key",
  "verifier_key", "written", "committed", "constructed", "serialized", "fixed", "adaptive",
  "hidden", "observed", "residual", "construction", "prover", "offline", "ideal", "context",
  "commit", "pin", "grind", "retry", "samples", "layout", "derived", "interactive", "authored",
  "bits", "carry", "recover"]

/-- A program that uses `word` as a parameter, as the binder that starts a statement, as a port
and as the payload of a send. -/
def contextualWordProgram (word : String) : String :=
  s!"module t
def f({word}: nat) -> nat:
    mut total = {word}
    total := total + {word}
    return total
def g(x: nat) -> nat:
    {word} = x
    return {word}
protocol X roles(P, V)({word}: nat @P):
    received <- send {word} to V
"

end Zkc.Tests.Frontend
