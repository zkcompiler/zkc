/-!
# Programs for the typing of bodies

Programs over the library of `NameCases`, in the block format. `expect` is `accept` (no refusal,
and the package of every root that is a function is admitted by the core), `refuse <rule>
<line>[:<column>]` (the first refusal), or `wait` (no refusal, and a root waits for a form that is
not typed yet). A line `// uses <name>` says that some emitted package applies the operation or the
row of that name; `// not uses <name>` that none does; `// applies <name> <n>` that the packages
name the operation `n` times, once for each application of an operation of the core;
`// obligations <n>` that the laws typed leave `n` obligations; `// waits <text>` that a root
waits for a reason that contains the text; `// says <text>` that a refusal has the text in its
message.
-/

namespace Zkc.Tests.Frontend

def typingCases : String := "
=== identity | accept | a parameter is a value of its type (FN4)
module t
def id(x: nat) -> nat: x
def unit(x: nat): ()

=== literal-field | accept | a number checks against a field below its characteristic (TY6)
module t
type F = primitive(\"bls12-381.fr\")
def three(x: F) -> F: x + 3
// uses field.add

=== literal-characteristic | refuse TY6 3 | a number at least the characteristic is no element (TY6)
module t
type F = primitive(\"koala-bear\")
def bad(x: F) -> F: x + 2130706433

=== literal-group | refuse TY6 3 | the only literal of a group is `0` (TY6)
module t
type G = primitive(\"bls12-381.g1\")
def bad(g: G) -> G: g + 1

=== literal-group-zero | accept | `0` of a group is its identity (TY6)
module t
type G = primitive(\"bls12-381.g1\")
def zero() -> G: 0
// uses group.zero

=== literal-nonzero | accept | a number not a multiple of the characteristic is a unit (TY6)
module t
type F = primitive(\"koala-bear\")
def half(x: F) -> F: x / 2
def inverse(x: nonzero<F>) -> nonzero<F>: 1 / x
// uses field.inverse
// uses field.from_nonzero

=== literal-nonzero-zero | refuse TY6 3 | `0` is not a unit (TY6)
module t
type F = primitive(\"koala-bear\")
def bad(x: F) -> F: x / 0

=== literal-index | accept | a number below the bound is an index (TY6)
module t
def three() -> index<4>: 3

=== literal-bool | refuse TY6 2 | a number does not check against `bool` (TY6)
module t
def bad() -> bool: 1

=== units | accept | the units are closed under `*`, `/`, `^` and `-` (TY6)
module t
type F = primitive(\"koala-bear\")
def unit(x: nonzero<F>) -> nonzero<F>: -(1 / x) * x^3 / 2^5

=== static-literal | accept | a static natural is the number it evaluates to (TY2, TY6)
module t
type F = primitive(\"koala-bear\")
def scale<k: nat>(x: F) -> F where (k <= 20): x / 2^k
// instantiate: scale<3>

=== index-sized | refuse TY7 2 | an index of a sized collection needs its range below the size (TY7)
module t
def at(xs: [byte; 8], i: nat) -> byte: xs[i]

=== index-range | accept | an `index<s>` indexes a collection of `s` elements (TY7, TY8)
module t
def at(xs: [byte; 8], i: index<8>) -> byte: xs[i]
// uses fin.to_nat

=== index-guard | accept | a guard gives the range (TY4, TY9)
module t
def get(xs: [byte; 8], i: nat) -> byte:
    guard i < 8
    return xs[i]

=== index-unsized | refuse TY7 2 | a collection of run-time length needs the order fact (TY7)
module t
def first(xs: [byte]) -> byte: xs[0]

=== index-unsized-guard | accept | the order fact of a guard (TY4)
module t
def first(xs: [byte], i: nat) -> byte:
    guard i < length(xs)
    return xs[i]
// uses seq.length
// uses seq.at

=== index-subtraction | accept | `b - u` is below `b` when `1 <= u` (TY4)
module t
def last(xs: [byte], u: index<3>) -> byte:
    guard 1 <= u else refused
    guard u <= length(xs) else refused
    return xs[length(xs) - u]

=== index-sum | accept | `a + u` is at least `a` (TY4)
module t
def window(xs: [byte], start: nat, count: nat) -> [byte]:
    guard start + count <= length(xs)
    return xs[start..start + count]
// uses seq.slice

=== fact-scope | refuse TY7 5 | a fact made in an arm does not leave it (TY4)
module t
def f(xs: [byte], c: bool) -> byte:
    if c:
        guard 0 < length(xs)
    return xs[0]

=== fact-other-name | refuse TY7 4 | a fact is about its term (TY4)
module t
def f(xs: [byte], ys: [byte]) -> byte:
    guard 0 < length(xs)
    return ys[0]

=== narrowing-if | accept | the arms of an `if` have the facts of its condition and of its negation (TY9)
module t
def head(xs: [byte]) -> byte: if 0 < length(xs) then xs[0] else 0
def last(xs: [byte]) -> byte: if length(xs) < 1 then 0 else xs[length(xs) - 1]

=== narrowing-and | accept | the right operand of `and` has the facts of the left one (TY9)
module t
def starts(xs: [byte]) -> bool: 0 < length(xs) and xs[0] == 0
def empty_or(xs: [byte]) -> bool: length(xs) == 0 or xs[0] == 0

=== narrowing-and-order | refuse TY7 2 | the left operand has no fact of the right one (TY9)
module t
def starts(xs: [byte]) -> bool: xs[0] == 0 and 0 < length(xs)

=== and-condition | accept | a condition whose right operand needs a fact of the left one is a local `if`, and the choice on it is made one operand at a time: the arm of a condition that does not hold stands once per operand (TY9)
module t
def f(xs: [byte], n: nat) -> nat:
    mut out: nat = 0
    if 0 < length(xs) and xs[0] == 1:
        out := xs[0]
    else:
        out := n % 3
    return out
def g(xs: [byte], n: nat) -> nat: if 0 < length(xs) and xs[0] == 1 then xs[0] else n % 5
def h(xs: [byte]) -> byte:
    guard 0 < length(xs) and xs[0] == 1
    return xs[0]
def k(xs: [byte], n: nat) -> nat: if length(xs) == 0 or xs[0] == 1 then n / 7 else xs[0]
// applies nat.rem 4
// applies nat.div 2

=== and-condition-right | accept | an arm that needs a fact of the right operand of a condition computed as one local `if` is chosen one operand at a time (TY9)
module t
def f(i: nat, j: nat, ys: [byte; 4]) -> byte: if 1 <= i and (i - 1 < 3 and j < 4) then ys[j] else 0
def g(i: nat, j: nat, ys: [byte; 4]) -> byte: if i == 0 or (4 <= i - 1 or 4 <= j) then 0 else ys[j]
def h(i: nat, j: nat, ys: [byte; 4]) -> byte:
    mut out: byte = 0
    if 1 <= i and (i - 1 < 3 and j < 4):
        out := ys[j]
    return out
def k(i: nat, j: nat, ys: [byte; 4]) -> byte: if not (i == 0 or (4 <= i - 1 or 4 <= j)) then ys[j] else 0

=== and-regroup | accept | the right operand of `and` that needs a fact of the right operand of a left `and` computed as a local `if` (TY9)
module t
def f(i: nat, j: nat, ys: [byte; 4]) -> bool: (1 <= i and (i - 1 < 3 and j < 4)) and ys[j] == 0
def g(i: nat, j: nat, ys: [byte; 4]) -> bool: (i == 0 or (4 <= i - 1 or 4 <= j)) or ys[j] == 0
def h(i: nat, j: nat, ys: [byte; 4]) -> bool: not (i == 0 or (4 <= i - 1 or 4 <= j)) and ys[j] == 0

=== filter-choice | accept | a comprehension whose element needs a fact of the right operand of its condition, computed as one local `if`, takes the condition one operand at a time (TY9, TY11)
module t
def f(i: nat, js: [nat; 3], ys: [byte; 4]) -> [byte]: [ys[j] for j in js if 1 <= i and (i - 1 < 3 and j < 4)]
def g(i: nat, js: [nat; 3], ys: [byte; 4]) -> [byte]: [ys[j] for j in js if not (i == 0 or (4 <= i - 1 or 4 <= j))]

=== guard-not-or | accept | a guard on the negation of `or` is a guard on the negation of each operand (TY9)
module t
def f(i: nat, ys: [byte; 4]) -> byte:
    guard not (i == 0 or 4 <= i - 1) else refused
    return ys[i - 1]

=== loop-empty | accept | a loop of no iteration is a loop of the count 0, whose body has no fact (TY10)
module t
def f(xs: [byte; 0]) -> bool: ∀ i ∈ 0..0, xs[i] == 0
// uses loop

=== and-row | accept | `and` of operands that need no fact of each other is the boolean row
module t
def both(a: nat, b: nat) -> bool: a < 3 and b < 4
// uses bool.and

=== less-equal | accept | `a <= b` is `not (b < a)`
module t
def le(a: nat, b: nat) -> bool: a <= b
// uses bool.not
// uses nat.less

=== static-if | accept | an `if` on a static condition is the arm taken (TY9)
module t
pub def first<n: nat>(xs: [byte; n]) -> byte: if 0 < n then xs[0] else 0

=== static-if-taken | refuse TY7 2 | the arm taken is typed (TY9)
module t
pub def first<n: nat>(xs: [byte; n]) -> byte: if 0 <= n then xs[0] else 0

=== subtraction | refuse TY8 2 | a subtraction needs its order known (TY8)
module t
def minus(a: nat, b: nat) -> nat: a - b

=== subtraction-guard | accept | the order of a guard (TY8)
module t
def minus(a: nat, b: nat) -> nat:
    guard b <= a
    return a - b
// uses nat.sub

=== division | refuse TY8 2 | a division needs `1 <= b` (TY8)
module t
def quotient(a: nat, b: nat) -> nat: a / b

=== division-range | accept | the range of the divisor (TY8)
module t
def quotient(a: nat, b: index<4>) -> nat:
    guard 1 <= b
    return a / b + a % b

=== range-index | refuse TY8 2 | a natural where an index is expected needs its range (TY8)
module t
def next(i: index<8>) -> index<8>: i + 1

=== range-index-fits | accept | a range below the bound converts (TY5, TY8)
module t
def next(i: index<7>) -> index<8>: i + 1
// uses nat.below

=== widening | accept | `[T; s]` widens to `[T]`, `index<s>` to a larger one (TY5)
module t
def forget(xs: [byte; 4]) -> [byte]: xs
def larger(i: index<3>) -> index<8>: i
// uses seq.unsized
// uses fin.widen

=== sized-by-fact | accept | a collection of run-time length with the size fact converts (TY5)
module t
def eight(xs: [byte]) -> [byte; 8]:
    guard length(xs) == 8
    return xs
// uses seq.sized

=== sized-without-fact | refuse TY5 2 | without the fact it does not (TY5)
module t
def eight(xs: [byte]) -> [byte; 8]: xs

=== nonzero-by-fact | accept | a field element with the nonzero fact converts (TY5, TY9)
module t
type F = primitive(\"koala-bear\")
def inverse(x: F) -> F:
    guard x != 0
    return 1 / x
// uses field.is_nonzero
// uses field.nonzero

=== nonzero-without-fact | refuse TY5 3 | without the fact it does not (TY5)
module t
type F = primitive(\"koala-bear\")
def inverse(x: F) -> F: 1 / x

=== join-if | accept | the arms of an `if` meet at their join (TY5)
module t
def pick(c: bool, a: index<3>, b: index<5>) -> index<5>: if c then a else b

=== tuple-index | refuse TY7 2 | a tuple is indexed by a static natural (TY7)
module t
def pick(pair: (byte, byte), i: index<2>) -> byte: pair[i]

=== tuple-position | accept | a position of a tuple (TY7)
module t
def second(pair: (byte, nat)) -> nat: pair.1 + pair[0]

=== loop-range | refuse CT6 4 | a range needs `a <= b` (TY10, CT6)
module t
def f() -> nat:
    mut acc: nat = 0
    for i in 5..2:
        acc := acc + i
    return acc

=== loop-uniform | accept | a uniform loop over a static range carries its `mut` names (TY10)
module t
def total(xs: [byte; 4]) -> nat:
    mut acc: nat = 0
    for i in 0..4:
        acc := acc + xs[i]
    return acc

=== loop-runtime | accept | a loop with a run-time count (TY10)
module t
def total(xs: [byte], n: nat) -> nat:
    mut acc: nat = 0
    for i in 0..length(xs):
        acc := acc + xs[i]
    return acc

=== loop-collection | accept | a loop over a collection of run-time length (TY10)
module t
def total(xs: [byte]) -> nat:
    mut acc: nat = 0
    for x in xs:
        acc := acc + x
    return acc

=== loop-state | refuse TY10 4 | a loop with a run-time count carries state of one type (TY10)
module t
def shrink(xs: [byte; 8], n: index<4>) -> byte:
    mut rest = xs
    for i in 0..n:
        rest := rest[0..4]
    return rest[0]

=== loop-stepped-tuple | accept | a loop whose iterations type differently is its iterations in sequence (TY10)
module t
def firsts(t: ([byte; 2], [byte; 4])) -> nat:
    mut acc: nat = 0
    for j in 0..2:
        x = t[j]
        acc := acc + x[0]
    return acc

=== loop-static-index | accept | an index in a static position types each iteration (TY10)
module t
def sum(t: (nat, nat, nat)) -> nat:
    mut acc: nat = 0
    for j in 0..3:
        acc := acc + t[j]
    return acc

=== comprehension | accept | a comprehension collects (TY11)
module t
def doubled(xs: [byte; 4]) -> [nat; 4]: [x * 2 for x in xs]
def indices<n: nat>(xs: [byte; n]) -> [(index<n>, byte); n]: [(i, xs[i]) for i in 0..n]
def evens(xs: [byte]) -> [byte]: [x for x in xs if x % 2 == 0]
// instantiate: indices<3>

=== binder-natural | accept | `∑` over naturals carries its sum; its range is index by index (TY8, TY11)
module t
def weight(flags: [bool; 8]) -> index<9>: ∑ f ∈ flags, if f then 1 else 0
def value(units: [byte; 2]) -> index<65536>: ∑ i ∈ 0..2, units[i] * 256^i

=== binder-range | refuse TY8 2 | the range of a sum (TY8)
module t
def value(units: [byte; 9]) -> index<2^64>: ∑ i ∈ 0..9, units[i] * 256^i

=== binder-bool | accept | `∀` and `∃` (TY11)
module t
def all_small(xs: [byte]) -> bool: ∀ x ∈ xs, x < 16
def any_zero(xs: [byte; 4]) -> bool: any([x == 0 for x in xs])

=== binder-field | accept | `∑` on a field applies the row to the collected elements (TY11)
module t
type F = primitive(\"koala-bear\")
def total(xs: [F; 4]) -> F: ∑ x ∈ xs, x
def squares(xs: [F; 4]) -> F: sum([x * x for x in xs])
// uses seq.sum

=== binder-declared | refuse NL6 7 | `∑` on a declared type needs `add` and `zero` (NL6)
module t
type F = primitive(\"bls12-381.fr\")
struct Pair:
    pub left: F
    pub right: F
def add(a: Pair, b: Pair) -> Pair: Pair{left = a.left + b.left, right = a.right + b.right}
def total(xs: [Pair; 4]) -> Pair: ∑ x ∈ xs, x

=== binder-declared-zero | accept | with `zero` the form folds the home functions (NL6, TY11)
module t
struct Count:
    pub value: nat
def add(a: Count, b: Count) -> Count: Count{value = a.value + b.value}
def zero() -> Count: Count{value = 0}
def total(xs: [Count; 4]) -> Count: ∑ x ∈ xs, x

=== equality-structural | accept | `==` on tuples, records and variants is structural (TY12)
module t
use zkc::option::{Option}
struct Pair:
    pub left: nat
    pub right: bool
def same(a: Pair, b: Pair) -> bool: a == b
def same_pair(a: (nat, bool), b: (nat, bool)) -> bool: a != b
def same_option(a: Option<nat>, b: Option<nat>) -> bool: a == b
def same_bytes(a: [byte], b: [byte]) -> bool: a == b

=== equality-sizes | refuse TY12 2 | collections of different static sizes (TY12)
module t
def same(a: [byte; 2], b: [byte; 3]) -> bool: a == b

=== order-field | refuse TY12 3 | field elements are not ordered (TY12)
module t
type F = primitive(\"koala-bear\")
def less(a: F, b: F) -> bool: a < b

=== field-zero | accept | the comparison with `0` is the domain row (TY9)
module t
type F = primitive(\"koala-bear\")
def is_zero(a: F) -> bool: a == 0
// uses field.is_nonzero
// not uses field.equal

=== record | accept | a record is built, read and updated (TY13)
module t
struct Pair<T>:
    pub left: T
    pub right: T
def make(a: nat) -> Pair<nat>: Pair{left = a, right = a}
def swap(p: Pair<nat>) -> Pair<nat>: {p with left = p.right, right = p.left}
def left(p: Pair<nat>) -> nat:
    Pair{left, right} = p
    return left + p.right

=== record-missing | refuse TY13 6 | a construction gives every field (TY13)
module t
struct Pair:
    pub left: nat
    pub right: nat
def make(a: nat) -> Pair:
    return Pair{left = a}

=== match | accept | `match` binds the payload of each alternative (TY13)
module t
use zkc::option::{Option}
def or_zero(x: Option<nat>) -> nat:
    mut out: nat = 0
    match x:
        case Some(y):
            out := y
        case None:
            ()
    return out
def head(xs: [byte]) -> Option<byte>: if 0 < length(xs) then Some(xs[0]) else None

=== match-cover | refuse TY13 7 | `match` is exhaustive (TY13)
module t
enum Side:
    Left
    Right
def f(s: Side) -> nat:
    mut out: nat = 0
    match s:
        case Left:
            out := 1
    return out

=== event | refuse FN1 3 | an event stands only in a protocol body (FN1)
module t
def f(x: nat) -> nat:
    y <- send x to V
    return y

=== kernel-stop | refuse FN5 2 | a kernel stands on a `def` whose body cannot stop (FN5)
module t
#[kernel(\"test.first\")]
def first(xs: [byte]) -> byte:
    guard 0 < length(xs)
    return xs[0]

=== kernel-total | accept | a kernel on a body that cannot stop (FN5)
module t
#[kernel(\"test.double\")]
def double(x: nat) -> nat: x * 2

=== at-stop | refuse FN3 2 | a function named `at` cannot stop (FN3)
module t
def at(x: nat) -> nat:
    guard x < 4
    return x

=== stops-through-call | refuse FN5 5 | a function that calls a function that can stop can stop (FN2)
module t
def checked(x: nat) -> nat:
    guard x < 4
    return x
#[kernel(\"test.outer\")]
def outer(x: nat) -> nat: checked(x)

=== recursion | refuse NL1 3 | a definition reaches itself through bodies (NL1)
module t
def f(x: nat) -> nat: g(x)
def g(x: nat) -> nat: f(x)

=== arguments | accept | positional and named arguments (FN6)
module t
def sub(a: nat, b: nat) -> nat:
    guard b <= a
    return a - b
def call(x: nat) -> nat: sub(b = 1, a = x + 1)

=== arguments-missing | refuse FN6 3 | every parameter is given (FN6)
module t
def two(a: nat, b: nat) -> nat: a + b
def call(x: nat) -> nat: two(x)

=== inference | accept | static arguments are inferred from the arguments (SP6)
module t
def first<T, n: nat>(xs: [T; n]) -> T where (1 <= n): xs[0]
def use_it(xs: [byte; 3]) -> byte: first(xs)

=== inference-fails | refuse SP6 4 | an unknown that nothing gives (SP6)
module t
def zeros<n: nat>() -> [byte; n]: [0; n]
def g() -> nat:
    xs = zeros()
    return length(xs)

=== dot-call | accept | `e.m(a)` is the function of the home module of the type (NL5)
module t
struct Counter:
    pub value: nat
def bump(c: Counter, by: nat) -> Counter: Counter{value = c.value + by}
def twice(c: Counter) -> Counter: c.bump(1).bump(2)

=== dot-call-missing | refuse NL5 4 | the home module has the function (NL5)
module t
struct Counter:
    pub value: nat
def twice(c: Counter) -> Counter: c.bump(1)

=== operator-home | accept | an operator on a declared type is the function of the home module (NL6)
module t
struct Mod:
    pub value: index<7>
def add(a: Mod, b: Mod) -> Mod: Mod{value = (a.value + b.value) % 7}
def twice(a: Mod) -> Mod: a + a

=== operator-scalar | refuse NL6 3 | the scalar stands on the right of the point (§3.5)
module t
type G = primitive(\"bls12-381.g1\")
def bad(g: G, r: G::Scalar) -> G: r * g

=== operator-power-group | refuse NL6 3 | a group has no `^` (§3.5)
module t
type G = primitive(\"bls12-381.g1\")
def bad(g: G, r: G::Scalar) -> G: g ^ r

=== sort-member | accept | a function member of a sort applies its row (§7.4)
module t
type F = primitive(\"koala-bear\")
def lift(n: nat) -> F: F::from_nat(n)
// uses field.from_nat

=== partial | refuse SP9 5 | a member that can stop is declared `partial` (SP9)
module t
interface I:
    def small(x: nat) -> nat
module M: I:
    def small(x):
        guard x < 4
        return x
def g(x: nat) -> nat: M::small(x)

=== rational | refuse TY1 2 | `rational` is a type of specifications (TY1)
module t
def bound(e: nat) -> rational: e / 3

=== spec-call | refuse SX2 3 | deployed code does not call a specification function (SX2)
module t
spec def half(x: nat) -> nat: x / 2
def f(x: nat) -> nat: half(x)

=== relation-formula | accept | a relation's formula is a `bool` that cannot stop, applied with its split (SX3)
module t
relation Below(x: nat; y: nat): y < x
relation Twice(x: nat; y: nat, z: nat): Below(x; y) and Below(x; z)
spec def check(x: nat) -> bool: Twice(x; 1, 2)

=== relation-split | refuse SX3 3 | an application gives each side as many arguments as the relation has (SX3)
module t
relation Below(x: nat; y: nat): y < x
spec def check(x: nat) -> bool: Below(x, 1)

=== relation-stops | refuse FN3 5 | the formula of a relation cannot stop (FN3)
module t
def checked(x: nat) -> nat:
    guard x < 4
    return x
relation Small(x: nat): checked(x) == 0

=== rational | accept | `rational` in a specification: naturals converted, `/` exact, integer exponents (TY8)
module t
spec def bound(e: nat, k: nat) -> rational: (1 - e / 2^k)^3 + 2^-64
spec def small(e: nat) -> bool: bound(e, 4) <= 1 / 2

=== rational-remainder | refuse TY8 2 | `%` is not an operator of `rational` (TY8)
module t
spec def bound(e: nat) -> rational: e % 3

=== rational-deployed | refuse TY1 2 | `rational` is a type of specifications (TY1)
module t
def bound(e: nat) -> rational: e

=== law-interface | accept | a law of an interface is typed at each implementing module, and leaves an obligation (SP10)
module t
interface Doubler:
    def double(x: nat) -> nat
    law even(x: nat): double(x) % 2 == 0
module Twice: Doubler:
    def double(x): x + x
module Shifted: Doubler:
    def double(x): 2 * x + 2
// obligations 2

=== law-own | accept | a law with static parameters of its own is typed at their default values, where its `where` holds (SP10, SP7)
module t
interface Halver:
    def half<n: nat>(xs: [byte; 2 * n]) -> [byte; n]
    law keeps<n: nat>(xs: [byte; 2 * n]) where (1 <= n): half<n = n>(xs)[0] == xs[0]
module Front: Halver:
    def half(xs): xs[0..n]
// obligations 3

=== law-module | accept | a law of a module is typed and leaves an obligation of the module (SP10)
module t
def double(x: nat) -> nat: x + x
law even(x: nat): double(x) % 2 == 0
// obligations 1

=== law-stops | refuse SP10 5 | a law is an expression that cannot stop (SP10, FN3)
module t
def checked(x: nat) -> nat:
    guard x < 4
    return x
law small(x: nat): checked(x) < 4

=== member-own-static | accept | a member function with static parameters of its own: written, or inferred (SP8, SP6)
module t
interface Halver:
    def half<n: nat>(xs: [byte; 2 * n]) -> [byte; n]
module Front: Halver:
    def half(xs): xs[0..n]
def f(xs: [byte; 4]) -> [byte; 2]: Front::half(xs)
def g(xs: [byte; 6]) -> bool:
    h = Front::half<n = 3>(xs)
    return h[0] == xs[0]

=== nested-payload | accept | a pattern inside a payload: a tuple, and the alternative of a variant with one alternative (TY13)
module t
enum Wrapped:
    Wrap(nat, bool)
enum Shape:
    Point
    Pair((nat, Wrapped))
def f(s: Shape) -> nat:
    mut out: nat = 0
    match s:
        case Pair((a, Wrap(b, _))):
            out := a + b
        case Point:
            ()
    return out

=== nested-refutable | refuse TY13 6 | a pattern inside a payload covers every value of its type (TY13)
module t
use zkc::option::{Option}
def f(o: Option<Option<nat>>) -> nat:
    mut out: nat = 0
    match o:
        case Some(Some(x)):
            out := x
        case None:
            ()
    return out

=== opaque-members | accept | an operator, a form and `==` on a type member of a module parameter are members of the interface (NL6, SP12)
module t
interface Carrier:
    type T
    def zero() -> T
    def add(a: T, b: T) -> T
    def equal(a: T, b: T) -> bool
module Weird: Carrier:
    type T = nat
    def zero(): 1
    def add(a, b): a * b + 1
    def equal(a, b): a + 1 == b
pub def twice<X: Carrier>(x: X::T) -> X::T: x + x
pub def total<X: Carrier, n: nat>(xs: [X::T; n]) -> X::T: ∑ x ∈ xs, x
pub def same<X: Carrier>(x: X::T, y: X::T) -> bool: x == y
pub def pair<X: Carrier>(p: (X::T, nat), q: (X::T, nat)) -> bool: p == q

=== opaque-equal | refuse SP12 6 | `==` on a type member whose interface declares no `equal` (SP12)
module t
interface Carrier:
    type T
module Naturals: Carrier:
    type T = nat
pub def same<X: Carrier>(x: X::T, y: X::T) -> bool: x == y

=== opaque-operator | refuse NL6 8 | an operator whose member the interface does not declare (NL6)
module t
interface Carrier:
    type T
    def add(a: T, b: T) -> T
module Naturals: Carrier:
    type T = nat
    def add(a, b): a + b
pub def square<X: Carrier>(x: X::T) -> X::T: x * x

=== opaque-literal | refuse TY6 8 | a number does not check against a type member (TY6)
module t
interface Carrier:
    type T
    def add(a: T, b: T) -> T
module Naturals: Carrier:
    type T = nat
    def add(a, b): a + b
pub def next<X: Carrier>(x: X::T) -> X::T: x + 1

=== opaque-carrier | refuse SP12 8 | a value of the definition is not a value of the type member (SP12)
module t
interface Carrier:
    type T
    def add(a: T, b: T) -> T
module Naturals: Carrier:
    type T = nat
    def add(a, b): a + b
pub def shift<X: Carrier>(x: X::T, n: nat) -> X::T: X::add(x, n)

=== opaque-helper | refuse SP12 6 | a helper that the definition instantiates with the fresh type is typed at it (SP12)
module t
interface Carrier:
    type T
module Naturals: Carrier:
    type T = nat
def same<A>(a: A, b: A) -> bool: a == b
pub def both<X: Carrier>(x: X::T) -> bool: same(x, x)

=== opaque-equated | accept | a `where` that equates the member makes it that type (SP12)
module t
interface Carrier:
    type T
module Naturals: Carrier:
    type T = nat
pub def is_zero<X: Carrier>(x: X::T) -> bool where (X::T == nat): x == 0

=== opaque-sort | accept | a type member with a sort as its bound has the operations of the sort (SP12)
module t
type G = primitive(\"bls12-381.g1\")
interface Holder:
    type T: Group
module Points: Holder:
    type T = G
pub def doubled<X: Holder>(x: X::T) -> bool: x + x == x

=== opaque-applications | accept | two applications of one fresh type member are matched argument by argument (SP12, SP6)
module t
interface Round:
    type State<v: nat>
    def message<v: nat>(s: State<v + 1>) -> nat
    def bind<v: nat>(s: State<v + 1>, r: nat) -> State<v>
module Pairs: Round:
    type State<v: nat> = [nat; 2^v]
    def message(s): s[0]
    def bind(s, r): s[0..2^v]
pub def two<R: Round>(s: R::State<2>) -> nat: R::message(R::bind(s, 1))

=== opaque-member-definition | refuse NL6 11 | a member definition generic over a module parameter of its module is typed opaquely (SP12)
module t
interface Carrier:
    type T
    def add(a: T, b: T) -> T
module Naturals: Carrier:
    type T = nat
    def add(a, b): a + b
interface Doubler<C: Carrier>:
    def double(x: C::T) -> C::T
module Squared<C: Carrier>: Doubler<C>:
    def double(x): x * x
def apply(x: nat) -> nat: Squared<Naturals>::double(x)

=== spec-def | accept | a specification function is typed and emitted as a specification-only function (SX1, §7.2)
module t
spec def square(x: nat) -> nat: x * x
spec def twice(x: nat) -> nat: square(x) + square(x)

=== mut-written | accept | an update widens to the written type of a `mut` name (TY10)
module t
def f(a: index<3>) -> index<8>:
    mut x: index<8> = 0
    x := a
    return x

=== mut-join | accept | after a choice a `mut` name has the join of its types (TY5, TY10)
module t
def f(c: bool, xs: [byte; 4], ys: [byte; 8]) -> [byte]:
    mut out = xs
    if c:
        out := ys
    return out

=== skipped-default-called | refuse SP4 2:35 | a call at values that a default instance skipped is refused (SP4, SP7)
module t
pub def f<n: nat>() -> nat where (n != 0): n
pub def top() -> nat: f<n = 0>()

=== skipped-default-private | refuse SP4 2:31 | the same refusal when the callee has no default instance (SP4)
module t
def f<n: nat>() -> nat where (n != 0): n
pub def top() -> nat: f<n = 0>()

=== skipped-default-from-default | refuse SP4 2:35 | a default instance that calls at skipped values is refused (SP4, SP7)
module t
pub def f<n: nat>() -> nat where (n != 0): n
pub def g<m: nat>() -> nat: f<n = 0>()

=== skipped-default-later | refuse SP4 3:35 | the refusal does not depend on the order of the declarations (SP4, SP7)
module t
pub def g<m: nat>() -> nat: f<n = 0>()
pub def f<n: nat>() -> nat where (n != 0): n

=== empty-loop-record | refuse TY5 11:23 | the type that a loop of no iteration collects names its own record, not the next one made (TY16)
module t
struct Pair<T>:
    pub a: T
    pub b: T
struct R<T>:
    pub z: T
def f() -> nat:
    for i in 0..0 collect (ys = Pair{a = i, b = i}):
        x = 0
    q = R{z = true}
    w: [R<bool>; 0] = ys
    return length(w)

=== empty-loop-record-read | accept | a name collected by a loop of no iteration is read at the record of its type (TY16)
module t
struct Pair<T>:
    pub a: T
    pub b: T
def f() -> nat:
    for i in 0..0 collect (ys = Pair{a = i, b = i}):
        x = 0
    zs = [p.a for p in ys]
    return length(zs)

=== empty-loop-types-nothing | accept | a loop of no iteration types no function that only its body calls (TY10)
module t
def h<n: nat>() -> nat: true
def f() -> nat:
    for i in 0..0 collect (ys = h<n = 2>()):
        x = 0
    return length(ys)

=== case-name-of-another-variant | accept | a case that is one name is decided against the matched variant: an alternative of another variant of that name does not make it one (TY13)
module t
enum Color:
    Red
    Green
enum Unrelated:
    other
    more
def f(c: Color) -> nat:
    mut r = 0
    match c:
        case Red:
            r := 1
        case other:
            r := 2
    return r

=== case-name-twice | refuse TY13 10 | a case that is one name of an alternative of the matched variant is the case of that alternative (TY13)
module t
enum Color:
    Red
    Green
def f(c: Color) -> nat:
    mut r = 0
    match c:
        case Red:
            r := 1
        case Red:
            r := 2
        case Green:
            r := 3
    return r

=== fact-mut-until-assigned | accept | a fact about a `mut` name is about the value it has, until it is assigned again (TY4)
module t
def f(xs: [nat; 8], start: nat) -> nat:
    mut i = start
    guard i < 8 else refused
    return xs[i]

=== fact-mut-after-assignment | refuse TY7 6 | an assignment makes a `mut` name another value, of which nothing is known (TY4)
module t
def f(xs: [nat; 8], start: nat) -> nat:
    mut i = start
    guard i < 8 else refused
    i := i + 1
    return xs[i]

=== fact-through-binding | accept | a name is the value of its right side, with its order facts (TY4)
module t
def f(a: nat, b: nat) -> nat:
    guard b <= a else refused
    c = b
    return a - c

=== fact-code-that-does-not-run | accept | code that does not run at an instance is asked no fact: the body of a comprehension over an empty range (TY4)
module t
def last<n: nat>(xs: [nat; n]) -> [nat; n]: [xs[n - 1 - i] for i in 0..n]
def f() -> [nat; 0]: last<n = 0>([])

=== every-refusal-of-a-function | refuse TY5 3 | every refusal of a function body is reported, in the order of the source: the first is on line 3
module t
def f(a: nat) -> bool:
    x: bool = a
    y: bool = a
    return x

=== literal-scale-of-a-collection | accept | the literal on the right of `*` at a sized collection of group elements is a scalar, as beside a value (TY6, TY11)
module t
type G = primitive(\"bls12-381.g1\")
def scaled() -> [G; 2]:
    xs: [G; 2] = 0 * 3
    return xs
def beside(xs: [G; 2]) -> [G; 2]: xs * 3
// uses seq.scale

=== empty-collection-declared | accept | every value of the type of `[]`, a declared one included, is the collection of no elements (TY6)
module t
def named() -> [nat]:
    e = []
    return e ++ [1, 2]
def declared(e: [(); 0]) -> [nat; 0]: e
def other(e: [(); 0], xs: [nat]) -> [nat]: e ++ xs

=== inner-product-of-naturals | accept | `⟪a, b⟫` of naturals is the sum of the products, term by term (§3.5)
module t
def dot(xs: [nat; 3], ys: [nat; 3]) -> nat: ⟪xs, ys⟫
def indices(xs: [index<4>; 2], ys: [nat; 2]) -> nat: ⟪xs, ys⟫
// uses nat.mul

=== record-pattern-in-a-payload | accept | a record pattern inside a payload covers its type (TY13)
module t
use zkc::option::{Option}
struct Pair:
    pub left: nat
    pub right: nat
def total(o: Option<Pair>) -> nat:
    mut out: nat = 0
    match o:
        case Some(Pair{left, right}):
            out := left + right
        case None:
            ()
    return out

=== record-pattern-in-a-payload-field | refuse TY13 9 | a record pattern names fields of the record (TY13)
module t
use zkc::option::{Option}
struct Pair:
    pub left: nat
    pub right: nat
def total(o: Option<Pair>) -> nat:
    mut out: nat = 0
    match o:
        case Some(Pair{middle}):
            out := middle
        case None:
            ()
    return out

=== bound-row-without-statics | refuse NL9 3 | a name of the vocabulary bound at static arguments for which it has no row is refused (NL9)
module t
type F = primitive(\"koala-bear\")
def nz(x: F) -> nonzero<F> = primitive(\"field.nonzero\")
def use_it(x: F) -> nonzero<F>: nz(x)
// says is a row of the vocabulary

=== bound-row-signature | refuse NL9 3 | the signature written is that of the row at the instance (NL9)
module t
type F = primitive(\"koala-bear\")
def nz(x: F) -> F = primitive(\"field.nonzero\", F)
// says the signature written is not that of the row

=== bound-row-domain | refuse TY5 4 | a function bound to a restricted row is applied where its domain is known (TY5)
module t
type F = primitive(\"koala-bear\")
def nz(x: F) -> nonzero<F> = primitive(\"field.nonzero\", F)
def use_it(x: F) -> nonzero<F>: nz(x)
// says applies the row `field.nonzero`, which is defined where `field.is_nonzero` holds

=== project-row-at-a-record | accept | a row of a project at a record is no row of the vocabulary, and its package is admitted (NL9)
module t
struct Pair:
    pub left: nat
    pub right: nat
def size_of<T>(x: T) -> nat = primitive(\"custom.size_of\")
def at_record(p: Pair) -> nat: size_of(p)
def at_nat(n: nat) -> nat: size_of(n)

=== wording-index | refuse TY7 2 | the message of an index without its fact (TY7)
module t
def f(xs: [nat], i: nat) -> nat: xs[i]
// says `xs[i]` reads a collection whose length is a run-time value: `i < length(xs)` is not known; write `guard i < length(xs)` before it

=== wording-subtraction | refuse TY8 2 | the message of a subtraction without its order (TY8)
module t
def f(a: nat, b: nat) -> nat: a - b
// says `a - b` subtracts naturals: `b <= a` is not known; write `guard b <= a` before it

=== wording-sized-index | refuse TY7 2 | the message of an index that can be too large (TY7)
module t
def f(xs: [nat; 8], i: index<10>) -> nat: xs[i]
// says `i` can be as large as 9; `xs` has 8 elements
"

end Zkc.Tests.Frontend
