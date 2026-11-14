/-!
# Programs for the check of instances

Programs over the library of `NameCases`, in the block format. `expect` is `accept` or
`refuse <rule> <line>[:<column>] [in <file>]`, the first refusal of the test. A line
`// content <instance> holds <text>` says what an instance holds, as `renderContent` prints it; a
line `// chain <frame>` names the innermost frame of the first refusal; `// default <name> =
<count>, <first>` gives the default instances of a declaration, `// no default <name>` says
it has none, and `// reached <name>` says that a root reaches it, so that it has no report of
default instances.
-/

namespace Zkc.Tests.Frontend

def instanceCases : String := "
=== sizes | accept | the types of a signature at an instance (TY2, TY3)
module t
def take<n: nat, m: nat>(xs: [byte; n]) -> [byte; n - m] where (m <= n): xs[m..n]
// instantiate: take<n = 5, m = 2>
// content take<n = 5, m = 2> holds (xs: [index<256>; 5]) -> [index<256>; 3]

=== size-negative | refuse TY2 2:51 | a size is a natural (TY2)
module t
def take<n: nat, m: nat>(xs: [byte; n]) -> [byte; n - m]: xs[m..n]
// instantiate: take<n = 3, m = 8>
// chain take<n = 3, m = 8>

=== size-division | refuse TY2 2 | division in a size is exact (TY2)
module t
def halve<n: nat>(xs: [byte; n]) -> [byte; n / 2]: xs[0..n / 2]
// instantiate: halve<3>

=== size-log | refuse TY2 2 | log2 takes a power of two (TY2)
module t
def bits<n: nat>(x: index<log2(n)>) -> nat: x
// instantiate: bits<12>

=== size-log-power | accept | log2 of a power of two
module t
def bits<n: nat>(x: index<log2(n)>) -> nat: x
// instantiate: bits<16>
// content bits<n = 16> holds (x: index<4>) -> nat

=== size-call | refuse TY2 3 | a size contains no call of a function (TY2)
module t
def three() -> nat: 3
nat N = three()

=== size-port | refuse TY2 2 | a port is a run-time value, not a size (TY2)
module t
protocol X roles(P, V)(n: nat @P, x: [byte; n] @V):
    y <- send x to P

=== static-name | accept | a static name is evaluated with its scope (TY2)
module t
nat N = 2^3 - 1
def f(x: [byte; N]) -> nat: 0
// content N holds = 7
// content f holds (x: [index<256>; 7]) -> nat

=== where-fails | refuse SP4 2 | a `where` holds at each instance (SP4)
module t
def take<n: nat, m: nat>(xs: [byte; n]) -> [byte; n - m] where (m <= n): xs[m..n]
// instantiate: take<n = 3, m = 8>
// chain take<n = 3, m = 8>

=== where-call | refuse SP4 3 | a `where` calls no function (SP4)
module t
def bound() -> nat: 3
pub def f<n: nat>(xs: [byte; n]) -> byte where (bound() <= n): xs[0]

=== where-port | refuse SP4 2 | a `where` names no port (SP4)
module t
protocol X roles(P, V)(n: nat @(P, V)) where (n == 2):
    y <- send n to V

=== where-types | accept | an equality of types in a `where` (SP4)
module t
def same<A, B>(a: A, b: B) -> A where (A == B): a
// instantiate: same<nat, nat>

=== where-types-differ | refuse SP4 2 | an equality of types that does not hold (SP4)
module t
def same<A, B>(a: A, b: B) -> A where (A == B): a
// instantiate: same<nat, bool>

=== recursive-record | refuse NL1 3 | a record that contains itself (NL1)
module t
struct Node:
    next: Node

=== recursive-alias | refuse NL1 2 | an alias of itself (NL1)
module t
type Loop = [Loop; 2]

=== sort-bound | refuse SP3 3 | a parameter of a sort takes a type of the sort (SP3)
module t
use zkc::fields::{G1}
struct Box<F: Field>:
    value: F
def f(b: Box<G1>) -> nat: 0
// chain Box<F = G1>

=== linear-bound | refuse SP3 4 | a parameter without `linear` takes freely copied data (SP3)
module t
linear struct Token:
    id: nat
struct Wrap<T>:
    value: T
def f(w: Wrap<Token>) -> nat: 0

=== linear-bounded | accept | a parameter bounded `linear` takes a linear type (SP3)
module t
linear struct Token:
    id: nat
struct Wrap<T: linear>:
    value: T
def f(w: Wrap<Token>) -> nat: 0
// content Wrap<T = Token> holds {value: Token}

=== interface-bound | refuse SP3 8 | a module parameter takes a module that names its interface (SP3)
module t
interface A:
    nat Size
interface B:
    nat Size
module M: A:
    nat Size = 2
struct Holder<X: B>:
    value: index<X::Size>
def f(h: Holder<M>) -> nat: 0

=== interface-where | refuse SP4 2 | the `where` of an interface is a condition on each implementing module (SP4)
module t
interface Sized where (2 <= Width):
    nat Width
module One: Sized:
    nat Width = 1

=== numerals-by-name | refuse SP5 4 | numerals among natural arguments are written by name (SP5)
module t
struct Grid<a: nat, b: nat>:
    cells: [byte; a * b]
def f(g: Grid<2, 3>) -> nat: 0

=== named-argument | refuse SP5 4 | a named argument names a parameter (SP5)
module t
struct Grid<a: nat, b: nat>:
    cells: [byte; a * b]
def f(g: Grid<a = 2, c = 3>) -> nat: 0

=== cannot-infer | refuse SP6 4 | a reference in a type leaves no parameter to inference (SP6)
module t
struct Grid<a: nat, b: nat>:
    cells: [byte; a * b]
def f(g: Grid<a = 2>) -> nat: 0

=== by-name | accept | numerals by name, and terms by position (SP5)
module t
struct Grid<a: nat, b: nat>:
    cells: [byte; a * b]
def f(g: Grid<a = 2, b = 3>) -> nat: 0
pub def g<n: nat>(x: Grid<n, n>) -> nat: 0
// content Grid<a = 2, b = 3> holds {cells: [index<256>; 6]}
// content f holds (g: Grid<2, 3>) -> nat

=== class | refuse GR5 4 | a natural where a type is expected (GR5)
module t
struct Box<T>:
    value: T
def f(b: Box<3>) -> nat: 0

=== scope-arguments | accept | from outside, the parameters of a scope come first (SP2)
module t
section <n: nat>:
    pub struct Row:
        cells: [byte; n]
    pub def width(r: Row) -> index<n + 1>: n
def f(r: Row<4>) -> nat: 0
// content Row<n = 4> holds {cells: [index<256>; 4]}

=== member-missing | refuse SP8 4 | an implementing module defines every member of its interface (SP8)
module t
interface Sized:
    nat Width
module Empty: Sized:
    nat Height = 2

=== member-extra | refuse SP8 6 | a member definition defines a member of the interface (SP8)
module t
interface Source:
    def value() -> nat
module Two: Source:
    def value(): 2
    def other(): 3

=== member-spec | refuse SP8 5 | a member that the interface declares `def` is deployed code (SP8)
module t
interface Source:
    def value() -> nat
module Hidden: Source:
    spec def value(): 3

=== member-binders | refuse SP8 5 | a member definition has a binder per parameter of the member (SP8)
module t
interface Pair:
    def add(a: nat, b: nat) -> nat
module Sum: Pair:
    def add(a): a

=== members | accept | the member table of an implementing module (SP8)
module t
use zkc::fields::{Fr}
interface Carrier:
    type T
    nat Size
    def unit() -> T
module Values: Carrier:
    type T = Fr
    nat Size = 4
    def unit(): 0
def f(x: index<Values::Size>) -> Values::T: 0
// content Values holds Carrier: T = Fr, Size = 4, unit defined
// content f holds (x: index<4>) -> Fr

=== module-arguments | accept | a module at its arguments, and its members (SP2, SP8)
module t
interface Shape:
    nat Size
module grid<T, n: nat>: Shape:
    nat Size = 2 * n
    pub type Cell = T
def f(x: [grid<bool, 3>::Cell; grid<bool, 3>::Size]) -> nat: 0
// content f holds (x: [bool; 6]) -> nat

=== vocabulary-module | refuse SP8 4 | a module of the vocabulary implements what its row implements (SP8)
module t
interface Mapping:
    nat Size
module Wrong: Mapping = primitive(\"hash.sha256\")

=== spec-order | refuse SP11 2 | the specification-only parameters stand last (SP11)
module t
pub relation R<spec e: nat, n: nat>(xs: [byte; n]): n <= e

=== spec-deployed | refuse SP11 2 | a specification-only parameter occurs in no deployed type (SP11)
module t
pub def pad<n: nat, spec e: nat>(xs: [byte; n]) -> [byte; n + e]: xs

=== spec-specification | accept | a specification item reads a specification-only parameter, typed at 0, 1, 2 and 3 without a goal (SP11)
module t
section <n: nat, spec e: nat>:
    pub relation Near(; xs: [byte; n]): n <= e
// default Near = 16, Near<n = 0, spec e = 0>

=== row-library | refuse NL9 2 | a library under `zkc::` binds rows of the vocabulary only (NL9)
module zkc::extra
pub type Thing = primitive(\"nothing\")

=== row-project | accept | a row of a project is reported and taken as written (NL9)
module t
type Thing = primitive(\"project.thing\")

=== asset-type | refuse NL9 5 | an asset gives naturals and data (NL9)
module t
interface Opaque:
    type Row
    nat Rows
module Imported: Opaque = asset(table)

=== vocabulary-members | accept | the members of a type of the vocabulary at an instance
module t
use zkc::fields::{Fr, G1}
def orders<G: PrimeOrderGroup>(x: index<G::Scalar::Bytes>) -> nat: x
// instantiate: orders<G1>
// content orders<G = G1> holds (x: index<32>) -> nat

=== collection-group | accept | a sized collection of elements of a `Group` is a `Group` (TY11)
module t
use zkc::fields::{G1}
struct Box<T: Group>:
    value: T
def f(b: Box<[G1; 2]>) -> nat: 0
// content Box<T = [G1; 2]> holds {value: [G1; 2]}

=== defaults | accept | the default instances of public declarations (SP7)
module t
interface Carrier:
    type T
module Naturals: Carrier:
    type T = nat
pub def first<T, n: nat>(xs: [T; n]) -> T where (1 <= n): xs[0]
pub def pick<k: nat>(xs: [byte; 5]) -> byte where (k <= 4): xs[k]
pub def twice<X: Carrier>(x: X::T) -> X::T: x
pub def unit<F: Field>(x: F) -> F: x
// default first = 3, first<T = bool, n = 1>
// default pick = 5, pick<k = 0>
// default twice = 1, twice<X = Naturals>
// default unit = 1, unit<F = koala-bear>

=== no-default | accept | a declaration without a default instance is reported (SP7)
module t
interface Carrier:
    type T
pub def twice<X: Carrier>(x: X::T) -> X::T: x
// no default twice

=== skipped-default | accept | a default instance whose `where` fails is skipped and refuses nothing (SP7)
module t
pub def f<n: nat>() -> nat where (n != 0): n
// default f = 3, f<n = 1>

=== reached-through-a-body | accept | a declaration that a root reaches through a body has no default instance (SP7)
module t
pub def f<n: nat>() -> nat where (n != 0): n
pub def top() -> nat: f<n = 2>()
// reached f
// content f<n = 2> holds () -> nat

=== reached-through-a-signature | accept | a declaration that a root reaches through a signature has no default instance (SP7)
module t
pub type Word<n: nat> = [bool; n]
pub def top(w: Word<3>) -> bool: w[0]
// reached Word
"

end Zkc.Tests.Frontend
