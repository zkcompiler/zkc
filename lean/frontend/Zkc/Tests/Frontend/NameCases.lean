/-!
# Programs for the check of names

A small library, given to the tests in memory, and programs in the block format of the
conformance tests (`=== ID | expect | note`, with `--- file` between the modules of one test).
A module `zkc::…` of a test stands in place of the library module.

`expect` is `accept`, or `refuse <rule> <line>[:<column>] [in <file>]`: the first refusal of the
test, in its first module or in module `<file>`. A line `// at <line> <text> = <steps>` says that
the first occurrence of `<text>` on that line starts a path whose resolution is `<steps>`, as
`renderResolution` prints it; `<line>#<k>` names the `k`-th occurrence instead. A line
`// none <line> <text>` says that it has no entry.
-/

namespace Zkc.Tests.Frontend

/-- The library of the tests: what the rules read of the core library, and no more. -/
def nameLibrary : Array (String × String) := #[
  ("zkc::prelude", "module zkc::prelude
pub use zkc::algebra::{
    Group, Ring, PrimeOrderGroup, Field, PrimeField, ExtensionField, TwoAdicField
}
pub type byte = index<256>
pub def length<T: linear>(values: [T]) -> nat = primitive(\"seq.length\")
"),
  ("zkc::algebra", "module zkc::algebra
pub interface Group:
    type Scalar: Ring
    nat Order
pub interface Ring where (Self: Group, Self::Scalar == Self):
    nat Characteristic
    def from_nat(n: nat) -> Self
pub interface PrimeOrderGroup where (Self: Group, Self::Scalar: PrimeField):
    def generator() -> Self
pub interface Field where (Self: Ring):
    type Prime: PrimeField
    nat Dimension
pub interface PrimeField where (Self: Field, Self::Prime == Self):
    nat Bytes
    def to_nat(x: Self) -> index<Self::Order>
pub interface ExtensionField where (Self: Field):
    type Base: Field
pub interface TwoAdicField where (Self: Field, 1 <= TwoAdicity):
    nat TwoAdicity
"),
  ("zkc::option", "module zkc::option
pub enum Option<T>:
    Some(T)
    None
"),
  ("zkc::layout", "module zkc::layout
pub interface Layout:
    type Unit
    def write_natural(n: nat) -> [Unit]
pub module canonical: Layout:
    type Unit = byte
    def write_natural(n): [0]
"),
  ("zkc::fields", "module zkc::fields
pub type Fr = primitive(\"bls12-381.fr\")
pub type G1 = primitive(\"bls12-381.g1\")
"),
  ("lib::cycle_a", "module lib::cycle_a
pub use lib::cycle_b::{x}
"),
  ("lib::cycle_b", "module lib::cycle_b
pub use lib::cycle_a::{x}
"),
  ("lib::misnamed", "module lib::other
pub def f() -> nat: 0
")]

def nameCases : String := "
=== library | accept | the library of these tests resolves
module t
use zkc::option::{Option}
use zkc::layout::{canonical}
use zkc::fields::{Fr}
def f(x: Fr) -> Option<Fr>: Some(x)

=== steps-local-parameter | accept | a local name and a static parameter
module t
def f<n: nat>(x: [byte; n]) -> [byte; n]:
    y = x
    return y
// at 2 byte = declaration byte
// at 2 n] = parameter n
// at 4 y = local

=== steps-prelude | accept | the names of the prelude are in scope without `use` (NL4)
module t
def f<F: Field>(xs: [F]) -> nat: length(xs)
// at 2 Field = declaration zkc::algebra (use) / declaration Field (use)
// at 2 length = declaration length

=== steps-fixed | accept | the functions of the fixed table and `log2` have no declaration
module t
def f(xs: [nat]) -> nat: sum(xs) + product(xs)
def g<n: nat>(x: index<log2(n)>) -> nat: x
// at 2 sum = fixed sum
// at 2 product = fixed product
// at 3 log2 = log2

=== steps-member-of-sort | accept | a member of a sort through a static parameter
module t
def f<G: PrimeOrderGroup>(x: G::Scalar) -> G: G::generator() * x
def g<G: Group>(n: nat) -> G::Scalar: G::Scalar::from_nat(G::Scalar::Characteristic + n)
// at 2 G::Scalar = parameter G / member Scalar of Group
// at 2 G::generator = parameter G / member generator of PrimeOrderGroup
// at 3 G::Scalar::from_nat = parameter G / member Scalar of Group / member from_nat of Ring

=== steps-member-through-where | accept | a `where` gives a static path the interfaces of its bound
module t
interface Holder:
    type T
def f<X: Holder>(n: nat) -> nat where (X::T: Group): X::T::Order + n
// at 4 X::T::Order = parameter X / member T of Holder / member Order of Group

=== steps-member-through-interface-where | accept | the `where` of an interface states a bound on a member
module t
interface Holder where (Value: PrimeField):
    type Value
def f<X: Holder>(x: X::Value) -> nat: X::Value::Bytes
// at 4 X::Value::Bytes = parameter X / member Value of Holder / member Bytes of PrimeField

=== steps-member-open | accept | a member equated with a type is left to the instance
module t
interface Holder:
    type T
def f<X: Holder>(n: nat) -> nat where (X::T == nat): X::T::Anything
// at 4 X::T::Anything = parameter X / member T of Holder / member Anything at the instance

=== steps-declared-type | accept | a member of a declared type is left to the instance
module t
use zkc::fields::{G1}
def f() -> G1: G1::generator()
// at 3 G1::generator = declaration zkc::fields (use) / declaration G1 (use) / member generator at the instance

=== steps-self | accept | `Self` and the members of an interface and of the interfaces it requires
module t
interface Counted where (Self: Group):
    def count(x: Self) -> index<Order>
// at 3 Self = Self of Counted
// at 3 Order = Self of Counted / member Order of Group

=== steps-alternative | accept | an alternative through its variant, and a bare one that typing completes; a case that is one name is bound, and typing decides against the matched variant whether it is its alternative (TY13)
module t
use zkc::option::{Option}
def f(x: nat) -> Option<nat>: Option::Some(x)
def g() -> Option<nat>: None
def h(x: Option<nat>) -> nat:
    mut out = 0
    match x:
        case Some(y):
            out := y
        case None:
            out := 1
    return out
// at 3 Option::Some = declaration zkc::option (use) / declaration Option (use) / alternative Option::Some
// at 4 None = alternative None of the expected variant
// at 8 Some = alternative Some of the expected variant

=== steps-generated | accept | the generated members of a protocol, a scheme and a layout module (§8)
module t
use zkc::layout::{canonical}
use zkc::security::{soundness, random_oracle}
protocol P roles(A, B)(x: nat @A):
    y <- send x to B
def view(inputs: P::Inputs<B>) -> P::Received<B>: P::Received<B>{y = 0}
def units(n: nat) -> [byte]: canonical::write<nat>(n)
scheme S = P:
    construction interactive
goal sound = soundness(S, model = random_oracle, stage = written, clause = main, corrupted = A)
// at 6 P::Inputs = declaration P / generated Inputs <…>
// at 6 B> = role B
// at 7 canonical::write = declaration zkc::layout (use) / declaration canonical (use) / generated write <…>
// at 10 soundness = vocabulary module zkc::security (use) / entry zkc::security::soundness (use)
// at 10 written = word written
// at 10 main = label main
// at 10 A = role A

=== steps-import-arguments | accept | the static arguments of an import are fixed by it (SP2)
module t
use m<nat>::{double}
def f(x: nat) -> nat: double(x)
// at 3 double = declaration m <…> (use) / declaration double (use)
--- file
module m<T>
pub def double(x: T) -> T: x

=== steps-use | accept | a `use` binds the last name of its path, the name after `as`, or the names listed (NL3)
module t
use zkc::option
use zkc::option as choice
use zkc::option::{Option}
def f(x: option::Option<nat>, y: choice::Option<nat>) -> Option<nat>: x
// at 2 zkc::option = declaration zkc::option (use)
// at 3 choice = declaration zkc::option (use)
// at 4 Option = declaration zkc::option (use) / declaration Option (use)
// at 5 option::Option = declaration zkc::option (use) / declaration Option <…>
// at 5 choice::Option = declaration zkc::option (use) / declaration Option <…>

=== steps-self-module | accept | `Self` in a module that implements an interface is the module (SP8)
module t
interface Wrapped:
    type Item
    def wrap(x: Item) -> [Item; 1]
module Bytes: Wrapped:
    type Item = byte
    def wrap(x): [x]
    def first(xs: [Self::Item; 1]) -> Self::Item: xs[0]
// at 8 Self::Item = declaration Bytes / declaration Item

=== steps-host | accept | a module bound to the vocabulary names the members of its interface in its `where` (SP4)
module t
interface Hashing:
    nat Size
module Sha: Hashing where (Size == 32) = primitive(\"hash.sha256\")
// at 4 Size = declaration Sha / member Size of Hashing

=== steps-section | accept | a section gives its parameters to its items (SP1)
module t
section <n: nat>:
    pub def first(xs: [byte; n]) -> byte: xs[0]
// at 3 n] = parameter n

=== steps-member-definition | accept | a member definition reads the interface's parameters of the member, and not its own name (SP8)
module t
interface Halver:
    def half<n: nat>(xs: [byte; 2 * n]) -> [byte; n]
    def evaluate(x: nat) -> nat
def evaluate(x: nat) -> nat: x
module Front: Halver:
    def half(xs): xs[0..n]
    def evaluate(x): evaluate(x) + 1
// at 7 n] = parameter n
// at 8 evaluate(x) + = declaration evaluate

=== steps-contract | accept | a contract reads the ports, the results where they are in scope, and the names at a loop (SX5)
module t
relation Holds(x: nat): x == x
protocol P roles(A, B)(x: nat @(A, B)) -> y: nat @(A, B):
    mut s = x
    for i in 0..3 collect (zs = s):
        s := s + 1
    return s
spec for P:
    requires Holds(x)
    ensures Holds(y)
    invariant Holds(s) at i
// at 10 y = local
// at 11 s) = local

=== nl2-enclosing | refuse NL2 5:9 | a suite does not rebind a name of an enclosing suite
module t
def f(n: nat) -> nat:
    m = n
    for i in 0..2:
        m = i
    return m

=== nl2-same-suite | refuse NL2 4:5 | a local name is bound once
module t
def f(n: nat) -> nat:
    m = n
    m = n + 1
    return m

=== nl2-siblings | accept | two sibling suites may bind one name
module t
def f(n: nat) -> nat:
    mut out = 0
    if n == 0:
        m = 1
        out := m
    else:
        m = 2
        out := m
    return out

=== nl2-static-parameter | refuse NL2 2:30 | a binder does not shadow a static parameter
module t
def f<n: nat>(xs: [byte; n], n: nat) -> nat: n

=== nl2-comprehension | refuse NL2 2:35 | a binder of a comprehension is a local name
module t
def f(x: nat) -> [nat; 3]: [x for x in 0..3]

=== nl2-declarations | refuse NL2 3:5 | two declarations of a module do not share a name
module t
def f() -> nat: 0
def f() -> nat: 1

=== nl2-import | refuse NL2 3:5 | a declaration and an import do not share a name
module t
use zkc::option::{Option}
def Option() -> nat: 0

=== nl2-parameters | refuse NL2 2:15 | a static parameter list names a parameter once
module t
def f<n: nat, n: nat>() -> nat: 0

=== nl2-members | refuse NL2 4:9 | two members of an interface do not share a name
module t
interface I:
    nat Size
    nat Size

=== nl2-events | accept | two events with one name are refused by the rule of sites (EV3), not here
module t
protocol P roles(A, B)(x: nat @A):
    y <- send x to B
    y <- send x to B

=== nl2-hiding | accept | a local name may hide a declaration and a name of the prelude
module t
def g() -> nat: 0
def f(g: nat, byte: nat) -> nat: g + byte
// at 3 g + = local
// at 3#2 byte = local

=== nl3-expression | refuse NL3 2:27 | a name that nothing binds
module t
def f(x: nat) -> nat: x + y

=== nl3-type | refuse NL3 2:10 | a type that nothing binds
module t
def f(x: Missing) -> nat: 0

=== nl3-use-name | refuse NL3 2:19 | a `use` names something (NL3)
module t
use zkc::option::{Maybe}

=== nl3-use-module | refuse NL3 2:5 | a `use` of a module that no file has
module t
use zkc::nothing::{x}

=== nl3-alternative | refuse NL3 3:33 | a variant has the alternatives it declares
module t
use zkc::option::{Option}
def f() -> Option<nat>: Option::Nothing

=== nl3-local-member | refuse NL3 2:26 | a local name has no member through `::`
module t
def f(x: nat) -> nat: x::y

=== nl3-generated | refuse NL3 4:13 | a protocol has its generated members only
module t
protocol P roles(A, B)(x: nat @A):
    y <- send x to B
def f(r: P::Record) -> nat: 0

=== nl3-interface | refuse NL3 4:21 | a member is not reached through an interface
module t
interface I:
    nat Size
def f() -> index<I::Size>: 0

=== nl3-cycle | refuse NL3 2:24 in 1 | imports that form a cycle bind nothing
module t
use lib::cycle_a::{x}
--- file
module lib::cycle_a
pub use lib::cycle_b::{x}

=== nl3-absolute | refuse NL3 2:17 | a module is named by `use`; nothing else is in scope without it (NL4)
module t
def f() -> nat: zkc::prelude::length([1])

=== nl3-unreached | refuse NL3 2:55 | names are resolved in a declaration that no root reaches (SP7)
module t
pub def f<n: nat>(xs: [byte; n]) -> nat: length(xs) + nothing

=== nl3-not-exported | refuse NL3 2:9 | a `use` without `pub` does not export
module t
use u::{Option}
--- file
module u
use zkc::option::{Option}
pub def f() -> nat: 0

=== nl3-self | refuse NL3 2:10 | `Self` stands in an interface and in a module that implements one
module t
def f(x: Self) -> nat: 0

=== sp2-arguments-twice | refuse SP2 3:23 | a name whose `use` fixes static arguments takes no more (SP2)
module t
use m<nat> as n
def f(x: nat) -> nat: n<bool>::double(x)
--- file
module m<T>
pub def double(x: T) -> T: x

=== nl4-two-files | refuse NL4 1:8 in 1 | no two files have one path
module t
def f() -> nat: 0
--- file
module t
def g() -> nat: 0

=== nl4-misnamed | refuse NL4 1:8 in lib::misnamed | the header of a library file states its path
module t
use lib::misnamed::{f}

=== nl4-replace | accept | a given module stands in place of the library module
module t
use zkc::option::{Option}
def f() -> Option<nat>: Option::Absent
--- file
module zkc::option
pub enum Option<T>:
    Present(T)
    Absent

=== nl7-declaration | refuse NL7 3:20 | a declaration without `pub` is visible in its module only
module t
use u
def g() -> nat: u::hidden()
--- file
module u
def hidden() -> nat: 0

=== nl7-inside | accept | a declaration without `pub` is visible in its module, nested modules included
module t
def hidden() -> nat: 0
module nested:
    def h() -> nat: hidden()
    module deeper:
        pub def k() -> nat: nested::h()
// at 6 nested::h = declaration nested / declaration h

=== nl7-record | refuse NL7 3:28 | a record with a field that is not `pub` is built only in its module
module t
use u::{Point}
def make(x: nat) -> Point: Point{x}
--- file
module u
pub struct Point:
    x: nat

=== nl7-record-pattern | refuse NL7 4:5 | nor matched by a record pattern outside it
module t
use u::{Point}
def read(p: Point) -> nat:
    Point{x} = p
    return x
--- file
module u
pub struct Point:
    x: nat

=== nl7-record-inside | accept | a record is built in its module
module u
pub struct Point:
    x: nat
pub def make(x: nat) -> Point: Point{x}

=== nl7-members | accept | the members of an implementing module are visible as the interface's
module t
use u::{Two}
def f() -> nat: Two::size()
--- file
module u
interface Sized:
    def size() -> nat
pub module Two: Sized:
    def size(): 2

=== nl10-prelude-name | refuse NL10 2:5 | a module outside the core library declares no name of the prelude
module t
def length(xs: [nat]) -> nat: 0

=== fixed-function-declared | accept | a declaration with the name of a function of the fixed table hides it (NL4)
module t
def sum(xs: [nat]) -> nat: 0
def f(xs: [nat]) -> nat: sum(xs)
// at 3 sum( = declaration sum

=== fixed-function-module | accept | a module named after a function of the fixed table (NL4)
module t
module inner<k: nat>:
    pub def size() -> nat: 2^k
def f() -> nat: inner<3>::size()
// at 4 inner<3>::size = declaration inner <…> / declaration size

=== nl10-fixed-function-local | accept | a local name may hide a function of the fixed table
module t
def f(sum: nat, inner: nat) -> nat: sum + inner
// at 2 sum + = local

=== nl10-item | refuse NL10 1:8 in 1 | a language item is declared in its module, public and with its kind
module t
use zkc::option::{Maybe}
def f() -> Maybe<nat>: Maybe::Nothing
--- file
module zkc::option
pub enum Maybe<T>:
    Something(T)
    Nothing

=== nl10-item-kind | refuse NL10 2:12 in 1 | a language item has the kind of the table
module t
use zkc::option::{Option}
--- file
module zkc::option
pub struct Option<T>:
    pub value: T

=== sp3-member | refuse SP3 2:38 | a member that the sorts of a static parameter do not declare
module t
def f<G: PrimeOrderGroup>() -> G: G::identity()

=== sp3-type-parameter | refuse SP3 2:27 | a type parameter without a bound has no member
module t
def f<T>(x: T) -> nat: T::Size

=== sp3-self | refuse SP3 3:32 | a member of `Self` that the interface does not declare
module t
interface Counted where (Self: Group):
    def count() -> index<Self::Size>
"

end Zkc.Tests.Frontend
