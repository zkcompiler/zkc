/-!
# Programs for the typing of protocol bodies

Protocols over the library of `NameCases`, in the block format of `TypingCases`: the holders of
expressions and the roles that compute statements (§6.4), events and sites (§6.5), guards (§6.6),
choices and loops (§6.7), role maps (§6.8), laws (TY15), the facts of each role (TY4, TY14), and
what the core does not have yet; and the uses of linear values, in functions and in protocol
bodies (§6.9).
-/

namespace Zkc.Tests.Frontend

def protocolCases : String := "
=== schnorr | accept | a sample, two sends, a draw and a guard (EV1, EV5, EV6, GU2, TY15)
module t
type G = primitive(\"bls12-381.g1\")
protocol Schnorr roles(P, V)(base: G @(P, V), point: G @(P, V), scalar: G::Scalar @P):
    nonce @P <- sample G::Scalar
    commitment <- send base * nonce to V
    challenge <- draw G::Scalar from V to P
    response <- send nonce + challenge * scalar to V
    guard @V base * response == commitment + point * challenge
// uses law.uniform

=== no-former | refuse HO1 5 | no role can form an expression of names that different roles hold (HO1)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(a: F @P, b: F @V):
    m <- send a to V
    c = a + b

=== binder-subset | refuse HO2 4 | the roles written on a binder are among the holders of its value (HO2)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(a: F @P):
    c @V = a + 1

=== binder-restricted | accept | a binder restricted to one of the holders of its value (HO2)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(a: F @(P, V)):
    c @V = a + 1
    guard @V c != a

=== update-holder | refuse HO1 6 | an update is computed by the holders of its name, which hold its value (HO1)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(a: F @P, b: F @V):
    mut c: F = 0
    m <- send a to V
    c := c + b

=== result-holder | refuse HO1 4 | each holder of a result computes it (HO1)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(a: F @P) -> r: F @(P, V):
    return a

=== sample-binder | refuse HO5 4 | the binder of a `sample` names its one role (HO5)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)():
    s <- sample F

=== send-binder | refuse HO5 4 | the binder of a `send` takes no `@` (HO5)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(a: F @P):
    m @V <- send a to V

=== draw-binder | refuse HO5 4 | the binder of a `draw` takes no `@` (HO5)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)():
    c @P <- draw F from V to P

=== sender | refuse EV5 4 | a payload that two roles other than the receiver hold names its sender (EV5)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V, W)(a: F @(P, W)):
    m <- send a to V

=== sender-written | accept | `from` names the sender of a payload that two roles hold (EV5)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V, W)(a: F @(P, W)):
    m <- send a from W to V
    guard @V m != 0

=== sender-holds | refuse EV5 4 | the sender holds the payload (EV5)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V, W)(a: F @P):
    m <- send a from W to V

=== two-receivers | accept | a send to two receivers is one event with a part per receiver (EV3, EV5)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V, W)(a: F @P):
    m <- send a to V, W
    guard @(V, W) m != 0
// applies exchange 2

=== draw-owner | refuse EV6 4 | the owner of a draw is none of its receivers (EV6)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)():
    c <- draw F from V to P, V

=== two-names | refuse EV3 6 | two events of one name (EV3)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(a: F @P, again: bool @(P, V)):
    m <- send a to V
    if again:
        m <- send a to V

=== site-attribute | refuse EV3 4 | `#[site(…)]` names the site of a binder otherwise (EV3)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(a: F @P):
    #[site(y)]
    x <- send a to V

=== site-attribute-pattern | accept | `#[site(…)]` names the site of a tuple pattern (EV3)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(a: F @P):
    #[site(pair)]
    (x, y) <- send (a, a + 1) to V
    guard @V x + 1 == y

=== event-function | refuse EV1 5 | a function is not an event: it is bound with `=` (EV1)
module t
type F = primitive(\"bls12-381.fr\")
def twice(x: F) -> F: x + x
protocol T roles(P, V)(a: F @P):
    y <- twice(a)

=== application-results | refuse EV1 7 | an application with results binds them (EV1)
module t
type F = primitive(\"bls12-381.fr\")
protocol C roles(P, V)(a: F @P) -> r: F @(P, V):
    m <- send a to V
    return m
protocol T roles(P, V)(a: F @P):
    C(a)

=== role-map | refuse RM1 6 | a callee role without a namesake is mapped by name (RM1)
module t
type F = primitive(\"bls12-381.fr\")
protocol C roles(O, R)(a: F @O):
    m <- send a to R
protocol T roles(P, V)(a: F @P):
    C(a)

=== role-map-injective | refuse RM1 6 | a role map gives no role two callee roles (RM1)
module t
type F = primitive(\"bls12-381.fr\")
protocol C roles(O, R)(a: F @(O, R)):
    m <- send a from O to R
protocol T roles(P, V)(a: F @(P, V)):
    C(a) @(O = P, R = P)

=== application | accept | roles mapped by name; results bound by one name and read by `y.r` (RM1, RM3)
module t
type F = primitive(\"bls12-381.fr\")
protocol Ask roles(O, R)() -> (value: F @(O, R), nonce: F @O):
    nonce @O <- sample F
    value <- send nonce * nonce to R
    return (value, nonce)
protocol T roles(P, V)():
    asked <- Ask() @(O = P, R = V)
    guard @P asked.value == asked.nonce * asked.nonce
    guard @V asked.value != 0

=== application-pattern | accept | results bound by a tuple pattern, each with its own holders (RM3)
module t
type F = primitive(\"bls12-381.fr\")
protocol Ask roles(O, R)() -> (value: F @(O, R), nonce: F @O):
    nonce @O <- sample F
    value <- send nonce * nonce to R
    return (value, nonce)
protocol T roles(P, V)():
    (value, nonce) <- Ask() @(O = P, R = V)
    guard @P value == nonce * nonce

=== application-argument | refuse HO1 6 | an argument is computed by the mapped holders of its port (HO1, RM2)
module t
type F = primitive(\"bls12-381.fr\")
protocol C roles(P, V)(a: F @(P, V)):
    guard @V a != 0
protocol T roles(P, V)(a: F @P):
    C(a)

=== specification-port | refuse SX4 6 | an application binds every specification port (SX4)
module t
type F = primitive(\"bls12-381.fr\")
protocol C roles(P, V)(spec bound: nat, a: F @P):
    m <- send a to V
protocol T roles(P, V)(a: F @P):
    C(a)

=== specification-parameter | refuse SP11 6 | an application gives every specification-only parameter (SP11)
module t
type F = primitive(\"bls12-381.fr\")
protocol C<spec e: nat> roles(P, V)(a: F @P):
    m <- send a to V
protocol T roles(P, V)(a: F @P):
    C(a)

=== guard-roles | refuse GU2 4 | a guard in a protocol body names its roles (GU2)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(a: F @(P, V)):
    guard a != 0

=== guard-holder | refuse GU2 4 | the roles of a guard hold its condition (GU2)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(a: F @P):
    guard @V a != 0

=== choice | accept | a choice on a condition held by both participants updates a `mut` name per holder (CT1, CT3)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(a: F @(P, V), b: bool @(P, V)):
    mut c = a
    if b:
        c := c + 1
    m <- send c from P to V
    guard @V m == c

=== choice-condition | refuse CT2 4 | every participant holds the condition (CT2)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(a: F @P, b: bool @P):
    if b:
        m <- send a to V

=== choice-no-role | refuse CT1 4 | a choice in which no role acts (CT1)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(b: bool @(P, V)):
    if b:
        x = 1

=== choice-static | accept | an `if` with a static condition is the arm taken: it has no participant (TY9, CT1)
module t
type F = primitive(\"bls12-381.fr\")
protocol T<n: nat> roles(P, V)(a: F @P):
    if n == 0:
        m <- send a to V
// instantiate: T<0>
// instantiate: T<1>

=== choice-private | accept | a choice that only the prover makes, with no event in it (CT1, CT2)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(a: F @P, b: bool @P):
    mut c = a
    if b:
        c := c + 1
    m <- send c to V
    guard @V m != 0

=== loop | accept | a loop of static count carries a `mut` name and collects a value per iteration (TY10, TY16, CT1)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(a: F @P):
    mut s = a
    for i in 0..3 collect (sent = m):
        m <- send s to V
        s := s + 1
    guard @V sent[0] + 1 == sent[1]

=== loop-runtime | accept | a loop with a run-time count bounded at each participant (CT4)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(n: index<4> @(P, V), a: F @P):
    mut s = a
    for i in 0..n:
        m <- send s to V
        s := s + 1

=== loop-unbounded | refuse CT4 4 | the count of a loop of a protocol body has a static bound (CT4)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(n: nat @(P, V), a: F @P):
    for i in 0..n:
        m <- send a to V
// says the count of this loop has no static bound at P: `n` is a `nat`; write `guard @P n <= N` first, or take it from an `index<N>`

=== loop-guarded | accept | a guard gives the count its bound (CT4)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(n: nat @(P, V), a: F @P):
    guard @(P, V) n <= 4
    for i in 0..n:
        m <- send a to V

=== loop-bound | refuse CT2 4 | every participant holds the bounds of the range (CT2)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(n: index<4> @P, a: F @P):
    for i in 0..n:
        m <- send a to V

=== loop-no-role | refuse CT1 4 | a loop in which no role acts (CT1)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(a: F @P):
    for i in 0..3:
        x = 1

=== loop-empty | accept | a loop of no iteration types nothing; a name it collects is empty (TY10, TY16)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(a: F @P):
    for i in 0..0 collect (sent = m):
        m <- send a to V
    guard @V length(sent) == 0

=== loop-empty-record | refuse TY5 12:23 | the type that a loop of no iteration collects names its own record (TY16)
module t
type F = primitive(\"bls12-381.fr\")
struct Pair<T>:
    pub a: T
    pub b: T
struct R<T>:
    pub z: T
protocol T roles(P, V)(a: F @P):
    for i in 0..0 collect (sent = Pair{a = m, b = m}):
        m <- send a to V
    q = R{z = true}
    w: [R<bool>; 0] = sent
    guard @V length(w) == 0

=== loop-empty-record-read | accept | a name collected by a loop of no iteration is read at the record of its type (TY16)
module t
type F = primitive(\"bls12-381.fr\")
struct Pair<T>:
    pub a: T
    pub b: T
protocol T roles(P, V)(a: F @P):
    for i in 0..0 collect (sent = Pair{a = m, b = m}):
        m <- send a to V
    firsts = [p.a for p in sent]
    guard @V length(firsts) == 0

=== loop-stepped | accept | a loop whose state changes type is its iterations in sequence, each event a site per iteration (TY10, EV3)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(a: [F; 1] @P):
    mut s = a
    for i in 0..3 collect (sent = m):
        m <- send s to V
        s := s ++ s
    guard @V length(sent.2) == 4
// applies exchange 3
// not uses repeat

=== loop-static-index | accept | a loop whose index is static in its body is its iterations in sequence (TY10)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(a: [F; 3] @P):
    for i in 0..3 collect (sent = m):
        m <- send a[0..i] to V
    guard @V length(sent.2) == 2

=== loop-stepped-function | accept | a stepped loop of a function: its iterations in sequence; the values collected have one type (TY10, TY16)
module t
type F = primitive(\"bls12-381.fr\")
def doubled(a: [F; 1]) -> [nat; 3]:
    mut s = a
    for i in 0..3 collect (lengths = length(s)):
        s := s ++ s
    return lengths
// not uses loop

=== spec-argument | accept | a specification argument is typed against its port and not emitted (SX4)
module t
type F = primitive(\"bls12-381.fr\")
spec def twice(x: F) -> F: x + x
protocol C roles(P, V)(spec bound: F, a: F @P):
    m <- send a to V
protocol T roles(P, V)(a: F @(P, V)):
    C(a, spec bound = twice(a))

=== spec-argument-type | refuse TY5 6 | a specification argument has the type of its port (SX4)
module t
type F = primitive(\"bls12-381.fr\")
protocol C roles(P, V)(spec bound: F, a: F @P):
    m <- send a to V
protocol T roles(P, V)(a: F @(P, V), b: bool @P):
    C(a, spec bound = b)

=== spec-argument-port | refuse RM3 6 | a specification argument names a specification port of the callee (RM3)
module t
type F = primitive(\"bls12-381.fr\")
protocol C roles(P, V)(a: F @P):
    m <- send a to V
protocol T roles(P, V)(a: F @(P, V)):
    C(a, spec bound = a)

=== empty-collection | accept | `[]` checks against a collection of size 0 and gives the size to inference (TY6, SP6)
module t
type F = primitive(\"bls12-381.fr\")
def count<k: nat>(xs: [F; k]) -> nat: k
def none() -> nat: count([])
def joined(xs: [F; 2]) -> [F; 2]: xs ++ []

=== match | accept | a `match` is a choice on the alternative of the matched value (TY13, CT1)
module t
type F = primitive(\"bls12-381.fr\")
enum E:
    A(F)
    B
protocol T roles(P, V)(e: E @P, a: F @P):
    mut c = a
    match e:
        case E::A(x):
            c := c + x
        case E::B:
            ()
    m <- send c to V
// uses case

=== match-holder | refuse CT2 7 | every participant holds the matched value (CT2)
module t
type F = primitive(\"bls12-381.fr\")
enum E:
    A(F)
    B
protocol T roles(P, V)(e: E @P, a: F @P):
    match e:
        case E::A(x):
            m <- send x to V
        case E::B:
            ()

=== match-cases | refuse TY13 11 | a `match` of a protocol body has one case per alternative (TY13)
module t
type F = primitive(\"bls12-381.fr\")
enum E:
    A(F)
    B
protocol T roles(P, V)(e: E @P, a: F @P):
    mut c = a
    match e:
        case E::A(x):
            c := c + x
        case E::A(y):
            c := c + y
        case E::B:
            ()

=== law-empty | refuse TY15 4 | `index<0>` is not a law (TY15)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)():
    c <- draw index<0> from V to P

=== law-tuple | accept | a law that is a tuple is one sampling row at the tuple (TY15)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)():
    c <- draw (F, F) from V to P
// uses law.uniform

=== law-collection | accept | a law that is a sized collection of laws, and an empty collection of no law (TY15)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)():
    c <- draw [nonzero<F>; 3] from V to P
    e @P <- sample [index<0>; 0]

=== law-unsized | refuse TY15 4 | an unsized collection is not a law (TY15)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)():
    c <- draw [F] from V to P

=== facts-per-role | refuse TY4 5 | the verifier's guard gives the prover no fact (TY4)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(xs: [F] @(P, V)):
    guard @V length(xs) == 2
    y = xs[1]
// says `P` computes `xs[1]` without a fact that `V` holds
// says or restrict the binder to `@V`

=== facts-restricted | accept | the binding restricted to the role that holds the fact (TY4, HO2)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(xs: [F] @(P, V)):
    guard @V length(xs) == 2
    y @V = xs[1]
    guard @V y != 0

=== wire-type | refuse TY7 6 | the receiver has the type on the wire, without the sender's facts (TY14)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(xs: [F] @P):
    guard @P length(xs) == 2
    m <- send xs to V
    y @V = m[1]

=== wire-type-written | accept | a type written at the send is the type on the wire (TY14)
module t
type F = primitive(\"bls12-381.fr\")
protocol T roles(P, V)(xs: [F] @P):
    guard @P length(xs) == 2
    m: [F; 2] <- send xs to V
    y @V = m[1]
    guard @V y != 0

=== linear-once | accept | a linear value passed on once (LN1, LN2)
module t
type F = primitive(\"bls12-381.fr\")
linear struct Ticket:
    value: F
def redeem(t: Ticket) -> F:
    Ticket{value} = t
    return value
def pass(t: Ticket) -> F: redeem(t)

=== linear-twice | refuse LN2 8:47 | a linear value used twice (LN2)
module t
type F = primitive(\"bls12-381.fr\")
linear struct Ticket:
    value: F
def redeem(t: Ticket) -> F:
    Ticket{value} = t
    return value
def twice(t: Ticket) -> F: redeem(t) + redeem(t)

=== linear-never | refuse LN2 8:10 | a linear parameter that is never passed on (LN2)
module t
type F = primitive(\"bls12-381.fr\")
linear struct Ticket:
    value: F
def redeem(t: Ticket) -> F:
    Ticket{value} = t
    return value
def drop(t: Ticket, x: F) -> F: x

=== linear-wildcard | refuse LN3 9 | `_` does not match a linear value (LN3)
module t
type F = primitive(\"bls12-381.fr\")
linear struct Ticket:
    value: F
def redeem(t: Ticket) -> F:
    Ticket{value} = t
    return value
def drop(t: Ticket) -> F:
    _ = t
    return 0

=== linear-arm | refuse LN2 10 | a linear value used in one arm of a choice only (LN2)
module t
type F = primitive(\"bls12-381.fr\")
linear struct Ticket:
    value: F
def redeem(t: Ticket) -> F:
    Ticket{value} = t
    return value
def maybe(t: Ticket, b: bool) -> F:
    mut x: F = 0
    if b:
        x := redeem(t)
    return x

=== linear-arms | accept | a linear value used in both arms of a choice (LN2)
module t
type F = primitive(\"bls12-381.fr\")
linear struct Ticket:
    value: F
def redeem(t: Ticket) -> F:
    Ticket{value} = t
    return value
def either(t: Ticket, b: bool) -> F:
    mut x: F = 0
    if b:
        x := redeem(t)
    else:
        x := redeem(t) + 1
    return x

=== linear-loop | refuse LN2 11 | a linear value is not used inside a loop outside its scope (LN2)
module t
type F = primitive(\"bls12-381.fr\")
linear struct Ticket:
    value: F
def redeem(t: Ticket) -> F:
    Ticket{value} = t
    return value
def repeated(t: Ticket) -> F:
    mut x: F = 0
    for i in 0..1:
        x := redeem(t)
    return x

=== linear-collection | refuse LN2 8:10 | a collection of linear values is linear (LN1)
module t
type F = primitive(\"bls12-381.fr\")
linear struct Ticket:
    value: F
def redeem(t: Ticket) -> F:
    Ticket{value} = t
    return value
def keep(ts: [Ticket; 2]) -> F: 0

=== linear-comprehension | accept | each element of a collection of linear values used once (LN1, LN2)
module t
type F = primitive(\"bls12-381.fr\")
linear struct Ticket:
    value: F
def redeem(t: Ticket) -> F:
    Ticket{value} = t
    return value
def all(ts: [Ticket; 2]) -> [F; 2]: [redeem(t) for t in ts]

=== linear-holders | accept | a linear value of two holders used once by one statement, at both (LN2)
module t
type F = primitive(\"bls12-381.fr\")
linear struct Ticket:
    value: F
def redeem(t: Ticket) -> F:
    Ticket{value} = t
    return value
protocol T roles(P, V)(t: Ticket @(P, V)):
    x = redeem(t)
    guard @(P, V) x != 0

=== linear-port | refuse LN2 8:24 | a linear port that is never passed on (LN2)
module t
type F = primitive(\"bls12-381.fr\")
linear struct Ticket:
    value: F
def redeem(t: Ticket) -> F:
    Ticket{value} = t
    return value
protocol T roles(P, V)(t: Ticket @P, a: F @P):
    m <- send a to V

=== linear-sent | accept | a linear value sent is passed on (LN2)
module t
type F = primitive(\"bls12-381.fr\")
linear struct Ticket:
    value: F
def redeem(t: Ticket) -> F:
    Ticket{value} = t
    return value
protocol T roles(P, V)(t: Ticket @P):
    m <- send redeem(t) to V
    guard @V m != 0

=== linear-updated | accept | a linear `mut` name consumed and assigned in one arm, used after the choice (LN2)
module t
type F = primitive(\"bls12-381.fr\")
linear struct Ticket:
    value: F
def redeem(t: Ticket) -> F:
    Ticket{value} = t
    return value
def bump(t: Ticket) -> Ticket:
    Ticket{value} = t
    return Ticket{value = value + 1}
def maybe(t: Ticket, b: bool) -> F:
    mut u = t
    if b:
        u := bump(u)
    return redeem(u)

=== linear-updated-dropped | refuse LN2 13 | an update drops a linear value that was not used (LN2)
module t
type F = primitive(\"bls12-381.fr\")
linear struct Ticket:
    value: F
def redeem(t: Ticket) -> F:
    Ticket{value} = t
    return value
def bump(t: Ticket) -> Ticket:
    Ticket{value} = t
    return Ticket{value = value + 1}
def lost(t: Ticket, s: Ticket) -> F:
    mut u = t
    u := bump(s)
    return redeem(u)

=== loop-empty-domain | accept | the collection of a loop of no iteration is evaluated once all the same, where that can stop (TY10, CT1)
module t
def none_if(b: bool) -> [nat; 0]:
    guard b
    return []
protocol T roles(V)(b: bool @V) -> r: nat @V:
    mut s: nat = 0
    for x in none_if(b):
        s := s + x
    return s
// uses none_if

=== inner-product-in-a-protocol | accept | `⟪a, b⟫` of naturals in a protocol body (§3.5)
module t
protocol T roles(V)(xs: [nat; 3] @V, ys: [nat; 3] @V) -> r: nat @V:
    s = ⟪xs, ys⟫
    return s
"

end Zkc.Tests.Frontend
