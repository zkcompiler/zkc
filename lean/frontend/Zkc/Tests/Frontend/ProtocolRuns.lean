import Zkc.Tests.Frontend.Protocols

/-!
# Run tests of protocol constructs that no other test executes

One small program for each construct, typed, emitted, admitted and run by the core's executor
with every role. The expected outputs are written from the source of each program, not taken
from a run; where a program has a guard, a second run must stop there. Field elements are of
`bls12-381.fr`, small numbers in the honest runs.

- `broadcast`: a send to two receivers, each of which computes its own output from the message.
- `relay`: three roles, a message passed from the first to the second and on to the third.
- `mapped`: an application with an explicit role map, whose result is the callee's output.
- `looped`: an application in a loop, at each iteration on a value that the loop updates.
- `bare`: an application without results, written as a statement.
- `pattern`: an application whose results are bound by a tuple pattern, one of them sampled.
- `guarded`: a guard at two roles.
- `private`: an `if` that only the prover takes, on a condition that only it holds.
- `static`: a static `if` in a protocol generic over a natural, at two instances.
- `bounded`: a loop whose run-time count is bounded by a guard.
- `ticket`: a linear value of the prover, passed on once into a message.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend
open Zkc.Frontend.Syntax
open Zkc.Core.Concrete (Datum)

/-- The programs of the run tests, each a module of its own. -/
def protocolRunPrograms : Array (String × String) := #[
  ("broadcast", "module broadcast
type F = primitive(\"bls12-381.fr\")
protocol Broadcast roles(P, V, W)(a: F @P) -> (v: F @V, w: F @W):
    m <- send a + 1 to V, W
    guard @(V, W) m != 0
    return (m * 2, m * 3)
"),
  ("relay", "module relay
type F = primitive(\"bls12-381.fr\")
protocol Relay roles(A, B, C)(x: F @A) -> y: F @C:
    m <- send x * 2 to B
    n <- send m + 3 from B to C
    guard @C n != 5
    return n
"),
  ("mapped", "module mapped
type F = primitive(\"bls12-381.fr\")
protocol Square roles(O, R)(a: F @O) -> b: F @R:
    m <- send a * a to R
    return m + 1
protocol Mapped roles(P, V)(x: F @P) -> y: F @V:
    r <- Square(x) @(O = P, R = V)
    guard @V r != 10
    return r * 2
"),
  ("looped", "module looped
type F = primitive(\"bls12-381.fr\")
protocol Step roles(P, V)(a: F @P) -> b: F @V:
    m <- send a to V
    return m
protocol Looped roles(P, V)(a: F @P) -> total: F @V:
    mut c = a
    mut s: F @V = 0
    for i in 0..3:
        r <- Step(c)
        s := s + r
        c := c + 1
    return s
"),
  ("bare", "module bare
type F = primitive(\"bls12-381.fr\")
protocol Check roles(P, V)(a: F @(P, V)):
    guard @V a != 0
protocol Bare roles(P, V)(a: F @(P, V)) -> b: F @P:
    Check(a)
    return a + 1
"),
  ("pattern", "module pattern
type F = primitive(\"bls12-381.fr\")
protocol Ask roles(O, R)() -> (value: F @(O, R), nonce: F @O):
    nonce @O <- sample F
    value <- send nonce * nonce to R
    return (value, nonce)
protocol Pattern roles(P, V)() -> (n: F @P, v: F @V):
    (value, nonce) <- Ask() @(O = P, R = V)
    return (nonce, value)
"),
  ("guarded", "module guarded
type F = primitive(\"bls12-381.fr\")
protocol Both roles(P, V)(a: F @(P, V), b: F @P) -> c: F @V:
    m <- send b to V
    guard @(P, V) a != 0
    return m + a
"),
  ("private", "module private
type F = primitive(\"bls12-381.fr\")
protocol Private roles(P, V)(a: F @P, b: bool @P) -> c: F @V:
    mut x = a
    if b:
        x := x * 2
    m <- send x to V
    return m + 1
"),
  ("static", "module static
type F = primitive(\"bls12-381.fr\")
protocol Branch<n: nat> roles(P, V)(a: F @P) -> c: F @V:
    mut x: F @V = 0
    if n == 0:
        first <- send a to V
        x := first
    else:
        second <- send a + 1 to V
        x := second * 2
    return x
protocol Both roles(P, V)(a: F @P) -> (zero: F @V, one: F @V):
    r <- Branch<0>(a)
    s <- Branch<1>(a)
    return (r, s)
"),
  ("bounded", "module bounded
type F = primitive(\"bls12-381.fr\")
protocol Bounded roles(P, V)(n: nat @(P, V), a: F @P) -> total: F @V:
    guard @(P, V) n <= 4
    mut s: F @V = 0
    for i in 0..n:
        m <- send a to V
        s := s + m
    return s
"),
  ("ticket", "module ticket
type F = primitive(\"bls12-381.fr\")
linear struct Ticket:
    value: F
def redeem(t: Ticket) -> F:
    Ticket{value} = t
    return value
protocol Spend roles(P, V)(t: Ticket @P) -> c: F @V:
    m <- send redeem(t) to V
    guard @V m != 0
    return m * 3
")]

/-- The program of a run test, typed; or a failure that says why not. -/
def protocolRunCheck (name : String) : TestM (Option TypingCheck) := do
  let some (_, text) := protocolRunPrograms.find? (·.1 == name)
    | failure s!"run tests: no program {name}"
      return none
  let input : SourceInput := { name, parsed := parseString name text }
  let nameCheck := Id.run (checkNames #[input] (memoryLoader nameLibrary))
  if let some first := nameCheck.refusals[0]? then
    failure s!"run tests: {name}: the names do not resolve: {first.render}"
    return none
  let check := checkTyping (checkInstances nameCheck #[name]) #[name]
  if let some first := check.refusals[0]? then
    failure s!"run tests: {name}: {first.render}"
    return none
  checkPackages s!"run tests: {name}" check
  return some check

def protocolRunTests : TestM Unit := do
  let label := "run tests"
  let accepted (roles : List (String × List Datum)) : List (String × RoleExpected) :=
    roles.map fun (role, outputs) => (role, .returned outputs)
  -- a send to two receivers: each computes its output from `a + 1`; `a = -1` makes the message 0
  if let some check ← protocolRunCheck "broadcast" then
    expectProtocolRun s!"{label}, broadcast" check "Broadcast" [.number 4]
      (accepted [("P", []), ("V", [.number 10]), ("W", [.number 15])])
    expectProtocolRun s!"{label}, broadcast, the message zero" check "Broadcast" [.number (fr - 1)]
      [("P", .returned []), ("V", .stopped .reject), ("W", .stopped .reject)]
  -- three roles: `n = 2x + 3`, which is 5 for `x = 1`
  if let some check ← protocolRunCheck "relay" then
    expectProtocolRun s!"{label}, relay" check "Relay" [.number 2]
      (accepted [("A", []), ("B", []), ("C", [.number 7])])
    expectProtocolRun s!"{label}, relay, n = 5" check "Relay" [.number 1]
      [("A", .returned []), ("B", .returned []), ("C", .stopped .reject)]
  -- an explicit role map: `r = x * x + 1`, refused when it is 10
  if let some check ← protocolRunCheck "mapped" then
    expectProtocolRun s!"{label}, mapped" check "Mapped" [.number 2]
      (accepted [("P", []), ("V", [.number 10])])
    expectProtocolRun s!"{label}, mapped, r = 10" check "Mapped" [.number 3]
      [("P", .returned []), ("V", .stopped .reject)]
  -- an application in a loop: `a + (a + 1) + (a + 2)`
  if let some check ← protocolRunCheck "looped" then
    expectProtocolRun s!"{label}, looped" check "Looped" [.number 5]
      (accepted [("P", []), ("V", [.number 18])])
  -- an application without results: the guard of the callee stops the verifier only
  if let some check ← protocolRunCheck "bare" then
    expectProtocolRun s!"{label}, bare" check "Bare" [.number 4]
      (accepted [("P", [.number 5]), ("V", [])])
    expectProtocolRun s!"{label}, bare, a = 0" check "Bare" [.number 0]
      [("P", .returned [.number 1]), ("V", .stopped .reject)]
  -- results bound by a tuple pattern: the verifier's value is the square of the prover's nonce
  if let some check ← protocolRunCheck "pattern" then
    match completeRoot check "Pattern" with
    | .error missing => failure s!"{label}, pattern: not run: {missing}"
    | .ok completed =>
      match completed.runProtocol "Pattern" [] with
      | .ok runs =>
        let outcomes : List (Zkc.Core.Execute.Outcome (List Datum)) := runs.toList.map (·.outcome)
        match outcomes with
        | [.returned [nonce], .returned [value]] =>
          expectTrue (value.toNat == nonce.toNat * nonce.toNat % fr)
            s!"{label}, pattern: the value {value.toNat} is not the square of the nonce {nonce.toNat}"
        | _ => failure s!"{label}, pattern: {outcomes.map describeRole}"
      | .error message => failure s!"{label}, pattern: does not run: {message}"
  -- a guard at two roles: both stop when `a = 0`
  if let some check ← protocolRunCheck "guarded" then
    expectProtocolRun s!"{label}, guarded" check "Both" [.number 2, .number 3]
      (accepted [("P", []), ("V", [.number 5])])
    expectProtocolRun s!"{label}, guarded, a = 0" check "Both" [.number 0, .number 3]
      [("P", .stopped .reject), ("V", .stopped .reject)]
  -- an `if` of the prover alone: the message is `2a` or `a`
  if let some check ← protocolRunCheck "private" then
    expectProtocolRun s!"{label}, private, true" check "Private" [.number 3, Datum.ofBool true]
      (accepted [("P", []), ("V", [.number 7])])
    expectProtocolRun s!"{label}, private, false" check "Private" [.number 3, Datum.ofBool false]
      (accepted [("P", []), ("V", [.number 4])])
  -- a static `if`: the instance at 0 sends `a`, the one at 1 sends `a + 1` and doubles it
  if let some check ← protocolRunCheck "static" then
    expectProtocolRun s!"{label}, static" check "Both" [.number 5]
      (accepted [("P", []), ("V", [.number 5, .number 12])])
  -- a loop bounded by a guard: `n` messages of `a`; refused for `n = 5`
  if let some check ← protocolRunCheck "bounded" then
    expectProtocolRun s!"{label}, bounded" check "Bounded" [.number 3, .number 2]
      (accepted [("P", []), ("V", [.number 6])])
    expectProtocolRun s!"{label}, bounded, none" check "Bounded" [.number 0, .number 2]
      (accepted [("P", []), ("V", [.number 0])])
    expectProtocolRun s!"{label}, bounded, n = 5" check "Bounded" [.number 5, .number 2]
      [("P", .stopped .reject), ("V", .stopped .reject)]
  -- a linear value passed on once: the ticket's value, tripled; refused when it is 0
  if let some check ← protocolRunCheck "ticket" then
    expectProtocolRun s!"{label}, ticket" check "Spend" [.sequence [.number 4]]
      (accepted [("P", []), ("V", [.number 12])])
    expectProtocolRun s!"{label}, ticket, zero" check "Spend" [.sequence [.number 0]]
      [("P", .returned []), ("V", .stopped .reject)]

end Zkc.Tests.Frontend
