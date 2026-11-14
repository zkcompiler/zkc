import Zkc.Tests.Frontend.Typing
import Zkc.Tests.Frontend.NamesReference

/-!
# Running emitted functions

Functions typed, emitted and admitted run under the model of the vocabulary's rows, and give the
results their definitions give.

- Without the reference: the arguments of a call and the fields of a construction are evaluated
  in the order the source writes them, which the first stop shows; a sum carried by a loop, a sum
  written out term by term, a loop of no iteration and the choices on `and` and `or` give the
  values of their definitions; a definition generic over a module parameter calls the members
  of the module its operators resolve to.
- With the reference: every public function of `zkc::sequence`, at instances over `koala-bear`
  and `bls12-381.fr` and at size 0 where its `where` allows, runs on inputs, and its result is
  the one that a plain function over lists and numbers, written here, computes. `get` and
  `slice` stop with their guard's reason outside their range. Every run ends in a return or an
  authored stop, never `undefined`. The function members of the sorts and the arithmetic of the
  quartic extension of KoalaBear and of G1 run from source, against values stated here.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend
open Zkc.Frontend.Syntax
open Zkc.Core.Concrete (Datum)

/-- How a run ends, as the test states it. -/
inductive Expected where
  | returned (outputs : List Datum)
  /-- Returns outputs that have a property. -/
  | returnedSuch (property : List Datum → Bool)
  | stopped (reason : PIR.Stop)

def Expected.matches : Expected → Zkc.Core.Vocabulary.Run → Bool
  | .returned outputs, .returned found => outputs == found
  | .returnedSuch property, .returned found => property found
  | .stopped reason, .stopped found => reason == found
  | _, _ => false

def describeOutcome : Zkc.Core.Vocabulary.Run → String
  | .returned outputs => s!"returned {reprStr outputs}"
  | .stopped reason => s!"stopped {reprStr reason}"
  | .limit elements => s!"reached the limit of {elements} elements"
  | .failed message => s!"failed: {message}"

/-- The completed result of one root of a check, as the tool runs it: no error reported, no check
incomplete, and the root's package admitted by the core; or what is missing. -/
def completeRoot (check : TypingCheck) (root : String) : Except String (Completed RootPackage) :=
  match (check.session.admitRoots (some #[root])).complete with
  | .ok completed => .ok completed
  | .error missing => .error ("; ".intercalate missing.toList)

/-- Runs a root of a check and compares the outcome; a run that stops `undefined` or does not
start fails. -/
def expectRun (label : String) (check : TypingCheck) (root : String) (inputs : List Datum)
    (expected : Expected) : TestM Unit := do
  match completeRoot check root with
  | .error missing => failure s!"{label}: {root} is not run: {missing}"
  | .ok completed =>
    let outcome := completed.runFunction root inputs
    match outcome with
    | .stopped .undefined | .stopped .incomplete =>
      failure s!"{label}: {root} stops {describeOutcome outcome}"
    | .failed message => failure s!"{label}: {root} does not run: {message}"
    | _ =>
      expectTrue (expected.matches outcome)
        s!"{label}: {root} on {reprStr inputs}: {describeOutcome outcome}"

def numbers (values : List Nat) : Datum := .sequence (values.map .number)

/-! ## Without the reference -/

def runningProgram : String := "module t
use zkc::option::{Option}
def a(x: nat) -> nat:
    guard x < 1 else abort
    return x
def b(x: nat) -> nat:
    guard x < 2 else refused
    return x
def pick<T>(o: Option<T>, n: T) -> T: n
def g(x: nat) -> nat: pick(Some(a(x)), b(x))
struct P:
    pub l: nat
    pub r: nat
def h(x: nat) -> P: P{r = b(x), l = a(x)}
def value(units: [byte; 3]) -> index<16777216>: ∑ i ∈ 0..3, units[i] * 256^i
def weight(flags: [bool; 3]) -> index<4>: ∑ f ∈ flags, if f then 1 else 0
def none(xs: [nat; 0]) -> nat: ∑ x ∈ xs, x
def first(xs: [byte], n: nat) -> nat: if 0 < length(xs) and xs[0] == 1 then xs[0] else n % 5
def choose(i: nat, j: nat, ys: [byte; 4]) -> byte: if 1 <= i and (i - 1 < 3 and j < 4) then ys[j] else 0
def skip(i: nat, j: nat, ys: [byte; 4]) -> byte: if i == 0 or (4 <= i - 1 or 4 <= j) then 0 else ys[j]
def kept(i: nat, js: [nat; 3], ys: [byte; 4]) -> [byte]: [ys[j] for j in js if 1 <= i and (i - 1 < 3 and j < 4)]
def unskipped(i: nat, js: [nat; 3], ys: [byte; 4]) -> [byte]:
    [ys[j] for j in js if not (i == 0 or (4 <= i - 1 or 4 <= j))]
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
interface Doubler<C: Carrier>:
    def double(x: C::T) -> C::T
module Twice<C: Carrier>: Doubler<C>:
    def double(x): x + x
def doubled(x: nat) -> nat: Twice<Weird>::double(x)
"

def runningSuite : TestM Unit := do
  let input : SourceInput := { name := "running", parsed := parseString "running" runningProgram }
  let nameCheck := Id.run (checkNames #[input] (memoryLoader nameLibrary))
  if let some first := nameCheck.refusals[0]? then
    failure s!"running: the names do not resolve: {first.render}"
    return
  let check := checkTyping (checkInstances nameCheck #["running"]) #["running"]
  if let some first := check.refusals[0]? then
    failure s!"running: {first.render}"
    return
  checkPackages "running" check
  let label := "running"
  -- the deferred argument `Some(a(x))` comes before `b(x)`: `a` stops first
  expectRun label check "g" [.number 5] (.stopped .abort)
  expectRun label check "g" [.number 0] (.returned [.number 0])
  -- the field `r = b(x)` is written first: `b` stops first
  expectRun label check "h" [.number 5] (.stopped .refused)
  expectRun label check "h" [.number 0] (.returned [.sequence [.number 0, .number 0]])
  -- sums, a loop of no iteration, choices
  let units := [1, 2, 3]
  expectRun label check "value" [numbers units]
    (.returned [.number ((List.range 3).foldl (fun total i => total + units.getD i 0 * 256 ^ i) 0)])
  let flags := [true, false, true]
  expectRun label check "weight" [.sequence (flags.map Datum.ofBool)]
    (.returned [.number (flags.filter id).length])
  expectRun label check "none" [numbers []] (.returned [.number 0])
  for (xs, n) in [([1], 7), ([], 7), ([2, 1], 9)] do
    let expected := if 0 < xs.length && xs.head? == some 1 then 1 else n % 5
    expectRun label check "first" [numbers xs, .number n] (.returned [.number expected])
  let ys := [5, 6, 7, 8]
  for (i, j) in [(2, 1), (0, 1), (5, 1), (2, 9), (4, 3)] do
    let chosen := if 1 ≤ i && i - 1 < 3 && j < 4 then ys.getD j 0 else 0
    expectRun label check "choose" [.number i, .number j, numbers ys] (.returned [.number chosen])
    let skipped := if i == 0 || 4 ≤ i - 1 || 4 ≤ j then 0 else ys.getD j 0
    expectRun label check "skip" [.number i, .number j, numbers ys] (.returned [.number skipped])
  let js := [1, 5, 3]
  for i in [0, 2, 4, 5] do
    let kept := (js.filter fun j => 1 ≤ i && i - 1 < 3 && j < 4).map (ys.getD · 0)
    expectRun label check "kept" [.number i, numbers js, numbers ys] (.returned [numbers kept])
    let unskipped := (js.filter fun j => !(i == 0 || 4 ≤ i - 1 || 4 ≤ j)).map (ys.getD · 0)
    expectRun label check "unskipped" [.number i, numbers js, numbers ys] (.returned [numbers unskipped])

/-- The members of `Weird`: its `add`, `zero` and `equal` are not those of `nat`. -/
def weirdAdd (a b : Nat) : Nat := a * b + 1

/-- A definition generic over a module parameter calls, at its instance, the members of the
module that its opaque typing resolved its operators, forms and `==` to (SP12). -/
def opaqueRunSuite : TestM Unit := do
  let input : SourceInput := { name := "running", parsed := parseString "running" runningProgram }
  let nameCheck := Id.run (checkNames #[input] (memoryLoader nameLibrary))
  let check := checkTyping (checkInstances nameCheck #["running"]) #["running"]
  if let some first := check.refusals[0]? then
    failure s!"running: {first.render}"
    return
  let label := "opaque"
  expectRun label check "twice<Weird>" [.number 5] (.returned [.number (weirdAdd 5 5)])
  let xs := [2, 3, 4]
  expectRun label check "total<Weird, 3>" [numbers xs] (.returned [.number (xs.foldl weirdAdd 1)])
  for (x, y) in [(4, 5), (4, 4)] do
    expectRun label check "same<Weird>" [.number x, .number y] (.returned [Datum.ofBool (x + 1 == y)])
  -- a member definition generic over a module parameter of its module
  expectRun label check "doubled" [.number 5] (.returned [.number (weirdAdd 5 5)])

/-! ## `zkc::sequence`, over the reference -/

def koalaBear : Nat := 2130706433
def fr : Nat := 52435875175126190479447740508185965837690552500527637822603658699938581184513

/-- `base ^ exponent` modulo `modulus`, by repeated squaring. -/
def modularPower (base exponent modulus : Nat) : Nat := Id.run do
  let mut result := 1 % modulus
  let mut square := base % modulus
  let mut remaining := exponent
  while remaining > 0 do
    if remaining % 2 == 1 then result := result * square % modulus
    square := square * square % modulus
    remaining := remaining / 2
  return result

/-- The position whose `k` bits are those of `i` in reverse order. -/
def reversedBits (k i : Nat) : Nat :=
  (List.range k).foldl (fun total j => total + ((i / 2 ^ j) % 2) * 2 ^ (k - (j + 1))) 0

def sequenceProgram : String := "module running
use zkc::fields::{KoalaBear}
use zkc::curves::bls12_381::{Fr}
use zkc::sequence::{
    get, slice, zip, enumerate, count, reverse, flatten, low, high, fold, hadamard, powers,
    batch_inverse, bit_reverse
}
// instantiate: get<KoalaBear>
// instantiate: slice<KoalaBear>
// instantiate: zip<KoalaBear, Fr, 3>
// instantiate: zip<KoalaBear, KoalaBear, 0>
// instantiate: enumerate<KoalaBear, 3>
// instantiate: enumerate<KoalaBear, 0>
// instantiate: count<5>
// instantiate: count<0>
// instantiate: reverse<KoalaBear, 4>
// instantiate: reverse<KoalaBear, 0>
// instantiate: flatten<T = KoalaBear, n = 2, m = 3>
// instantiate: flatten<T = KoalaBear, n = 0, m = 2>
// instantiate: low<KoalaBear, 2>
// instantiate: low<KoalaBear, 0>
// instantiate: high<KoalaBear, 2>
// instantiate: high<KoalaBear, 0>
// instantiate: fold<KoalaBear, 1>
// instantiate: fold<Fr, 0>
// instantiate: hadamard<KoalaBear, 3>
// instantiate: hadamard<KoalaBear, 0>
// instantiate: powers<KoalaBear, 5>
// instantiate: powers<KoalaBear, 0>
// instantiate: batch_inverse<KoalaBear, 3>
// instantiate: batch_inverse<Fr, 2>
// instantiate: batch_inverse<KoalaBear, 0>
// instantiate: bit_reverse<KoalaBear, 3>
// instantiate: bit_reverse<KoalaBear, 0>
"

/-- Every public function of `zkc::sequence` runs and gives the result of its definition. -/
def sequenceRunSuite (reference : System.FilePath) : TestM Unit := do
  let load ← cachedLoader #[reference / "lib"]
  let input : SourceInput := { name := "running", parsed := parseString "running" sequenceProgram }
  let nameCheck ← checkNames #[input] fun names => (load names : IO _)
  if let some first := nameCheck.refusals[0]? then
    failure s!"running: the names do not resolve: {first.render}"
    return
  let check := checkTyping (checkInstances nameCheck #["running"]) #["running"]
  if let some first := check.refusals[0]? then
    failure s!"running: {first.span.file}: {first.render}"
    return
  checkPackages "running" check
  let p := koalaBear
  let label := "zkc::sequence"
  -- get and slice: inside their range, and stopped by their guard outside it
  let xs := [5, 6, 7]
  for position in [0:5] do
    let expected := if position < xs.length then Expected.returned [.number (xs.getD position 0)]
      else .stopped .refused
    expectRun label check "get<KoalaBear>" [numbers xs, .number position] expected
  for (start, count) in [(0, 0), (0, 3), (1, 2), (3, 0), (2, 2), (4, 0)] do
    let expected := if start + count ≤ xs.length
      then Expected.returned [numbers ((xs.drop start).take count)]
      else .stopped .refused
    expectRun label check "slice<KoalaBear>" [numbers xs, .number start, .number count] expected
  -- zip and enumerate
  let left := [1, 2, 3]
  let right := [fr - 1, 0, 9]
  expectRun label check "zip<KoalaBear, Fr, 3>" [numbers left, numbers right]
    (.returned [.sequence ((left.zip right).map fun (a, b) => numbers [a, b])])
  expectRun label check "zip<KoalaBear, KoalaBear, 0>" [numbers [], numbers []] (.returned [numbers []])
  expectRun label check "enumerate<KoalaBear, 3>" [numbers [7, 8, 9]]
    (.returned [.sequence ((List.range 3).zip [7, 8, 9] |>.map fun (i, v) => numbers [i, v])])
  expectRun label check "enumerate<KoalaBear, 0>" [numbers []] (.returned [numbers []])
  -- count
  let flags := [true, false, true, true, false]
  expectRun label check "count<5>" [.sequence (flags.map Datum.ofBool)]
    (.returned [.number (flags.filter id).length])
  expectRun label check "count<0>" [numbers []] (.returned [.number 0])
  -- reverse, flatten, low, high
  expectRun label check "reverse<KoalaBear, 4>" [numbers [1, 2, 3, 4]] (.returned [numbers [4, 3, 2, 1]])
  expectRun label check "reverse<KoalaBear, 0>" [numbers []] (.returned [numbers []])
  let parts := [[1, 2, 3], [4, 5, 6]]
  expectRun label check "flatten<KoalaBear, 2, 3>" [.sequence (parts.map numbers)]
    (.returned [numbers parts.flatten])
  expectRun label check "flatten<KoalaBear, 0, 2>" [numbers []] (.returned [numbers []])
  let eight := [10, 11, 12, 13, 14, 15, 16, 17]
  expectRun label check "low<KoalaBear, 2>" [numbers eight] (.returned [numbers (eight.take 4)])
  expectRun label check "high<KoalaBear, 2>" [numbers eight] (.returned [numbers (eight.drop 4)])
  expectRun label check "low<KoalaBear, 0>" [numbers [3, 4]] (.returned [numbers [3]])
  expectRun label check "high<KoalaBear, 0>" [numbers [3, 4]] (.returned [numbers [4]])
  -- fold: the halves combined with two scalars
  let v := [1, 2, p - 1, 4]
  let s := 10
  let t := p - 100
  expectRun label check "fold<KoalaBear, 1>" [numbers v, .number s, .number t]
    (.returned [numbers (((v.take 2).zip (v.drop 2)).map fun (a, b) => (a * s + b * t) % p)])
  expectRun label check "fold<Fr, 0>" [numbers [fr - 1, 2], .number 3, .number 5]
    (.returned [numbers [((fr - 1) * 3 + 2 * 5) % fr]])
  -- hadamard and powers
  let a := [2, 3, p - 1]
  let b := [5, 7, p - 1]
  expectRun label check "hadamard<KoalaBear, 3>" [numbers a, numbers b]
    (.returned [numbers ((a.zip b).map fun (x, y) => x * y % p)])
  expectRun label check "hadamard<KoalaBear, 0>" [numbers [], numbers []] (.returned [numbers []])
  expectRun label check "powers<KoalaBear, 5>" [.number 3]
    (.returned [numbers ((List.range 5).map fun i => modularPower 3 i p)])
  expectRun label check "powers<KoalaBear, 0>" [.number 3] (.returned [numbers []])
  -- batch_inverse, over the units of a field
  let units := [1, 2, p - 1]
  expectRun label check "batch_inverse<KoalaBear, 3>" [numbers units]
    (.returned [numbers (units.map fun x => modularPower x (p - 2) p)])
  let frUnits := [3, fr - 2]
  expectRun label check "batch_inverse<Fr, 2>" [numbers frUnits]
    (.returned [numbers (frUnits.map fun x => modularPower x (fr - 2) fr)])
  expectRun label check "batch_inverse<KoalaBear, 0>" [numbers []] (.returned [numbers []])
  -- bit_reverse
  let values := (List.range 8).map (· * 3)
  expectRun label check "bit_reverse<KoalaBear, 3>" [numbers values]
    (.returned [numbers ((List.range 8).map fun i => values.getD (reversedBits 3 i) 0)])
  expectRun label check "bit_reverse<KoalaBear, 0>" [numbers [42]] (.returned [numbers [42]])
  note s!"{check.packages.size} instances of zkc::sequence run"

/-! ## The function members of the sorts and the arithmetic of the types, over the reference -/

/-- The order of the base field of BLS12-381. -/
def baseOrder : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- The generator of G1 of BLS12-381. -/
def generatorX : Nat :=
  0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb
def generatorY : Nat :=
  0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1

/-- The generator of the subgroup of order `2^24` of KoalaBear. -/
def koalaBearRoot : Nat := 1791270792

/-- The product in KoalaBear's quartic extension, whose elements are their coefficients over
`x^4 = 3`. -/
def extensionProduct (a b : List Nat) : List Nat :=
  let p := koalaBear
  let full := (List.range 7).map fun k =>
    (List.range 4).foldl (fun total i =>
      if i ≤ k && k - i < 4 then total + a.getD i 0 * b.getD (k - i) 0 else total) 0
  (List.range 4).map fun k => (full.getD k 0 + 3 * full.getD (k + 4) 0) % p

def membersProgram : String := "module members
use zkc::fields::{KoalaBear, KoalaBear4}
use zkc::curves::bls12_381::{Fr, G1}
def kb_from_nat(n: nat) -> KoalaBear: KoalaBear::from_nat(n)
def kb_to_nat(x: KoalaBear) -> index<KoalaBear::Order>: KoalaBear::to_nat(x)
def kb_root(k: index<25>) -> nonzero<KoalaBear>: KoalaBear::root(k)
def kb_components(x: KoalaBear) -> [KoalaBear; 1]: KoalaBear::components(x)
def ext_embed(x: KoalaBear) -> KoalaBear4: KoalaBear4::embed(x)
def ext_coefficients(x: KoalaBear4) -> [KoalaBear; 4]: KoalaBear4::coefficients(x)
def ext_from_coefficients(c: [KoalaBear; 4]) -> KoalaBear4: KoalaBear4::from_coefficients(c)
def ext_product(a: KoalaBear4, b: KoalaBear4) -> KoalaBear4: a * b
def ext_inverse(a: nonzero<KoalaBear4>) -> nonzero<KoalaBear4>: 1 / a
def fr_to_nat(x: Fr) -> index<Fr::Order>: Fr::to_nat(x)
def g1_generator() -> G1: G1::generator()
def g1_multiple(s: Fr) -> G1: G1::generator() * s
"

/-- The function members of the sorts at `koala-bear`, its quartic extension, `bls12-381.fr` and
`bls12-381.g1`, and the arithmetic of the extension and of G1, run from source. -/
def membersRunSuite (reference : System.FilePath) : TestM Unit := do
  let load ← cachedLoader #[reference / "lib"]
  let input : SourceInput := { name := "members", parsed := parseString "members" membersProgram }
  let nameCheck ← checkNames #[input] fun names => (load names : IO _)
  if let some first := nameCheck.refusals[0]? then
    failure s!"members: the names do not resolve: {first.render}"
    return
  let check := checkTyping (checkInstances nameCheck #["members"]) #["members"]
  if let some first := check.refusals[0]? then
    failure s!"members: {first.render}"
    return
  checkPackages "members" check
  let p := koalaBear
  let label := "members"
  expectRun label check "kb_from_nat" [.number (p + 5)] (.returned [.number 5])
  expectRun label check "kb_to_nat" [.number (p - 1)] (.returned [.number (p - 1)])
  expectRun label check "kb_components" [.number 9] (.returned [numbers [9]])
  -- the root of order 2^k: the power of the generator of the subgroup of order 2^24
  for k in [0:25] do
    let root := modularPower koalaBearRoot (2 ^ (24 - k)) p
    let order (exponent : Nat) := modularPower root exponent p
    expectTrue (order (2 ^ k) == 1 && (k == 0 || order (2 ^ (k - 1)) != 1))
      s!"{label}: the stated generator gives no root of order 2^{k}"
    expectRun label check "kb_root" [.number k] (.returned [.number root])
  -- the quartic extension
  let a := [1, 2, 3, p - 4]
  let b := [5, 0, p - 7, 11]
  expectRun label check "ext_embed" [.number 5] (.returned [numbers [5, 0, 0, 0]])
  expectRun label check "ext_coefficients" [numbers a] (.returned [numbers a])
  expectRun label check "ext_from_coefficients" [numbers b] (.returned [numbers b])
  expectRun label check "ext_product" [numbers a, numbers b] (.returned [numbers (extensionProduct a b)])
  for value in [a, b, [0, 0, 0, 1]] do
    expectRun label check "ext_inverse" [numbers value]
      (.returnedSuch fun outputs => match outputs with
        | [.sequence items] => extensionProduct value (items.map (·.toNat)) == [1, 0, 0, 0]
        | _ => false)
  -- bls12-381.fr and G1
  expectRun label check "fr_to_nat" [.number (fr - 1)] (.returned [.number (fr - 1)])
  let generator := numbers [generatorX, generatorY]
  expectRun label check "g1_generator" [] (.returned [generator])
  expectRun label check "g1_multiple" [.number 1] (.returned [generator])
  expectRun label check "g1_multiple" [.number 0] (.returned [numbers []])
  expectRun label check "g1_multiple" [.number (fr - 1)]
    (.returned [numbers [generatorX, baseOrder - generatorY]])

end Zkc.Tests.Frontend
