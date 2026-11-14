/-!
# A generated program for measurements

A module of numbered units. Each unit holds records and variants, functions with loops,
`match` and mathematical forms in both spellings, relations with a `where`, an interface with a
law and its implementation, a protocol with its events and guards, a contract, a scheme, a
section with a specification-only parameter, a law of the module and a goal. The units differ by
their names and constants, so that no two declarations are equal.
-/

namespace Zkc.Tools.Frontend.Generate

def header : String :=
  "// A generated program: numbered units that mix the forms of the language.
module generated

use zkc::curves::bls12_381::{Fr, G1}
use zkc::option::{Option}
use zkc::security::{soundness}
"

/-- One unit; `i` gives its names and constants. -/
def generatedUnit (i : Nat) : String :=
  let n := i % 4 + 1
  s!"
// Unit {i}: a record, a variant, functions, a protocol, a specification and a scheme.
pub struct Pair{i}<T>:
    pub left: T
    pub right: T

pub enum Side{i}:
    Left
    Right(nat)

nat Size{i} = {i % 7 + 1}

pub def weighted{i}<F: Field>(xs: [F], weight: F) -> F:
    mut acc: F = 0
    for x in xs:
        acc := acc * weight + x
    if {i % 5} < length(xs):
        acc := acc + xs[0]
    else if length(xs) == 0:
        acc := -acc^2
    else:
        acc := acc - 1
    return acc

pub def pick{i}<T>(pair: Pair{i}<T>, side: Side{i}) -> T:
    Pair{i}\{left, right} = pair
    mut chosen = left
    match side:
        case Left:
            ()
        case Right(count):
            guard count < {i + 2} else abort
            chosen := right
    return chosen

pub def total{i}<F: Field, n: nat>(xs: [F; n], ys: [F; n]) -> F:
    (∑ k ∈ 0..n, xs[k] * ys[k]) + sum([x * x for x in xs]) + ⟪xs, ys⟫ - inner(ys, xs)

pub def swap{i}<T>(pair: Pair{i}<T>) -> Pair{i}<T>: \{pair with left = pair.right, right = pair.left}

pub relation Sorted{i}<n: nat>(xs: [byte; n]) where (1 <= n): ∀ k ∈ 0..n - 1, xs[k] <= xs[k + 1]

pub relation Opening{i}<G: PrimeOrderGroup>(base: G, point: G; scalar: G::Scalar):
    point == base * scalar and any([s != 0 for s in [scalar]]) or ∃ s ∈ [scalar], s == 0

pub interface Carrier{i}:
    type T
    def unit() -> T
    def add(a: T, b: T) -> T
    law unit_left(a: T): add(unit(), a) == a

pub module Counted{i}: Carrier{i}:
    type T = nat
    def unit(): {i}
    def add(a, b): a + b

pub protocol Exchange{i}<G: PrimeOrderGroup> roles(P, V)(
    base: G @(P, V),
    point: G @(P, V),
    scalar: G::Scalar @P
) -> accepted: bool @V:
    nonce @P <- sample G::Scalar
    commitment <- send base * nonce to V
    challenge <- draw G::Scalar from V to P
    response <- send nonce + challenge * scalar to V
    guard @V base * response == commitment + point * challenge else reject
    for round in 0..{n} collect (marks = round * 2):
        echo <- send round from V to P
        guard @P echo == round
    accepted @V = if challenge == 0 then false else not (response == 0)
    return accepted

spec for Exchange{i}:
    proves Opening{i}(base, point; scalar)
    ensures accepted
    charge sites.challenge <= 1 / G::Scalar::Order

scheme Dealt{i} = Exchange{i}<G1>:
    prover P
    construction interactive

section <F: Field, spec e: nat>:
    pub relation NearZero{i}(; xs: [F; {n}]): (∑ k ∈ 0..{n}, if xs[k] == 0 then 0 else 1) <= e
    law small{i}(x: index<{n}>): x < {n}

law doubled{i}(): {i} * 2 == {2 * i}

goal Sound{i} = soundness(Dealt{i}, statement = fixed, spec e = {n})
"

/-- A program of about `lines` lines. -/
def program (lines : Nat) : String := Id.run do
  let unitLines := (generatedUnit 0).foldl (fun count c => if c == '\n' then count + 1 else count) 0
  let units := max 1 ((lines + unitLines - 1) / unitLines)
  let mut text := header
  for i in [0:units] do
    text := text ++ generatedUnit i
  return text

end Zkc.Tools.Frontend.Generate
