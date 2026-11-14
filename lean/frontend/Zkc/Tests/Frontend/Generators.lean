import Zkc.Tests.Frontend.NamesReference
import Zkc.Tools.Frontend.Differential

/-!
# Generators of true statements

A protocol run on inputs drawn by type is mostly run on a false statement: an honest verifier
stops at its first check, and what comes after it is not run. So a change after the first
check is not seen: the fold of Sumcheck with its two halves exchanged agrees with the right
one under every seed on drawn inputs.

A **generator** is a function of the language in a test module beside its protocol: from
freely drawn values to a statement and its witness, in the order of the protocol's inputs. The
table `generators` names, for each protocol root, its generator and a second function whose
statement is false in one component. The free values have types that exclude a degenerate
statement where the type can: the logarithm of a base is a unit.

The suite runs each protocol, with the worked programs of the reference:

- on the statements of its generator, where every role returns and the package is observed to
  agree with itself;
- on the false statements, where the verifier stops: the check that a verifier is not
  satisfied by everything.

The runs are under draws taken from the stream first (`statementSeeds`): under a boundary draw
every coin of a run is one boundary value, and with a challenge of zero the verifier of
Schnorr's protocol accepts every response.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend
open Zkc.Frontend.Syntax
open Zkc.Tools.Frontend.Differential

/-- The test modules of the generators, each with its protocol: the worked program's, named by
`use`, or its text where the worked program does not make it public. -/
def generatorPrograms : Array (String × String) := #[
  ("schnorr_statements", "// True statements of Schnorr's protocol, from free values, and a false one for a control.
module schnorr_statements

use schnorr::{Schnorr}
use zkc::curves::bls12_381::{Fr, G1}

pub def statement(base_log: nonzero<Fr>, scalar: Fr) -> (G1, G1, Fr):
    base = G1::generator() * base_log
    return (base, base * scalar, scalar)

// The point is one base more than the base times the scalar.
pub def false_statement(base_log: nonzero<Fr>, scalar: Fr) -> (G1, G1, Fr):
    base = G1::generator() * base_log
    return (base, base * scalar + base, scalar)

// instantiate: Schnorr<G1>
"),
  ("chaum_pedersen_statements", "// Chaum–Pedersen's protocol with true statements from free values, and a false one for a
// control. The protocol is the worked program's, which another module cannot name.
module chaum_pedersen_statements

use zkc::curves::bls12_381::{Fr, G1}

section <G: PrimeOrderGroup>:
    protocol ChaumPedersen roles(P, V)(
        g: G @(P, V),
        h: G @(P, V),
        u: G @(P, V),
        v: G @(P, V),
        x: G::Scalar @P
    ):
        r @P <- sample G::Scalar
        (a, b) <- send (g * r, h * r) to V
        c <- draw G::Scalar from V to P
        z <- send r + c * x to V
        guard @V g * z == a + u * c
        guard @V h * z == b + v * c

pub def statement(g_log: nonzero<Fr>, h_log: nonzero<Fr>, x: Fr) -> (G1, G1, G1, G1, Fr):
    g = G1::generator() * g_log
    h = G1::generator() * h_log
    return (g, h, g * x, h * x, x)

// The second point has another logarithm than the first.
pub def false_statement(g_log: nonzero<Fr>, h_log: nonzero<Fr>, x: Fr) -> (G1, G1, G1, G1, Fr):
    g = G1::generator() * g_log
    h = G1::generator() * h_log
    return (g, h, g * x, h * x + h, x)

// instantiate: ChaumPedersen<G1>
"),
  ("or_statements", "// True statements of the OR proof, from free values, and a false one for a control.
module or_statements

use sigma_or::{Or, Witness}
use zkc::curves::bls12_381::{Fr, G1}

pub def statement(base_log: nonzero<Fr>, known: Fr, other: Fr) -> (G1, G1, G1, Witness<G1>):
    base = G1::generator() * base_log
    return (base, base * known, base * other, Witness::Left(known))

// The prover holds the logarithm of neither point.
pub def false_statement(base_log: nonzero<Fr>, known: Fr, other: Fr) -> (G1, G1, G1, Witness<G1>):
    base = G1::generator() * base_log
    return (base, base * known + base, base * other, Witness::Left(known))

// instantiate: Or<G1>
"),
  ("inner_product_statements", "// The inner-product argument at one round with true statements from free values, and a false
// one for a control. The protocol is the worked program's, which another module cannot name.
module inner_product_statements

use zkc::curves::bls12_381::{Fr, G1}
use zkc::sequence::{low, high, fold}

section <G: PrimeOrderGroup>:
    def commitment<m: nat>(
        g: [G; 2^m],
        h: [G; 2^m],
        u: G,
        a: [G::Scalar; 2^m],
        b: [G::Scalar; 2^m]
    ) -> G:
        ⟪g, a⟫ + ⟪h, b⟫ + u * ⟪a, b⟫

    protocol InnerProduct<n: nat> roles(P, V)(
        g: [G; 2^n] @(P, V),
        h: [G; 2^n] @(P, V),
        u: G @(P, V),
        target: G @(P, V),
        a: [G::Scalar; 2^n] @P,
        b: [G::Scalar; 2^n] @P
    ):
        mut gk = g
        mut hk = h
        mut pk = target
        mut ak = a
        mut bk = b
        for k in 0..n:
            left <- send commitment(high(gk), low(hk), u, low(ak), high(bk)) to V
            right <- send commitment(low(gk), high(hk), u, high(ak), low(bk)) to V
            x <- draw nonzero<G::Scalar> from V to P
            y = 1 / x
            gk := fold(gk, y, x)
            hk := fold(hk, x, y)
            pk := left * x^2 + pk + right * y^2
            ak := fold(ak, x, y)
            bk := fold(bk, y, x)
        a_last <- send ak[0] to V
        b_last <- send bk[0] to V
        guard @V pk == gk[0] * a_last + hk[0] * b_last + u * (a_last * b_last)

pub def statement(g: [G1; 2], h: [G1; 2], u: G1, a: [Fr; 2], b: [Fr; 2]) -> ([G1; 2], [G1; 2], G1, G1, [Fr; 2], [Fr; 2]):
    return (g, h, u, commitment<G1, 1>(g, h, u, a, b), a, b)

// The target is one `u` more than the commitment.
pub def false_statement(g: [G1; 2], h: [G1; 2], u: G1, a: [Fr; 2], b: [Fr; 2]) -> ([G1; 2], [G1; 2], G1, G1, [Fr; 2], [Fr; 2]):
    return (g, h, u, commitment<G1, 1>(g, h, u, a, b) + u, a, b)

// instantiate: InnerProduct<G1, 1>
"),
  ("sumcheck_statements", "// True statements of Sumcheck at ten rounds, from a free table, and a false one for a control.
module sumcheck_statements

use sumcheck<Fr>::{Sumcheck, Table}
use zkc::curves::bls12_381::{Fr}

pub def statement(values: Table<10>) -> (Table<10>, Fr):
    return (values, sum(values))

// The claim is one more than the sum.
pub def false_statement(values: Table<10>) -> (Table<10>, Fr):
    return (values, sum(values) + 1)

// instantiate: Sumcheck<10>
")
]

/-- For each test module: its protocol root, the generator of its true statements, and the
function whose statement is false. -/
def generators : Array (String × String × String × String) := #[
  ("schnorr_statements", "Schnorr<G1>", "statement", "false_statement"),
  ("chaum_pedersen_statements", "ChaumPedersen<G1>", "statement", "false_statement"),
  ("or_statements", "Or<G1>", "statement", "false_statement"),
  ("inner_product_statements", "InnerProduct<G1, 1>", "statement", "false_statement"),
  ("sumcheck_statements", "Sumcheck<Fr, 10>", "statement", "false_statement")
]

/-- The generators of a test module, for the settings of a comparison. -/
def generatorsOf (program : String) : Array (String × String) :=
  generators.filterMap fun (name, root, generator, _) =>
    if name == program then some (root, generator) else none

/-- Each protocol on the statements of its generator and on the false statements, under the
first seeds of `statementSeeds`. -/
def generatorSuite (reference : System.FilePath) : TestM Unit := do
  let programs := reference / "programs"
  let load ← cachedLoader #[reference / "lib", programs, programs / "support"]
  let defaults : Settings := {}
  let seeds := (statementSeeds defaults.seeds).take 1
  for (name, root, generator, falseGenerator) in generators do
    let some (_, text) := generatorPrograms.find? (·.1 == name)
      | failure s!"{name}: no such test module"
    let emission ← match ← emit #[{ name, parsed := parseString name text }] load with
      | .ok emission => pure emission
      | .error message => do failure s!"{name}: {message}"; continue
    let rootOf (description : String) : Option Zkc.Core.Raw.Package :=
      (emission.roots.find? (·.1 == description)).map (·.2)
    let some package := rootOf root | do failure s!"{name}: no root {root}"; continue
    let some trueStatements := rootOf generator
      | do failure s!"{name}: no generator {generator}"; continue
    let some falseStatements := rootOf falseGenerator
      | do failure s!"{name}: no generator {falseGenerator}"; continue
    let settings : Settings := { seeds }
    -- a true statement: every role returns, and the package agrees with itself
    let onTrue := compareRoot settings package package emission.sites emission.sites
      (some trueStatements)
    expectTrue (onTrue matches .agree _)
      s!"{name}: {root} on the statements of its generator: {onTrue.describe}"
    -- a false statement: the verifier stops
    let onFalse := compareRoot settings package package emission.sites emission.sites
      (some falseStatements)
    let stops := match onFalse with
      | .incomplete (.cannotRun reason) => (reason.splitOn "stopped reject").length > 1
      | _ => false
    expectTrue stops s!"{name}: {root} on a false statement: {onFalse.describe}"

end Zkc.Tests.Frontend
