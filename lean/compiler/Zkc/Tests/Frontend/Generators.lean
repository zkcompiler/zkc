import Zkc.Tests.Frontend.NamesReference
import Zkc.Tools.Frontend.PackageRuns

/-!
# Generators of true statements

A protocol run on inputs drawn by type is mostly run on a false statement: an honest verifier
stops at its first check, and what comes after it is not run.

A **generator** is a function of the language in a test module beside its protocol: from
freely drawn values to a statement and its witness, in the order of the protocol's inputs. The
table `generators` names, for each protocol root, its generator and a second function whose
statement is false in one component. The free values have types that exclude a degenerate
statement where the type can: the logarithm of a base is a unit.

The suite emits each test module with the worked programs of the repository, runs the generator
by the core's executor on values drawn by type (`PackageRuns.inputs`), and runs every role of
the protocol together on what it returns, with the coins of a seed:

- on the statement of its generator, every role returns;
- on the false statement, a role stops `reject`: the check that a verifier is not satisfied by
  everything.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend
open Zkc.Frontend.Syntax
open Zkc.Core.Concrete (Datum)

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

/-- The seed of the free values and of the coins of the runs. -/
def generatorSeed : Nat := 14

/-- The packages of the complete roots of a test module, by their descriptions. -/
def emittedRoots (name text : String) (load : Array String → IO (Option SourceInput)) :
    IO (Except String (Array (String × Zkc.Core.Raw.Package))) := do
  let check ← checkNames #[{ name, parsed := parseString name text }] load
  if let some first := check.refusals[0]? then
    return .error s!"the names are refused: {first.render}"
  let schemes := checkSchemes (checkTyping (checkInstances check #[name]) #[name])
  return match (schemes.session.admitRoots none).completeRoots with
    | .ok (roots, _) => .ok (roots.held.map fun (description, held) => (description, held.package))
    | .error reported => .error s!"nothing is emitted: {"; ".intercalate reported.toList}"

/-- The inputs of the newest protocol of a package as the source has them: the ports that an
agreement over the inputs names are one input held by several roles, and every other port is
an input of its own; in the order of their first ports. -/
def sourceInputs (package : Zkc.Core.Raw.Package) : List (List Nat) :=
  match package.protocols.getLast? with
  | none => []
  | some protocol =>
    let agreed := (protocol.agreements.filter (!·.overOutputs)).map (·.ports)
    let alone := (List.range protocol.inputs.length).filter fun port => !agreed.any (·.contains port)
    (agreed ++ alone.map ([·])).mergeSort fun first second => first.headD 0 ≤ second.headD 0

/-- The statement and the witness that a generator gives for a protocol: the last function of
the generator's package run on values drawn for its inputs, its outputs in the order of the
protocol's inputs in the source; one datum per input port of the protocol. A generator that
returns one tuple gives its components. -/
def statementOf (generator protocol : Zkc.Core.Raw.Package) : Except String (List Datum) := do
  let typed ← match Zkc.Core.elaborate generator with
    | .ok typed => pure typed
    | .error refusal => throw s!"the core refuses the generator: {reprStr refusal}"
  let some header := typed.functions.head? | throw "the generator has no function"
  let free ← Zkc.Tools.Frontend.PackageRuns.inputs generator.types.toArray generatorSeed header.inputs
  let inputs := sourceInputs protocol
  let ports := (protocol.protocols.getLast?.map (·.inputs.length)).getD 0
  match Zkc.Core.Vocabulary.runData Zkc.Core.Vocabulary.table generator
      (typed.functions.length - 1) free with
  | .returned outputs =>
    let given := match outputs with
      | [.sequence items] => if inputs.length == 1 then outputs else items
      | other => other
    if given.length != inputs.length then
      throw s!"the generator gives {given.length} values, and the protocol has {inputs.length} inputs"
    return (inputs.zip given).foldl (init := List.replicate ports (default : Datum))
      fun data (held, datum) => held.foldl (fun data port => data.set port datum) data
  | .stopped reason => throw s!"the generator stops {Zkc.Tools.Frontend.PackageRuns.stopText reason}"
  | .limit elements => throw s!"the generator reaches the limit of {elements} elements"
  | .failed message => throw s!"the generator fails: {message}"

/-- Every role of the newest protocol of a package run together on a statement and a witness,
with the coins of the seed: how each ended. -/
def runOnStatement (package : Zkc.Core.Raw.Package) (data : List Datum) :
    Except String (List (Zkc.Core.Execute.Outcome (List Datum))) := do
  let roles := (package.protocols.getLast?.map (·.roles)).getD 0
  let run ← Zkc.Core.Vocabulary.runEntry Zkc.Core.Vocabulary.table package (List.range roles) data
    [generatorSeed]
  return run.outcomes

/-- The ends of the roles, as a line. -/
def describeEnds (ends : List (Zkc.Core.Execute.Outcome (List Datum))) : String :=
  "; ".intercalate (ends.map Zkc.Tools.Frontend.PackageRuns.describe)

/-- Each protocol on the statement of its generator, where every role returns, and on the false
statement, where a role stops `reject`. -/
def generatorSuite (repository : Repository) : TestM Unit := do
  let programs := repository.examples
  let load ← cachedLoader #[repository.libraries, programs, programs / "support"]
  for (name, root, generator, falseGenerator) in generators do
    let some (_, text) := generatorPrograms.find? (·.1 == name)
      | failure s!"{name}: no such test module"
    let roots ← match ← emittedRoots name text load with
      | .ok roots => pure roots
      | .error message => do failure s!"{name}: {message}"; continue
    let rootOf (description : String) : Option Zkc.Core.Raw.Package :=
      (roots.find? (·.1 == description)).map (·.2)
    let some package := rootOf root | do failure s!"{name}: no root {root}"; continue
    let some trueStatements := rootOf generator
      | do failure s!"{name}: no generator {generator}"; continue
    let some falseStatements := rootOf falseGenerator
      | do failure s!"{name}: no generator {falseGenerator}"; continue
    -- a true statement: every role returns
    match statementOf trueStatements package >>= runOnStatement package with
    | .ok ends =>
      expectTrue (!ends.isEmpty && ends.all (· matches .returned _))
        s!"{name}: {root} on the statement of its generator: {describeEnds ends}"
    | .error message => failure s!"{name}: {root} on the statement of its generator: {message}"
    -- a false statement: a role stops `reject`
    match statementOf falseStatements package >>= runOnStatement package with
    | .ok ends =>
      expectTrue (ends.any (· matches .stopped .reject))
        s!"{name}: {root} on a false statement: {describeEnds ends}"
    | .error message => failure s!"{name}: {root} on a false statement: {message}"

end Zkc.Tests.Frontend
