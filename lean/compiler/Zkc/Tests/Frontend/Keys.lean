import Zkc.Tests.Frontend.Names
import Zkc.Tests.Frontend.NameCases
import Zkc.Tools.Frontend.Reading

/-!
# The keys of the coins of a run

The run of an emitted package gives the coin of a draw or a sample by the key of its site in the
source, from the table of sites that the frontend keeps for each protocol (`PackageRuns.keyOf`),
and the second reading keys its coins alike (`Zkc.Tools.Frontend.Reading`). These checks are
about that code itself, on a protocol of two draws whose two sites are exchanged in its package:
with the rows of its table exchanged alike, each draw keeps the key of its event and the runs
agree; with the original's table the two coins are exchanged and the runs differ; a site without
a row has no key and cannot be run; a table that gives two sites one key is refused
(`PackageRuns.duplicateKey?`); and with no seed nothing is observed.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend.Syntax
open Zkc.Tools.Frontend

/-- A protocol whose verifier draws two challenges and returns them. -/
def twoDrawsProgram : String := "module two_draws
type F = primitive(\"bls12-381.fr\")
protocol TwoDraws roles(P, V)(x: F @(P, V)) -> (first: F @(P, V), second: F @(P, V)):
    c <- draw F from V to P
    d <- draw F from V to P
    return (c + x, d)
"

/-- The text of a package with the sites `a` and `b` of its draws, samples and applications
exchanged: the same protocol, its sites numbered otherwise. -/
partial def exchangeSites (a b : Nat) : Zkc.Json → Zkc.Json
  | .arr items =>
    let position := match items[0]? with
      | some (.str "draw") | some (.str "apply") => some 3
      | some (.str "sample") => some 2
      | _ => none
    let items := items.map (exchangeSites a b)
    let exchange : Zkc.Json → Zkc.Json
      | .num n => .num (if n == a then b else if n == b then a else n)
      | other => other
    .arr (match position with
      | some index => items.modify index exchange
      | none => items)
  | other => other

/-- The verdict over seeds of two packages of one protocol, every role of each run on the same
inputs: what each role of the first shows against the second. -/
def runsAgainst (left right : PackageRuns.Side) (seeds : List Nat) : PackageRuns.Verdict :=
  match left.typed.protocols.head? with
  | none => .incomplete (.cannotRun "the package has no protocol")
  | some header =>
    PackageRuns.overSeeds seeds fun seed => do
      let inputs := PackageRuns.agreed (PackageRuns.agreementsOf left.package)
        (← PackageRuns.inputs left.package.types.toArray seed (header.inputs.map (·.type)))
      let first ← PackageRuns.runProtocol left seed inputs
      let second ← PackageRuns.runProtocol right seed inputs
      return (inputs, PackageRuns.compareShown first second)

/-- The keys of the coins of the protocol of two draws. -/
def keyingSuite : TestM Unit := do
  let trees ← match ← Trees.treesOf
      #[{ name := "two_draws", parsed := parseString "two_draws" twoDrawsProgram }]
      (fun names => pure (Id.run (memoryLoader nameLibrary names))) with
    | .ok trees => pure trees
    | .error message => do failure s!"two draws: {message}"; return
  let held ← match (trees.session.admitRoots none).completeRoots with
    | .ok (roots, _) => pure roots.held
    | .error reported => do failure s!"two draws: nothing is emitted: {"; ".intercalate reported.toList}"; return
  let some (_, root) := held[0]? | failure "two draws: no root"
  let package := root.package
  let sites := Reading.siteTables trees
  let some (name, rows) := sites[0]? | failure "two draws: no table of sites"
  let some first := rows[0]? | failure "two draws: no site 0"
  let some second := rows[1]? | failure "two draws: no site 1"
  let render (package : Zkc.Core.Raw.Package) := Zkc.Json.render (Zkc.Core.Raw.printPackage package)
  let exchanged ← match Zkc.Core.Raw.parsePackage (Zkc.Json.render (exchangeSites 0 1 (Zkc.Core.Raw.printPackage package))) with
    | .ok exchanged => pure exchanged
    | .error message => do failure s!"two draws: {message}"; return
  expectTrue (render exchanged != render package) "two draws: the sites exchanged change the text"
  -- the keys of the sites of the newest protocol, outside any application
  let site (number : Nat) : Zkc.Core.Site :=
    { path := [], definition := package.protocols.length - 1, number }
  let swapped := #[(name, #[second, first])]
  let withoutRow := #[(name, #[second])]
  let original := PackageRuns.keyOf package sites
  let renumbered := PackageRuns.keyOf exchanged swapped
  expectTrue ((original (site 0)).isSome && (original (site 1)).isSome &&
      original (site 0) != original (site 1))
    "two draws: the table gives the two sites two keys"
  expectTrue (renumbered (site 0) == original (site 1) && renumbered (site 1) == original (site 0))
    "two draws: renumbered with the table, each draw keeps the key of its event"
  expectTrue (PackageRuns.keyOf exchanged withoutRow (site 1)).isNone
    "two draws: a site without a row has no key"
  -- a table that gives two sites one key: the two would get the same coins
  expectTrue (PackageRuns.duplicateKey? package sites).isNone
    "two draws: the frontend's table gives no key twice"
  expectTrue (PackageRuns.duplicateKey? package #[(name, #[first, first])]).isSome
    "two draws: a table that names a key twice is refused"
  -- the runs
  let side (package : Zkc.Core.Raw.Package) (sites : Array (String × Array PackageRuns.SiteRow)) :
      TestM (Option PackageRuns.Side) := do
    match PackageRuns.side package sites with
    | .ok side => return some side
    | .error message => do failure s!"two draws: {message}"; return none
  let some originalSide ← side package sites | return
  let some renumberedSide ← side exchanged swapped | return
  let some unkeyedSide ← side exchanged sites | return
  let some rowlessSide ← side exchanged withoutRow | return
  let seeds := List.range 4
  expectTrue (runsAgainst originalSide renumberedSide seeds matches .agree _)
    "two draws: renumbered with the table, observed to agree"
  expectTrue (runsAgainst originalSide unkeyedSide seeds matches .differ ..)
    "two draws: renumbered without the table, observed to differ"
  expectTrue (runsAgainst originalSide rowlessSide seeds matches .incomplete (.cannotRun _))
    "two draws: a site without a row cannot be run"
  -- without a seed nothing is observed
  expectTrue (runsAgainst originalSide originalSide [] matches .incomplete .noSeed)
    "two draws: without a seed the comparison is incomplete"

end Zkc.Tests.Frontend
