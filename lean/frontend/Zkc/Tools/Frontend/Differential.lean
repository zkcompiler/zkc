import Zkc.Tools.Frontend.Names
import Zkc.Core.Digest
import Zkc.Core.Declaration
import Zkc.Core.RunComparison
import Zkc.Core.UninterpretedRows
import Zkc.Core.Mutation

/-!
# Differential runs: the packages of a program compared with a baseline by their runs

A **baseline** of a program is what a fixed commit of the frontend emitted for it, kept in a
directory: the package of every complete root, the package and the declaration of every
complete scheme, and the table of sites of every protocol typed (`writeBaseline`). The program
as the frontend emits it now is compared with it root by root (`compareProgram`):

- a root whose package is the same text as the baseline's, with the same tables of sites for
  its protocols, is **identical**, and nothing is run;
- otherwise the two packages are run by the core's executor under several seeds, one at a time
  while the time of the root is within a budget and at least under the boundary draws
  (`Zkc.Core.RunComparison`, `underBudget`): a function on drawn inputs, every role of a protocol on drawn
  inputs and coins, the prover and the verifier of a constructed scheme. The root is **observed
  to agree** when under every seed every role does the same things in the same order and ends
  alike, and no run reached a limit; **observed to differ** with the first seed, the inputs, the
  role and the first place that show it; and otherwise **incomplete**, with why: a run reached
  the limit, no seed was run, the root cannot be run, or the root was left out of a sample;
- a root of the baseline that the program no longer has, and one that the baseline does not
  have, are counted apart; a root or a scheme that is not complete (one that waits for a form not
  typed yet) is incomplete, with why.

**Coins by the source.** The coin of a draw or a sample is keyed by what the source says of its
site, which the table of sites gives for every site of every protocol typed: the number of its
event in the text, its part and its iteration. A site under applications is keyed by the sites
of the applications that reach it, each by its event, part and iteration, outermost first. Two
packages that number their sites differently thus get the same coin for the same event. A
draw, a sample or an application of a package whose site has no entry in the table is an
error of the comparison: the root cannot be compared, and the site is named. So is a table
that gives two sites of one protocol the same key: the two would get the same coins.

**True statements.** A protocol run on inputs drawn by type is mostly run on a false
statement, on which an honest verifier stops at its first check. A root that has a
**generator** (`Settings.generators`: the description of a protocol root and of a function root
of the same program) is run on the generator's outputs: a statement and its witness made from
freely drawn values, in the order of the protocol's inputs. Every role of the baseline must
return on them. A generator is used under a provider that computes the rows; under
uninterpreted rows no statement is true or false.

**Mutants** (`mutantScore`) measure how much the runs tell apart: the package of a root is
changed at one instruction so that the core still admits it (`Zkc.Core.Mutation`), and each
mutant is compared with the package by runs. A mutant that the runs tell apart is killed; one
that is observed to agree with the package survives. A survivor is **unreached** when the
package with a stop before the mutant's instruction is observed to agree with the package too:
no seed reaches the instruction. Any other survivor is listed **to be read**.
-/

namespace Zkc.Tools.Frontend.Differential

open Zkc.Frontend
open Zkc.Core.Concrete (Datum)

/-- A row of a table of sites: what the source says of a site of a protocol. -/
structure SiteRow where
  event : Nat
  part : String
  iteration : Array Nat
  deriving Inhabited, BEq

/-- What the frontend emits for a program: the package of every complete root by its
description, the package and the declaration of every complete scheme by its name, the table
of sites of every protocol typed by its name, and the roots and schemes that are not complete
with why. -/
structure Emission where
  roots : Array (String × Zkc.Core.Raw.Package)
  schemes : Array (String × Zkc.Core.Raw.Package × Zkc.Core.Raw.Declaration)
  sites : Array (String × Array SiteRow)
  lacking : Array (String × String)
  /-- What each definition of the program does, apart from how it is written
  (`Zkc.Core.Named.Package.digests`): each function, and each role of each protocol, by its
  name, with the hash of its digest. -/
  digests : Array (String × UInt64) := #[]
  deriving Inhabited

/-- What the definitions that the roots of a program reach do: each name with each digest that
a package gives it, once. Two definitions may have one name (a member of two modules), and one
definition is emitted in the package of every root that reaches it: a name has every digest
that some definition of that name has. -/
def digestsOf (state : Compile.State) : Array (String × UInt64) := Id.run do
  let mut seen : Std.HashSet (String × UInt64) := {}
  let mut found := #[]
  for root in Typing.functionRoots state do
    let .ok named := Typing.namedRoot state root | continue
    for (name, digest) in named.digests do
      let entry := (name, hash digest)
      if seen.contains entry then continue
      seen := seen.insert entry
      found := found.push entry
  return found

/-- The text of a package, as the frontend writes it. -/
def packageText (package : Zkc.Core.Raw.Package) : String :=
  (Zkc.Core.Raw.printPackage package).render ++ "\n"

def declarationText (declaration : Zkc.Core.Raw.Declaration) : String :=
  (Zkc.Core.Raw.printDeclaration declaration).render ++ "\n"

/-- What the frontend emits for a program of given files: names, instances, typing, packages and
schemes, the complete roots and schemes as `types --packages` writes them. An error or an
incomplete check anywhere emits nothing, with why. -/
def emit (inputs : Array SourceInput) (load : Array String → IO (Option SourceInput)) :
    IO (Except String Emission) := do
  let names := inputs.map (·.name)
  let check ← checkNames inputs load
  if let some first := check.refusals[0]? then
    return .error s!"the names are refused: {first.span.file}: {first.render}"
  let result := checkTyping (checkInstances check names) names
  let schemes := checkSchemes result
  match (schemes.session.admitRoots none).completeRoots,
      (schemes.session.admitSchemes none).completeRoots with
  | .ok (roots, lackingRoots), .ok (constructed, lackingSchemes) =>
    let mut sites : Array (String × Array SiteRow) := #[]
    let bodies := result.state.results.bodies.entries.toList.mergeSort (fun a b => a.key ≤ b.key)
    for entry in bodies do
      let .done (.protocol code) := entry.state | continue
      sites := sites.push (code.name, code.sites.map fun site =>
        { event := site.event, part := site.part, iteration := site.iteration })
    return .ok {
      roots := roots.held.map fun (description, held) => (description, held.package)
      schemes := constructed.held.map fun (name, scheme) => (name, scheme.package, scheme.declaration)
      sites
      lacking := (lackingRoots ++ lackingSchemes).map fun (name, lack) => (name, lack.describe)
      digests := digestsOf result.state }
  | .error reported, _ | _, .error reported =>
    return .error s!"nothing is emitted: {"; ".intercalate reported.toList}"

/-! ## The baseline directory -/

def manifestName : String := "manifest.json"

/-- Writes the baseline of a program into a directory: `root-<n>.json` for each root,
`scheme-<n>.json` and `scheme-<n>.declaration.json` for each scheme, `sites.json`, and
`manifest.json`, which names them: `[[description, file]…]` of the roots, `[[name, package,
declaration]…]` of the schemes, and `[[name, why]…]` of those not complete. -/
def writeBaseline (directory : System.FilePath) (emission : Emission) : IO Unit := do
  IO.FS.createDirAll directory
  let mut roots : Array Zkc.Json := #[]
  for (description, package) in emission.roots do
    let file := s!"root-{roots.size}.json"
    IO.FS.writeFile (directory / file) (packageText package)
    roots := roots.push (.arr #[.str description, .str file])
  let mut schemes : Array Zkc.Json := #[]
  for (name, package, declaration) in emission.schemes do
    let index := schemes.size
    let file := s!"scheme-{index}.json"
    let declarationFile := s!"scheme-{index}.declaration.json"
    IO.FS.writeFile (directory / file) (packageText package)
    IO.FS.writeFile (directory / declarationFile) (declarationText declaration)
    schemes := schemes.push (.arr #[.str name, .str file, .str declarationFile])
  let tables : Array Zkc.Json := emission.sites.map fun (name, rows) =>
    .arr #[.str name, .arr (rows.map fun row =>
      .arr #[.num row.event, .str row.part, .arr (row.iteration.map Zkc.Json.num)])]
  IO.FS.writeFile (directory / "sites.json") ((Zkc.Json.arr tables).render ++ "\n")
  IO.FS.writeFile (directory / "structure.json")
    ((Zkc.Json.arr (emission.digests.map fun (name, digest) =>
      .arr #[.str name, .num digest.toNat])).render ++ "\n")
  let lacking : Array Zkc.Json := emission.lacking.map fun (name, why) => .arr #[.str name, .str why]
  IO.FS.writeFile (directory / manifestName)
    ((Zkc.Json.arr #[.arr roots, .arr schemes, .arr lacking]).render ++ "\n")

/-- A program of a baseline: the texts of its packages and declarations as written, and what
they read as. -/
structure Baseline where
  roots : Array (String × String × Zkc.Core.Raw.Package)
  schemes : Array (String × String × Zkc.Core.Raw.Package × String × Zkc.Core.Raw.Declaration)
  sites : Array (String × Array SiteRow)
  lacking : Array (String × String)
  /-- What each definition did when the baseline was written; none in a baseline written
  before the digests existed. -/
  digests : Option (Array (String × UInt64)) := none

def readString : Zkc.Json → Except String String
  | .str text => .ok text
  | other => .error s!"expected a string, found {other.render}"

def readNumber : Zkc.Json → Except String Nat
  | .num value => .ok value
  | other => .error s!"expected a number, found {other.render}"

def readItems : Zkc.Json → Except String (Array Zkc.Json)
  | .arr items => .ok items
  | other => .error s!"expected an array, found {other.render}"

def readSites (text : String) : Except String (Array (String × Array SiteRow)) := do
  let tables ← readItems (← Zkc.Json.parse text)
  tables.mapM fun table => do
    let .arr #[name, rows] := table | throw "a table of sites is [name, rows]"
    let rows ← (← readItems rows).mapM fun row => do
      let .arr #[event, part, iteration] := row | throw "a row of sites is [event, part, iteration]"
      return { event := ← readNumber event, part := ← readString part
               iteration := ← (← readItems iteration).mapM readNumber : SiteRow }
    return (← readString name, rows)

/-- Reads the baseline of a program from its directory. -/
def readBaseline (directory : System.FilePath) : IO (Except String Baseline) := do
  let manifestPath := directory / manifestName
  unless ← manifestPath.pathExists do return .error s!"{directory} has no {manifestName}"
  let manifest ← IO.FS.readFile manifestPath
  let parts ← match Zkc.Json.parse manifest with
    | .ok (.arr #[.arr roots, .arr schemes, .arr lacking]) => pure (roots, schemes, lacking)
    | _ => return .error s!"{manifestPath} is not a manifest"
  let (rootEntries, schemeEntries, lackingEntries) := parts
  let mut roots := #[]
  for entry in rootEntries do
    let .arr #[.str description, .str file] := entry | return .error s!"{manifestPath}: a root is [description, file]"
    let text ← IO.FS.readFile (directory / file)
    match Zkc.Core.Raw.parsePackage text with
    | .ok package => roots := roots.push (description, text, package)
    | .error message => return .error s!"{directory / file}: {message}"
  let mut schemes := #[]
  for entry in schemeEntries do
    let .arr #[.str name, .str file, .str declarationFile] := entry
      | return .error s!"{manifestPath}: a scheme is [name, package, declaration]"
    let text ← IO.FS.readFile (directory / file)
    let declarationText ← IO.FS.readFile (directory / declarationFile)
    match Zkc.Core.Raw.parsePackage text, Zkc.Core.Raw.parseDeclaration declarationText with
    | .ok package, .ok declaration =>
      schemes := schemes.push (name, text, package, declarationText, declaration)
    | .error message, _ | _, .error message => return .error s!"{directory}: scheme {name}: {message}"
  let sites ← match readSites (← IO.FS.readFile (directory / "sites.json")) with
    | .ok sites => pure sites
    | .error message => return .error s!"{directory / "sites.json"}: {message}"
  let lacking := lackingEntries.filterMap fun
    | .arr #[.str name, .str why] => some (name, why)
    | _ => none
  let structurePath := directory / "structure.json"
  let digests ← if ← structurePath.pathExists then
      match Zkc.Json.parse (← IO.FS.readFile structurePath) with
      | .ok (.arr entries) => pure (some (entries.filterMap fun
          | .arr #[.str name, .num digest] => some (name, digest.toUInt64)
          | _ => none))
      | _ => return .error s!"{structurePath} is not a list of digests"
    else pure none
  return .ok { roots, schemes, sites, lacking, digests }

/-- The definitions that do something else than in the baseline: a function, or a role of a
protocol, whose digest changed or that is no longer there. -/
def digestChanges (baseline : Baseline) (current : Emission) : Array String :=
  match baseline.digests with
  | none => #[]
  | some before => before.filterMap fun (name, digest) =>
    if current.digests.contains (name, digest) then none
    else if current.digests.any (·.1 == name) then
      some s!"`{name}` does something else than in the baseline"
    else some s!"`{name}` is in the baseline and is not emitted now"

/-! ## Coins keyed by the source -/

/-- A number for the name of a part: its characters as digits in base 257, modulo 2^61. -/
def partNumber (part : String) : Nat :=
  part.foldl (init := 0) fun acc char => (acc * 257 + char.toNat + 1) % 2 ^ 61

/-- The key of one site in its table: its event, its part, and its iteration. -/
def SiteRow.key (row : SiteRow) : List Nat :=
  [row.event, partNumber row.part, row.iteration.size] ++ row.iteration.toList

mutual
  /-- The applications of a protocol region: the site of each and its callee. -/
  partial def applications : Zkc.Core.Raw.ProtocolRegion → List (Nat × Nat)
    | .ret _ | .stop _ => []
    | .step instruction next => applicationsOf instruction ++ applications next
    | .block _ body next => applications body ++ applications next

  partial def applicationsOf : Zkc.Core.Raw.ProtocolStep → List (Nat × Nat)
    | .apply callee _ site _ => [(site, callee)]
    | .«repeat» _ _ _ _ _ body => applications body
    | .choose _ _ _ _ _ arms => arms.toList.flatMap applications
    | _ => []
end

mutual
  /-- The sites of a protocol region at which a coin is given or an application is made. -/
  partial def keyedSites : Zkc.Core.Raw.ProtocolRegion → List Nat
    | .ret _ | .stop _ => []
    | .step instruction next => keyedSitesOf instruction ++ keyedSites next
    | .block _ body next => keyedSites body ++ keyedSites next

  partial def keyedSitesOf : Zkc.Core.Raw.ProtocolStep → List Nat
    | .draw _ _ site _ _ | .sample _ site _ _ | .apply _ _ site _ => [site]
    | .«repeat» _ _ _ _ _ body => keyedSites body
    | .choose _ _ _ _ _ arms => arms.toList.flatMap keyedSites
    | _ => []
end

/-- The table of sites of each protocol of a package, by the package's names of its protocols. -/
def tablesOf (package : Zkc.Core.Raw.Package) (sites : Array (String × Array SiteRow)) :
    Array (Option (Array SiteRow)) :=
  let names := (package.names.map (·.protocols)).getD []
  (List.range package.protocols.length).toArray.map fun definition =>
    (names[definition]?).bind fun name => (sites.find? (·.1 == name)).map (·.2)

/-- The sites of a package at which a coin is given or an application is made that have no
entry in its tables of sites, each named. -/
def unkeyed (package : Zkc.Core.Raw.Package) (sites : Array (String × Array SiteRow)) :
    Array String := Id.run do
  let tables := tablesOf package sites
  let names := (package.names.map (·.protocols)).getD []
  let mut found := #[]
  for definition in [0:package.protocols.length] do
    let some protocol := package.protocols[definition]? | continue
    for site in keyedSites protocol.body do
      let known := (tables[definition]?).any fun table => (table.bind (·[site]?)).isSome
      unless known do
        found := found.push s!"site {site} of {(names[definition]?).getD s!"protocol {definition}"}"
  return found

/-- A key that the table of sites of a protocol of a package gives to two of its sites, named
with the protocol and the two sites. -/
def duplicateKey? (package : Zkc.Core.Raw.Package) (sites : Array (String × Array SiteRow)) :
    Option String := Id.run do
  let tables := tablesOf package sites
  let names := (package.names.map (·.protocols)).getD []
  for definition in [0:package.protocols.length] do
    let some (some table) := tables[definition]? | continue
    let mut seen : Std.HashMap (List Nat) Nat := {}
    for site in [0:table.size] do
      let key := table[site]!.key
      match seen[key]? with
      | some earlier =>
        return some s!"the table of sites of {(names[definition]?).getD s!"protocol {definition}"} gives the sites {earlier} and {site} one key"
      | none => seen := seen.insert key site
  return none

/-- Whether two tables of sites give the protocols of a package the same rows. -/
def sameTables (package : Zkc.Core.Raw.Package) (first second : Array (String × Array SiteRow)) :
    Bool :=
  tablesOf package first == tablesOf package second

/-- The key of a site of a run of a package: the keys of the sites of the applications that
reach it, from the newest protocol, and its own. -/
def keyOf (package : Zkc.Core.Raw.Package) (sites : Array (String × Array SiteRow)) :
    Zkc.Core.Site → Option (List Nat) :=
  let tables := tablesOf package sites
  let calls : Array (List (Nat × Nat)) :=
    package.protocols.toArray.map fun protocol => applications protocol.body
  let rowOf (definition site : Nat) : Option SiteRow :=
    ((tables[definition]?).bind id).bind (·[site]?)
  fun site =>
    let rec walk : Nat → List Nat → Option (List Nat)
      | definition, [] =>
        if definition == site.definition then (rowOf definition site.number).map SiteRow.key
        else none
      | definition, application :: rest => do
        let row ← rowOf definition application
        let callee ← ((calls[definition]?).getD []).lookup application
        return row.key ++ (← walk callee rest)
    (walk (package.protocols.length - 1) site.path).map fun key => (site.path.length + 1) :: key

/-! ## Comparing a program with its baseline -/

/-- Why the comparison of a root or a scheme is incomplete. -/
inductive Incomplete where
  /-- A run reached the limit under a seed, and no seed showed a difference. -/
  | limit (seed elements : Nat)
  | noSeed
  | cannotRun (reason : String)
  /-- Of a different text, and not run: a root left out of a sample. -/
  | sampledOut (spacing : Nat) (protocol : Bool)

def Incomplete.ofCore : Zkc.Core.RunComparison.Incomplete → Incomplete
  | .limit seed elements => .limit seed elements
  | .noSeed => .noSeed
  | .cannotRun reason => .cannotRun reason

def Incomplete.describe : Incomplete → String
  | .limit seed elements => s!"a run reached the limit of {elements} elements under seed {seed}"
  | .noSeed => "no seed was run"
  | .cannotRun reason => s!"cannot be run: {reason}"
  | .sampledOut spacing protocol =>
    s!"not run: one {if protocol then "protocol" else "function"} root in {spacing} is run"

/-- What became of a root or a scheme in a comparison. -/
inductive Found where
  | identical
  /-- Observed to agree under this many seeds. -/
  | agree (seeds : Nat)
  /-- Observed to differ: the seed, the inputs, the role when the root is a protocol or a
  scheme, and the first place where the two differ, in the baseline and now. -/
  | differ (seed : Nat) (inputs : List Datum) (role : Option Nat) (baseline current : String)
  | incomplete (why : Incomplete)
  /-- In the program and not in the baseline. -/
  | added
  /-- In the baseline and no longer complete in the program. -/
  | missing (why : String)

def Found.ofVerdict : Zkc.Core.RunComparison.Verdict → Found
  | .agree seeds => .agree seeds
  | .differ seed inputs role left right => .differ seed inputs role left right
  | .incomplete why => .incomplete (.ofCore why)

def Found.describe : Found → String
  | .identical => "identical"
  | .agree seeds => s!"observed to agree under {seeds} seeds"
  | .differ seed inputs role baseline current =>
    let place := match role with
      | some role => s!", role {role}"
      | none => ""
    let draw := if seed < Zkc.Core.ValidData.boundaryDraws then " (a boundary draw)" else ""
    s!"observed to differ under seed {seed}{draw}, inputs {Zkc.Core.RunComparison.dataText inputs}{place}: the baseline {baseline}; now {current}"
  | .incomplete why => s!"incomplete: {why.describe}"
  | .added => "not in the baseline"
  | .missing why => s!"in the baseline and not complete now: {why}"

/-- What the comparison of a program found, root by root and scheme by scheme. -/
structure Comparison where
  program : String
  found : Array (String × Found)
  deriving Inhabited

/-- How a comparison runs: the provider of the runs, the seeds, and whether a package of the
same text is still run. -/
structure Settings where
  /-- What the packages are run under: the model of the vocabulary's rows, or the provider of
  uninterpreted rows (`Zkc.Core.UninterpretedRows`). -/
  provider : Zkc.Core.RunComparison.Provider := Zkc.Core.RunComparison.arithmetic
  seeds : List Nat := List.range 16
  byRunsOnly : Bool := false
  /-- A root is run under its seeds one at a time, while the time spent on it is within this many
  milliseconds, and under at least the first `minimumSeeds` (the boundary draws) whatever the
  time: a run of a protocol over points of G1 takes seconds. -/
  budget : Nat := 2000
  minimumSeeds : Nat := 3
  /-- One function root in this many of a program, and one protocol root in that many, is run
  when its text differs; the others are counted as sampled out. -/
  functionSpacing : Nat := 1
  protocolSpacing : Nat := 1
  /-- The generators of true statements: the description of a protocol root, and of the function
  root of the program whose outputs are its statement and witness. -/
  generators : Array (String × String) := #[]

/-- One side of the comparison of a protocol root. -/
def side (package : Zkc.Core.Raw.Package) (sites : Array (String × Array SiteRow)) :
    Except String Zkc.Core.RunComparison.Side :=
  match Zkc.Core.elaborate package with
  | .ok typed => .ok { package, typed, key := keyOf package sites }
  | .error refusal => .error s!"the core refuses the package: {reprStr refusal}"

/-- Two packages of a root compared by runs: a function root by its last function, a protocol
root by its newest protocol, after the check that every site that needs a key has one. With a
generator, the protocol is run on its statements. -/
def compareRoot (settings : Settings) (baseline current : Zkc.Core.Raw.Package)
    (baselineSites currentSites : Array (String × Array SiteRow))
    (generator : Option Zkc.Core.Raw.Package := none) : Found :=
  if baseline.protocols.isEmpty && current.protocols.isEmpty then
    .ofVerdict (Zkc.Core.RunComparison.compareFunctions settings.provider baseline current
      settings.seeds)
  else
    match (unkeyed baseline baselineSites ++ unkeyed current currentSites)[0]?,
        (duplicateKey? baseline baselineSites).or (duplicateKey? current currentSites) with
    | some site, _ => .incomplete (.cannotRun s!"{site} has no entry in the table of sites")
    | none, some twice => .incomplete (.cannotRun twice)
    | none, none =>
      -- a statement is true only under a provider that computes the rows
      let statements : Except String (Option (Nat → Except String (List Datum))) :=
        match if settings.provider.computes then generator else none with
        | none => .ok none
        | some generator =>
          (Zkc.Core.RunComparison.statementsOf settings.provider generator baseline).map some
      match side baseline baselineSites, side current currentSites, statements with
      | .ok left, .ok right, .ok statements =>
        .ofVerdict (Zkc.Core.RunComparison.compareProtocols settings.provider left right
          settings.seeds (statements := statements))
      | .error reason, _, _ | _, .error reason, _ | _, _, .error reason =>
        .incomplete (.cannotRun reason)

/-- One side of the comparison of a scheme: its package and declaration as the core elaborates
and constructs them. -/
def schemeSide (package : Zkc.Core.Raw.Package) (declaration : Zkc.Core.Raw.Declaration)
    (sites : Array (String × Array SiteRow)) : Except String Zkc.Core.RunComparison.SchemeSide := do
  let typed ← match Zkc.Core.elaborateWritten package with
    | .ok typed => pure typed
    | .error refusal => throw s!"the core refuses the package: {reprStr refusal}"
  let stepped ← match Zkc.Core.construct typed declaration with
    | .ok stepped => pure stepped
    | .error refusal => throw s!"the core's construction refuses the scheme: {reprStr refusal}"
  return { package, typed, stepped, prover := declaration.prover, verifier := declaration.verifier
           key := keyOf package sites }

/-- The proof identity that a declaration carries, when its suite carries one. -/
def identityOf? (declaration : Zkc.Core.Raw.Declaration) : Option (List Nat) :=
  match declaration.suite with
  | some (.catalogue _ _ _ _ _ identity) => some identity
  | _ => none

/-- The proof identity is a digest of the text of the package, and every challenge of the
constructed scheme depends on it. So two emissions of one scheme whose texts differ give
different proofs by construction, and nothing is learnt from that. The scheme now is run under
the identity of the baseline: the two then differ only when the programs do. -/
def compareScheme (settings : Settings) (baseline : Zkc.Core.Raw.Package × Zkc.Core.Raw.Declaration)
    (current : Zkc.Core.Raw.Package × Zkc.Core.Raw.Declaration)
    (baselineSites currentSites : Array (String × Array SiteRow)) : Found :=
  let current := match identityOf? baseline.2 with
    | some identity => (current.1, current.2.withIdentity identity)
    | none => current
  match (unkeyed baseline.1 baselineSites ++ unkeyed current.1 currentSites)[0]?,
      (duplicateKey? baseline.1 baselineSites).or (duplicateKey? current.1 currentSites) with
  | some site, _ => .incomplete (.cannotRun s!"{site} has no entry in the table of sites")
  | none, some twice => .incomplete (.cannotRun twice)
  | none, none =>
    match schemeSide baseline.1 baseline.2 baselineSites, schemeSide current.1 current.2 currentSites with
    | .ok left, .ok right =>
      .ofVerdict (Zkc.Core.RunComparison.compareSchemes settings.provider left right settings.seeds)
    | .error reason, _ | _, .error reason => .incomplete (.cannotRun reason)

/-- A comparison under the seeds one at a time: every seed while the time spent is within the
budget, and at least the first `minimumSeeds`. The first seed that shows a difference ends it,
and so does a root that cannot be run. A run that reaches the limit under a seed does not: a
later seed may show a difference, and when none does the comparison is incomplete. So is one
in which no seed was run. -/
def underBudget (settings : Settings) (compareSeeds : List Nat → Found) : IO Found := do
  let start ← IO.monoMsNow
  let mut count := 0
  let mut tried := 0
  let mut reached : Option Incomplete := none
  for seed in settings.seeds do
    if tried ≥ settings.minimumSeeds && (← IO.monoMsNow) - start > settings.budget then break
    tried := tried + 1
    match compareSeeds [seed] with
    | .agree _ => count := count + 1
    | .incomplete (.limit seed elements) => reached := reached.or (some (.limit seed elements))
    | other => return other
  return match reached with
    | some why => .incomplete why
    | none => if count == 0 then .incomplete .noSeed else .agree count

/-- The seeds for runs on true statements: the draws taken from the stream first, then the mixed
draws, then the boundary draws. Under a boundary draw every coin of a run is the same boundary
value, and a protocol is degenerate there: with a challenge of zero Schnorr's verifier accepts
every response. Such draws are run last, so that a root whose runs are long is run under
draws that tell. -/
def statementSeeds (seeds : List Nat) : List Nat :=
  let boundary := Zkc.Core.ValidData.boundaryDraws
  let mixed := boundary + Zkc.Core.ValidData.mixedDraws
  seeds.filter (mixed ≤ ·) ++ seeds.filter (fun seed => boundary ≤ seed && seed < mixed) ++
    seeds.filter (· < boundary)

/-- The package of the generator of a root among the roots of an emission, when the settings
name one for it. -/
def generatorOf (settings : Settings) (roots : Array (String × Zkc.Core.Raw.Package))
    (description : String) : Option Zkc.Core.Raw.Package := do
  let (_, generator) ← settings.generators.find? (·.1 == description)
  (roots.find? (·.1 == generator)).map (·.2)

/-- A program compared with its baseline, root by root and scheme by scheme. -/
def compareProgram (settings : Settings) (program : String) (baseline : Baseline)
    (current : Emission) : IO Comparison := do
  let mut found := #[]
  let mut protocolRoots := 0
  let mut functionRoots := 0
  for (description, package) in current.roots do
    match baseline.roots.find? (·.1 == description) with
    | none => found := found.push (description, .added)
    | some (_, text, old) =>
      let protocol := !package.protocols.isEmpty
      let (spacing, counted) := if protocol then (settings.protocolSpacing, protocolRoots)
        else (settings.functionSpacing, functionRoots)
      if !settings.byRunsOnly && text == packageText package &&
          sameTables package baseline.sites current.sites then
        found := found.push (description, .identical)
      else if counted % spacing != 0 then
        found := found.push (description, .incomplete (.sampledOut spacing protocol))
      else
        let generator := generatorOf settings current.roots description
        let ordered := if generator.isSome && settings.provider.computes then
          { settings with seeds := statementSeeds settings.seeds } else settings
        let result ← underBudget ordered fun seeds =>
          compareRoot { settings with seeds } old package baseline.sites current.sites generator
        found := found.push (description, result)
      if protocol then protocolRoots := protocolRoots + 1 else functionRoots := functionRoots + 1
  for (description, _, _) in baseline.roots do
    unless current.roots.any (·.1 == description) do
      let why := ((current.lacking.find? (·.1 == description)).map (·.2)).getD "no such root"
      found := found.push (description, .missing why)
  for (name, package, declaration) in current.schemes do
    let label := s!"scheme {name}"
    match baseline.schemes.find? (·.1 == name) with
    | none => found := found.push (label, .added)
    | some (_, text, oldPackage, oldDeclarationText, oldDeclaration) =>
      if !settings.byRunsOnly && text == packageText package &&
          oldDeclarationText == declarationText declaration &&
          sameTables package baseline.sites current.sites then
        found := found.push (label, .identical)
      else
        let result ← underBudget settings fun seeds =>
          compareScheme { settings with seeds } (oldPackage, oldDeclaration) (package, declaration)
            baseline.sites current.sites
        found := found.push (label, result)
  for (name, _, _, _, _) in baseline.schemes do
    unless current.schemes.any (·.1 == name) do
      let why := ((current.lacking.find? (·.1 == name)).map (·.2)).getD "no such scheme"
      found := found.push (s!"scheme {name}", .missing why)
  -- a root or a scheme that is not complete, now and in the baseline, cannot be run
  for (name, why) in current.lacking do
    unless baseline.roots.any (·.1 == name) || baseline.schemes.any (·.1 == name) do
      found := found.push (name, .incomplete (.cannotRun s!"not complete: {why}"))
  return { program, found }

/-! ## Mutants -/

/-- The mutant score of a root: its mutants that the runs tell apart, those that survive, and
those whose comparison is incomplete, each with its description. -/
structure Score where
  killed : Nat := 0
  /-- Mutants observed to agree with their package under every seed tried, whose instruction
  the runs reach, or are not known not to reach: to be read. -/
  survivors : Array String := #[]
  /-- Mutants observed to agree with their package whose instruction no seed reaches. -/
  unreached : Array String := #[]
  /-- Mutants whose comparison with their package is incomplete, with why. -/
  incomplete : Array (String × String) := #[]
  /-- Roots whose packages are not run, so that no mutant of them is made: a run too long, or a
  row that the model does not compute. -/
  skipped : Nat := 0
  /-- Mutants not compared, because the time of their root ran out. -/
  late : Nat := 0
  /-- Of the mutants told apart, those first told apart under a boundary draw: the inputs and
  the coins are then zeros, ones and largest values, on which a statement may be degenerate. -/
  atBoundary : Nat := 0
  deriving Inhabited

def Score.total (score : Score) : Nat :=
  score.killed + score.survivors.size + score.unreached.size + score.incomplete.size

def Score.add (first second : Score) : Score :=
  { killed := first.killed + second.killed, survivors := first.survivors ++ second.survivors
    unreached := first.unreached ++ second.unreached
    incomplete := first.incomplete ++ second.incomplete, skipped := first.skipped + second.skipped
    late := first.late + second.late, atBoundary := first.atBoundary + second.atBoundary }

/-- The score as a line. -/
def Score.describe (score : Score) : String :=
  s!"{score.total}, of which {score.killed} told apart ({score.atBoundary} first under a boundary draw), {score.survivors.size} survive to be read, {score.unreached.size} survive unreached, {score.incomplete.size} incomplete; {score.skipped} roots not run, without mutants; {score.late} not compared in the time of their root"

/-- The mutants of the package of a root, at most `candidates` of its changes of the first three
kinds and as many of the fourth before admission, each compared with the package by runs under
the budget of the settings. A survivor is unreached when the probe of its instruction is
observed to agree with the package too. A package whose run
would be too long, or that applies a row the model does not compute, gets no mutant; the mutants
of a root after `rootBudget` milliseconds are not compared, and are counted. -/
def mutantScore (settings : Settings) (label : String) (package : Zkc.Core.Raw.Package)
    (sites : Array (String × Array SiteRow)) (candidates rootBudget : Nat)
    (generator : Option Zkc.Core.Raw.Package := none) : IO Score := do
  let mut score : Score := {}
  if (Zkc.Core.RunComparison.tooLarge? package).isSome ||
      (settings.provider.refuses package).isSome then
    return { score with skipped := 1 }
  let settings := if generator.isSome && settings.provider.computes then
    { settings with seeds := statementSeeds settings.seeds } else settings
  let start ← IO.monoMsNow
  -- the probes of the package, made when a mutant first survives; and what each place is known
  -- to be: reached or not
  let mut probes : Option (List Zkc.Core.Mutation.Mutant) := none
  let mut reached : Std.HashMap String Bool := {}
  for mutant in Zkc.Core.Mutation.mutants package candidates ++
      Zkc.Core.Mutation.replacements package candidates do
    if (← IO.monoMsNow) - start > rootBudget then
      score := { score with late := score.late + 1 }
      continue
    let name := s!"{label}: {mutant.description}"
    let found ← underBudget settings fun seeds =>
      compareRoot { settings with seeds } package mutant.package sites sites generator
    match found with
    | .differ seed .. =>
      score := { score with killed := score.killed + 1
                            atBoundary := score.atBoundary +
                              (if seed < Zkc.Core.ValidData.boundaryDraws then 1 else 0) }
    | .agree _ =>
      -- whether a seed reaches the instruction: the package with a stop before it
      let known ← match reached[mutant.place]? with
        | some known => pure known
        | none =>
          let made := probes.getD (Zkc.Core.Mutation.probes package)
          probes := some made
          let known ← match made.find? (·.place == mutant.place) with
            | none => pure true
            | some probe =>
              let found ← underBudget settings fun seeds =>
                compareRoot { settings with seeds } package probe.package sites sites generator
              pure !(found matches .agree _)
          reached := reached.insert mutant.place known
          pure known
      score := if known then { score with survivors := score.survivors.push name }
        else { score with unreached := score.unreached.push name }
    | .incomplete why => score := { score with incomplete := score.incomplete.push (name, why.describe) }
    | _ => pure ()
  return score

/-- The time given to the mutants of one root, in milliseconds: fifteen times the time of the
seeds of one root, thirty seconds by default. -/
def mutantRootBudget (settings : Settings) : Nat := 15 * settings.budget

/-! ## The command -/

/-- The counts of a list of comparisons, as a line: the three verdicts counted apart, and the
incomplete roots by why. -/
def tally (comparisons : Array Comparison) : String := Id.run do
  let mut identical := 0
  let mut agree := 0
  let mut differ := 0
  let mut limit := 0
  let mut noSeed := 0
  let mut cannotRun := 0
  let mut sampledOut := 0
  let mut added := 0
  let mut missing := 0
  for comparison in comparisons do
    for (_, found) in comparison.found do
      match found with
      | .identical => identical := identical + 1
      | .agree _ => agree := agree + 1
      | .differ .. => differ := differ + 1
      | .incomplete (.limit ..) => limit := limit + 1
      | .incomplete .noSeed => noSeed := noSeed + 1
      | .incomplete (.cannotRun _) => cannotRun := cannotRun + 1
      | .incomplete (.sampledOut ..) => sampledOut := sampledOut + 1
      | .added => added := added + 1
      | .missing _ => missing := missing + 1
  let incomplete := limit + noSeed + cannotRun + sampledOut
  return s!"{identical} identical, {agree} observed to agree, {differ} observed to differ, {incomplete} incomplete ({cannotRun} cannot be run, {limit} reached a limit, {noSeed} without a seed, {sampledOut} sampled out), {added} not in the baseline, {missing} missing"

/-- Whether a comparison found a root that differs, or one that is missing. -/
def Comparison.failed (comparison : Comparison) : Bool :=
  comparison.found.any fun (_, found) => found matches .differ .. | .missing _

/-- `compare [--library <dir>]… --baseline <dir> [--write] [--seeds <n>] [--budget <ms>] [--runs]
[--uninterpreted] [--generator <root>=<function root>]… [--mutants <n>] <files>…`: with `--write`, writes the baseline of the program of the files into
the directory; otherwise compares what the frontend emits for them with the baseline there,
root by root and scheme by scheme, printing one line each and the counts. `--seeds n` runs
under the seeds `0` to `n - 1` (sixteen by default: three boundary draws, eleven mixed draws
and two drawn from the seed), one at a time within the budget of a root (`underBudget`, two
seconds by default, `--budget ms`); `--runs` runs the packages also when their text is
identical; `--uninterpreted` runs them under the provider of uninterpreted rows, which runs every
row and compares terms; `--generator` runs a protocol root on the true statements that a function
root of the program gives; `--mutants n` also gives the mutant score of the roots of the baseline, at most `n`
changes of each before admission and fifteen budgets of time for the mutants of a root, and
lists the survivors. The counts name the three verdicts apart, and the incomplete roots by why.
The exit code is 1 when a root or a scheme is observed to differ or is missing. -/
def compare (options : Names.Options) : IO UInt32 := do
  let some directory := options.baseline | do IO.eprintln "compare needs --baseline"; return 2
  let inputs ← options.files.mapM Names.readInput
  let emission ← match ← emit inputs (Names.libraryLoader options.libraries) with
    | .ok emission => pure emission
    | .error message => do IO.println message; return 1
  if options.write then
    writeBaseline directory emission
    IO.println s!"written: {emission.roots.size} roots, {emission.schemes.size} schemes, {emission.lacking.size} not complete"
    return 0
  let baseline ← match ← readBaseline directory with
    | .ok baseline => pure baseline
    | .error message => do IO.println message; return 1
  let defaults : Settings := {}
  let settings : Settings := { seeds := List.range options.seeds, byRunsOnly := options.runs
                               budget := options.budget.getD defaults.budget
                               provider := if options.uninterpreted then
                                 Zkc.Core.UninterpretedRows.provider else defaults.provider
                               generators := options.generators }
  let comparison ← compareProgram settings directory.toString baseline emission
  for (name, found) in comparison.found do
    IO.println s!"{name}: {found.describe}"
  IO.println (tally #[comparison])
  if let some candidates := options.mutants then
    let mut score : Score := {}
    for (description, _, package) in baseline.roots do
      score := score.add (← mutantScore settings description package baseline.sites candidates
        (mutantRootBudget settings)
        (generatorOf settings (baseline.roots.map fun (name, _, package) => (name, package))
          description))
    IO.println s!"mutants: {score.describe}"
    for survivor in score.survivors do IO.println s!"  survives, to be read: {survivor}"
    for survivor in score.unreached do IO.println s!"  survives, unreached: {survivor}"
    for (mutant, reason) in score.incomplete do IO.println s!"  incomplete: {mutant}: {reason}"
  return if comparison.failed then 1 else 0

end Zkc.Tools.Frontend.Differential
