import Zkc.Core.VocabularyObserved

/-!
# Runs of an emitted package, for the second reading

What the second reading of a typed tree (`Zkc.Tools.Frontend.Reading`) is compared with: every
role of the newest protocol of the package that the frontend emits for a root, run by the core's
executor under the model of the vocabulary's rows, with what each role did
(`Zkc.Core.Observed`).

- **Keys.** The coin of a draw or a sample is given by the key of its site in the source: the
  number of its event in the text, its part and its iteration, from the table of sites that the
  frontend keeps for each protocol, after the keys of the applications that reach the site,
  outermost first (`keyOf`). The reading keys its coins alike, so the run and the reading get
  the same coin for the same event however the package numbers its sites. A site without a key
  gets no coin, and the run fails there. A table that gives two sites of one protocol the same
  key is refused (`duplicateKey?`): the two would get the same coins.
- **Data.** One value per input of the protocol under a seed (`inputs`), the inputs of one port
  held by several roles alike (`agreed`), and the coins (`coin`): values by type made of
  numbers of the seed, and of the key and the count for a coin. A leaf that has a law is the
  value of its law (`Vocabulary.lawValue`), a point of G1 with a scalar below `pointScalars`; a
  `nat` is below 1024, a collection without a size has fewer than four elements, and a variant
  takes an alternative by a number.
- **What is compared.** For each role, what it did in the order in which it did so (what it
  sent, received and heard, what it drew and sampled), each by its kind, the key of its site
  and its value, and how it ended (`compareShown`). What two different roles did is not ordered
  against each other.
- **Size.** A root whose run would be too long for a run of the corpus (`tooLarge?`) is not
  run, with the estimate.

**Three verdicts** over seeds (`overSeeds`). The two are *observed to agree* when, under every
seed, every role shows the same and no run reached a limit. They are *observed to differ* when
under some seed a role does not show the same: with the seed, the inputs, the role and the first
place where the two differ. Otherwise the comparison is *incomplete*: a run reached the limit,
no seed was run, or a run failed otherwise (the model does not compute a row, an input is not a
value, a site has no coin), which is no end to compare by.
-/

set_option autoImplicit false

namespace Zkc.Tools.Frontend.PackageRuns

open Zkc.Core
open Zkc.Core.Concrete (Datum)

/-! ## What a role shows -/

/-- The message with which the executor ends a role that waits for a message that is never
sent. -/
def waitingMessage : String := "waits for a message that is never sent"

/-- A datum as text: a number, or its items in brackets. -/
partial def datumText : Datum → String
  | .number value => toString value
  | .sequence items => "[" ++ ", ".intercalate (items.map datumText) ++ "]"

def stopText : PIR.Stop → String
  | .reject => "reject" | .abort => "abort" | .exhausted => "exhausted"
  | .incomplete => "incomplete" | .refused => "refused" | .undefined => "undefined"

/-- An outcome of a role, as a line. -/
def describe : Execute.Outcome (List Datum) → String
  | .returned outputs => s!"returned {datumText (.sequence outputs)}"
  | .stopped reason => s!"stopped {stopText reason}"
  | .limit elements => s!"reached the limit of {elements} elements"
  | .failed message => s!"failed: {message}"

/-- What one role of a run shows: what it did, each with the key of its site in the source,
and how it ended. -/
structure Shown where
  did : List (Execute.Event.Kind × Option (List Nat) × Datum)
  ended : Execute.Outcome (List Datum)

/-- What the runs of one seed show. -/
inductive Seen where
  | agree
  /-- A role does not show the same in the two. The first place where the two differ, each as
  a line. -/
  | differ (role : Option Nat) (left right : String)
  /-- A run reached the limit. -/
  | limit (elements : Nat)
  /-- A run did not come to an end by which the two are compared. -/
  | broken (reason : String)

/-- Why a comparison is incomplete. -/
inductive Incomplete where
  /-- A run reached the limit under a seed, and no seed showed a difference. -/
  | limit (seed elements : Nat)
  | noSeed
  | cannotRun (reason : String)

def Incomplete.describe : Incomplete → String
  | .limit seed elements => s!"a run reached the limit of {elements} elements under seed {seed}"
  | .noSeed => "no seed was run"
  | .cannotRun reason => s!"cannot be run: {reason}"

/-- The verdict of a comparison over seeds. -/
inductive Verdict where
  /-- Under every one of this many seeds every role shows the same, and no run reached a
  limit. -/
  | agree (seeds : Nat)
  /-- The first seed under which a role does not show the same, with its inputs. -/
  | differ (seed : Nat) (inputs : List Datum) (role : Option Nat) (left right : String)
  | incomplete (why : Incomplete)

/-- Why a role's run is no end to compare by: a failure other than waiting for a message. -/
def broken? : Execute.Outcome (List Datum) → Option String
  | .failed message => if message == waitingMessage then none else some message
  | _ => none

/-- The limit that a role reached. -/
def limit? : Execute.Outcome (List Datum) → Option Nat
  | .limit elements => some elements
  | _ => none

/-- Two ends of one role are the same end. A limit is no end. -/
def sameEnd : Execute.Outcome (List Datum) → Execute.Outcome (List Datum) → Bool
  | .returned left, .returned right => left == right
  | .stopped left, .stopped right => left == right
  | .failed left, .failed right => left == right
  | _, _ => false

/-- One thing that a role did, as a line. -/
def describeDid (step : Execute.Event.Kind × Option (List Nat) × Datum) : String :=
  let key := match step.2.1 with
    | some key => s!"the site of key {key}"
    | none => "a site without a key"
  s!"{step.1.describe} {datumText step.2.2} at {key}"

/-- The first position at which what a role did in the two runs differs, each side as a line.
With `both`, only a position that both runs have: a run that was cut short shows fewer
things, which is no difference. -/
def firstDifference (both : Bool) :
    Nat → List (Execute.Event.Kind × Option (List Nat) × Datum) →
      List (Execute.Event.Kind × Option (List Nat) × Datum) → Option (String × String)
  | _, [], [] => none
  | position, first :: rest, second :: others =>
    if first.1 == second.1 && first.2.1 == second.2.1 && first.2.2 == second.2.2 then
      firstDifference both (position + 1) rest others
    else some (s!"event {position}: {describeDid first}", s!"event {position}: {describeDid second}")
  | position, first :: _, [] =>
    if both then none else some (s!"event {position}: {describeDid first}", s!"no event {position}")
  | position, [], second :: _ =>
    if both then none else some (s!"no event {position}", s!"event {position}: {describeDid second}")

/-- What the roles of two runs show, compared role by role. A difference at a position that
both runs have is a difference whatever became of the runs. Otherwise a run that failed, or
that reached the limit, is no run to compare; and otherwise the roles show the same when each
did the same things in the same order and ended alike. -/
def compareShown (left right : List Shown) : Seen :=
  let roles := (List.range (max left.length right.length)).filterMap fun role =>
    match left[role]?, right[role]? with
    | some first, some second => some (role, first, second)
    | _, _ => none
  match roles.findSome? fun (role, first, second) =>
      (firstDifference true 0 first.did second.did).map fun (a, b) => (role, a, b) with
  | some (role, first, second) => .differ (some role) first second
  | none =>
    let ends := (left ++ right).map (·.ended)
    match ends.findSome? broken?, ends.findSome? limit? with
    | some reason, _ => .broken reason
    | none, some elements => .limit elements
    | none, none =>
      if left.length != right.length then
        .differ none s!"{left.length} roles" s!"{right.length} roles"
      else
        match roles.findSome? fun (role, first, second) =>
            match firstDifference false 0 first.did second.did with
            | some (a, b) => some (role, a, b)
            | none =>
              if sameEnd first.ended second.ended then none
              else some (role, describe first.ended, describe second.ended) with
        | some (role, first, second) => .differ (some role) first second
        | none => .agree

/-- The verdict over seeds of a comparison under each seed: the inputs it drew and what it saw,
or why it drew none. The first difference ends it, and so does a run that fails. A run that
reaches the limit under a seed does not end it: a later seed may show a difference; when none
does, the comparison is incomplete. -/
def overSeeds (seeds : List Nat) (underSeed : Nat → Except String (List Datum × Seen)) : Verdict :=
  go seeds 0 none
where
  go : List Nat → Nat → Option Incomplete → Verdict
    | [], count, reached =>
      match reached with
      | some why => .incomplete why
      | none => if count == 0 then .incomplete .noSeed else .agree count
    | seed :: rest, count, reached =>
      match underSeed seed with
      | .error reason => .incomplete (.cannotRun reason)
      | .ok (_, .broken reason) => .incomplete (.cannotRun reason)
      | .ok (inputs, .differ role left right) => .differ seed inputs role left right
      | .ok (_, .limit elements) => go rest count (reached.or (some (.limit seed elements)))
      | .ok (_, .agree) => go rest (count + 1) reached

/-! ## The size of a run

A root whose run would be too long for a run of the corpus is not run: one whose estimated
number of operations, every loop at its count (a run-time count at its maximum, or 1024 without
one) and every call at its callee's, is above `workBound`, or whose inputs or outputs hold more
than `dataBound` numbers. -/

def workBound : Nat := 2 ^ 20

def dataBound : Nat := 2 ^ 16

/-- The count of a loop, for the estimate. -/
def loopCount : Raw.LoopCount → Nat
  | .static count => count
  | .runtime (some maximum) _ => maximum
  | .runtime none _ => 1024

mutual
  /-- The estimated operations of a local region, with those of the functions it calls. -/
  partial def localWork (callees : Array Nat) : Raw.LocalRegion → Nat
    | .ret _ | .stop _ => 0
    | .step instruction next => stepWork callees instruction + localWork callees next
    | .block _ body next => localWork callees body + localWork callees next

  partial def stepWork (callees : Array Nat) : Raw.LocalStep → Nat
    | .loop count _ _ _ body => loopCount count * (1 + localWork callees body)
    | .conditional _ _ _ onTrue onFalse =>
      1 + max (localWork callees onTrue) (localWork callees onFalse)
    | .«match» _ _ _ _ arms => 1 + (arms.toList.map (localWork callees)).foldl max 0
    | .call callee _ => 1 + callees.getD callee 0
    | _ => 1
end

mutual
  /-- The estimated operations of a protocol region, with those of the functions it calls and
  of the protocols it applies. -/
  partial def protocolWork (functions protocols : Array Nat) : Raw.ProtocolRegion → Nat
    | .ret _ | .stop _ => 0
    | .step instruction next =>
      protocolStepWork functions protocols instruction + protocolWork functions protocols next
    | .block _ body next => protocolWork functions protocols body + protocolWork functions protocols next

  partial def protocolStepWork (functions protocols : Array Nat) : Raw.ProtocolStep → Nat
    | .at _ step => stepWork functions step
    | .«repeat» _ count _ _ _ body =>
      let times := match count with
        | .static count => count
        | .runtime maximum _ => maximum
      times * (1 + protocolWork functions protocols body)
    | .choose _ _ _ _ _ arms => 1 + (arms.toList.map (protocolWork functions protocols)).foldl max 0
    | .apply callee _ _ _ => 1 + protocols.getD callee 0
    | _ => 1
end

/-- The estimated operations of each function of a package, and of each protocol. -/
def workOf (package : Raw.Package) : Array Nat × Array Nat :=
  let functions := package.functions.foldl (init := #[]) fun done function =>
    done.push ((function.body.map (localWork done)).getD 0)
  let protocols := package.protocols.foldl (init := #[]) fun done protocol =>
    done.push (protocolWork functions done protocol.body)
  (functions, protocols)

/-- How many numbers a value of a type holds, at most. -/
partial def dataSize : Ty → Nat
  | .seq element (some size) => size * dataSize element
  | .seq element none => 3 * dataSize element
  | .tuple components | .record _ _ components => (components.map dataSize).foldl (· + ·) 0
  | .variant _ alternatives => 1 + (alternatives.map dataSize).foldl max 0
  | _ => 1

/-- Why the run of the newest protocol of a package would be too long, when it would. -/
def tooLarge? (package : Raw.Package) : Option String :=
  let (_, protocols) := workOf package
  let (work, types) := match package.protocols.getLast? with
    | some protocol => (protocols.back?.getD 0, (protocol.inputs ++ protocol.outputs).map Located.type)
    | none => (0, [])
  let data := (types.map dataSize).foldl (· + ·) 0
  if work > workBound then some s!"a run of about {work} operations is above the bound of {workBound}"
  else if data > dataBound then
    some s!"inputs and outputs of {data} numbers are above the bound of {dataBound}"
  else none

/-! ## Data by type -/

/-- A 64-bit mixing step (the finaliser of SplitMix64). -/
def mix (value : Nat) : Nat :=
  let modulus := 2 ^ 64
  let x := (value + 0x9e3779b97f4a7c15) % modulus
  let x := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9 % modulus
  let x := (x ^^^ (x >>> 27)) * 0x94d049bb133111eb % modulus
  x ^^^ (x >>> 31)

/-- The numbers of a seed and a key, each below 2^256. -/
def stream (seed : Nat) (key : List Nat) : Nat → Nat := fun index =>
  let start := (key ++ [index]).foldl (init := mix seed) fun state part =>
    mix ((state ^^^ (part % 2 ^ 64)) + part / 2 ^ 64)
  let w0 := mix start
  let w1 := mix (w0 + 1)
  let w2 := mix (w1 + 2)
  let w3 := mix (w2 + 3)
  w0 + w1 * 2 ^ 64 + w2 * 2 ^ 128 + w3 * 2 ^ 192

/-- The bound on the scalar of a point: a point is validated by a multiplication by the order of
the group, which is costly for a large scalar. -/
def pointScalars : Nat := 2 ^ 16

/-- A value of a type of a package, whose nominal rows are those of `types`, from the numbers of
a stream at the position `next` and after; with the position after the numbers it read. -/
partial def value (types : Array CatalogueRow) (numbers : Nat → Nat) :
    Ty → Nat → Except String (Datum × Nat)
  | .nat, next => .ok (.number (numbers next % 1024), next + 1)
  | .seq item size, next => do
    let (count, next) := match size with
      | some size => (size, next)
      | none => (numbers next % 4, next + 1)
    let (items, next) ← (List.range count).foldlM (init := (#[], next)) fun (items, next) _ => do
      let (datum, next) ← value types numbers item next
      return (items.push datum, next)
    return (.sequence items.toList, next)
  | .tuple components, next | .record _ _ components, next => do
    let (items, next) ← components.foldlM (init := (#[], next)) fun (items, next) component => do
      let (datum, next) ← value types numbers component next
      return (items.push datum, next)
    return (.sequence items.toList, next)
  | .variant _ alternatives, next => do
    if alternatives.isEmpty then throw "a variant without an alternative has no value"
    let position := numbers next % alternatives.length
    let (payload, next) ← value types numbers (alternatives[position]!) (next + 1)
    return (.sequence [.number position, payload], next)
  | type, next =>
    match Vocabulary.closedOf types type with
    | some closed => Vocabulary.lawValue Vocabulary.table pointScalars numbers closed next
    | none => .error "a type that the vocabulary does not close"

/-- Values of the types of the inputs of a run under a seed, one per type, in order. -/
def inputs (types : Array CatalogueRow) (seed : Nat) (inputTypes : List Ty) :
    Except String (List Datum) := do
  let numbers := stream seed []
  let (data, _) ← inputTypes.foldlM (init := (#[], 0)) fun (data, next) type => do
    let (datum, next) ← value types numbers type next
    return (data.push datum, next)
  return data.toList

/-- The `count`-th coin at a site whose key is given, under a seed: a value of the type of its
law. -/
def coin (types : Array CatalogueRow) (seed : Nat) (key : List Nat) (count : Nat) (type : Ty) :
    Except String Datum :=
  (·.1) <$> value types (stream seed (key ++ [count])) type 0

/-- The data of the inputs of a protocol with its agreements over its inputs kept: the inputs of
an agreement, one port held by several roles, all take the datum of the first. -/
def agreed (agreements : List Raw.Agreement) (data : List Datum) : List Datum :=
  agreements.foldl (init := data) fun data agreement =>
    match agreement.overOutputs, agreement.ports with
    | false, first :: rest =>
      match data[first]? with
      | some datum => rest.foldl (fun data port => data.set port datum) data
      | none => data
    | _, _ => data

/-- The agreements over the inputs of the newest protocol of a package. -/
def agreementsOf (package : Raw.Package) : List Raw.Agreement :=
  (package.protocols.getLast?.map (·.agreements)).getD []

/-! ## Keys of sites -/

/-- A row of a table of sites: what the source says of a site of a protocol. -/
structure SiteRow where
  event : Nat
  part : String
  iteration : Array Nat
  deriving Inhabited, BEq

/-- A number for the name of a part: its characters as digits in base 257, modulo 2^61. -/
def partNumber (part : String) : Nat :=
  part.foldl (init := 0) fun acc char => (acc * 257 + char.toNat + 1) % 2 ^ 61

/-- The key of one site in its table: its event, its part, and its iteration. -/
def SiteRow.key (row : SiteRow) : List Nat :=
  [row.event, partNumber row.part, row.iteration.size] ++ row.iteration.toList

mutual
  /-- The applications of a protocol region: the site of each and its callee. -/
  partial def applications : Raw.ProtocolRegion → List (Nat × Nat)
    | .ret _ | .stop _ => []
    | .step instruction next => applicationsOf instruction ++ applications next
    | .block _ body next => applications body ++ applications next

  partial def applicationsOf : Raw.ProtocolStep → List (Nat × Nat)
    | .apply callee _ site _ => [(site, callee)]
    | .«repeat» _ _ _ _ _ body => applications body
    | .choose _ _ _ _ _ arms => arms.toList.flatMap applications
    | _ => []
end

/-- The table of sites of each protocol of a package, by the package's names of its protocols. -/
def tablesOf (package : Raw.Package) (sites : Array (String × Array SiteRow)) :
    Array (Option (Array SiteRow)) :=
  let names := (package.names.map (·.protocols)).getD []
  (List.range package.protocols.length).toArray.map fun definition =>
    (names[definition]?).bind fun name => (sites.find? (·.1 == name)).map (·.2)

/-- A key that the table of sites of a protocol of a package gives to two of its sites, named
with the protocol and the two sites. -/
def duplicateKey? (package : Raw.Package) (sites : Array (String × Array SiteRow)) :
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

/-- The key of a site of a run of a package: the keys of the sites of the applications that
reach it, from the newest protocol, and its own. -/
def keyOf (package : Raw.Package) (sites : Array (String × Array SiteRow)) :
    Site → Option (List Nat) :=
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

/-! ## The run -/

/-- A package to run, as the core elaborates it, with the key in the source of each of its
sites, by which coins are given. -/
structure Side where
  package : Raw.Package
  typed : Typed
  key : Site → Option (List Nat)

/-- The package of a root as the core elaborates it, with its tables of sites. -/
def side (package : Raw.Package) (sites : Array (String × Array SiteRow)) : Except String Side :=
  match elaborate package with
  | .ok typed => .ok { package, typed, key := keyOf package sites }
  | .error refusal => .error s!"the core refuses the package: {reprStr refusal}"

/-- The coins of a seed for the sites of a package that have a key. -/
def coinsOf (side : Side) (seed : Nat) : Execute.Coins (Vocabulary.model Vocabulary.table side.package) :=
  Vocabulary.validCoins Vocabulary.table side.package fun site count type =>
    match side.key site with
    | none => none
    | some found =>
      match coin side.package.types.toArray seed found count type with
      | .ok datum => Execute.valueOf (Vocabulary.model Vocabulary.table side.package) rfl type datum
      | .error _ => none

/-- Every role of the newest protocol of a package run together on data, one datum per input
port: what each role shows. -/
def runProtocol (side : Side) (seed : Nat) (data : List Datum) : Except String (List Shown) := do
  let some header := side.typed.protocols.head? | throw "the program has no protocol"
  let inputs := Vocabulary.checkedInputs Vocabulary.table side.package header.inputs data
  unless inputs.all Option.isSome do throw "an input is not a value of its port's type"
  let run ← Vocabulary.runRolesObserved Vocabulary.table side.package side.typed
    side.typed.program.protocols Identities.written (List.range header.roles) inputs
    (coinsOf side seed)
  return (run.outcomes.zip run.did).map fun (ended, did) =>
    { ended, did := did.map fun step => (step.kind, side.key step.site, step.value) }

end Zkc.Tools.Frontend.PackageRuns
