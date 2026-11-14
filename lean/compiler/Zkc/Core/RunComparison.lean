module

public import Zkc.Core.ValidData
public import Zkc.Core.VocabularyObserved
public import Zkc.Core.Specialize

@[expose] public section

/-! Two packages of one program compared by their runs.

Two packages that a frontend emits for one root may differ in their bytes for reasons that are
no rule of the language. They are compared by what they do: for the same inputs and the same
coins, each role of the two must do the same things in the same order and end alike.

- **Inputs.** For each seed, one datum per input of the root, drawn from the types of the first
  package's inputs (`ValidData.inputs`), the inputs of one port held by several roles alike (the
  protocol's agreements over its inputs); each package validates them at its own types.
- **Coins.** A coin is given by a key of its site in the source, which the caller gives for
  each package (`Side.key`): the coin of a draw or a sample is a value of the law's type drawn
  from the seed, the key and the count at the site (`ValidData.coin`), so the two packages get
  the same coin for the same event however they number their sites. A site that has no key
  gets no coin, and the run fails there.
- **Runs.** A function by the steps of `Vocabulary.run`, the last function of each package,
  elaborated once for all seeds (`functionRunner`); a protocol by
  `Vocabulary.runRolesObserved` on every role of its newest protocol; a constructed scheme by
  `Vocabulary.runRoleObserved` on the prover, whose first output is the proof, then on the
  verifier with that proof.
- **What is compared.** For each role, what it did in the order in which it did so (what it
  sent, received and heard, what it drew and sampled), each by its kind, the key of its site
  and its value, and how it ended: the same outputs as data, the same stop, the same wait for a
  message that is never sent. What two different roles did is not ordered against each other. A
  program may not reorder what one role does, so the order of a role is compared as it is.
- **Size.** A root whose run would be too long for a comparison of a corpus (`tooLarge?`) is not
  run, with the estimate.

**Three verdicts.** The two are *observed to agree* when, under every seed, every role shows
the same and no run reached a limit. They are *observed to differ* when under some seed a role
does not show the same: with the seed, the inputs, the role and the first place where the two
differ. Otherwise the comparison is *incomplete*: a run reached the limit, under a seed that
is named; no seed was run; or a run failed otherwise (the model does not compute a row, an input
is not a value, a site has no coin), which is no end to compare by. A limit that both runs
reach is incomplete, not agreement: neither program returned and neither stopped.
-/

set_option autoImplicit false

namespace Zkc.Core.RunComparison

open Zkc.Core.Concrete (Datum)
open Vocabulary

/-- The message with which the executor ends a role that waits for a message that is never
sent. -/
def waitingMessage : String := "waits for a message that is never sent"

/-- A datum as text: a number, or its items in brackets. -/
partial def datumText : Datum → String
  | .number value => toString value
  | .sequence items => "[" ++ ", ".intercalate (items.map datumText) ++ "]"

/-- Data as text, in brackets. -/
def dataText (data : List Datum) : String := datumText (.sequence data)

def stopText : PIR.Stop → String
  | .reject => "reject" | .abort => "abort" | .exhausted => "exhausted"
  | .incomplete => "incomplete" | .refused => "refused" | .undefined => "undefined"

/-- An outcome of a role, as a line. -/
def describe : Execute.Outcome (List Datum) → String
  | .returned outputs => s!"returned {dataText outputs}"
  | .stopped reason => s!"stopped {stopText reason}"
  | .limit elements => s!"reached the limit of {elements} elements"
  | .failed message => s!"failed: {message}"

/-- An outcome of a function, as a line. -/
def describeRun : Vocabulary.Run → String
  | .returned outputs => s!"returned {dataText outputs}"
  | .stopped reason => s!"stopped {stopText reason}"
  | .limit elements => s!"reached the limit of {elements} elements"
  | .failed message => s!"failed: {message}"

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

/-- What one role of a run shows: what it did, each with the key of its site in the source,
and how it ended. -/
structure Shown where
  did : List (Execute.Event.Kind × Option (List Nat) × Datum)
  ended : Execute.Outcome (List Datum)

/-- What the runs of one seed show. -/
inductive Seen where
  | agree
  /-- A role does not show the same in the two; no role for a function. The first place where
  the two differ, each as a line. -/
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

/-- The ends of two runs of a function. -/
def compareRuns : Vocabulary.Run → Vocabulary.Run → Seen
  | .failed message, _ | _, .failed message => .broken message
  | .limit elements, _ | _, .limit elements => .limit elements
  | .returned left, .returned right => if left == right then .agree
      else .differ none (describeRun (.returned left)) (describeRun (.returned right))
  | .stopped left, .stopped right => if left == right then .agree
      else .differ none (describeRun (.stopped left)) (describeRun (.stopped right))
  | left, right => .differ none (describeRun left) (describeRun right)

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

A root whose runs would be too long for a comparison of the corpus is not run: one whose
estimated number of operations, every loop at its count (a run-time count at its maximum, or
1024 without one) and every call at its callee's, is above `workBound`, or whose inputs or
outputs hold more than `dataBound` numbers. -/

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

/-- Why the runs of the newest protocol, or else of the last function, of a package would be
too long for the comparison, when they would. -/
def tooLarge? (package : Raw.Package) : Option String :=
  let (functions, protocols) := workOf package
  let (work, types) := match package.protocols.getLast?, package.functions.getLast? with
    | some protocol, _ =>
      (protocols.back?.getD 0, (protocol.inputs ++ protocol.outputs).map Located.type)
    | none, some function => (functions.back?.getD 0, function.inputs ++ function.outputs)
    | none, none => (0, [])
  let data := (types.map dataSize).foldl (· + ·) 0
  if work > workBound then some s!"a run of about {work} operations is above the bound of {workBound}"
  else if data > dataBound then
    some s!"inputs and outputs of {data} numbers are above the bound of {dataBound}"
  else none

/-! ## Functions -/

/-- The run of the last function of a package on data, the package elaborated and its rows
checked against the vocabulary once: what `Vocabulary.runData` does on each call, for runs under
many seeds. The data are validated at the types of the function's inputs on each run. -/
def functionRunner (package : Raw.Package) (limit : Nat) :
    Except String (FunctionHeader × (List Datum → Vocabulary.Run)) := do
  let typed ← match elaborate package with
    | .ok typed => pure typed
    | .error refusal => throw s!"the core refuses the package: {reprStr refusal}"
  if let first :: _ := missing table package then throw first
  let some ⟨header, meaning⟩ := nthFunction typed.functions
      (limitedFunctions table package typed limit) 0
    | throw "the package has no function"
  return (header, fun data =>
    if data.length != header.inputs.length then
      .failed s!"the function takes {header.inputs.length} inputs; {data.length} are given"
    else
      match (header.inputs.zip data).mapM fun (type, datum) => checked? table package type datum with
      | none => .failed "an input is not a value of its type"
      | some inputs =>
        match Concrete.ofData header.inputs (inputs.map (·.datum)) with
        | none => .failed "an input is not a value of its type"
        | some arguments =>
          let process := meaning arguments
          match limitOf? (model table package) package.protocols.length process with
          | some reached => .limit reached
          | none =>
            match finish process with
            | .error message => .failed message
            | .ok (.error reason) => .stopped reason
            | .ok (.ok values) => .returned (Concrete.toData header.outputs values))

/-! ## Protocols -/

/-- One package to run, as the core elaborates it, with the key in the source of each of its
sites, by which coins are given. -/
structure Side where
  package : Raw.Package
  typed : Typed
  key : Site → Option (List Nat)

/-- The coins of a seed for the sites of a package that have a key. -/
def coinsOf (package : Raw.Package) (key : Site → Option (List Nat)) (seed : Nat) :
    Execute.Coins (model table package) :=
  validCoins table package fun site count type =>
    match key site with
    | none => none
    | some found =>
      match ValidData.coin table package.types.toArray seed found count type with
      | .ok datum => Execute.valueOf (model table package) rfl type datum
      | .error _ => none

/-- Inputs validated at the types of ports, one per port: or the first datum that is not a value
of its port's type. -/
def checkedAll (package : Raw.Package) (ports : List Located) (data : List Datum) :
    Except String (List (Option (Checked table package))) :=
  let inputs := checkedInputs table package ports data
  if inputs.all Option.isSome then .ok inputs
  else .error "an input is not a value of its port's type"

/-- What a role shows, from how it ended and what it did, with the key of each site. -/
def shown (key : Site → Option (List Nat)) (ended : Execute.Outcome (List Datum))
    (did : List Execute.Did) : Shown :=
  { ended, did := did.map fun step => (step.kind, key step.site, step.value) }

/-- Every role of the newest protocol of a package run together on data, one datum per input
port: what each role shows. -/
def runProtocol (side : Side) (seed : Nat) (data : List Datum) (limit : Nat := defaultLimit) :
    Except String (List Shown) := do
  let some header := side.typed.protocols.head? | throw "the program has no protocol"
  let inputs ← checkedAll side.package header.inputs data
  let run ← runRolesObserved table side.package side.typed side.typed.program.protocols
    Identities.written (List.range header.roles) inputs (coinsOf side.package side.key seed) limit
  return (run.outcomes.zip run.did).map fun (ended, did) => shown side.key ended did

/-! ## Constructed schemes -/

/-- A constructed scheme to run: its package and the program of the construction's steps, as
the core elaborates and constructs them, its prover and its verifier, and the key in the source
of each site. -/
structure SchemeSide where
  package : Raw.Package
  typed : Typed
  stepped : Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions
  prover : Nat
  verifier : Nat
  key : Site → Option (List Nat)

/-- The ports of the entry after the proof, the verifier's first input. -/
def SchemeSide.ports (side : SchemeSide) : List Located :=
  ((side.stepped.headers.head?.map (·.inputs)).getD []).drop 1

/-- The inputs of a role: none for the proof, then the data that the role holds, validated at
the types of their ports. -/
def SchemeSide.inputsOf (side : SchemeSide) (role : Nat) (data : List Datum) :
    Except String (List (Option (Checked table side.package))) := do
  let held ← (side.ports.zip data).mapM fun (port, datum) =>
    if port.holder != role then pure none
    else match checked? table side.package port.type datum with
      | some input => pure (some input)
      | none => throw "an input is not a value of its port's type"
  return none :: held

/-- The prover's run on data and, when it gives a proof, the verifier's run on that proof: what
each shows. -/
def runScheme (side : SchemeSide) (seed : Nat) (data : List Datum) (limit : Nat := defaultLimit) :
    Except String (List Shown) := do
  let coins := coinsOf side.package side.key seed
  let proving ← side.inputsOf side.prover data
  let (proved, sampled) ← runRoleObserved table side.package side.typed side.stepped.protocols
    side.stepped.identities side.prover proving coins limit
  match proved with
  | .returned (proof :: _) =>
    let some bytes := asBytes proof | throw "the proof is not bytes"
    let checking ← side.inputsOf side.verifier data
    let (verified, derived) ← runRoleObserved table side.package side.typed side.stepped.protocols
      side.stepped.identities side.verifier
      (some (Checked.ofBytes table side.package bytes) :: checking.drop 1) coins limit
    return [shown side.key proved sampled, shown side.key verified derived]
  | other => return [shown side.key other sampled]

/-! ## Providers

What a comparison runs two packages under: a provider gives the inputs of a seed and runs a
function, the roles of a protocol and a constructed scheme, each with what it shows. The
comparison is one for every provider. `arithmetic` is the model of the vocabulary's rows, with
inputs and coins that validation accepts and the limit; `Zkc.Core.UninterpretedRows` gives a
provider whose rows are uninterpreted. -/

structure Provider where
  name : String
  /-- Whether the provider computes the rows, so that a statement is true or false under it. A
  generator of true statements is used only under such a provider. -/
  computes : Bool
  /-- Why the provider does not run a package, when it does not. -/
  refuses : Raw.Package → Option String
  /-- One datum per input, for the types of the inputs of a root of a package, under a seed. -/
  inputs : Raw.Package → Nat → List Ty → Except String (List Datum)
  /-- The last function of a package, prepared once for runs under a limit: its header, and
  its run under a seed on data. -/
  function : Raw.Package → Nat → Except String (FunctionHeader × (Nat → List Datum → Vocabulary.Run))
  /-- Every role of the newest protocol of a package together, under a seed, on data, under a
  limit: what each role shows. -/
  protocol : Side → Nat → List Datum → Nat → Except String (List Shown)
  /-- The prover and the verifier of a constructed scheme, when the provider runs schemes. -/
  scheme : Option (SchemeSide → Nat → List Datum → Nat → Except String (List Shown))

/-- The model of the vocabulary's rows: valid data by type, coins that are values of their
laws, and the limit. -/
def arithmetic : Provider where
  name := "the model of the vocabulary's rows"
  computes := true
  refuses package := (missing table package).head?
  inputs package seed types := ValidData.inputs table package.types.toArray (.ofSeed seed []) types
  function package limit :=
    (functionRunner package limit).map fun (header, run) => (header, fun _ data => run data)
  protocol side seed data limit := runProtocol side seed data limit
  scheme := some fun side seed data limit => runScheme side seed data limit

/-! ## True statements

A protocol run on inputs drawn by type is mostly run on a false statement, and an honest
verifier stops at its first check: what comes after the check is not run, and a change there
is not seen. A **generator** is a function whose outputs are the statement and the witness of
a protocol, in the order of the protocol's inputs in the source, made from freely drawn values
so that the statement is true. With one, the inputs of a seed are the generator's outputs on
the inputs drawn for it, and every role of the first package must return: a statement on which
an honest run stops is not a true one, and the comparison says so and is incomplete. -/

/-- The inputs of the newest protocol of a package as the source has them: the ports that an
agreement over the inputs names are one input held by several roles, and every other port is
an input of its own; in the order of their first ports. -/
def sourceInputs (package : Raw.Package) : List (List Nat) :=
  match package.protocols.getLast? with
  | none => []
  | some protocol =>
    let agreed := (protocol.agreements.filter (!·.overOutputs)).map (·.ports)
    let alone := (List.range protocol.inputs.length).filter fun port => !agreed.any (·.contains port)
    (agreed ++ alone.map ([·])).mergeSort fun first second => first.headD 0 ≤ second.headD 0

/-- The statements of a generator for a protocol, under a provider: for a seed, one datum per
input port of the protocol. The generator is the last function of its package; a function that
returns one tuple gives its components. -/
def statementsOf (provider : Provider) (generator protocol : Raw.Package)
    (limit : Nat := defaultLimit) : Except String (Nat → Except String (List Datum)) := do
  let (header, run) ← provider.function generator limit
  let inputs := sourceInputs protocol
  let ports := (protocol.protocols.getLast?.map (·.inputs.length)).getD 0
  return fun seed => do
    let free ← provider.inputs generator seed header.inputs
    match run seed free with
    | .returned outputs =>
      let given := match outputs with
        | [.sequence items] => if inputs.length == 1 then outputs else items
        | other => other
      if given.length != inputs.length then
        throw s!"the generator gives {given.length} values, and the protocol has {inputs.length} inputs"
      return (inputs.zip given).foldl (init := List.replicate ports (default : Datum))
        fun data (held, datum) => held.foldl (fun data port => data.set port datum) data
    | other => throw s!"the generator does not return: {describeRun other}"

/-! ## The comparisons -/

/-- The last functions of two packages run on the same inputs under each seed. -/
def compareFunctions (provider : Provider) (left right : Raw.Package) (seeds : List Nat)
    (limit : Nat := defaultLimit) : Verdict :=
  match tooLarge? left, provider.function left limit, provider.function right limit with
  | some reason, _, _ => .incomplete (.cannotRun reason)
  | none, .error reason, _ | none, _, .error reason => .incomplete (.cannotRun reason)
  | none, .ok (header, first), .ok (_, second) =>
    overSeeds seeds fun seed => do
      let inputs ← provider.inputs left seed header.inputs
      return (inputs, compareRuns (first seed inputs) (second seed inputs))

/-- The newest protocols of two packages run with every role on the same inputs and the same
coins under each seed. With `statements`, the inputs of a seed are a true statement and its
witness, on which every role of the first package must return. -/
def compareProtocols (provider : Provider) (left right : Side) (seeds : List Nat)
    (limit : Nat := defaultLimit)
    (statements : Option (Nat → Except String (List Datum)) := none) : Verdict :=
  match left.typed.protocols.head?, right.typed.protocols.head?, tooLarge? left.package with
  | _, _, some reason => .incomplete (.cannotRun reason)
  | some header, some other, none =>
    if header.roles != other.roles || header.inputs.length != other.inputs.length then
      .incomplete (.cannotRun "the two protocols have different roles or ports")
    else
      overSeeds seeds fun seed => do
        let inputs ← match statements with
          | some statement => statement seed
          | none => pure (agreed (agreementsOf left.package)
              (← provider.inputs left.package seed (header.inputs.map (·.type))))
        let first ← provider.protocol left seed inputs limit
        if statements.isSome then
          -- the role that stops, when one does; otherwise one that does not return
          let roles := first.zipIdx.map fun (shown, role) => (role, shown.ended)
          let stopped := roles.find? fun (_, ended) => ended matches .stopped _
          let other := roles.find? fun (_, ended) => !(ended matches .returned _ | .limit _)
          if let some (role, ended) := stopped.or other then
            throw s!"under seed {seed} role {role} does not return on a statement of the generator: {describe ended}"
        let second ← provider.protocol right seed inputs limit
        return (inputs, compareShown first second)
  | _, _, none => .incomplete (.cannotRun "a package has no protocol")

/-- The provers of two constructed schemes on the same statement and witness and the same coins,
and their verifiers each on its prover's proof, under each seed: what the prover and the
verifier show compared, the proof among it. -/
def compareSchemes (provider : Provider) (left right : SchemeSide) (seeds : List Nat)
    (limit : Nat := defaultLimit) : Verdict :=
  match provider.scheme with
  | none => .incomplete (.cannotRun s!"{provider.name} does not run a constructed scheme")
  | some run =>
    if let some reason := tooLarge? left.package then .incomplete (.cannotRun reason)
    else if left.ports.length != right.ports.length then
      .incomplete (.cannotRun "the two entries have different ports")
    else
      overSeeds seeds fun seed => do
        let inputs := agreed (agreementsOf left.package)
          (← provider.inputs left.package seed (left.ports.map (·.type)))
        let first ← run left seed inputs limit
        let second ← run right seed inputs limit
        return (inputs, compareShown first second)

end Zkc.Core.RunComparison
