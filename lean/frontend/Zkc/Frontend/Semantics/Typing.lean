module

public import Zkc.Core.Facts
public import Zkc.Core.ProtocolFacts
public import Zkc.Core.Admission
public import Zkc.Core.VocabularyModel
public import Zkc.Core.VocabularyExecute
public import Zkc.Frontend.Semantics.Instances
public import Zkc.Frontend.Emit.Root

@[expose] public section

set_option autoImplicit false

/-!
# The typing of bodies and their elaboration to the core

After the check of instances, in the same state: the body of every function instance is typed
and elaborated to local code (`Typing.typeProgram`), and a package of the core is emitted for
every root that is a function or a protocol (the roots, the instances that comments ask for and
the default instances, SP7) and admitted by the core: by its `elaborate`, then by its check of
facts, which every function and every protocol of the package passes. Every body passed its own
check before, so a package that the core refuses, or a function or a protocol of a package that
does not pass the check, is a defect of the frontend or a finding about the core, and is logged
as a defect; a root that needs a form that is not typed yet waits, with the reason.
-/

namespace Zkc.Frontend

open Instances
open Static

namespace PackageReport

/-- The package emitted for the root, when one was. -/
def package? (report : PackageReport) : Option Zkc.Core.Raw.Package :=
  match report.outcome with
  | .admitted package | .unjustified _ package | .refused _ package => some package
  | _ => none

end PackageReport

/-- The package of a root that the core admitted: what is run, once a completed result holds
it. -/
structure RootPackage where
  root : InstanceId
  package : Zkc.Core.Raw.Package
  /-- The package as the core elaborates it, computed when it is first needed. -/
  typed : Thunk (Except String Zkc.Core.Typed)
  /-- The code of the protocol, when the root is a protocol. -/
  protocol : Option Typing.ProtocolCode

namespace RootPackage

/-- The admitted package of a root, elaborated again when it is run. -/
def ofPackage (root : InstanceId) (package : Zkc.Core.Raw.Package)
    (protocol : Option Typing.ProtocolCode) : RootPackage :=
  { root, package, protocol
    typed := Thunk.mk fun _ => match Zkc.Core.elaborate package with
      | .ok typed => .ok typed
      | .error refusal => .error s!"the core refuses the package: {reprStr refusal}" }

end RootPackage

/-! ## Running a protocol -/

/-- How one role of a protocol run ends: the outcome that the core's executor gives the program
of the role. It returns its outputs, it stops with a reason, a reading of a value reaches the
limit of the run, or it fails: its program waits for a message that no role sends (a peer
stopped), or it does not run. -/
structure RoleRun where
  role : String
  outcome : Zkc.Core.Execute.Outcome (List Zkc.Core.Concrete.Datum)

/-- The messages of a run of roles against given ones: a site of the root protocol and a value,
in order. -/
abbrev Messages := List (Nat × Zkc.Core.Concrete.Datum)

/-- The protocol of a package that the core has elaborated, with one input per input port of its
entry, validated at the type of the port (none where the datum given is not a value of it). Only
a completed result makes one (`Completed.protocolInputs`). -/
structure ProtocolInputs where
  private mk ::
  package : Zkc.Core.Raw.Package
  typed : Zkc.Core.Typed
  code : Typing.ProtocolCode
  inputs : List (Option (Zkc.Core.Vocabulary.Checked Zkc.Core.Vocabulary.table package))

namespace Running

open Zkc.Core

/-- A change of the first message at a site, for the tests that change a message: the site of
a definition (the root's when none is given) under the path of the applications that reach it,
outermost first (the root's sites have the empty path). At the site of a draw, the coin that the
receivers hear is changed. -/
structure Change where
  site : Nat
  change : Zkc.Core.Concrete.Datum → Zkc.Core.Concrete.Datum
  definition : Option Nat := none
  path : List Nat := []

end Running

/-- The projection of an elaborated protocol package to the program of each of its roles, as the
core makes it; the number of role programs. -/
def projectRoles (package : Zkc.Core.Raw.Package) (typed : Zkc.Core.Typed) (roles : Nat) :
    Except String Nat := do
  for role in [0:roles] do
    let _ ← Zkc.Core.Vocabulary.wholeEntry Zkc.Core.Vocabulary.table package typed
      typed.program.protocols Zkc.Core.Identities.written role
  return roles

end Zkc.Frontend

end

/- The runners of a completed result are the only users of the executor here: their bodies are
not exposed, so that they may call it. -/
public section

namespace Zkc.Frontend

namespace Running

open Zkc.Core

/-- The source of coins of the frontend's runs: the coins of a seed, each the value of the law
of its type as the vocabulary defines it (`Vocabulary.seededCoins`). A test that fixes its coins
gives a function of the type and of the executor's field element of the seed at the site
(`Execute.coin`) in place of the law. Every coin is validated at its type where it enters the
run (`Vocabulary.validCoins`). -/
def coins (package : Raw.Package) (fixed : Option (Ty → Concrete.Datum → Concrete.Datum))
    (seed : List Nat) : Execute.Coins (Vocabulary.model Vocabulary.table package) :=
  match fixed with
  | none => Vocabulary.seededCoins Vocabulary.table package seed
  | some law =>
    Vocabulary.validCoins Vocabulary.table package fun site occurrence type =>
      Execute.valueOf (Vocabulary.model Vocabulary.table package) rfl type
        (law type (Execute.coin seed site occurrence))

end Running

/-- The protocol of a package that the core has elaborated, with its inputs validated once at
the types of their ports, from one datum per port that is not `spec`: run it as often as a caller
likes (`ProtocolInputs.run`). A datum that is not a value of its port's type is no input, and a
run of a role that holds it does not start. -/
private def ProtocolInputs.of (package : Zkc.Core.Raw.Package) (typed : Zkc.Core.Typed)
    (code : Typing.ProtocolCode) (inputs : List Zkc.Core.Concrete.Datum) :
    Except String ProtocolInputs := do
  let some header := typed.protocols.head? | throw "the program has no protocol"
  let portCount := (code.inputPorts.foldl max 0) + 1
  if !code.inputPorts.isEmpty && inputs.length != portCount then
    throw s!"the protocol takes {portCount} inputs, one per port; {inputs.length} are given"
  let data := code.inputPorts.toList.map fun port => inputs.getD port default
  return { package, typed, code
           inputs := Zkc.Core.Vocabulary.checkedInputs Zkc.Core.Vocabulary.table package header.inputs
             data }

/-- Runs the protocol of a package that the core has elaborated, by the core's executor under
the core's model of the vocabulary's rows (`Vocabulary.model`), with the limit on the work of
reading: every role together, or the roles given (`Vocabulary.runRoles`), on the inputs validated
once; the coins are those of a seed, each the value of its law (`Running.coins`).

Against messages given, or with the first message or coin at a site changed, each role given
runs alone (`Execute.run`) from a state that holds what the others send: the coins of an honest
run of every role, and the messages that each role sends when it runs alone against those coins.
A change applies to the first coin or message at its site, before the roles given run; messages
given take the place of those sent, each at the type of the message sent at its site. A role
that receives a message before it sends sends only what comes before that receive, and a role
that ends against the coins alone needs no message: its outcome is that of its run alone. -/
def ProtocolInputs.run (prepared : ProtocolInputs) (seed : List Nat := [1])
    (selected : Option (List Nat) := none) (messages : Messages := [])
    (change : Option Running.Change := none) : Except String (Array RoleRun) := do
  let { package, typed, code, inputs := checked } := prepared
  let table := Zkc.Core.Vocabulary.table
  let model := Zkc.Core.Vocabulary.model table package
  let some header := typed.protocols.head? | throw "the program has no protocol"
  let roles := selected.getD (List.range code.roles.size)
  let name (role : Nat) : String := code.roles[role]?.getD "?"
  let against := !messages.isEmpty || change.isSome
  -- the inputs of the roles that run, every role for a run against what the others send
  for (port, input) in header.inputs.zip checked do
    if input.isNone && (against || roles.contains port.holder) then
      throw s!"an input of {name port.holder} is not a value of its port's type"
  let coins := Running.coins package none seed
  let named (outcomes : List (Zkc.Core.Execute.Outcome (List Zkc.Core.Concrete.Datum))) :
      Array RoleRun :=
    (roles.zip outcomes).toArray.map fun (role, outcome) => { role := name role, outcome }
  unless against do
    let run ← Zkc.Core.Vocabulary.runRoles table package typed typed.program.protocols
      Zkc.Core.Identities.written roles checked coins
    return named run.outcomes
  let processes ← (List.range code.roles.size).mapM fun role =>
    Zkc.Core.Vocabulary.roleProcess table package role checked
      (Zkc.Core.Vocabulary.limitedEntry table package typed typed.program.protocols
        Zkc.Core.Identities.written role Zkc.Core.defaultLimit)
  let root := package.protocols.length - 1
  let changed : Option Zkc.Core.Site := change.map fun change =>
    { path := change.path, definition := change.definition.getD root, number := change.site }
  let edit (type : Zkc.Core.Ty) (value : model.Value type) : Except String (model.Value type) := do
    let some change := change | return value
    let some edited := Zkc.Core.Execute.valueOf model rfl type
        (change.change (Zkc.Core.Execute.datumOf model rfl type value))
      | throw s!"the value changed at site {change.site} is not a value of its type"
    return edited
  -- the coins of an honest run of every role, the first at the site of the change changed
  let honest := Zkc.Core.Execute.run model coins processes
  let mut heard : Zkc.Core.Execute.Shared model :=
    { Zkc.Core.Execute.Shared.start model with board := honest.shared.board }
  if let some site := changed then
    if let ⟨type, value⟩ :: rest := heard.board site then
      let edited ← edit type value
      let announced := heard.board
      heard := { heard with
        board := fun other => if other = site then ⟨type, edited⟩ :: rest else announced other }
  -- the messages that each role sends when it runs alone against those coins
  let alone := processes.map fun process => Zkc.Core.Execute.run model coins [process] heard
  let sent : Zkc.Core.Mail model := fun site => alone.flatMap fun run => run.shared.mail site
  let mut mail := sent
  if let some site := changed then
    match sent site with
    | ⟨type, value⟩ :: rest => mail := sent.set site (⟨type, ← edit type value⟩ :: rest)
    | [] =>
      if (heard.board site).isEmpty then
        throw s!"no message is sent and no coin drawn at site {site.number} of definition {site.definition}"
  unless messages.isEmpty do
    let mut given : Zkc.Core.Mail model := Zkc.Core.Mail.empty
    for (number, datum) in messages do
      let site : Zkc.Core.Site := { path := [], definition := root, number }
      let some ⟨type, _⟩ := (sent site).head? | throw s!"no role sends a message at site {number}"
      let some value := Zkc.Core.Execute.valueOf model rfl type datum
        | throw s!"the message at site {number} is not a value of its type"
      given := given.put site type value
    mail := given
  -- each role given, alone, from those coins and messages; a role that ended against the coins
  -- alone received no message, and ends so again
  let reserved := some (Zkc.Core.reservedDefinition Zkc.Core.Identities.written
    typed.protocols.length)
  let outcomeOf (role : Nat) (run : Zkc.Core.Execute.Run model (List Zkc.Core.Concrete.Datum)) :
      Zkc.Core.Execute.Outcome (List Zkc.Core.Concrete.Datum) :=
    match run.roles with
    | [one] => Zkc.Core.Execute.ended model reserved run.shared one
    | _ => .failed s!"the run of {name role} has no role"
  let outcomes := roles.map fun role =>
    match alone[role]?, processes[role]? with
    | some first, some process =>
      match outcomeOf role first with
      | .failed _ => outcomeOf role (Zkc.Core.Execute.run model coins [process] { heard with mail })
      | ended => ended
    | _, _ => .failed s!"{name role} has no program"
  return named outcomes

namespace Completed

/-- Runs a function of the package of a root that a completed result holds, on data validated at
the types of its inputs, under the core's model of the vocabulary's rows with the limit: the root
itself, or the function of the package of the name given. -/
def runFunction (completed : Completed RootPackage) (root : String)
    (inputs : List Zkc.Core.Concrete.Datum) (function : Option String := none) :
    Zkc.Core.Vocabulary.Run :=
  match completed.find? root with
  | none => .failed s!"the result does not hold {root}"
  | some { package, .. } =>
    let names := (package.names.map (·.functions)).getD []
    let number := match function with
      | some name => names.findIdx? (· == name)
      | none => if package.functions.isEmpty then none else some (package.functions.length - 1)
    match number with
    | some number => Zkc.Core.Vocabulary.runData Zkc.Core.Vocabulary.table package number inputs
    | none => .failed s!"the package of {root} has no function {function.getD ""}"

/-- The protocol of a root that a completed result holds, on the package as the core elaborates
it, with its inputs validated once: see `ProtocolInputs.of`. -/
def protocolInputs (completed : Completed RootPackage) (root : String)
    (inputs : List Zkc.Core.Concrete.Datum) : Except String ProtocolInputs := do
  let some rootPackage := completed.find? root | throw s!"the result does not hold {root}"
  let some code := rootPackage.protocol | throw s!"{root} is no protocol"
  ProtocolInputs.of rootPackage.package (← rootPackage.typed.get) code inputs

/-- Runs the protocol of a root that a completed result holds: see `ProtocolInputs.run`. -/
def runProtocol (completed : Completed RootPackage) (root : String)
    (inputs : List Zkc.Core.Concrete.Datum) (seed : List Nat := [1])
    (selected : Option (List Nat) := none) (messages : Messages := [])
    (change : Option Running.Change := none) : Except String (Array RoleRun) := do
  (← completed.protocolInputs root inputs).run seed selected messages change

end Completed

end Zkc.Frontend

end

@[expose] public section

namespace Zkc.Frontend

open Instances
open Static

namespace Typing

/-- The function instances among the roots, once each. -/
def functionRoots (state : Compile.State) : Array InstanceId := Id.run do
  let mut seen : Std.HashSet InstanceId := {}
  let mut result := #[]
  for root in state.roots do
    if seen.contains root then continue
    seen := seen.insert root
    let some entry := state.table.entries[root]? | continue
    let some found := state.program.declarations[entry.key.declaration]? | continue
    if found.kind == .function || found.kind == .relation || found.kind == .law
        || found.kind == .lawMember || found.kind == .protocol then
      result := result.push root
  return result

/-- A root as source writes it, with the words of a default instance. -/
def rootDescription (state : Compile.State) (root : InstanceId) : String :=
  let description := renderInstance state root
  if state.results.isDefault root then s!"default instance `{description}`" else description

/-- What an admitted result holds of a root that is a function or a protocol: the package that
the core admitted, or why it has none: refused (by the frontend or the core), waiting, not checked
to the end, or without a package of its own (a specification item, a function bound to a row). -/
def rootPackage (state : Compile.State) (root : InstanceId) : Except Lack RootPackage :=
  let body := state.results.body? root
  let protocol := match body with
    | some (.protocol code) => some code
    | _ => none
  let outcome : Option PackageOutcome :=
    (state.results.packageReports.find? (·.root == root)).map (·.outcome)
  match outcome with
  | some (.admitted package) => .ok (RootPackage.ofPackage root package protocol)
  | some (.unjustified functions _) =>
    .error (.refused s!"the core's check of facts does not justify {"; ".intercalate functions.toList}")
  | some (.refused reason _) => .error (.refused s!"the core refuses its package: {reason}")
  | some (.waiting reason) => .error (.waiting reason)
  | some (.typedOnly reason) => .error (.noPackage reason)
  | some (.defect message) => .error (.defect message)
  | some (.exhausted exhaustion) => .error (.exhausted exhaustion)
  | none =>
    match body with
    | some (.exhausted exhaustion) => .error (.exhausted exhaustion)
    | some (.waiting reason) => .error (.waiting reason)
    | some .failed => .error (.refused "its body is refused")
    | some (.row _) => .error (.noPackage "it is bound to a row of the vocabulary")
    | _ => .error (.defect "no package is emitted for it")

/-- The package of a root and what the core makes of it. -/
def admit (state : Compile.State) (root : InstanceId) : Option PackageOutcome :=
  match state.results.body? root with
  | some (.done _) | some (.protocol _) =>
    match emitRoot state root with
    | .ok { package, claims } =>
      match Zkc.Core.admit package claims with
      | .ok _ => some (.admitted package)
      | .error [.elaboration refusal] => some (.refused (reprStr refusal) package)
      | .error refusals =>
        -- the definitions whose normal form does not pass the check of facts
        let functionNames := (package.names.map (·.functions)).getD []
        let protocolNames := (package.names.map (·.protocols)).getD []
        let described := refusals.filterMap fun
          | .facts (.function number) unjustified =>
            some s!"{functionNames.getD number s!"function {number}"}: {reprStr unjustified.requirement} at {unjustified.path}"
          | .facts (.protocol number) unjustified =>
            some s!"protocol {protocolNames.getD number s!"{number}"}: {reprStr unjustified.requirement} at {unjustified.path}"
          | .copies number refusal =>
            some s!"protocol {protocolNames.getD number s!"{number}"}: copies: {reprStr refusal.unmet} at {refusal.path}"
          | .sites number =>
            some s!"protocol {protocolNames.getD number s!"{number}"}: its sites are not numbered in the order of its body"
          | .keys number =>
            some s!"protocol {protocolNames.getD number s!"{number}"}: its sites do not have one key each"
          | .stops number =>
            some s!"{functionNames.getD number s!"function {number}"}: what is stated of whether it can stop is not what its body says"
          | .row reason => some reason
          | .literal (.function number) row =>
            some s!"{functionNames.getD number s!"function {number}"}: a literal of the type of row {row} whose data are not data of the type"
          | .literal (.protocol number) row =>
            some s!"protocol {protocolNames.getD number s!"{number}"}: a literal of the type of row {row} whose data are not data of the type"
          | .elaboration refusal => some (reprStr refusal)
        some (.unjustified described.toArray package)
    | .error (.waiting reason) => some (.waiting reason)
    | .error (.defect message) => some (.defect message)
    | .error (.noCoreForm reason) => some (.typedOnly reason)
  | some (.waiting reason) => some (.waiting reason)
  | some (.exhausted exhaustion) => some (.exhausted exhaustion)
  | _ => none

end Typing

/-- The phase of packages: the package of every root that is a function or a protocol, emitted
and admitted by the core, reported in the order of the roots. -/
def Typing.reportPackages : CompileM Unit := do
  let state ← get
  let reports := (Typing.functionRoots state).filterMap fun root =>
    let description := Typing.rootDescription state root
    (Typing.admit state root).map fun outcome => ({ root, description, outcome } : PackageReport)
  modifyResults fun results => { results with packageReports := reports }
  -- every body passed its own check before its package was emitted, so a package that the
  -- core does not admit is a defect of the frontend, and is logged as one: such a program is
  -- not accepted
  for report in reports do
    let reason : Option String := match report.outcome with
      | .unjustified found _ => some s!"the core does not admit it: {"; ".intercalate found.toList}"
      | .refused reason _ => some s!"the core refuses it: {reason}"
      | .defect message => some message
      | _ => none
    if let some reason := reason then
      let span := (((state.table.entries[report.root]?).bind fun entry =>
        state.program.declarations[entry.key.declaration]?).bind (·.name)).map (·.span)
      logError "defect" (span.getD default) (.ofText
        s!"a defect of the frontend: the package of `{report.description}`, whose bodies passed their own checks: {reason}")
        (origin := .core)

end Zkc.Frontend
