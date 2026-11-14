module

public import Zkc.Core.Serialize
public import Zkc.Core.ProofIdentity
public import Zkc.Core.Unelaborate
public import Zkc.Frontend.Semantics.Typing

@[expose] public section

set_option autoImplicit false

/-!
# Schemes: the derived construction

A scheme `scheme S = P<σ>:` with the line `construction derived(M)`, `M` a module bound to a
suite of the catalogue whose rows the vocabulary has, and the layout `zkc::layout::canonical`
(no `layout` line, or `layout canonical` without entries), is constructed here (§6.13, §7.8):

- the prover and the verifier are computed from the exchanges and the draws of the instance,
  through its applications, and a line `prover P` is checked against them (SC3);
- the statement is the inputs that both hold, in the order of the signature, and the witness
  the inputs that the prover holds alone; an input that the verifier holds alone is refused,
  and one marked `private` waits (SC4);
- every draw between the two is of the suite's challenge field (SC5): a draw of another law
  that the suite decodes (`nonzero` of it, `bool`, `index<n>`, a tuple or a collection) waits,
  and one of a law that it does not decode is refused;
- the package of the protocol instance is emitted with the suite's transcript and label types,
  a row that absorbs at each type the transcript absorbs (the statement's types and those of
  the prover's messages), a row that derives at each law drawn, and the rows of the layout,
  over bytes, with `put` and `take` at each message type. The declaration names them, its
  online roles are the two roles, and its suite carries the proof identity
  (`Zkc.Core.Raw.proofIdentity`);
- the core elaborates the package and constructs it: Fiat–Shamir, then serialize
  (`Zkc.Core.construct`). The constructed program is admitted as an emitted package is: its
  raw form is elaborated again, and its functions and protocols pass the check of facts. The
  core projects it to the programs of the prover and the verifier.

Every other line (`context`, `samples`, `commit`, `grind`, `retry`, `pin`, `offline`, `ideal`, a
`layout` with `carry` or `recover`, a layout other than `canonical`), a suite in source, the
constructions `interactive` and `authored`, and the generated members of a scheme (§8) wait,
with the reason.

After serialize the prover sends nothing: each role runs alone. The prover's program runs on
the statement and the witness, its samples answered by the sampler, and its first output is the
proof; the verifier's runs on the proof, its first input, and the statement, and accepts when
it returns (SC4).
-/

namespace Zkc.Frontend

open Instances
open Static
open Zkc.Core.Concrete (Datum)

namespace Scheme

/-! ## The flows of a protocol (SC3) -/

/-- An exchange, or a draw from its owner to one receiver, of a protocol instance, with the
roles mapped to those of the scheme's protocol; the type sent or drawn, the law's row of a draw,
and the site's name and line for messages. -/
structure Flow where
  draw : Bool
  source : Nat
  target : Nat
  type : ClosedType
  law : Option Typing.RowId := none
  name : String
  line : Nat
  deriving Inhabited

def siteName : Option Typing.SiteEntry → String
  | some entry => entry.name.getD s!"site{entry.event}"
  | none => "?"

def siteLine : Option Typing.SiteEntry → Nat
  | some entry => entry.place.startLine.toNat
  | none => 0

/-- The flows of a protocol instance, in order, through its applications, with the roles mapped
to those of the scheme's protocol. -/
partial def flowsOf (state : Compile.State) (code : Typing.ProtocolCode) (roleMap : Array Nat) :
    Array Flow :=
  code.flows.flatMap fun
    | .exchange sender receiver type site =>
      let entry := code.sites[site]?
      #[{ draw := false, source := roleMap.getD sender sender, target := roleMap.getD receiver receiver
          type, name := siteName entry, line := siteLine entry }]
    | .draw owner receivers law site =>
      let entry := code.sites[site]?
      let type := ((state.results.rows[law]?).bind (·.outputs[0]?)).getD .bool
      receivers.map fun receiver =>
        { draw := true, source := roleMap.getD owner owner, target := roleMap.getD receiver receiver
          type, law := some law, name := siteName entry, line := siteLine entry }
    | .apply callee calleeMap =>
      match state.results.body? callee with
      | some (.protocol inner) => flowsOf state inner (calleeMap.map fun role => roleMap.getD role role)
      | _ => #[]

/-- Why a scheme is not constructed. -/
inductive Stop where
  | refused (refusal : Diagnostic)
  | waiting (reason : String)
  | defect (message : String)
  /-- Emitted, and refused by the core. -/
  | core (reason : String) (package : Zkc.Core.Raw.Package)
  /-- The protocol is not checked to the end: a budget of the compiler ran out. -/
  | exhausted (exhaustion : Exhaustion)
  deriving Inhabited

abbrev SchemeM := Except Stop

def refuseAt {α : Type} (rule : String) (span : Syntax.Span) (message : String) : SchemeM α :=
  .error (.refused { origin := .emission, rule, span, message := .ofText message })

/-- The roles of a list, each once, in the order of first occurrence. -/
def distinct (roles : Array Nat) : Array Nat :=
  roles.foldl (init := #[]) fun seen role => if seen.contains role then seen else seen.push role

/-- The prover and the verifier (SC3): the role that sends to the other online role, or, when
none sends, the role that does not draw; a line `prover P` must name it. -/
def proverAndVerifier (scheme : SchemeEntry) (protocol : String) (code : Typing.ProtocolCode)
    (flows : Array Flow) : SchemeM (Nat × Nat) := do
  let roles := code.roles
  let name (role : Nat) : String := roles.getD role s!"role {role}"
  if roles.size != 2 then
    refuseAt "SC3" scheme.span s!"under `derived` exactly two roles are online; {", ".intercalate roles.toList} are online"
  let sends := flows.filter fun flow => !flow.draw && flow.source != flow.target
  let draws := flows.filter fun flow => flow.draw && flow.source != flow.target
  let senders := distinct (sends.map (·.source))
  let drawers := distinct (draws.map (·.source))
  let firstOf (flows : Array Flow) (role : Nat) : Flow := (flows.find? (·.source == role)).getD default
  if let #[first, second] := senders then
    let a := firstOf sends first
    let b := firstOf sends second
    refuseAt "SC3" scheme.span s!"under `derived` only the prover sends: {name first} sends `{a.name}` (line {a.line}) and {name second} sends `{b.name}` (line {b.line})"
  if let #[first, second] := drawers then
    let a := firstOf draws first
    let b := firstOf draws second
    refuseAt "SC3" scheme.span s!"under `derived` only the verifier draws: {name first} draws `{a.name}` (line {a.line}) and {name second} draws `{b.name}` (line {b.line})"
  if let (#[sender], #[drawer]) := (senders, drawers) then
    if sender == drawer then
      let m := firstOf sends sender
      let c := firstOf draws drawer
      refuseAt "SC3" scheme.span s!"{name sender} sends `{m.name}` (line {m.line}) and draws `{c.name}` (line {c.line}): the role that sends is the prover and the role that draws is the verifier, and under `derived` they differ"
  let computed : Option (Nat × String) :=
    match senders[0]?, drawers[0]? with
    | some sender, _ => some (sender, s!"{name sender} sends to the other online role, so the prover is {name sender}")
    | none, some drawer => some (1 - drawer, s!"{name drawer} draws, so the prover is {name (1 - drawer)}")
    | none, none => none
  let written := scheme.lines.findSome? fun
    | .prover span role => some (span, role)
    | _ => none
  match computed, written with
  | some (prover, why), some (span, role) =>
    if name prover != role.text then
      refuseAt "SC3" span s!"`prover {role.text}` contradicts the protocol: {why}"
    return (prover, 1 - prover)
  | some (prover, _), none => return (prover, 1 - prover)
  | none, some (span, role) =>
    match roles.findIdx? (· == role.text) with
    | some prover => return (prover, 1 - prover)
    | none => refuseAt "SC3" span s!"`prover {role.text}` names no role of `{protocol}`"
  | none, none =>
    refuseAt "SC3" scheme.span s!"cannot tell the prover from the verifier of `{protocol}`: no online role sends to the other and none draws; write `prover P`"

/-- The names of the ports of a protocol instance that are not `spec`, and whether each is
marked `private`. -/
def portsOf (state : Compile.State) (inst : InstanceId) : Array (String × Bool) :=
  match state.table.entries[inst]? with
  | some entry =>
    match state.program.declarations[entry.key.declaration]? with
    | some declaration =>
      match declaration.node with
      | .protocol node => node.head.ports.filterMap fun
        | .port _ name _ _ isPrivate => some (name.text, isPrivate)
        | _ => none
      | _ => #[]
    | none => #[]
  | none => #[]

/-- The statement and the witness (SC4): the ports held by both, in the order of the signature,
and the ports that the prover holds alone. -/
def statementAndWitness (scheme : SchemeEntry) (code : Typing.ProtocolCode)
    (ports : Array (String × Bool)) (prover verifier : Nat) : SchemeM (Array Nat × Array Nat) := do
  let mut statement := #[]
  let mut witness := #[]
  for port in [0:ports.size] do
    let holders := ((code.inputPorts.zip code.inputs).filter (·.1 == port)).map (·.2.2)
    let (name, isPrivate) := ports[port]!
    if holders.contains prover && holders.contains verifier then statement := statement.push port
    else if holders.contains verifier then
      if isPrivate then
        throw (.waiting s!"`{name}`, an input that the verifier holds alone: a `private` input is not constructed yet")
      refuseAt "SC4" scheme.span s!"`{name}` is held by {code.roles.getD verifier "?"} alone; under `construction derived` such an input is `private`"
    else if holders.contains prover then witness := witness.push port
  return (statement, witness)

/-- Whether the suite decodes a law (SC5): its challenge field, `nonzero` of it, `bool`,
`index<n>`, and tuples and sized collections of them. -/
partial def decodes (challenge : ClosedType) : ClosedType → Bool
  | .bool | .index _ => true
  | .nonzero field => Static.typeEq field challenge
  | .seq element (some _) => decodes challenge element
  | .tuple components _ => components.all (decodes challenge)
  | type => Static.typeEq type challenge

/-- Every draw between the prover and the verifier is of a law that the suite decodes (SC5); a
law other than the challenge field waits, since its decoder is not implemented. -/
def checkDraws (scheme : SchemeEntry) (state : Compile.State) (suite : String) (challenge : ClosedType)
    (flows : Array Flow) : SchemeM Unit := do
  for flow in flows do
    unless flow.draw && flow.source != flow.target do continue
    if Static.typeEq flow.type challenge then continue
    let law := renderType state flow.type
    if decodes challenge flow.type then
      throw (.waiting s!"`{flow.name}` draws a `{law}`: the decoders of the suite `{suite}` other than that of its challenge field are not implemented")
    refuseAt "SC5" scheme.span s!"`{flow.name}` draws a `{law}`; the suite `{suite}` decodes its challenge field `{renderType state challenge}`, `nonzero` of it, `bool`, `index<n>`, and tuples and sized collections of them. Draw units and apply a function"

/-! ## Emission -/

/-- The rows of the suite and of the layout, after the protocol instance, and the declaration
that names them, without the proof identity. -/
def emitDeclaration (root : InstanceId) (suite : String) (roles : Nat) (prover verifier : Nat)
    (absorbed messages : Array ClosedType) (laws : Array (Typing.RowId × ClosedType)) :
    Typing.EmitM Zkc.Core.Raw.Declaration := do
  let entry ← Emit.protocolOf root
  let row (name : String) (statics : Array Typing.RowStatic) : Typing.EmitM Nat := do
    match Typing.rowOf? { name, statics } with
    | some found => Typing.rowNumberOf found
    | none => throw (.waiting s!"the row `{name}` is not in the vocabulary at its static arguments")
  let state ← Typing.toTy (.nominal s!"{suite}.state" #[])
  let label ← match ← Typing.toTy (.nominal s!"{suite}.label" #[]) with
    | .nominal number => pure number
    | _ => Typing.defect "the label type of a suite is not a nominal type"
  let bytes ← Typing.toTy (.seq (.index 256) none)
  let start ← row s!"{suite}.start" #[]
  let absorbing ← absorbed.toList.mapM fun type => row s!"{suite}.absorb" #[.type type]
  let deriving_ ← laws.toList.mapM fun (law, type) => do
    return (← Typing.rowNumber law, ← row s!"{suite}.derive" #[.type type])
  let opening ← row "layout.canonical.open" #[]
  let closing ← row "layout.canonical.close" #[]
  let reading ← row "layout.canonical.read" #[]
  let exhausted ← row "layout.canonical.exhausted" #[]
  let putting ← messages.toList.mapM fun type => row "layout.canonical.put" #[.type type]
  let taking ← messages.toList.mapM fun type => row "layout.canonical.take" #[.type type]
  return { entry, prover, verifier, online := List.range roles
           suite := some (.catalogue state label start absorbing deriving_ [])
           layout := some { writer := bytes, reader := bytes, proof := bytes, start := opening
                            close := closing, read := reading, exhausted, putting, taking } }

/-- The types of a list, each once, in order. -/
def distinctTypes (types : Array ClosedType) : Array ClosedType :=
  types.foldl (init := #[]) fun seen type => if seen.any (Static.typeEq · type) then seen else seen.push type

end Scheme

/-! ## Constructed schemes -/

open Scheme in
/-- Constructs a scheme whose instance is typed. -/
def constructScheme (vocabulary : Vocabulary) (state : Compile.State) (scheme : SchemeEntry) :
    SchemeM Constructed := do
  if let .error reason := scheme.suite then throw (.waiting reason)
  if let some reason := scheme.waits then throw (.waiting reason)
  let .ok suite := scheme.suite | throw (.defect "no suite")
  let code ← match state.results.body? scheme.protocol with
    | some (.protocol code) => pure code
    | some (.waiting reason) => throw (.waiting reason)
    | some (.exhausted exhaustion) => throw (.exhausted exhaustion)
    | _ => throw (.defect "the protocol of the scheme has no code")
  if let some reason := code.waiting then throw (.waiting reason)
  let protocol := renderInstance state scheme.protocol
  -- the suite's rows and its challenge field
  unless (Zkc.Core.Vocabulary.table.row? s!"{suite}.start" []).isSome do
    throw (.waiting s!"the suite `{suite}` has no rows in the vocabulary that the construction applies")
  let some challenge := (vocabulary.module? suite).bind fun entry =>
      (entry.typeMembers.find? (·.1 == "Challenge")).map (·.2)
    | throw (.waiting s!"the suite `{suite}` has no challenge field")
  let flows := flowsOf state code (Array.range code.roles.size)
  let (prover, verifier) ← proverAndVerifier scheme protocol code flows
  let ports := portsOf state scheme.protocol
  let (statement, witness) ← statementAndWitness scheme code ports prover verifier
  checkDraws scheme state suite challenge flows
  -- the types absorbed: the statement's, and those of the prover's messages to the verifier
  let messages := distinctTypes ((flows.filter fun flow =>
    !flow.draw && flow.source == prover && flow.target == verifier).map (·.type))
  let statementTypes := statement.filterMap fun port =>
    ((code.inputPorts.zip code.inputs).find? (·.1 == port)).map (·.2.1)
  let absorbed := distinctTypes (statementTypes ++ messages)
  let laws := (flows.filter fun flow => flow.draw && flow.source != flow.target).foldl (init := #[])
    fun laws flow => match flow.law with
      | some law => if laws.any (·.1 == law) then laws else laws.push (law, flow.type)
      | none => laws
  let ({ package, claims }, declaration) ← match Typing.emitWith state
      (emitDeclaration scheme.protocol suite code.roles.size prover verifier absorbed messages laws) with
    | .ok emitted => pure emitted
    | .error (.waiting reason) | .error (.noCoreForm reason) => throw (.waiting reason)
    | .error (.defect message) => throw (.defect message)
  let identity := Zkc.Core.Raw.proofIdentity package declaration
  let declaration := declaration.withIdentity identity
  -- the core admits the package, constructs, and admits what each step returns
  let source ← match Zkc.Core.admit package claims.asWritten with
    | .ok source => pure source
    | .error refusals =>
      throw (.core s!"the core does not admit the package of the scheme: {reprStr refusals}" package)
  let construction ← match Zkc.Core.constructAdmitted source declaration with
    | .ok construction => pure construction
    | .error .stepped =>
      throw (.core "the core constructs a scheme on a program as written only" package)
    | .error (.step refusal) =>
      throw (.core s!"the core's construction refuses the scheme: {reprStr refusal}" package)
    | .error (.derived refusals) =>
      throw (.core s!"the core does not admit what the Fiat–Shamir step returns: {reprStr refusals}" package)
    | .error (.serialized refusals) =>
      throw (.core s!"the core does not admit what the serialize step returns: {reprStr refusals}" package)
  let projected : Except String Nat := do
    for role in [prover, verifier] do
      let _ ← Zkc.Core.Vocabulary.wholeEntry Zkc.Core.Vocabulary.table source.package source.typed
        construction.serialized.protocols construction.serialized.identities role
    return 2
  return { name := scheme.name, source, declaration, construction, identity, roles := code.roles
           prover, verifier, ports := ports.map (·.1), statement, witness
           inputPorts := code.inputPorts, projected }

namespace Constructed

/-- The data of the entry's inputs from the statement and the witness, one datum per port of
each, in the order of the signature. -/
def entryData (scheme : Constructed) (statement witness : List Datum) : List Datum :=
  scheme.inputPorts.toList.map fun port =>
    match scheme.statement.findIdx? (· == port), scheme.witness.findIdx? (· == port) with
    | some index, _ => statement.getD index default
    | none, some index => witness.getD index default
    | none, none => default

end Constructed

/-- Why the prover's program of a scheme gives no proof: the statement or the witness is not
taken, or the program does not return one; or a reading of a value reached the limit of the
run, so that the program was not run to its end. -/
inductive NoProof where
  | refused (message : String)
  | limit (elements : Nat)

def NoProof.describe : NoProof → String
  | .refused message => message
  | .limit elements => s!"a reading of a value reached the limit of {elements} elements"

instance : ToString NoProof := ⟨NoProof.describe⟩

end Zkc.Frontend

end

/- Proving and verifying a completed result are the only users of the programs of the prover and
the verifier: their bodies are not exposed, so that they may call them. -/
public section

namespace Zkc.Frontend

open Zkc.Core.Concrete (Datum)

namespace Constructed

/-- The inputs of the entry of the constructed program that a role holds, validated once at the
types of their ports, from the data of the entry's inputs (`entryData`): none for the proof, the
verifier's first input, and none for a port that the role does not hold. Or the name of the first
port that the role holds whose datum is not a value of its type. -/
def checkedInputs (scheme : Constructed) (role : Nat) (data : List Datum) :
    Except String (List (Option (Zkc.Core.Vocabulary.Checked Zkc.Core.Vocabulary.table scheme.package))) := do
  let some header := scheme.stepped.headers.head? | throw "the constructed program has no protocol"
  -- the proof is the first input of the entry, then the inputs of the protocol instance
  let ports := (header.inputs.drop 1).zip (data.zip scheme.inputPorts.toList)
  let inputs ← ports.mapM fun (port, datum, number) =>
    if port.holder != role then pure none
    else match Zkc.Core.Vocabulary.checked? Zkc.Core.Vocabulary.table scheme.package port.type datum with
      | some input => pure (some input)
      | none => throw (scheme.ports.getD number "?")
  return none :: inputs

/-- Runs the program of a role alone on validated inputs, its samples answered by the coins of a
seed (`Running.coins`), under the core's model of the vocabulary's rows with the
limit. -/
private def runRole (scheme : Constructed) (role : Nat)
    (inputs : List (Option (Zkc.Core.Vocabulary.Checked Zkc.Core.Vocabulary.table scheme.package)))
    (law : Option (Zkc.Core.Ty → Datum → Datum)) (seed : List Nat) :
    Except String (Zkc.Core.Execute.Outcome (List Datum)) :=
  Zkc.Core.Vocabulary.runRole Zkc.Core.Vocabulary.table scheme.package scheme.typed
    scheme.stepped.protocols scheme.stepped.identities role inputs
    (Running.coins scheme.package law seed)

/-- The proof of the prover's program on a statement and a witness, one datum per port of each,
validated at the types of their ports, its samples the values of their laws under the coins of
the seed (`Running.coins`) or under the law given. Only a completed result is proved
(`Completed.prove`). -/
private def prove (scheme : Constructed) (statement witness : List Datum) (seed : List Nat := [1])
    (law : Option (Zkc.Core.Ty → Datum → Datum) := none) : Except NoProof (List Nat) := do
  if statement.length != scheme.statement.size then
    throw (.refused s!"the statement has {scheme.statement.size} values, one per port: {", ".intercalate (scheme.statement.toList.map fun port => scheme.ports.getD port "?")}")
  if witness.length != scheme.witness.size then
    throw (.refused s!"the witness has {scheme.witness.size} values, one per port: {", ".intercalate (scheme.witness.toList.map fun port => scheme.ports.getD port "?")}")
  let inputs ← match scheme.checkedInputs scheme.prover (scheme.entryData statement witness) with
    | .ok inputs => pure inputs
    | .error name => throw (.refused s!"`{name}` is not a value of its type")
  match scheme.runRole scheme.prover inputs law seed with
  | .ok (.returned (proof :: _)) => return proof.toBytes
  | .ok (.limit elements) => throw (.limit elements)
  | .ok other => throw (.refused s!"the prover's program does not give a proof: {other.describe reprStr}")
  | .error message => throw (.refused s!"the prover's program does not run: {message}")

end Constructed

/-- The verifier's program of a scheme on a statement validated once, at the types of its ports,
for runs on proofs: a proof is bytes, which are values of their type, so a run on a proof
validates nothing again. Only a completed result makes one (`Completed.verifier`). -/
structure Verifier where
  private mk ::
  scheme : Constructed
  inputs : List (Option (Zkc.Core.Vocabulary.Checked Zkc.Core.Vocabulary.table scheme.package))

namespace Verifier

/-- The verifier's program on a proof: it accepts when it returns. -/
def verify (verifier : Verifier) (proof : List Nat) :
    Except String (Zkc.Core.Execute.Outcome (List Datum)) := do
  let some bytes := Zkc.Core.Vocabulary.asBytes (Datum.ofBytes proof) | throw "the proof is not bytes"
  let proofInput := Zkc.Core.Vocabulary.Checked.ofBytes Zkc.Core.Vocabulary.table
    verifier.scheme.package bytes
  verifier.scheme.runRole verifier.scheme.verifier (some proofInput :: verifier.inputs.drop 1)
    none [1]

end Verifier

namespace Completed

/-- The proof of the prover's program of a scheme that a completed result holds, on a statement
and a witness, one datum per port of each: see `Constructed.prove`. -/
def prove (completed : Completed Constructed) (name : String) (statement witness : List Datum)
    (seed : List Nat := [1]) (law : Option (Zkc.Core.Ty → Datum → Datum) := none) :
    Except NoProof (List Nat) := do
  let some scheme := completed.find? name
    | throw (.refused s!"the result does not hold the scheme {name}")
  scheme.prove statement witness seed law

/-- The verifier's program of a scheme that a completed result holds, on a statement, one datum
per port, validated once: run it on proofs with `Verifier.verify`. -/
def verifier (completed : Completed Constructed) (name : String) (statement : List Datum) :
    Except String Verifier := do
  let some scheme := completed.find? name | throw s!"the result does not hold the scheme {name}"
  if statement.length != scheme.statement.size then
    throw s!"the statement has {scheme.statement.size} values, one per port"
  let data := scheme.entryData statement (scheme.witness.toList.map fun _ => default)
  match scheme.checkedInputs scheme.verifier data with
  | .ok inputs => return { scheme, inputs }
  | .error _ => throw "a value of the statement is not a value of its type"

/-- The verifier's program of a scheme that a completed result holds, on a statement and a
proof: it accepts when it returns. -/
def verify (completed : Completed Constructed) (name : String) (statement : List Datum)
    (proof : List Nat) : Except String (Zkc.Core.Execute.Outcome (List Datum)) := do
  (← completed.verifier name statement).verify proof

end Completed

end Zkc.Frontend

end

@[expose] public section

namespace Zkc.Frontend

open Instances
open Static
open Zkc.Core.Concrete (Datum)

/-- The phase of schemes: every scheme of a typed program is constructed, or waits, or is refused
with a diagnostic; the reports in the order of the schemes. -/
def constructSchemes : CompileM Unit := do
  let state ← get
  let vocabulary ← getVocabulary
  let mut reports := #[]
  for scheme in state.schemes do
    let description := s!"scheme {scheme.name} = {renderInstance state scheme.protocol}"
    let outcome : SchemeOutcome := match constructScheme vocabulary state scheme with
      | .ok constructed => .constructed constructed
      | .error (.waiting reason) => .waiting reason
      | .error (.refused refusal) => .refused refusal
      | .error (.defect message) => .defect message
      | .error (.core reason package) => .refusedByCore reason package
      | .error (.exhausted exhaustion) => .exhausted exhaustion
    if let .refused refusal := outcome then
      modify fun state => { state with log := state.log.add refusal }
    reports := reports.push { name := scheme.name, description, outcome }
  modifyResults fun results => { results with schemeReports := reports }

end Zkc.Frontend
