import Zkc.Frontend.Driver.SourcePhases
import Zkc.Frontend.Written.Selection

open Zkc.Frontend

namespace ProtocolViews

private def protocol := "protocol Sharing roles(P, V, W)(claim: bool @(P, V), secret: bool @P):
    hidden @P <- sample bool
    notice <- send secret to V, W
    challenge <- draw bool from V to P
"

private def functions := "def reveal(inputs: Sharing::Inputs<V>, coins: Sharing::Coins<V>) -> bool:
    return inputs.claim == coins.challenge
def transcript(received: Sharing::Received<W>) -> bool:
    return received.notice
def make_received(notice: bool) -> Sharing::Received<W>:
    return Sharing::Received<W>{notice}
def fork(runs: Sharing::Runs<2>) -> bool:
    return runs[1].challenge
"

/-- Compile source declarations, including their ordinary signatures and bodies. -/
private def compile (text : String) (context : Compile.Context := {vocabulary}) : Compile.State := Id.run do
  let file := "views.zkc"
  let source : SourceInput := ⟨file, Syntax.parseString file ("module views\n" ++ text)⟩
  let assembly := Id.run <| assemble #[source] fun _ => pure none
  let mut state : Compile.State := {}
  for phase in Driver.sourcePhases assembly do
    state := (phase.runIn context state).2
  return (Typing.typeProgram.run (Typing.withProtocolBodies context) state).2

private def describe (state : Compile.State) : String :=
  "\n".intercalate (state.log.entries.map (·.render state.env.renderer)).toList

/-- Identical clause text under two owners selects distinct declarations. Removing
the diagnostic projection must preserve the index, reference and local binder. -/
private def checkContractIdentity : IO Unit := do
  let part := "    relation R(p: bool; w: bool): p == w
    protocol Share roles(P, V)(p: bool @(P, V), w: bool @P):
        m <- send w to V
        c <- draw bool from V to P
    def pick(p: bool, runs: Share::Runs<2>) -> bool: p
    spec for Share:
        knowledge R(p) by pick
"
  let s := compile ("module left:\n" ++ part ++ "module right:\n" ++ part)
  if s.log.hasErrors then throw (IO.userError (describe s))
  let store : ModuleStore := { s.env.modules with records := s.env.modules.records.map fun (r : ModuleRecord) => {r with resolutions := {}} }
  let s : Compile.State := { s with env := {s.env with modules := {store with indexes := Instances.indexesOf store}} }
  let mut count := 0
  for (d, id) in s.program.declarations.zipIdx do
    unless d.kind == .protocol && s.program.nameOf id == "Share" do continue
    let .ok c := Written.clause s id none default | throw (IO.userError "contract depended on its source map")
    let some r := c.rel.declaration? | throw (IO.userError "missing relation")
    let some e := c.extractor.declaration? | throw (IO.userError "missing extractor")
    unless s.program.nameOf r == "R" && s.program.nameOf e == "pick" &&
        [r, e].all (fun i => s.program.declarations[i]!.namespace == d.namespace) do
      throw (IO.userError "clause selected a declaration from another owner")
    let #[.positional _ (.local _ 0)] := c.arguments | throw (IO.userError "wrong statement binder")
    count := count + 1
  unless count == 2 do throw (IO.userError "missing contract owner")

def check : IO Unit := do
  checkContractIdentity
  for source in [functions ++ protocol, protocol ++ functions] do
    let state := compile source
    if state.log.hasErrors then throw (IO.userError (describe state))
    for name in ["reveal", "transcript", "make_received", "fork"] do
      let some (_, decl) := state.program.declarations.zipIdx.find? (fun (d, _) => d.name.any (·.text == name))
        | throw (IO.userError s!"missing {name}")
      let some inst := state.results.instance? {declaration := decl, arguments := #[]}
        | throw (IO.userError s!"missing {name} instance")
      let some (.done code) := state.results.body? inst | throw (IO.userError s!"unfinished {name}")
      if code.waiting.isSome then throw (IO.userError s!"pending {name}: {code.waiting}")
    let some (_, decl) := state.program.declarations.zipIdx.find? (fun (d, _) => d.name.any (·.text == "Sharing"))
      | throw (IO.userError "missing protocol")
    let some inst := state.results.instance? {declaration := decl, arguments := #[]} | throw (IO.userError "missing instance")
    let port := Typed.ViewOrigin.port
    let event := Typed.ViewOrigin.event
    for (view, expected) in [
        (ProtocolView.run, [("notice", event 1), ("challenge", event 2)]),
        (.inputs "V", [("claim", port 0)]), (.inputs "P", [("claim", port 0), ("secret", port 1)]),
        (.received "P", [("challenge", event 2)]), (.received "V", [("notice", event 1)]), (.received "W", [("notice", event 1)]),
        (.coins "V", [("challenge", event 2)]), (.coins "P", [("hidden", event 0)]), (.coins "W", [])] do
      let getFields := do Static.nominalViewFields (← Static.protocolViewRecord inst view default)
      let (.ok fields, _) := getFields.run {vocabulary} state
        | throw (IO.userError s!"missing {view.member}")
      unless fields.toList.map (fun f => (f.name, f.origin)) == expected && fields.all (·.type == .bool) do throw (IO.userError s!"incorrect fields of {view.member}")
  for (bad, reason) in [
      (functions.replace "inputs.claim" "inputs.secret", "has no field"),
      (functions.replace "coins.challenge" "coins.hidden", "has no field"),
      (functions.replace "received.notice" "received.challenge", "has no field"),
      (functions.replace "Runs<2>" "Runs<3>", "outside the draw domain"),
      (functions.replace "Runs<2>" "Runs<2, 2>", "one multiplicity"),
      (functions.replace "Runs<2>" "Runs<0>", "outside the draw domain"),
      (functions ++ "def swap(x: Sharing::Inputs<W>) -> Sharing::Coins<W>: x\n", "Coins<W>")] do
    let state := compile (bad ++ protocol)
    unless state.log.hasErrors && (describe state).contains reason do
      throw (IO.userError s!"expected {reason}, found {describe state}")

  let nested := compile (functions ++ protocol.replace "    challenge <- draw bool from V to P"
    "    for i in 0..2:\n        challenge <- draw bool from V to P")
  unless nested.log.entries.any (fun d => d.isError && d.rule == "SX9") do
    throw (IO.userError s!"a uniform loop was accepted as a fixed-depth fork: {describe nested}")

  -- A view that never observes the nested site keeps its ordinary schema. The owner
  -- of the coins still needs a collection, including when the loop has no iterations.
  for count in [0, 2] do
    let hidden := protocol.replace "    hidden @P <- sample bool"
      s!"    for i in 0..{count}:\n        hidden @P <- sample bool"
    let state := compile (hidden ++ functions)
    if state.log.entries.any (fun d => d.isError || d.isIncomplete) then throw (IO.userError (describe state))
    let some (_, decl) := state.program.declarations.zipIdx.find? (fun (d, _) => d.name.any (·.text == "Sharing"))
      | throw (IO.userError "missing private-loop protocol")
    let some inst := state.results.instance? {declaration := decl, arguments := #[]}
      | throw (IO.userError "missing private-loop instance")
    for (view, selectors) in [(ProtocolView.run, ["notice", "challenge"]), (.received "W", ["notice"]),
        (.coins "V", ["challenge"]), (.coins "W", [])] do
      let (.ok fields, _) := (Static.protocolViewFields inst view default).run {vocabulary} state
        | throw (IO.userError s!"private loop blocked {view.member}")
      unless fields.toList.map (·.name) == selectors do throw (IO.userError s!"incorrect {view.member}")
    let (.error (.waiting why), _) := (Static.protocolViewFields inst (.coins "P") default).run {vocabulary} state
      | throw (IO.userError "private loop lost the owner's coin field")
    unless why.render.contains "hidden" do throw (IO.userError why.render)

  -- The ordinary frontend checks each clause in its own role, even without a scheme.
  let contract := "spec for Sharing:\n    proves @P secret_check: secret == secret\n"
  for (text, valid) in [(contract, true), (contract.replace "@P" "@V", false),
      (contract.replace "@P " "", true), ((contract.replace "@P " "").replace "secret == secret" "claim == claim", false)] do
    let state := compile (protocol ++ text)
    let rejected := state.log.entries.any (fun d => d.isError && d.rule == "SX6")
    unless rejected == !valid && state.log.hasErrors == !valid do throw (IO.userError (describe state))

  for extra in [contract, "module other:\n    spec for Sharing:\n        requires true\n"] do
    let state := compile (protocol ++ contract ++ extra)
    unless state.log.entries.any (fun d => d.isError && d.rule == "SX5") do
      throw (IO.userError s!"expected ordinary contract ownership refusal: {describe state}")

  let reduction := "protocol Deliver roles(P, V)(spec tag: bool, x: bool @(P, V)) -> result: bool @P:
    return x
spec for Deliver:
    reduces (tag == x) to (result == result)
"
  for (source, valid) in [(reduction, true), (reduction.replace "reduces (" "reduces @V (", false)] do
    let state := compile source
    unless state.log.hasErrors == !valid && state.log.entries.any (fun d => d.rule == "SX6") == !valid do
      throw (IO.userError s!"incorrect deciding role for a reduced result: {describe state}")

  -- Both nominal records are first requested inside discarded typing. Collection order is
  -- reversed relative to declaration order, so their rebuilt instance numbers may differ.
  let one := "    for i in 0..0 collect (ys = Sharing::Inputs<V>{claim = true}):
        x = 0
    w: [Sharing::Inputs<V>; 0] = ys
"
  let reversed := "    for i in 0..0 collect (forV = verifier, forP = prover):
        prover = Sharing::Inputs<P>{claim = true, secret = false}
        verifier = Sharing::Received<V>{notice = true}
    a: [Sharing::Received<V>; 0] = forV
    b: [Sharing::Inputs<P>; 0] = forP
"
  for body in [one, reversed] do
    let cold := compile ("def cold() -> nat:\n" ++ body ++ "    return 0\n" ++ protocol)
    if cold.log.hasErrors then throw (IO.userError (describe cold))
    let some (_, decl) := cold.program.declarations.zipIdx.find? (fun (d, _) => d.name.any (·.text == "cold"))
      | throw (IO.userError "missing empty collect function")
    let some id := cold.results.instance? {declaration := decl, arguments := #[]}
      | throw (IO.userError "missing empty collect instance")
    let some (.done code) := cold.results.body? id | throw (IO.userError "unfinished empty collect")
    if let some why := code.waiting then throw (IO.userError s!"empty collect waiting: {why}")

  -- The leaf budget measures the actual fork. Its draw domain can be vastly larger.
  let large := "protocol Draw roles(P, V)():
    c <- draw [bool; 131072] from V to P
def large(runs: Draw::Runs<2>) -> bool: true
"
  let bounded := compile large {vocabulary, options := {budgets := {staticEvaluation := 100}}}
  if bounded.log.entries.any (fun d => d.isError || d.isIncomplete) then
    throw (IO.userError (describe bounded))
  let some (_, f) := bounded.program.declarations.zipIdx.find? (fun (d, _) => d.name.any (·.text == "large"))
    | throw (IO.userError "missing large-domain fork reader")
  let some id := bounded.results.instance? {declaration := f, arguments := #[]}
    | throw (IO.userError "missing large-domain fork reader instance")
  let some (.done code) := bounded.results.body? id | throw (IO.userError "unfinished large-domain fork reader")
  if let some why := code.waiting then throw (IO.userError why)

  for (type, limit, cardinality) in ([
      (.bool, 0, 0), (.bool, 9, 2), (.index 0, 1, 0),
      (.seq (.index 0) (some 0), 2, 1), (.seq (.index 0) (some 5), 1, 0),
      (.seq .bool (some 7), 1000, 128), (.seq .bool (some 7), 127, 127),
      (.tuple #[] #[], 2, 1), (.tuple #[.bool, .index 0] #[], 1, 0),
      (.nonzero (.index 0), 1, 0), (.nonzero (.index 4), 4, 3),
      (.nonzero (.index 4), 2, 2)] : List (ClosedType × Nat × Nat)) do
    let (.ok actual, _) := (Static.viewLawCapacity type limit).run {vocabulary} {}
      | throw (IO.userError "could not check a supported draw capacity")
    unless actual == cardinality do throw (IO.userError s!"expected capacity {cardinality}, got {actual}")

  let twoDraws := "protocol Two roles(P, V)():\n    a <- draw bool from V to P\n    b <- draw bool from V to P\n"
  let reader := "def read(r: Two::Runs<2, 2>) -> bool: r[3].b\n"
  let ready := compile (reader ++ twoDraws)
  if ready.log.hasErrors then throw (IO.userError (describe ready))
  let mixed := compile ((reader.replace "2, 2" "1, 2") ++ twoDraws)
  unless mixed.log.hasErrors && (describe mixed).contains "all exceed one" do
    throw (IO.userError s!"accepted a mixed rewind shape: {describe mixed}")

end ProtocolViews

def main : IO Unit := ProtocolViews.check
