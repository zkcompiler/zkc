import Zkc.Tools.Frontend.Names

/-!
# The typed trees of a program

`zkc-check trees` compiles a program and prints, per protocol instance, what became of its
body, and what the invariants of a typed tree find in the trees that the run holds. With
`--contents` it prints the trees.
-/

set_option autoImplicit false

namespace Zkc.Tools.Frontend.Trees

open Zkc.Frontend

/-- A refusal as a line: the rule, the place, the message. -/
def refusalLine (diagnostic : Diagnostic) : String :=
  s!"{diagnostic.rule} {diagnostic.span.startLine}:{diagnostic.span.startColumn} {diagnostic.message.render Renderer.plain}"

/-- A program after its compilation: its session, which holds the tree of every body. -/
structure ProgramTrees where
  session : Driver.Session

/-- Compiles a program. Refused names give no trees. -/
def treesOf (inputs : Array SourceInput) (load : Array String → IO (Option SourceInput)) :
    IO (Except String ProgramTrees) := do
  let names := inputs.map (·.name)
  let check ← checkNames inputs load
  if let some first := check.refusals[0]? then
    return .error s!"the names are refused: {first.span.file}: {first.render}"
  let schemes := checkSchemes (checkTyping (checkInstances check names) names)
  return .ok { session := schemes.session }

/-- The protocol instances of a program, each with what became of its body. -/
def protocolOutcomes (program : ProgramTrees) : Array (InstanceId × String × String) := Id.run do
  let state := program.session.state
  let mut found := #[]
  for index in [0:state.table.entries.size] do
    let entry := state.table.entries[index]!
    let some declaration := state.program.declarations[entry.key.declaration]? | continue
    unless declaration.kind == .protocol do continue
    let outcome := match state.results.body? index with
      | some (.protocol _) => "elaborated"
      | some .failed => "refused"
      | some (.waiting reason) => s!"waiting: {reason}"
      | some (.exhausted _) => "a budget ran out"
      | some _ => "no protocol"
      | none => "not typed"
    found := found.push (index, state.env.renderer.instance index, outcome)
  return found

/-- What the invariants of a typed tree find in the trees of a program that have no error
node. -/
def violationsOf (program : ProgramTrees) : Array String := Id.run do
  let state := program.session.state
  let mut lines := #[]
  for entry in state.results.trees.entries do
    let .done definition := entry.state | continue
    if definition.body.hasError then continue
    for violation in Passes.violations definition do
      lines := lines.push
        s!"{state.env.renderer.instance definition.instance}: {violation.span.file}:{violation.span.startLine}: {violation.message}"
  return lines

/-- `zkc-check trees --count`: the trees and nodes that a run holds. -/
def count (options : Names.Options) : IO UInt32 := do
  let inputs ← options.files.mapM Names.readInput
  let session ← Driver.Session.start.compile inputs
    (Names.libraryLoader options.libraries) "schemes"
  let trees := session.state.results.trees.entries
  let nodes := trees.foldl (init := 0) fun sum entry =>
    match entry.state with
    | .done definition => sum + definition.nodes
    | _ => sum
  IO.println s!"{session.state.table.entries.size} instances, {trees.size} trees, {nodes} nodes"
  return 0

def trees (options : Names.Options) : IO UInt32 := do
  let inputs ← options.files.mapM Names.readInput
  match ← treesOf inputs (Names.libraryLoader options.libraries) with
  | .error message =>
    IO.println message
    return 1
  | .ok program =>
    let results := program.session.state.results
    let renderer := program.session.state.env.renderer
    for refusal in (program.session.diagnosticsOf #["types", "default bodies"]).filter (·.isError) do
      IO.println s!"{refusal.span.file}: {refusalLine refusal}"
    for (inst, description, outcome) in protocolOutcomes program do
      IO.println s!"tree {description}: {outcome}"
      if options.contents then
        if let some entry := results.trees.entry? inst then
          if let .done definition := entry.state then
            IO.println (definition.print renderer)
    for line in violationsOf program do IO.println s!"  invariant: {line}"
    return 0

end Zkc.Tools.Frontend.Trees
