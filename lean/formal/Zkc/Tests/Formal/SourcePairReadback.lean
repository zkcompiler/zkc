import Zkc.Tests.Formal.SourcePairMembers
import Zkc.Frontend.Emit.Named
import Zkc.Frontend.Typed.Number
import Zkc.Frontend.Elab.Protocol
import Zkc.Frontend.Syntax.Parser
import Zkc.Frontend.Driver.SourcePhases
import Zkc.Frontend.Semantics.VocabularyTable
open Zkc.Frontend
open Zkc.Core
open Zkc.Tests.Formal.SourcePairMembers (certify sourceRows)

namespace Zkc.Tests.Formal.SourcePairReadback

inductive Variant where
  | original | rename | affine | reversed
  deriving DecidableEq, Repr

def source (variant : Variant) (path : System.FilePath) : IO SourceInput := do
  let data ← IO.FS.readBinFile path
  if path.fileName != some "sumcheck.zkc" || variant = .original then
    return ⟨path.toString, Syntax.parse path.toString data⟩
  let original := "def evaluate(m, r): (1 - r) * m.0 + r * m.1"
  let replacement := match variant with
    | .original => original
    | .rename => "def evaluate(pair, point): (1 - point) * pair.0 + point * pair.1"
    | .affine => "def evaluate(m, r): m.0 + r * (m.1 - m.0)"
    | .reversed => "def evaluate(m, r): m.0 + r * (m.0 - m.1)"
  let some text := String.fromUTF8? data | throw (IO.userError "invalid UTF-8 in Sumcheck source")
  unless (text.splitOn original).length == 2 do throw (IO.userError "the evaluation control requires exactly one source occurrence")
  return ⟨path.toString, Syntax.parseString path.toString (text.replace original replacement)⟩

def loadModule (root : System.FilePath) (variant : Variant) (segments : Array String) : IO (Option SourceInput) := do
  let file := (String.intercalate "/" segments.toList) ++ ".zkc"
  for base in ["libraries", "examples", "examples/support"] do
    let path := root / base / file
    if ← path.pathExists then return some (← source variant path)
  return none

open Static

private def members : CompileM (Array (String × InstanceId × ClosedType × Typed.FunctionBody)) := do
  let s ← get
  let #[root] := s.roots | throw (.defect "missing Sumcheck root")
  let some entry := s.table.entries[root]? | throw .abandoned
  let some field := entry.key.arguments[0]? | throw .abandoned
  let some ns := s.program.declarations[entry.key.declaration]? | throw .abandoned
  let some (.declaration pairs) := s.program.namespaces[ns.namespace]!.names["Pairs"]? | throw .abandoned
  let instanceId ← instantiate pairs #[field] ⟨"Pairs from Sumcheck", default⟩
  let some inner := s.program.declarations[pairs]!.inner | throw .abandoned
  let mut out := #[]
  for member in #["boundary", "evaluate"] do
    let some (.declaration id) := s.program.namespaces[inner]!.names[member]? | throw .abandoned
    let found := s.program.declarations[id]!
    let some lowered := s.env.modules.lowered? id | throw .abandoned
    let .memberDefinition binders (.body expression) := lowered.content | throw .abandoned
    let callee ← instantiate id #[field] ⟨member, default⟩
    let context : Elab.Context := { env := instanceEnv s.program found #[field], «instance» := callee, name := member }
    let ((tree, result), _) ← Elab.runElab context lowered.locals do
      let (ins, result) ← Elab.memberSignature instanceId member
      unless ins.size == binders.size do throw (.defect "member arity")
      return (← Elab.elabFunctionBody (binders.zip ins) result expression, result)
    out := out.push (member, callee, result, tree)
  return out

private def definitions (b : Zkc.Vocabulary.Project.Bindings) (s : Compile.State)
    (trees : Array (String × InstanceId × ClosedType × Typed.FunctionBody)) : IO (Array (Definition b.vocabulary)) := do
  let context : Emit.Named.Context b := { callees := default, apply := fun i _ _ => Typing.defect s!"unexpected function call {i}" }
  trees.mapM fun (name, id, out, tree) => do
    if (Typed.Body.function tree).hasError then throw (IO.userError s!"error node in {name}")
    let .function numbered := (Typed.Body.function tree).numbered.1 | throw (IO.userError s!"expected a function for {name}")
    match (Emit.Named.functionDefinition context ⟨id⟩ out numbered).run s with
    | .error failure => throw (IO.userError s!"emitting {name}: {repr failure}")
    | .ok (definition, _) => pure definition

private def checkLinked (s : Compile.State) (trees : Array (String × InstanceId × ClosedType × Typed.FunctionBody))
    (interpolation affine : Bool) : IO Unit := do
  let .ok bindings := ({} : Zkc.Vocabulary.Project.Bindings).insert ⟨"test.unit", .nil⟩ ⟨[], []⟩
    | throw (IO.userError "conflicting test primitive")
  let #[boundary, evaluate] ← definitions bindings s trees | throw (IO.userError "expected two members")
  let fresh := max boundary.key.number evaluate.key.number + 1
  let protocol (k : Nat) : Definition bindings.vocabulary := .protocol ⟨k⟩ 1 [] [] (.mk [] [] [])
  let identity : Definition bindings.vocabulary := .fn ⟨fresh+1⟩ [.nat] [.nat] false none ⟨[],[]⟩ (.mk [0] [] [0])
  let package : SourcePackage := ⟨bindings,⟨[protocol fresh, evaluate, identity, boundary, protocol (fresh+2)]⟩,
    ⟨[],[],[],[],[]⟩⟩
  let .ok evidence := package.checkEvidence | throw (IO.userError "mixed program refused")
  let rows := sourceRows bindings
  let program := evidence.admitted.program
  let canonical := rows.locateMembers program boundary.key evaluate.key (rows.evaluationReadback evaluate.key)
  let alternate := rows.locateMembers program boundary.key evaluate.key (rows.affineReadback evaluate.key)
  let wrong := rows.locateMembers program ⟨fresh+1⟩ evaluate.key (rows.evaluationReadback evaluate.key)
  unless canonical.isSome == interpolation && alternate.isSome == affine && wrong.isNone do
    throw (IO.userError "unexpected certificate for a member of the mixed program")

/-- Open the real example and its imports, elaborate the two Round members at their
instantiated interface, emit both definitions and check the independently proved meanings.
The controlled edits apply to the imported source in memory. -/
def check (root : System.FilePath) (variant : Variant) : IO Unit := do
  let entry ← source variant (root / "examples/sumcheck_example.zkc")
  let assembly ← assemble #[entry] (loadModule root variant)
  let mut state : Compile.State := {}
  for phase in Driver.sourcePhases assembly do
    let (report, next) := phase.runIn { vocabulary } state
    if let some reason := report.interrupted then throw (IO.userError s!"{phase.name}: {reason}")
    state := next
  let (result, finalState) := members.run { vocabulary } state
  unless !finalState.log.hasErrors && !finalState.log.hasIncomplete do
    let messages := finalState.log.entries.map fun e => s!"{e.rule} {Message.render Renderer.plain e.message}"
    throw (IO.userError ("source elaboration failed\n" ++ String.intercalate "\n" messages.toList))
  let .ok trees := result | throw (IO.userError "source member elaboration interrupted")
  let b : Zkc.Vocabulary.Project.Bindings := {}
  let defs ← definitions b finalState trees
  let #[boundary, evaluate] := defs | throw (IO.userError "expected two members")
  let package : SourcePackage := ⟨b, ⟨defs.toList⟩, ⟨[], [], [], [], []⟩⟩
  let .ok evidence := package.checkEvidence | throw (IO.userError "Core admission refused the emitted definitions")
  let interpolation := (certify .interpolation evidence.accepted boundary.key evaluate.key).isSome
  let affine := (certify .affine evidence.accepted boundary.key evaluate.key).isSome
  unless interpolation == (variant == .original || variant == .rename) && affine == (variant == .affine) do
    throw (IO.userError s!"unexpected certificate result for {repr variant}")
  checkLinked finalState trees interpolation affine
  IO.println s!"{repr variant}: standalone and mixed programs admitted; interpolation={interpolation}, affine={affine}"

def checkAll (root : System.FilePath) : IO Unit :=
  [.original, .rename, .affine, .reversed].forM (check root)

end Zkc.Tests.Formal.SourcePairReadback
