import Lean

/-! Exact module lookup for standalone audit tools.

Lake passes a full module-to-artifact map to Lean. Standalone `importModules`
otherwise uses first-component lookup, which cannot distinguish packages with
exclusive roots such as `Zkc.Program` and `Zkc.IR`. Build the same kind of map
from the selected Lake search path, keeping every private proof and IR part.
Distinct physical providers of one module are refused, not ordered by priority.
-/

namespace ZkcTools.ImportArtifacts
open Lean System

/-- Discover all built modules in the current package environment. Repeated paths
through symlinks denote one provider; distinct providers are an ambiguity. -/
def collect : IO (NameMap Lean.ImportArtifacts) := do
  let mut result : NameMap Lean.ImportArtifacts := {}
  let mut visited : Std.HashSet FilePath := {}
  for root in ← searchPathRef.get do
    unless ← root.isDir do continue
    let root ← IO.FS.realPath root
    if visited.contains root then continue
    visited := visited.insert root
    for path in ← root.walkDir do
      unless path.extension == some "olean" do continue
      let module := ((path.withExtension "").components.drop root.components.length).foldl
        Name.str Name.anonymous
      let path ← IO.FS.realPath path
      if let some previous := result.find? module then
        unless previous.olean? == some path do
          throw <| IO.userError s!"ambiguous module provider: {module}: {previous.olean?} and {path}"
        continue
      let server := path.withExtension "olean.server"
      let priv := path.withExtension "olean.private"
      let hasServer ← server.pathExists
      let hasPrivate ← priv.pathExists
      unless hasServer == hasPrivate do
        throw <| IO.userError s!"incomplete private module artifacts: {module}"
      let parts := if hasServer then #[path, server, priv] else #[path]
      let signature := path.withExtension "ir.sig"
      let ir := path.withExtension "ir"
      let irParts ← if ← signature.pathExists then do
          unless ← ir.pathExists do
            throw <| IO.userError s!"missing interpreter artifact: {module}"
          pure #[signature, ir]
        else pure #[]
      result := result.insert module ⟨#[parts, irParts]⟩
  return result

end ZkcTools.ImportArtifacts
