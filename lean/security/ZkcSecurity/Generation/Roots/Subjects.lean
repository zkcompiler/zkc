module

public import ZkcSecurity.Generation.Roots.Catalogue
public meta import ZkcSecurity.Generation.Roots.Catalogue
public meta import ZkcSecurity.Generation.Roots.ExportMetadata

@[expose] public section

/-! Subject and alias generation uses the production catalogue. Test modules
are executable drivers only because this library requires the module system. -/
namespace ZkcSecurity.Generation.Roots
open ZkcTools.StructuredSource.Root

run_cmd do
  let mut sources : List (String × String) := []
  let mut imports : List String := []
  for root in ← evaluateSelections do
    let [(_, original, producer, validator)] := exportDigests.filter (fun row => row.1 == root.name)
      | Lean.throwError "root-missing-export-metadata"
    let aliases := root.componentModule "Sources"
    let aliasSource ← match sourceAliasSource aliases root.sourceModule root.snapshot root.helpers with
      | .ok source => pure source
      | .error reason => Lean.throwError reason
    let output ← match subjectOutput root original producer validator with
      | .ok output => pure { output with sourceModule := aliases, originalExpression := aliases ++ ".original", importedExpression := aliases ++ ".imported" }
      | .error reason => Lean.throwError reason
    sources := sources ++ [(aliases, aliasSource), (root.subjectModule, fixedSubjectSource output)]
    imports := imports ++ ["public import " ++ root.subjectModule]
  let importSource := "module\n\n" ++ "\n".intercalate imports ++
    "\n\n/-! Generated catalogue imports for downstream production generation. -/\n"
  sources := sources ++ [("ZkcSecurity.Generation.Roots.SubjectImports", importSource)]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `subjectSources) : List (String × String) := $(Lean.quote sources)))

def generateSubjects (args : List String) : IO Unit := do
  match args with
  | ["--manifest"] => IO.println catalogueManifest
  | [directory] => writeSources directory subjectSources
  | _ => throw (IO.userError "expected output directory or --manifest")

end ZkcSecurity.Generation.Roots
