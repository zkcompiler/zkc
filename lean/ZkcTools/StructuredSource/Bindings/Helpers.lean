module

public import ZkcTools.StructuredSource.Bindings.Generate

@[expose] public section

/-! Candidate selection and complete helper-body association. Selection has no
semantic authority: emitted equations check the full signature, body and
operand order against the admitted helper table. -/
namespace ZkcTools.StructuredSource.Bindings
open Zkc.Source Zkc.Source.Structured
open ZkcTools.StructuredSource.Presentation

/-- Follow actual edges in the admitted dependency order. -/
def helperDependsOn (program : Program) (parent candidate : Helper) : Bool :=
  let reachable := program.payload.definitions.foldl (fun found definition =>
    if definition.helper == candidate || definition.helpers.any found.contains then
      definition.helper :: found
    else found) []
  reachable.contains parent

/-- A complete candidate signature, optionally restricted to an actual
ancestor's dependency closure. Ambiguity is an error. -/
def uniqueHelper (program : Program) (kind : HelperKind) (inputs outputs : List Ty)
    (within : Option CheckedDefinition := none) : Except String (CheckedDefinition × Nat) := do
  let [(definition, index)] := program.payload.definitions.zipIdx.filter (fun (definition, _) =>
    definition.kind == kind && definition.inputs == inputs && definition.outputs == outputs &&
      (within.map (fun parent => helperDependsOn program parent.helper definition.helper)).getD true)
    | throw "helper-association-ambiguous-or-missing"
  pure (definition, index)

/-- The import identity and declaration namespace of reusable helper templates. -/
structure HelperTemplateOutput where
  moduleName : String
  namespaceName : String

/-- Print a source-template body without selecting a closed payload. -/
def helperTemplateSource (program : Program) (name : String) (index : Nat) : Except String String := do
  let some definition := program.payload.definitions[index]? | throw "helper-association-index"
  let mut text := "abbrev " ++ name ++ "Helper : Helper := " ++ helperText definition.helper ++ "\n" ++
    "def " ++ name ++ "Body : Region dialect " ++ name ++ "Helper.inputs " ++ name ++
    "Helper.outputs :=\n  " ++ helperRegionText definition.body ++ "\n"
  if let [.collect spec] := definition.raw.operations then
    text := text ++ "abbrev " ++ name ++ "Collection : CollectSpec :=\n  " ++ collectText spec ++ "\n"
  pure (text ++ "\n")

/-- Associate an imported template with the actual checked helper table.
The emitted equality checks the complete signature, body and operand order. -/
def helperAssociationText (program : Program) (name : String) (index : Nat)
    (table observations template : String) : Except String String := do
  let some definition := program.payload.definitions[index]? | throw "helper-association-index"
  pure ("abbrev " ++ name ++ "Definition : CheckedDefinition := payload.definitions.get ⟨" ++
    toString index ++ ", by decide +kernel⟩\n" ++ template ++
    "theorem " ++ name ++ "_closed (args : Values (assignment F G) " ++ name ++ "Helper.inputs) :\n" ++
    "    invoke " ++ paren table ++ " " ++ name ++ "Helper args =\n" ++
    "      " ++ name ++ "Body.denote (Evaluation.meaning " ++ paren observations ++ " " ++ paren table ++ ") args.get :=\n" ++
    "  Evaluation.definitions_invoke_body_view_as " ++ paren observations ++ " payload.definitions payload.linked\n" ++
    "    " ++ name ++ "Definition (List.get_mem _ _) " ++ helperText definition.helper ++ " rfl " ++
    name ++ "Body rfl args\n\n")
/-- A closed application imports its template from the reusable owner. -/
def helperAssociationSource (program : Program) (name : String) (index : Nat)
    (table observations : String) : Except String String :=
  helperAssociationText program name index table observations ""

/-- A source view that owns its literal template prints both the template and
its checked association. Both forms share the same association printer. -/
def helperTemplateAssociationSource (program : Program) (name : String) (index : Nat)
    (table observations : String) : Except String String := do
  let template ← helperTemplateSource program name index
  helperAssociationText program name index table observations (template.dropEnd 1).toString

end ZkcTools.StructuredSource.Bindings
