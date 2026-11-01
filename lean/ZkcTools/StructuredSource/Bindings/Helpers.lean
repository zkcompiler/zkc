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

/-- Require exactly one candidate. Neither ordering nor a name breaks ties. -/
def uniqueCandidate {α : Type} (reason : String) (candidates : List α) : Except String α :=
  match candidates with
  | [candidate] => pure candidate
  | _ => throw reason

/-- Select by an ordinary predicate on the existing checked definition. This
is retrieval only; every installed candidate still needs its body equation. -/
def uniqueHelperWhere (program : Program) (predicate : CheckedDefinition → Bool) :
    Except String (CheckedDefinition × Nat) :=
  uniqueCandidate "helper-association-ambiguous-or-missing"
    (program.payload.definitions.zipIdx.filter fun (definition, _) => predicate definition)

/-- Resolve a complete helper reference, including its kind and ordered ABI. -/
def helperIndex (program : Program) (helper : Helper) : Except String Nat := do
  return (← uniqueHelperWhere program (·.helper == helper)).2

/-- Keep actual direct call occurrences in source order, including duplicates.
Unlike dependency closure, this can distinguish two placements of one helper. -/
def helperOccurrences (helpers : List Helper) (kind : HelperKind) (inputs outputs : List Ty) :
    List Helper :=
  helpers.filter fun helper => helper.kind == kind && helper.inputs == inputs && helper.outputs == outputs

/-- Retrieve a single primitive body, ignoring observation markers only. The
generated template still retains those markers and the exact operand routing. -/
def singlePrimitive (definition : CheckedDefinition) (primitive : Primitive) : Bool :=
  match definition.raw.operations.filter (fun | .mark _ => false | _ => true) with
  | [.exec found] => found == primitive
  | _ => false

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

/-- Expose the actual checked body rather than an independently owned template.
The invocation equation retains the complete results and all stops. -/
def helperBodySource (program : Program) (name : String) (index : Nat) : Except String String := do
  let some definition := program.payload.definitions[index]? | throw "helper-association-index"
  return "abbrev " ++ name ++ "Definition : CheckedDefinition := payload.definitions.get ⟨" ++
    toString index ++ ", by decide +kernel⟩\n" ++
    "abbrev " ++ name ++ "Helper := " ++ name ++ "Definition.helper\n" ++
    "theorem " ++ name ++ "_body (args : Values (assignment F G) " ++ name ++ "Helper.inputs) :\n" ++
    "    invoke (closedMeanings payload.definitions) " ++ name ++ "Helper args =\n" ++
    "      " ++ name ++ "Definition.body.denote (meaning F G (closedMeanings payload.definitions)) args.get :=\n" ++
    "  Evaluation.definitions_invoke_body_view_as SiteObservations.closed payload.definitions payload.linked\n" ++
    "    " ++ name ++ "Definition (List.get_mem _ _) " ++ helperText definition.helper ++ " rfl " ++
    name ++ "Definition.body rfl args\n\n"

/-- A checked table alias used by generated seams. It asserts no body law. -/
def helperAliasSource (program : Program) (name : String) (index : Nat) : Except String String := do
  let some _ := program.payload.definitions[index]? | throw "helper-association-index"
  return "abbrev " ++ name ++ "Definition : CheckedDefinition := payload.definitions.get ⟨" ++
    toString index ++ ", by decide +kernel⟩\nabbrev " ++ name ++ "Helper := " ++ name ++ "Definition.helper\n\n"

end ZkcTools.StructuredSource.Bindings
