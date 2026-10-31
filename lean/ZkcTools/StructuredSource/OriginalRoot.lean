module

public import ZkcTools.StructuredSource.Bindings.Generate
public import ZkcTools.StructuredSource.LibraryAssociation
public import ZkcTools.StructuredSource.Root
public import Zkc.Source.Structured.Bindings.Template

@[expose] public section

/-! Generic root templates over the existing typed normalizer. Installations
supply exact nominal metadata and laws for the actual helper table and immutable
protocol capture. Protocol family mathematics and representation-specific source
printers belong to ordinary method extensions. -/
set_option autoImplicit false
namespace ZkcTools.StructuredSource.OriginalRoot
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open ZkcTools.StructuredSource.Presentation

/-- A complete signature has exactly one source catalogue association. -/
def uniqueIndex {α : Type} [BEq α] (candidates : List α) (selected : α) : Except String Nat := do
  let [(_, index)] := candidates.zipIdx.filter (fun pair => pair.1 == selected)
    | throw "original-root-unique-association"
  return index

/-- Selection for the same checked source/normal-form boundary at an arbitrary
nominal model. Mathematical helper results remain indexed checked arguments. -/
structure TemplateOutput where
  moduleName : String
  namespaceName : String := moduleName
  sourceModule : String
  programExpression : String
  definitionIndex : Nat
  role : Nat
  signature : Signature

/-- Emit a dependent template, never a name-only certificate. This uses the
same normalizer as structural root generation and supports mixed carriers.
The emitted theorem is generic in the actual helper table and immutable
protocol capture; their laws cannot be replaced by selection strings. -/
def templateSource (program : Program) (output : TemplateOutput) : Except String String := do
  let some definition := program.payload.protocols[output.definitionIndex]?
    | throw "original-root-template-definition"
  unless output.role < definition.roles.length do throw "original-root-template-role"
  let form ← (normalize output.signature definition.body output.role definition.roles.length
    (Bindings.optionalPattern definition.inputs)).mapError (fun reason => "original-root-template-" ++ reason)
  unless NormalForms.callsMatch form do throw "original-root-template-calls"
  return "module\n\npublic import " ++ output.sourceModule ++
    "\npublic import Zkc.Source.Structured.Bindings.Template\n\n@[expose] public section\n" ++
    "namespace " ++ output.namespaceName ++
    "\nopen Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings\n" ++
    "set_option maxRecDepth 50000\nset_option maxHeartbeats 8000000\nnoncomputable section\n" ++
    "abbrev program : Program := " ++ output.programExpression ++ "\n" ++
    "abbrev definition : CheckedProtocol := program.payload.protocols.get ⟨" ++
      toString output.definitionIndex ++ ", by decide +kernel⟩\n" ++
    "theorem definition_member : definition ∈ program.payload.protocols := List.get_mem _ _\n" ++
    "def signature : Signature := ⟨" ++ listText (output.signature.laws.map lawText) ++ ", " ++
      boolText output.signature.strict ++ ", " ++ boolText output.signature.names ++ ", " ++
      listText (output.signature.kept.map helperText) ++ ", " ++
      listText (output.signature.callees.map calleeText) ++ "⟩\n" ++
    "def role : Nat := " ++ toString output.role ++ "\ndef roster : Nat := " ++
      toString definition.roles.length ++ "\ndef template : Template definition signature role roster where\n  form := " ++ formLiteral form ++
      "\n  normalized := by kernel_rfl\n  matched := by decide +kernel\n" ++
    "def helperTables (model : DomainModel) : Tables model :=\n  program.payload.definitions.foldl " ++
      "(Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩\n" ++
    "def capture (model : DomainModel) : ProtocolTable model.Value (Interface model) :=\n  " ++
      "(program.payload.protocols.take " ++ toString output.definitionIndex ++ ").foldl " ++
      "(extendProtocolTableOn model (.silent _) (participantActionsOn model.toCarriers) (helperTables model)) []\n" ++
    "theorem capture_exact (model : DomainModel) : capture model =\n  " ++
      "(program.payload.protocols.take " ++ toString output.definitionIndex ++ ").foldl " ++
      "(extendProtocolTableOn model (.silent _) (participantActionsOn model.toCarriers) (helperTables model)) [] := rfl\n" ++
    "theorem source_capture (model : DomainModel) :\n  " ++
      "invokeProtocol (program.payload.plainProtocolTableOn model) definition.signature =\n    " ++
      "definition.denoteWithOn model (.silent _) (participantActionsOn model.toCarriers) " ++
      "(helperTables model) (capture model) .silent := by kernel_rfl\n" ++
    "end\nend " ++ output.namespaceName ++ "\n"

end ZkcTools.StructuredSource.OriginalRoot
