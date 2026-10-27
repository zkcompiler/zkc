module

public import ZkcTools.StructuredSource.OriginalRoot

@[expose] public section

/-! Typed library-law installation for generic original-root templates. These
are candidate expressions. The generated theorem checks the actual helper table,
complete callee signatures, source role and immutable captured prefix. -/
set_option autoImplicit false
namespace ZkcTools.StructuredSource.TemplateInstallation

/-- Extra mathematical applicability remains an ordinary typed proposition.
No carrier, domain, field, role or protocol family is selected by this printer. -/
structure Applicability where
  name : String
  proposition : String
  proof : String

structure Output where
  moduleName : String
  templateModule : String
  mathematicsModule : String
  model : String
  modelLaws : String
  applicability : List Applicability
  results : String
  helperLaws : String
  processes : String
  calleeLaws : String

/-- Body correspondence is independent of the property ultimately consumed.
The library author supplies mathematical/representation laws. Source identity,
normalization, roles and capture come from the generated dependent template. -/
def source (output : Output) : String :=
  "module\n\npublic import " ++ output.templateModule ++ "\npublic import " ++ output.mathematicsModule ++
    "\n\n@[expose] public section\nset_option autoImplicit false\nnoncomputable section\nnamespace " ++
    output.moduleName ++ "\nopen Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm " ++
    "Zkc.Source.Structured.Bindings\nopen " ++ output.templateModule ++ "\n" ++
    "def model : DomainModel := " ++ output.model ++ "\n" ++
    "theorem modelLaws : DomainLaws program.snapshot.catalogue model := " ++ output.modelLaws ++ "\n" ++
    String.join (output.applicability.map fun law =>
      "theorem " ++ law.name ++ " : " ++ law.proposition ++ " := " ++ law.proof ++ "\n") ++
    "def results : LawResults model signature.laws := " ++ output.results ++ "\n" ++
    "theorem helperLaws {inputs : List Ty} (input : Values (Component model.Value) inputs) :\n" ++
      "    LawsHold (helperTables model) results input := " ++ output.helperLaws ++ "\n" ++
    "def processes : CalleeProcesses model signature.callees := " ++ output.processes ++ "\n" ++
    "theorem calleeLaws {inputs : List Ty} (input : Values (Component model.Value) inputs) :\n" ++
      "    CalleesHold (capture model) processes input := " ++ output.calleeLaws ++ "\n" ++
    "theorem binding (ctx : ProtocolContext) (distinct : RosterDistinct ctx role roster) " ++
      "(input : Values (Component model.Value) definition.inputs) :\n" ++
      "    invokeProtocol (program.payload.plainProtocolTableOn model) definition.signature " ++
      "ctx (ctx.roles role) input =\n" ++
      "      template.view model (helperTables model) (capture model) results processes ctx input :=\n" ++
      "  (congrFun (congrFun (congrFun (source_capture model) ctx) (ctx.roles role)) input).trans " ++
      "(template.binding model (helperTables model) (capture model) results processes ctx distinct input " ++
      "(helperLaws _) (calleeLaws _))\nend " ++ output.moduleName ++ "\n"

end ZkcTools.StructuredSource.TemplateInstallation
