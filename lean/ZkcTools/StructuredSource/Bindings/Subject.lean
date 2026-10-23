module

public import ZkcTools.StructuredSource.Bindings.Generate

@[expose] public section

/-! Fixed security Subject assembly is separate from the mathematical view.
The existing security builder proves source/pair/occurrence associations. The
descriptor selects request data, never probability or successful execution. -/

namespace ZkcTools.StructuredSource.Bindings

structure FixedSubjectOutput where
  moduleName : String
  sourceModule : String
  originalExpression : String
  importedExpression : String
  pairModule : String
  artifactsExpression : String
  modelModule : String
  modelExpression : String
  targetName : String
  inputPolicyExpression : String
  originalExportExpression : String
  producerExportExpression : String
  validatorExportExpression : String
  chargeSites : List String := []

def fixedSubjectSource (output : FixedSubjectOutput) : String :=
  let target := Presentation.quoted output.targetName
  "module\n\npublic import " ++ output.sourceModule ++ "\npublic import " ++ output.pairModule ++
  "\npublic import " ++ output.modelModule ++ "\npublic import ZkcSecurity.Tools.PairConstruction\n" ++
  "public import ZkcSecurity.Claims.SourceChargeSites\n\n" ++
  "@[expose] public section\n\n/-! Generated fixed request data and checked Subject assembly. -/\n" ++
  "namespace " ++ output.moduleName ++ "\nopen Zkc.Source.Structured\n" ++
  "set_option maxRecDepth 50000\nset_option maxHeartbeats 16000000\nnoncomputable section\n\n" ++
  "abbrev original : Snapshot := " ++ output.originalExpression ++ "\n" ++
  "abbrev imported : Imported original := " ++ output.importedExpression ++ "\n" ++
  "abbrev artifacts := " ++ output.artifactsExpression ++ "\n\n" ++
  "def selected : Zkc.Construction.AuthoredPair.Selection original :=\n" ++
  "  (Zkc.Construction.AuthoredPair.select original artifacts " ++ target ++ ").toOption.get (by decide +kernel)\n\n" ++
  "def inputPolicy : ZkcSecurity.Claims.HonestPair.InputPolicy imported.program.payload.entry.inputs :=\n" ++
  "  " ++ output.inputPolicyExpression ++ "\n\n" ++
  "def subject : ZkcSecurity.Claims.HonestPair.Subject\n" ++
  "    " ++ Presentation.paren output.modelExpression ++ " original imported selected := by\n" ++
  "  bind_authored_subject " ++ target ++ " using inputPolicy\n" ++
  "    exports " ++ output.originalExportExpression ++ ", " ++ output.producerExportExpression ++ ", " ++
  output.validatorExportExpression ++ "\n\n" ++
  "abbrev validatorArtifacts := subject.validatorArtifacts\n" ++
  "abbrev validatorCompiled := subject.validatorCompiled\n\n" ++
  "def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=\n  [" ++
    ",\n   ".intercalate (output.chargeSites.map fun label =>
      "(ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled " ++
      Presentation.quoted label ++
      ").toOption.get (by decide +kernel)") ++ "]\n\n" ++
  "def validatorSubject := subject.validatorSubject validatorSites\n\n" ++
  "end\nend " ++ output.moduleName ++ "\n"


/-- A closed request and its selected theorem export. Subject construction and
canonical meaning stay in their existing owners; no protocol names are matched. -/
structure FixedCompletenessOutput where
  moduleName : String
  subjectModule : String
  subjectNamespace : String
  proofModule : String
  proofName : String
  capabilitiesExpression : String
  error : Nat := 0

def fixedCompletenessSource (output : FixedCompletenessOutput) : String :=
  "\n".intercalate [
    "module", "",
    "public import " ++ output.subjectModule,
    "public import " ++ output.proofModule,
    "public import ZkcSecurity.Tools.ClaimConstruction", "",
    "@[expose] public section", "",
    "/-! Generated fixed compiled-pair request and canonical receipt. The",
    "selected theorem is checked against the meaning before attribution. -/",
    "set_option autoImplicit false",
    "set_option maxRecDepth 20000",
    "set_option maxHeartbeats 8000000",
    "noncomputable section", "",
    "namespace " ++ output.moduleName,
    "open Zkc.Claims ZkcSecurity.Claims",
    "open " ++ output.subjectNamespace ++ " (original imported selected)", "",
    "def capabilities := " ++ output.capabilitiesExpression,
    "def authority := CanonicalAuthority.authoredPair imported selected capabilities",
    "def subject := ULift.up.{1} " ++ output.subjectNamespace ++ ".subject",
    "def models : Registry authority.ModelExport := ⟨[authority.modelEntry ()]⟩",
    "noncomputable def properties := authority.properties models", "",
    "def completeData : Wire.Request := {",
    "  subject := subject.down.reference",
    "  property := ⟨\"completeness\", 0⟩",
    "  parameters := subject.down.inputPolicy.parameters",
    "  model := ⟨HonestPair.honestModelIdentifier, []⟩",
    "  target := subject.down.targetReference",
    "  accept := subject.down.acceptance",
    "  quantity := .scalar (.natural " ++ toString output.error ++ ")",
    "  capabilities := [] }", "",
    "def library : ZkcSecurity.Tools.ClaimConstruction.Library where",
    "  subject := ``subject",
    "  authority := some ``authority",
    "  properties := ``properties",
    "  models := ``models",
    "  normalization := [``subject, ``authority, ``properties, ``models, ``capabilities]",
    "  theoremMethods := [(⟨\"fs.honest_completeness\", 0⟩, ``" ++ output.proofName ++ ")]", "",
    "claim_request completeData using library method",
    "  (some (⟨⟨\"fs.honest_completeness\", 0⟩, []⟩ : Wire.Application))", "",
    "#print axioms completeReceipt", "",
    "end " ++ output.moduleName, ""]

end ZkcTools.StructuredSource.Bindings
