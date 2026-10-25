module

public import Lean
public import Zkc.Source.Structured.Import

@[expose] public section

/-! Fixed security Subject assembly is separate from the mathematical view.
The existing security builder proves source/pair/occurrence associations. The
descriptor selects request data, never probability or successful execution. -/

namespace ZkcTools.StructuredSource.Root

def quoted (value : String) : String := reprStr value
def paren (value : String) : String := "(" ++ value ++ ")"

/-- A source alias retains its kinded origin. Its generated ordinal selects the
helper table for Local and the admitted protocol table for protocol origins. -/
structure SourceAlias where
  origin : Zkc.Source.Structured.FunctionOrigin
  symbol : String
  index : Nat
  deriving Repr

/-- Missing, malformed and ambiguous origins are transport failures. This does
not infer a library realization from the spelling of an origin. -/
def sourceAliases (snapshot : Zkc.Source.Structured.Snapshot)
    (helpers : List String) : Except String (List SourceAlias) := do
  let mut candidates := []
  for definition in snapshot.definitions do
    let .function function := definition | continue
    if function.kind == .math then continue
    let some origin := function.origin | throw "root-missing-helper-origin"
    unless definition.headerValid do throw "root-malformed-helper-origin"
    if candidates.any (fun (retained, _) => retained == origin) then
      throw "root-ambiguous-helper-origin"
    candidates := candidates ++ [(origin, function.name)]
  -- Admission computes the actual dependency-ordered protocol table. It is
  -- separate from the helper table, even when both happen to have an index 0.
  let program ← Zkc.Source.Structured.check snapshot
  candidates.mapM fun (origin, symbol) => do
    let names := match origin with
      | .local .. => helpers
      | .protocol _ => program.payload.protocols.map (fun (definition : Zkc.Source.Structured.CheckedProtocol) => definition.name)
    let [index] := (names.zipIdx.filter (fun (name, _) => name == symbol)).map Prod.snd
      | throw "root-helper-origin-association"
    return ⟨origin, symbol, index⟩

/-- Decode the frontend's explicit UTF-8 label encoding. Unlabelled sites are
refused, rather than assigned a new request-visible identity. -/
def sourceLabel (site : String) : Except String String := do
  let some hex := site.dropPrefix? "label_" | throw "root-unlabelled-charge-site"
  let chars := hex.toString.toList
  unless chars.length % 2 == 0 do throw "root-malformed-charge-label"
  let digits := "0123456789abcdef".toList
  let values ← chars.mapM fun char => do
    let some value := digits.idxOf? char | throw "root-malformed-charge-label"
    pure value
  let bytes := (List.range (values.length / 2)).map fun index =>
    UInt8.ofNat (values[2 * index]! * 16 + values[2 * index + 1]!)
  let some label := String.fromUTF8? (ByteArray.mk bytes.toArray)
    | throw "root-malformed-charge-label"
  if label.isEmpty || label.contains '.' then throw "root-malformed-charge-label"
  return label

/-- Source identity, including specialization, determines the alias name.
Hex encoding avoids Lean keyword/identifier collisions and never reverses a
compiled symbol hash. Reordering the helper table only changes its witness. -/
def sourceAliasName (alias : SourceAlias) : String :=
  let hex := fun (value : String) => String.join (value.toByteArray.data.toList.map fun byte =>
    let digits := "0123456789abcdef".toList
    String.ofList [digits[byte.toNat / 16]!, digits[byte.toNat % 16]!])
  "source_" ++ hex alias.origin.toJson.compress

def originTermSource : Zkc.Source.Structured.OriginTerm → String
  | .natural value => "(.natural " ++ quoted value ++ ")"
  | .field name => "(.field " ++ quoted name ++ ")"
  | .group name => "(.group " ++ quoted name ++ ")"
  | .domain sort name => "(.domain " ++ quoted sort ++ " " ++ quoted name ++ ")"
  | .asset sort name => "(.asset " ++ quoted sort ++ " " ++ quoted name ++ ")"
  | .boolean => ".boolean" | .index => ".index" | .unit => ".unit"
  | .tuple terms => "(.tuple [" ++ ", ".intercalate (terms.map originTermSource) ++ "])"
  | .array element length => "(.array " ++ originTermSource element ++ " " ++ quoted length ++ ")"
  | .nominal kind path terms =>
    let kind := match kind with
      | .record => ".record" | .variant => ".variant"
      | .associated => ".associated" | .moduleType => ".moduleType"
    "(.nominal " ++ kind ++ " " ++ quoted path ++ " [" ++
      ", ".intercalate (terms.map originTermSource) ++ "])"
  | .builtin name terms => "(.builtin " ++ quoted name ++ " [" ++
      ", ".intercalate (terms.map originTermSource) ++ "])"
  | .formal name terms => "(.formal " ++ quoted name ++ " [" ++
      ", ".intercalate (terms.map originTermSource) ++ "])"

def originSource : Zkc.Source.Structured.FunctionOrigin → String
  | .local name bindings => "(.local " ++ quoted name ++ " [" ++
      ", ".intercalate (bindings.map fun (key, value) => "(" ++ quoted key ++ ", " ++ quoted value ++ ")") ++ "])"
  | .protocol origin => "(.protocol ⟨" ++ quoted origin.path ++ ", [" ++
      ", ".intercalate (origin.arguments.map fun (name, term) =>
        "(" ++ quoted name ++ ", " ++ originTermSource term ++ ")") ++ "]⟩)"

/-- Publish typed aliases and kernel-checked associations with the retained raw
origin. Alias ordinals and both source/checked positions are generated. -/
def sourceAliasSource (moduleName sourceModule : String)
    (snapshot : Zkc.Source.Structured.Snapshot) (helpers : List String) : Except String String := do
  let aliases ← sourceAliases snapshot helpers
  let mut text := "module\n\npublic import " ++ sourceModule ++
    "\npublic import Zkc.Source.KernelRfl\n\n@[expose] public section\n\n/-! Generated exact source-origin aliases. -/\n" ++
    "namespace " ++ moduleName ++ "\nopen Zkc.Source.Structured\n" ++
    "set_option maxRecDepth 50000\nset_option maxHeartbeats 16000000\nnoncomputable section\n\n" ++
    "abbrev imported := " ++ sourceModule ++ ".imported\n" ++
    "abbrev original := " ++ sourceModule ++ ".program.snapshot\n\n"
  for alias in aliases do
    let name := sourceAliasName alias
    let table := match alias.origin with
      | .local .. => "definitions"
      | .protocol _ => "protocols"
    text := text ++ "abbrev " ++ name ++ " := imported.program.payload." ++ table ++ ".get ⟨" ++
      toString alias.index ++ ", by decide +kernel⟩\n" ++
      "theorem " ++ name ++ "_symbol : " ++ name ++ ".name = " ++ quoted alias.symbol ++ " := by kernel_rfl\n" ++
      "theorem " ++ name ++ "_origin :\n" ++
      "    ((original.definitions.filterMap (fun | .function function => some function | _ => none)).find? (fun function => function.name == " ++ name ++ ".name)).bind\n" ++
      "      (fun function => function.origin) = some " ++ originSource alias.origin ++
      " := by kernel_rfl\n\n"
  return text ++ "end\nend " ++ moduleName ++ "\n"

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
  originalExportExpression : String
  producerExportExpression : String
  validatorExportExpression : String
  chargeSites : List String := []

def fixedSubjectSource (output : FixedSubjectOutput) : String :=
  let target := quoted output.targetName
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
  "def subject : ZkcSecurity.Claims.HonestPair.Subject\n" ++
  "    " ++ paren output.modelExpression ++ " original imported selected := by\n" ++
  "  bind_authored_subject " ++ target ++ "\n" ++
  "    exports " ++ output.originalExportExpression ++ ", " ++ output.producerExportExpression ++ ", " ++
  output.validatorExportExpression ++ "\n\n" ++
  "abbrev validatorArtifacts := subject.validatorArtifacts\n" ++
  "abbrev validatorCompiled := subject.validatorCompiled\n\n" ++
  "def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=\n  [" ++
    ",\n   ".intercalate (output.chargeSites.map fun label =>
      "(ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled " ++
      quoted label ++
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
  errorExpression : String := ".natural 0"
  normalization : List String := []
  theoremNormalization : List String := []

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
    "  model := ⟨HonestPair.honestModelIdentifier, [(some \"producer\", .application \"producers.compiled\" (some 0) [])]⟩",
    "  target := subject.down.targetReference",
    "  accept := subject.down.acceptance",
    "  quantity := .scalar (" ++ output.errorExpression ++ ")",
    "  capabilities := [] }", "",
    "def library : ZkcSecurity.Tools.ClaimConstruction.Library where",
    "  subject := ``subject",
    "  authority := some ``authority",
    "  properties := ``properties",
    "  models := ``models",
    "  normalization := [" ++ ", ".intercalate
      ((["subject", "authority", "properties", "models", "capabilities"] ++ output.normalization).map ("``" ++ ·)) ++ "]",
    "  theoremNormalization := [" ++ ", ".intercalate (output.theoremNormalization.map ("``" ++ ·)) ++ "]",
    "  theoremMethods := [(⟨\"fs.honest_completeness\", 0⟩, ``" ++ output.proofName ++ ")]", "",
    "claim_request completeData using library method",
    "  (some (⟨⟨\"fs.honest_completeness\", 0⟩, []⟩ : Wire.Application))", "",
    "#print axioms completeReceipt", "",
    "end " ++ output.moduleName, ""]

/-- Physical registration for a domain subject. The descriptor chooses existing
exports, not a security proposition, numerical bound, schedule or proof script.
Those come from the fixed request and registered theorem, checked by Lean. -/
structure DomainClaimLibraryOutput where
  moduleName : String
  imports : List String
  subjectExpression : String
  artifactsExpression : String
  capabilitiesExpression : String
  applicationParameter : Option String := none
  theoremMethods : List (String × Nat × String)
  theoremNormalization : List String := []

def domainClaimLibrarySource (output : DomainClaimLibraryOutput) : String :=
  let parameter := if output.applicationParameter.isSome then " (application : String)" else ""
  let argument := if output.applicationParameter.isSome then " application" else ""
  let context := match output.applicationParameter with
    | none => "ModelContext.empty"
    | some name => "ModelContext.parameter " ++ quoted name ++ " application"
  "\n".intercalate (["module", ""] ++
    output.imports.map ("public import " ++ ·) ++ [
    "public import ZkcSecurity.Tools.ClaimConstruction", "",
    "@[expose] public section", "",
    "/-! Generated physical registration. Canonical authority fixes the meaning;",
    "theorem exports are applied without per-request proof wrappers. -/",
    "set_option autoImplicit false", "noncomputable section", "",
    "namespace " ++ output.moduleName,
    "open Zkc.Claims ZkcSecurity.Claims", "",
    "abbrev subject := " ++ output.subjectExpression,
    "abbrev capabilities := " ++ output.capabilitiesExpression,
    "def authority := CanonicalAuthority.domains " ++
      paren output.artifactsExpression ++ " capabilities", "",
    "def modelContext" ++ parameter ++ " : ModelContext := " ++ context,
    "def models" ++ parameter ++ " : Registry authority.ModelExport :=",
    "  ⟨[authority.modelEntry (modelContext" ++ argument ++ ")]⟩",
    "def properties" ++ parameter ++ " := authority.properties (models" ++ argument ++ ")", "",
    "def library : ZkcSecurity.Tools.ClaimConstruction.Library where",
    "  subject := ``subject", "  authority := some ``authority",
    "  context := some ``modelContext", "  properties := ``properties", "  models := ``models",
    "  normalization := [``authority, ``modelContext, ``properties, ``models]",
    "  theoremNormalization := [" ++ ", ".intercalate (output.theoremNormalization.map ("``" ++ ·)) ++ "]",
    "  theoremMethods := [" ++ ",\n    ".intercalate (output.theoremMethods.map fun (name, version, theoremName) =>
      "(⟨" ++ quoted name ++ ", " ++ toString version ++ "⟩, ``" ++ theoremName ++ ")") ++ "]",
    "", "end " ++ output.moduleName, ""])

end ZkcTools.StructuredSource.Root
