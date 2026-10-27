module

public import ZkcTools.ConstructionBindings.Analysis
public import ZkcSecurity.Generation.ConstructionBindingsTemplates
public import ZkcExamples.Structured.SumcheckArtifacts.ArtifactOutputs
public import ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates
public import ZkcExamples.Structured.SumcheckArtifacts.OriginalProducerTemplates

@[expose] public section

/-! Source-qualified proposals and checked certificate emission. The installed
Reduce proof schemas are shared; all occurrence identities, loop positions,
captures, body selectors and SSA operands are read from checked source/artifacts. -/
set_option autoImplicit false
namespace ZkcSecurity.Generation.ConstructionBindings
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcTools.ConstructionBindings
open ZkcExamples.Structured.SumcheckArtifacts.ArtifactOutputs
open ZkcExamples.Structured.SumcheckArtifacts.ArtifactBinding
open ZkcTools.StructuredSource.Presentation


def literal {α : Type} [Repr α] (value : α) : String :=
  "(" ++ (reprStr value).replace "\n" " " ++ ")"

def preamble (name : String) (imports : List String) (search : Bool := true) : String :=
  "module\n\n" ++ String.join (imports.map fun name => "public import " ++ name ++ "\n") ++
  (if search then "\npublic meta import Zkc.Construction.ArtifactBindingTactic\npublic meta import Zkc.Construction.ProcessViewTactic\n" else "") ++
  "\n@[expose] public section\nset_option autoImplicit false\nset_option maxRecDepth 50000\n" ++
  "set_option maxHeartbeats 8000000\n" ++
  (if search then "set_option backward.isDefEq.respectTransparency false\n" else "") ++
  "noncomputable section\nnamespace " ++ name ++ "\n" ++
  "open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured\n" ++
  "open ZkcExamples.Structured.SumcheckArtifacts.ArtifactBinding\n" ++
  "variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]\n\n"

def occurrenceName (index : Nat) : String := "occurrence" ++ toString index

def occurrenceNames (layout : Layout) : List String := (List.range layout.calls.length).map occurrenceName

/-- Symbolic routing normalization. Explicit checked label equations close UTF-8
computations without a native evaluator or protocol-specific global simp rules. -/
def nominalSimp (layout : Layout) : String :=
  ", ".intercalate ((occurrenceNames layout).map (· ++ "_decimal") ++ ["Occurrence.low", "Occurrence.high", "Occurrence.draw",
    "Occurrence.delivery", "Occurrence.message", "Occurrence.steps", "Occurrence.protocol",
    "SourceOccurrences.repeatSites", "Template.origin", "Domain.templateOrigin",
    "Template.repeats", "Template.qualify", "Template.applicationPrefix", "context",
    "ProtocolContext.enter", "qualifyProtocolSite", "roleSubstitution",
    "SumcheckVerifierLaws.lowSite", "SumcheckVerifierLaws.highSite", "SumcheckVerifierLaws.challengeSite",
    "SumcheckVerifierLaws.deliverySite", "Context.message", "Context.query", "Context.role",
    "Context.service", "Context.request", "Context.contract", "Context.replacement?",
    "Origin.message", "Origin.query", "Domain.atCoordinates", "decimal", "decimalDigit", "Request.draw",
    "Occurrence.round_label", "Occurrence.challenge_label", "Occurrence.delivery_label"])

def routes (layout : Layout) (index : Nat) : String := Id.run do
  let occurrence := occurrenceName index
  let valid := (occurrenceNames layout).flatMap fun name =>
    ["low", "high", "draw", "delivery"].map fun kind => name ++ "_" ++ kind ++ "_valid"
  -- Routing concatenates message lists only when another call follows. Select
  -- structural normalization from that emitted syntax, for any number of calls.
  let messageAppendRules := if layout.calls.tail.isEmpty then "" else
    "List.cons_append, List.nil_append, "
  return "theorem " ++ occurrence ++ "_routes (handle index : Nat) :\n" ++
    "    Routes (routing handle) " ++ occurrence ++ ".protocol\n" ++
    "      [⟨qualifyProtocolSite " ++ occurrence ++ ".protocol.applicationPrefix \"s15\", index⟩]\n" ++
    "      handle (" ++ occurrence ++ ".origins context index) := by\n" ++
    "  constructor\n  · rfl\n  all_goals\n" ++
    "    simp only [Original.Routing.message, Original.Routing.draw, Occurrence.messages,\n" ++
    "      Occurrence.origins, OccurrenceResolution.resolve, " ++ messageAppendRules ++
    "List.filter_cons, List.filter_nil]\n" ++
    "    simp only [OccurrenceResolution.matchesOccurrence, " ++ ", ".intercalate valid ++ "]\n" ++
    "    simp [" ++ nominalSimp layout ++ "]\n\n"

/-- Applicability only: compare exact syntax with the installed layout before
attempting View conversion. This uses the existing structural Instruction equality;
it is not a semantic evaluator or a replacement for the emitted kernel checks. -/
def templateMatches (producer : Bool) (context : Zkc.Construction.Context)
    (occurrence : Occurrence) (offset : Nat) (instruction : Zkc.Construction.Instruction) : Bool :=
  let expected := if producer then
    ZkcExamples.Structured.SumcheckArtifacts.OriginalProducerTemplates.producerInstructions context occurrence offset
    else ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates.validatorInstructions context occurrence offset
  let outputs := if producer then
    (ZkcExamples.Structured.SumcheckArtifacts.OriginalProducerTemplates.producerOutputs context offset).references
    else (ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates.verifierOutputs context offset).references
  let sorts := if producer then
    ZkcExamples.Structured.SumcheckArtifacts.OriginalProducer.Outputs.sorts context.suite
    else VerifierOutputs.sorts context.suite
  match instruction.operation with
  | .loop site _ yielded =>
    decide (site = qualifyProtocolSite occurrence.protocol.applicationPrefix "s15") &&
    decide (yielded = outputs) && decide (instruction.results = sorts) &&
    @decide (instruction.body = expected) (Instruction.decideList instruction.body expected)
  | _ => false

/-- Check the chosen proof method, without interpreting a refusal as invalid
semantics or silently switching to another method. Derivation applicability is
ultimately established by elaborating and kernel-checking its emitted proof. -/
def checkApplicability (method : ProofMethod) (producer : Bool)
    (context : Zkc.Construction.Context) (occurrence : Occurrence) (offset : Nat)
    (instruction : Zkc.Construction.Instruction) (index : Nat) : Except String Unit := do
  if method == .sharedTemplate then
    unless templateMatches producer context occurrence offset instruction do
      throw ("construction-binding-template-unsupported: " ++
        (if producer then "Producer" else "Validator") ++ " call " ++ toString index)

/-- Print the four local origin equations once per source occurrence. -/
def originLaws (index : Nat) : String :=
  "theorem " ++ occurrenceName index ++ "_origins :\n" ++
  "    ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates.OriginLaws context " ++ occurrenceName index ++ " := by\n" ++
  "  constructor <;> intro index <;> kernel_rfl\n\n"

def source (program : Program) (validator producer : Participant)
    (moduleName sourceModule pairModule : String)
    (method : ProofMethod := .sharedTemplate) : Except String String := do
  let layout ← analyze program validator
  let producerLayout ← analyzeWithContext program layout.context producer
  unless producer.policy == validator.policy do throw "construction-binding-policy-mismatch"
  let rootName := moduleName.toName.getString!
  let imports := [sourceModule, pairModule,
    "ZkcExamples.Structured.Generated.Constructed." ++ rootName ++ "Validator",
    "ZkcExamples.Structured.Generated.Constructed." ++ rootName ++ "Producer",
    "ZkcExamples.Structured.SumcheckArtifacts.ArtifactOutputs",
    "ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates",
    "ZkcExamples.Structured.SumcheckArtifacts.OriginalProducerTemplates",
    "ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingLoop",
    "ZkcExamples.Structured.SumcheckArtifacts.OriginalProducerReduce",
    "Zkc.Source.Structured.BodyBindings"]
  let mut text := preamble moduleName imports (method == .checkedDerivation) ++
    "abbrev program := " ++ sourceModule ++ ".imported.program\n" ++
    "abbrev validatorArtifact := " ++ pairModule ++ ".Validator.participant\n" ++
    "abbrev producerArtifact := " ++ pairModule ++ ".Producer.participant\n" ++
    "abbrev context : Zkc.Construction.Context := " ++ literal layout.context ++ "\n" ++
    "theorem context_checked : exportContext program.snapshot validatorArtifact = some context := by decide +kernel\n" ++
    "theorem policy_checked : producerArtifact.policy = validatorArtifact.policy := by decide +kernel\n\n"
  for (call, index) in layout.calls.zipIdx do
    let occurrence := occurrenceName index
    text := text ++ "abbrev " ++ occurrence ++ " : Occurrence := ⟨context.entry, " ++ quoted call.library ++ ", " ++ quoted call.application ++ "⟩\n"
    text := text ++ "theorem " ++ occurrence ++ "_decimal : protocolSiteDecimal " ++ quoted call.application ++ ".utf8ByteSize = " ++ quoted (toString call.application.utf8ByteSize) ++ " := by decide +kernel\n"
    for kind in ["low", "high", "draw", "delivery"] do
      text := text ++ "theorem " ++ occurrence ++ "_" ++ kind ++ "_valid : SourceOccurrences.valid program.snapshot context " ++ occurrence ++ "." ++ kind ++ " = true := by decide +kernel\n"
    text := text ++ "theorem " ++ occurrence ++ "_delivery_checked : SourceDelivery.checked program.snapshot context " ++ occurrence ++ ".draw " ++ occurrence ++ ".delivery = true := by decide +kernel\n"
    -- A complete template equation prevents a family occurrence constructor from
    -- inventing authority when its installed local paths no longer fit source.
    text := text ++ "theorem " ++ occurrence ++ "_query : " ++ occurrence ++ ".draw = " ++ literal call.query ++ " := by kernel_rfl\n" ++
      "theorem " ++ occurrence ++ "_messages : " ++ occurrence ++ ".messages = " ++ literal call.messages ++ " := by kernel_rfl\n"
  for index in List.range layout.calls.length do text := text ++ originLaws index
  let names := occurrenceNames layout
  text := text ++ "\nabbrev routing (handle : Nat) : Original.Routing :=\n" ++
    "  ⟨program.snapshot, context, .validator, handle, " ++
    " ++ ".intercalate (names.map (· ++ ".messages")) ++ ", " ++
    listText (names.map (· ++ ".draw")) ++ ", " ++
    listText (names.map fun name => "⟨" ++ name ++ ".draw, " ++ name ++ ".delivery⟩") ++ ", []⟩\n\n"
  for index in List.range layout.calls.length do text := text ++ routes layout index
  text := text ++ "theorem helper_bodies : ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers.Bodies program := by bind_structured_bodies\n" ++
    "theorem verifier_bodies : SumcheckVerifierHelpers.Bodies program.payload.definitions :=\n  ⟨helper_bodies.sumcheck.empty, helper_bodies.sumcheck.append, helper_bodies.sumcheck.width, helper_bodies.sumcheck.«variables», helper_bodies.sumcheck.values⟩\n\n"
  for (role, selected) in [("Validator", layout), ("Producer", producerLayout)] do
    for (loop, index) in selected.loops.zipIdx do
      let sourceOccurrence : Occurrence := ⟨layout.context.entry, loop.call.library, loop.call.application⟩
      let some instruction := (if role == "Producer" then producer else validator).instructions[loop.instruction]?
        | throw "construction-binding-template-loop-index"
      checkApplicability method (role == "Producer") layout.context sourceOccurrence loop.offset instruction index
      let scope := role ++ "Call" ++ toString index
      let constructed := "ZkcExamples.Structured.Generated.Constructed." ++ moduleName.toName.getString! ++ role
      -- The caller supplies module naming; it never participates in analysis.
      let body := constructed ++ ".bodyStep" ++ toString loop.instruction ++ "Body"
      text := text ++ "namespace " ++ scope ++ "\nabbrev occurrence := " ++ occurrenceName index ++ "\n"
      let artifact := if role == "Validator" then "validatorArtifact" else "producerArtifact"
      let actual := if role == "Validator" then validator else producer
      let (outputType, outputValue, derivation) ← if role == "Validator" then do
        let outputs ← verifierOutputs layout.context.suite actual loop.instruction
        pure ("VerifierOutputs", literal outputs, "verifierOutputs")
      else do
        let outputs ← producerOutputs layout.context.suite actual loop.instruction
        pure ("ZkcExamples.Structured.SumcheckArtifacts.OriginalProducer.Outputs", literal outputs, "producerOutputs")
      text := text ++ "def outputs : " ++ outputType ++ " context.suite := " ++ outputValue ++ "\n" ++
        "theorem outputs_derived : ZkcExamples.Structured.SumcheckArtifacts.ArtifactOutputs." ++ derivation ++
        " context.suite " ++ artifact ++ " " ++ toString loop.instruction ++ " = .ok outputs := by decide +kernel\n" ++
        "theorem output_references : outputs.references = " ++ natsText loop.yielded ++ " := by kernel_rfl\n"
      text := text ++ "theorem capture_size : ((" ++ artifact ++ ".instructions.take " ++ toString loop.instruction ++
        ").foldl (fun size instruction => size + instruction.results.length) " ++ artifact ++ ".inputs.length) = " ++
        toString loop.offset ++ " := by kernel_rfl\n" ++
        "theorem loop_operands : (" ++ artifact ++ ".instructions.get ⟨" ++ toString loop.instruction ++
        ", by decide +kernel⟩).operands = " ++ natsText (loop.count :: loop.initial) ++ " := by kernel_rfl\n" ++
        "theorem loop_operation : (" ++ artifact ++ ".instructions.get ⟨" ++ toString loop.instruction ++
        ", by decide +kernel⟩).operation = " ++ literal (Operation.loop loop.site loop.maximum loop.yielded) ++ " := by kernel_rfl\n"
      if role == "Producer" then
        text := text ++ "open ZkcExamples.Structured.SumcheckArtifacts.OriginalProducer\n" ++
          "abbrev routing (handle : Nat) : Original.Routing := { " ++ moduleName ++ ".routing handle with mode := .producer }\n" ++
          (((((ConstructionBindingsTemplates.producerRoutes.replace "$DELIVERIES"
            (listText (names.map fun name => "⟨" ++ name ++ ".draw, " ++ name ++ ".delivery⟩"))).replace
            "$VALID_DELIVERY" (occurrenceName index ++ "_delivery_valid")).replace
            "$VALID_DRAW" (occurrenceName index ++ "_draw_valid")).replace
            "$VALIDATOR_ROUTES" (occurrenceName index ++ "_routes")).replace
            "$OCCURRENCE_DECIMAL" (occurrenceName index ++ "_decimal")) ++ "\n"
      else text := text ++ "abbrev routes := " ++ occurrenceName index ++ "_routes\n"
      let owner := if role == "Validator" then
        "ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates" else
        "ZkcExamples.Structured.SumcheckArtifacts.OriginalProducerTemplates"
      let roleName := if role == "Validator" then "validator" else "producer"
      let outputName := if role == "Validator" then "verifierOutputs" else "producerOutputs"
      let selectedInstruction := "(" ++ artifact ++ ".instructions.get ⟨" ++ toString loop.instruction ++ ", by decide +kernel⟩)"
      let bodySyntax := if method == .sharedTemplate then
        owner ++ "." ++ roleName ++ "Instructions context occurrence " ++ toString loop.offset
        else literal instruction.body
      text := text ++ "theorem body_syntax : " ++ selectedInstruction ++ ".body =\n    " ++
        bodySyntax ++ " := by kernel_rfl\n" ++
        "theorem loop_sorts : " ++ selectedInstruction ++ ".results = " ++
        (if role == "Validator" then "VerifierOutputs" else "ZkcExamples.Structured.SumcheckArtifacts.OriginalProducer.Outputs") ++
        ".sorts context.suite := by kernel_rfl\n" ++
        "theorem loop_site : " ++ quoted loop.site ++ " = qualifyProtocolSite occurrence.protocol.applicationPrefix \"s15\" := by kernel_rfl\n"
      if method == .sharedTemplate then
        text := text ++ "theorem body_instance : " ++ body ++ " (ringModel F G) program context =\n    " ++
          owner ++ "." ++ roleName ++ "Body (ringModel F G) program context occurrence " ++ toString loop.offset ++ " := by kernel_rfl\n" ++
          "theorem output_instance : outputs = " ++ owner ++ "." ++ outputName ++ " context " ++ toString loop.offset ++ " := by kernel_rfl\n"
      else
        text := text ++ "theorem body_correspondence : Domain.Correspondence.Block (program := program) (context := context)\n    " ++
          selectedInstruction ++ ".body (" ++ body ++ " (ringModel F G) program context) :=\n  " ++
          body ++ "_eq (ringModel F G) program context\n"
      let template := if role == "Validator" then ConstructionBindingsTemplates.validator method else ConstructionBindingsTemplates.producer method
      text := text ++ ((((template.replace "$OFFSET" (toString loop.offset)).replace "$BODY" body).replace
        "$ORIGINS" (occurrenceName index ++ "_origins")).replace
        "$ORIGIN_DEFINITIONS" (nominalSimp layout)) ++ "\n"
      let callbackType := if role == "Validator" then "VerifierCallback" else "ZkcExamples.Structured.SumcheckArtifacts.OriginalProducer.ProducerCallback"
      text := text ++ "def callback (handle : Nat) : " ++ callbackType ++ " program (routing handle) occurrence context outputs " ++ toString loop.offset ++ " handle\n  (" ++ body ++ " (ringModel F G) program context) :=\n"
      text := text ++ (if role == "Validator" then
        "  ⟨fun captured size index point scalar history => round captured size index handle point scalar history⟩\n"
        else "  ⟨fun captured size index raw dimension width point shape bounded positive history => round captured size index handle raw dimension width point shape bounded positive history⟩\n")
      text := text ++ "end " ++ scope ++ "\n\n"
  return text ++ "end " ++ moduleName ++ "\n"

end ZkcSecurity.Generation.ConstructionBindings
