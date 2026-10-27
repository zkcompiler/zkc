module

public import ZkcTools.ConstructionBindings.Analysis
public import ZkcSecurity.Generation.SubjectABI
public import ZkcExamples.Structured.SumcheckHelperBodies

@[expose] public section

/-! Candidate security bindings for the installed straight-line Sumcheck family.
The source normal form supplies calls and dependencies; source-qualified export
templates supply nominal associations. No instruction count selects a law.
Candidates remain untrusted until the emitted complete equations check. -/
set_option autoImplicit false
namespace ZkcSecurity.Generation.OriginalSecurityBindings
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcTools.StructuredSource ZkcTools.StructuredSource.OriginalRoot
open ZkcTools.ConstructionBindings ZkcExamples.Structured

structure Invocation where
  call : OriginalRoot.Step
  check : OriginalRoot.Step
  raw : Nat
  claim : Nat
  count : Nat
  service : Nat
  occurrence : Nat

structure Binding where
  assembly : Assembly
  calls : List Invocation
  conjunction : Option OriginalRoot.Step
  maximum : Nat
  count : Nat
  service : Nat
  publicPositions : List Nat
  producerPositions : List Nat
  booleanRef : Nat
  transcriptRef : Nat
  producerRef : Nat
  producerArity : Nat

def one {α : Type} (label : String) (values : List α) : Except String α :=
  match values with
  | [value] => .ok value
  | _ => .error ("original-security-" ++ label)

def parameter (step : OriginalRoot.Step) (ty : Ty) : Except String Nat := do
  let binder ← one "call-abi" (step.parameters.filter (·.slot == .component ty))
  return binder.order

def analyze (program : Program) (validator producer : Participant) : Except String Binding := do
  let root := program.payload.entry
  let library ← one "library" (program.payload.protocols.filter (·.name != root.name))
  let maximum ← libraryMaximum library
  let keys := [NormalForm.CalleeKey.mk library.signature 1 (Bindings.optionalPattern library.inputs) []]
  let signature : NormalForm.Signature := ⟨[], false, true, program.payload.definitions.map (·.helper), keys⟩
  let form ← NormalForm.normalize signature root.body 1 root.roles.length (Bindings.optionalPattern root.inputs)
  unless NormalForms.callsMatch form do throw "original-security-call-identity"
  let binders := root.inputs.zipIdx.map fun (ty, index) => Binder.mk ("input" ++ toString index) (.component ty) index
  let assembly ← OriginalRoot.assemble program keys root.inputs binders form 0
  unless assembly.identityReturn do throw "original-security-return"
  let layout ← ZkcTools.ConstructionBindings.analyze program validator
  let producerLayout ← analyzeWithContext program layout.context producer
  let publics := root.inputs.zipIdx.filterMap fun (ty, index) =>
    if Domain.dataType ty && (root.inputScopes[index]?.getD []).contains 1 then some index else none
  let producers := root.inputs.zipIdx.filterMap fun (ty, index) =>
    if Domain.dataType ty && (root.inputScopes[index]?.getD []).contains 0 then some index else none
  let count ← one "count" (root.inputs.zipIdx.filterMap fun (ty, index) => if ty == .index then some index else none)
  let some service := layout.context.service | throw "original-security-replacement-service"
  let some (.service contract) := root.inputs[service]? | throw "original-security-service"
  let mut calls : List Invocation := []
  let mut rest := assembly.steps
  for (nominal, index) in layout.calls.zipIdx do
    let call :: checked :: tail := rest | throw "original-security-call-check-order"
    unless call.callee == some 0 && call.helper.isNone &&
        checked.helper == some SumcheckHelperBodies.checkHelper do throw "original-security-call-check-association"
    let claim ← parameter call (.field "bls12-381.fr")
    let callCount ← parameter call .index
    let callService ← parameter call (.service contract)
    let raw ← parameter checked (.vector "bls12-381.fr")
    unless callCount == count && callService == service && call.parameters.length == 3 do
      throw "original-security-call-abi"
    unless checked.parameters.length == 2 && checked.parameters.any (fun binder =>
        binder.slot == .tuple library.outputs && binder.order == root.inputs.length + 2 * index) do
      throw "original-security-check-result-association"
    unless call.context == some (Presentation.app "ProtocolContext.enter"
        ["{}", Presentation.quoted nominal.application, Presentation.natsText [0, 1]]) do
      throw "original-security-source-order"
    unless producers.contains raw && publics.contains raw && publics.contains claim do
      throw "original-security-public-abi-association"
    calls := calls ++ [⟨call, checked, raw, claim, count, service, index⟩]
    rest := tail
  let conjunction ← match calls, rest with
    | [_], [] => pure none
    | [_, _], [step] => do
        unless step.helper.any (fun helper => helper.kind == .math && helper.inputs == [.boolean, .boolean] &&
            helper.outputs == [.boolean]) && step.parameters.map (·.order) ==
              [root.inputs.length + 1, root.inputs.length + 3] do
          throw "original-security-conjunction-association"
        pure (some step)
    | _, _ => throw "original-security-unsupported-spine"
  unless (calls.map (·.raw)).eraseDups.length == calls.length &&
      (calls.map (·.claim)).eraseDups.length == calls.length do throw "original-security-duplicate-input"
  unless publics == (root.inputs.zipIdx.filterMap fun (_, index) =>
      if index == count || calls.any (fun call => call.raw == index || call.claim == index) then some index else none) &&
      producers == publics.filter (fun index => index == count || calls.any (·.raw == index)) do
    throw "original-security-input-abi"
  unless layout.loops.all (·.maximum == maximum) && producerLayout.loops.all (·.maximum == maximum) do
    throw "original-security-bound-association"
  let [booleanRef, transcriptRef] := validator.returned | throw "original-security-validator-return"
  let [producerRef] := producer.returned | throw "original-security-producer-return"
  return ⟨assembly, calls, conjunction, maximum, count, service, publics, producers,
    booleanRef, transcriptRef, producerRef, producerLayout.arity⟩

def validateABI (program : Program) (binding : Binding) (metadata : SubjectABI.Metadata) : Except String Unit := do
  unless metadata.types == program.payload.entry.inputs && metadata.context.service == some binding.service &&
      metadata.publicPositions == binding.publicPositions && metadata.producerPositions == some binding.producerPositions do
    throw "original-security-subject-abi-association"
  unless (← metadata.targetPositions).all binding.publicPositions.contains do
    throw "original-security-private-target"

structure Output where
  moduleName : String
  originalModule : String
  artifactModule : String
  subjectModule : String
  abiModule : String
  formulaNamespace : String
  fieldType : String
  groupType : String
  modulus : String
  sampling : String
  capabilities : String

def input (index : Nat) : String := "input" ++ toString index
def args (positions : List Nat) : String := " ".intercalate (positions.map input)
def rawType : Ty → Except String String
  | .vector _ => pure "List F"
  | .field _ => pure "F"
  | .index | .service _ => pure "Nat"
  | _ => throw "original-security-type"
def params (program : Program) (positions : List Nat) : Except String String := do
  return " ".intercalate (← positions.mapM fun index => do
    let some ty := program.payload.entry.inputs[index]? | throw "original-security-input"
    return "(" ++ input index ++ " : " ++ (← rawType ty) ++ ")")
def sourceValues (program : Program) (binding : Binding) (producer honest : Bool) : String :=
  Presentation.valuesText (program.payload.entry.inputs.zipIdx.map fun (_, index) =>
    if index == binding.service then (if producer then "none" else "(some handle)")
    else if producer && !binding.producerPositions.contains index then "none"
    else if honest then match binding.calls.find? (·.claim == index) with
      | some call => "(some " ++ input call.raw ++ ".sum)"
      | none => "(some " ++ input index ++ ")"
    else "(some " ++ input index ++ ")")


/-- Installed mathematics for the nominal template route. These are source
expressions only; every applicability, helper and capture equation is checked
at the emitted dependent type, against the actual admitted declaration. -/
structure TemplateInstallation where
  moduleName : String
  templateModule : String
  mathematicsModule : String
  model : String
  modelLaws : String
  domain : String
  fieldLaw : String
  results : String
  helperLaws : String
  processes : String
  calleeLaws : String
  role : Nat
  roster : Nat

/-- This route has no carrier-name table, uniform price or root-count case
split. The template fixes the source, helpers, nominal signature and capture;
installed mathematics must meet those exact indices. -/
def templateBindings (output : TemplateInstallation) : String :=
  "module\n\npublic import " ++ output.templateModule ++ "\npublic import " ++ output.mathematicsModule ++
    "\n\n@[expose] public section\nset_option autoImplicit false\nnoncomputable section\nnamespace " ++
    output.moduleName ++ "\nopen Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm " ++
    "Zkc.Source.Structured.Bindings\nopen " ++ output.templateModule ++ "\n" ++
    "def model : DomainModel := " ++ output.model ++ "\n" ++
    "theorem modelLaws : DomainLaws program.snapshot.catalogue model := " ++ output.modelLaws ++ "\n" ++
    "theorem domainApplicable : program.snapshot.catalogue.require " ++ Presentation.quoted output.domain ++
      " .field \"Field\" = .ok () := by decide +kernel\n" ++
    "theorem fieldLaw : IsField (model.Field " ++ Presentation.quoted output.domain ++ ") := " ++ output.fieldLaw ++ "\n" ++
    "def results : LawResults model signature.laws := " ++ output.results ++ "\n" ++
    "theorem helperLaws {inputs : List Ty} (input : Values (Component model.Value) inputs) :\n" ++
      "    LawsHold (helperTables model) results input := " ++ output.helperLaws ++ "\n" ++
    "def processes : CalleeProcesses model signature.callees := " ++ output.processes ++ "\n" ++
    "theorem calleeLaws {inputs : List Ty} (input : Values (Component model.Value) inputs) :\n" ++
      "    CalleesHold (capture model) processes input := " ++ output.calleeLaws ++ "\n" ++
    "theorem binding (ctx : ProtocolContext) (distinct : RosterDistinct ctx " ++ toString output.role ++
      " " ++ toString output.roster ++ ") (input : Values (Component model.Value) definition.inputs) :\n" ++
      "    invokeProtocol (program.payload.plainProtocolTableOn model) definition.signature " ++
      "ctx (ctx.roles " ++ toString output.role ++ ") input =\n" ++
      "      template.view model (helperTables model) (capture model) results processes ctx input :=\n" ++
      "  (congrFun (congrFun (congrFun (source_capture model) ctx) (ctx.roles " ++ toString output.role ++
      ")) input).trans (template.binding model (helperTables model) (capture model) results processes ctx distinct input " ++
      "(helperLaws _) (calleeLaws _))\nend " ++ output.moduleName ++ "\n"

end ZkcSecurity.Generation.OriginalSecurityBindings
