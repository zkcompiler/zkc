module

public import ZkcTools.ConstructionBindings.Analysis
public import ZkcSecurity.Generation.SubjectABI
public import ZkcExamples.Structured.SumcheckHelperBodies
public import ZkcExamples.Structured.SumcheckPendingBodies

@[expose] public section

/-! Candidate security bindings for the installed straight-line Sumcheck family.
The source normal form supplies calls and dependencies; source-qualified export
templates supply nominal associations. No instruction count selects a law.
Candidates remain untrusted until the emitted complete equations check. -/
set_option autoImplicit false
namespace ZkcSecurity.Generation.OriginalSecurityBindings
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcTools.StructuredSource ZkcTools.StructuredSource.OriginalRoot ZkcTools.StructuredSource.Methods.SumcheckRoot
open ZkcTools.ConstructionBindings ZkcExamples.Structured

structure Invocation where
  pending : Methods.SumcheckRoot.Step
  call : Methods.SumcheckRoot.Step
  check : Methods.SumcheckRoot.Step
  raw : Nat
  claim : Nat
  count : Nat
  service : Nat
  occurrence : Nat

inductive TerminalTree where
  | leaf (index : Nat)
  | and (left right : TerminalTree)
  deriving Repr, BEq

def TerminalTree.leaves : TerminalTree → List Nat
  | .leaf index => [index]
  | .and left right => left.leaves ++ right.leaves

def TerminalTree.source : TerminalTree → String
  | .leaf index => "(.leaf " ++ toString index ++ ")"
  | .and left right => "(.and " ++ left.source ++ " " ++ right.source ++ ")"

structure Binding where
  assembly : Assembly
  calls : List Invocation
  conjunctions : List Methods.SumcheckRoot.Step
  terminal : TerminalTree
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

def parameter (step : Methods.SumcheckRoot.Step) (ty : Ty) : Except String Nat := do
  let binder ← one "call-abi" (step.parameters.filter (·.slot == .component ty))
  return binder.order

/-- Only the exact pure conjunction body is installed. A helper's name grants
no terminal meaning; the generated full helper equation checks this again. -/
def isConjunction : {inputs outputs : List Ty} → Region dialect inputs outputs → Bool
  | _, _, .letOp .booleanAnd (.cons left (.cons right .nil)) .nil (.ret (.cons result .nil)) =>
      left.index == 0 && right.index == 1 && result.index == 0
  | _, _, _ => false

/-- Recover the pure terminal dataflow from exact helper bodies and tuple
coordinates. Coverage is checked before any property binding is printed. -/
def analyzeTerminal (definitions : List CheckedDefinition) (calls : List Invocation)
    (steps : List Methods.SumcheckRoot.Step) (returned : Option Nat) : Except String TerminalTree := do
  let mut nodes := calls.map fun call =>
    (call.check.resultOrder, TerminalTree.leaf call.occurrence)
  for step in steps do
    let some helper := step.helper | throw "original-security-terminal-effect"
    unless helper.kind == .math && helper.inputs == [.boolean, .boolean] && helper.outputs == [.boolean] do
      throw "original-security-terminal-helper"
    let definition ← one "terminal-helper-body" (definitions.filter (·.helper == helper))
    unless isConjunction definition.body do
      throw "original-security-terminal-helper-body"
    let [(left, 0), (right, 0)] := step.operands | throw "original-security-conjunction-operands"
    let some leftTree := (nodes.find? (·.1 == left)).map (·.2)
      | throw "original-security-conjunction-dependency"
    let some rightTree := (nodes.find? (·.1 == right)).map (·.2)
      | throw "original-security-conjunction-dependency"
    nodes := nodes ++ [(step.resultOrder, .and leftTree rightTree)]
  let some returned := returned | throw "original-security-terminal-return"
  let some terminal := (nodes.find? (·.1 == returned)).map (·.2)
    | throw "original-security-terminal-return"
  unless terminal.leaves.mergeSort (· ≤ ·) == List.range calls.length do
    throw "original-security-conjunction-coverage"
  return terminal

def analyze (program : Program) (validator producer : Participant) : Except String Binding := do
  let root := program.payload.entry
  let library ← one "library" (program.payload.protocols.filter (·.name != root.name))
  let maximum ← libraryMaximum library
  let keys := [NormalForm.CalleeKey.mk library.signature 1 (Bindings.optionalPattern library.inputs) []]
  let signature : NormalForm.Signature := ⟨[], false, true, program.payload.definitions.map (·.helper), keys⟩
  let form ← NormalForm.normalize signature root.body 1 root.roles.length (Bindings.optionalPattern root.inputs)
  unless NormalForms.callsMatch form do throw "original-security-call-identity"
  let binders := root.inputs.zipIdx.map fun (ty, index) => Binder.mk ("input" ++ toString index) (.component ty) index
  let assembly ← Methods.SumcheckRoot.assemble program keys root.inputs binders form 0
  unless assembly.identityReturn do throw "original-security-return"
  let layout ← ZkcTools.ConstructionBindings.analyze program validator
  let producerLayout ← analyzeWithContext program layout.context producer
  unless root.inputScopes.length == root.inputs.length do throw "original-security-input-scopes"
  let publics := (root.inputs.zip root.inputScopes).zipIdx.filterMap fun ((ty, scope), index) =>
    if Domain.dataType ty && scope.contains 1 then some index else none
  let producers := (root.inputs.zip root.inputScopes).zipIdx.filterMap fun ((ty, scope), index) =>
    if Domain.dataType ty && scope.contains 0 then some index else none
  let count ← one "count" (root.inputs.zipIdx.filterMap fun (ty, index) => if ty == .index then some index else none)
  let some service := layout.context.service | throw "original-security-replacement-service"
  let some (.service contract) := root.inputs[service]? | throw "original-security-service"
  let mut calls : List Invocation := []
  let mut rest := assembly.steps
  for (nominal, index) in layout.calls.zipIdx do
    let pending :: call :: checked :: tail := rest | throw "original-security-pending-call-check-order"
    unless pending.helper == some SumcheckPendingBodies.pendingHelper && pending.owner == some 1 do
      throw "original-security-pending-association"
    unless call.callee == some 0 && call.helper.isNone &&
        checked.helper == some SumcheckHelperBodies.checkHelper do throw "original-security-call-check-association"
    let claim ← parameter pending (.field "bls12-381.fr")
    let callCount ← parameter call .index
    let callService ← parameter call (.service contract)
    let raw ← parameter checked (.vector "bls12-381.fr")
    unless callCount == count && callService == service && call.parameters.length == 3 &&
        pending.parameters.length == 1 && call.parameters.any (fun binder =>
          binder.slot == .tuple SumcheckPendingBodies.pendingHelper.outputs && binder.order == pending.resultOrder) do
      throw "original-security-call-abi"
    unless checked.parameters.length == 2 && checked.parameters.any (fun binder =>
        binder.slot == .tuple library.outputs && binder.order == call.resultOrder) do
      throw "original-security-check-result-association"
    unless call.context == some (Presentation.app "ProtocolContext.enter"
        ["{}", Presentation.quoted nominal.application, Presentation.natsText [0, 1]]) do
      throw "original-security-source-order"
    unless producers.contains raw && publics.contains raw && publics.contains claim do
      throw "original-security-public-abi-association"
    calls := calls ++ [⟨pending, call, checked, raw, claim, count, service, index⟩]
    rest := tail
  unless !calls.isEmpty do throw "original-security-no-calls"
  let conjunctions := rest
  let terminal ← analyzeTerminal program.payload.definitions calls rest assembly.returnedOrder
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
  return ⟨assembly, calls, conjunctions, terminal, maximum, count, service, publics, producers,
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

def callArguments (call : Invocation) (scalar count handle : String) : Except String String := do
  return " ".intercalate (← call.call.parameters.mapM fun binder =>
    if binder.order == call.pending.resultOrder && binder.slot == .tuple SumcheckPendingBodies.pendingHelper.outputs then
      pure ("(.cons (some []) (.cons (some " ++ scalar ++ ") .nil))")
    else if binder.order == call.count && binder.slot == .component .index then pure ("(some " ++ count ++ ")")
    else if binder.order == call.service then pure ("(some " ++ handle ++ ")")
    else throw "original-security-call-argument-association")

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


end ZkcSecurity.Generation.OriginalSecurityBindings
