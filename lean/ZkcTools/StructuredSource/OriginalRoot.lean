module

public import ZkcTools.StructuredSource.Bindings.Generate
public import ZkcTools.StructuredSource.LibraryAssociation
public import ZkcTools.StructuredSource.Root
public import Zkc.Source.Structured.Bindings.Template

@[expose] public section

/-! Structural original-root generation. Selection data names an admitted unit
and a mathematical family. All wiring is read from the existing normalizer's
typed form. Generated equations are independently checked by Region.Derivation;
this printer and its normalizer execution supply no semantic authority. -/
set_option autoImplicit false
namespace ZkcTools.StructuredSource.OriginalRoot
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open ZkcTools.StructuredSource.Presentation

structure LibraryComponent where
  familyModule : String
  maximum : Nat
  domain : String

/-- The installed Sumcheck method owns its source template and static ABI.
The selected field must match the nominal domain of its complete library body.
Max is read by name and kind, never inferred from a repeat in a candidate. -/
def sumcheckLibrary (domain : String := "bls12-381.fr")
    (familyModule : String := "ZkcExamples.Structured.OriginalSumcheckReduce") :
    LibraryAssociation.Installed LibraryComponent where
  template := ⟨"sumcheck::Reduce", ["F", "Max"]⟩
  instantiate arguments := do
    let [("F", .field selected), ("Max", .natural decimal)] := arguments
      | throw "original-root-library-arguments"
    unless selected == domain do throw "original-root-library-arguments"
    let some maximum := decimal.toNat? | throw "original-root-library-arguments"
    unless maximum < indexLimit do throw "original-root-library-maximum"
    return ⟨familyModule, maximum, selected⟩

structure Output where
  moduleName : String
  sourceModule : String
  /-- Installed methods supply template metadata independently of root names. -/
  libraries : List (LibraryAssociation.Installed LibraryComponent) := [sumcheckLibrary]

structure Binder where
  name : String
  slot : Slot
  order : Nat

structure Step where
  name : String
  parameters : List Binder
  arguments : String
  process : String
  realized : String
  outputs : List Ty
  helper : Option Helper := none
  context : Option String := none
  callee : Option Nat := none

structure Assembly where
  declarations : String := ""
  steps : List Step := []
  returned : String := ""
  identityReturn : Bool := false

/-- Missing names refuse; there are no placeholder expressions. -/
def binderAt (binders : List Binder) (index : Nat) : Except String Binder :=
  match binders[index]? with
  | some binder => .ok binder
  | none => .error "original-root-binder"

def compDependencies {Δ : Scope} {ty : Ty} : Comp [] Δ ty → Except String (List Nat)
  | .absent => pure []
  | .present term => match term with
    | .index _ => pure []
    | .bool _ => pure []
    | _ => throw "original-root-component"
  | .input binder | .read binder _ => pure [binder.index]

def dependencies {Δ : Scope} {types : List Ty} :
    Values (Comp [] Δ) types → Except String (List Nat)
  | .nil => pure []
  | .cons value rest => return (← compDependencies value) ++ (← dependencies rest)

def componentArguments {Δ : Scope} : {scope : Scope} →
    Values (Argument [] Δ) scope → Except String (List Nat × List String)
  | [], .nil => pure ([], [])
  | .component _ :: _, .cons value rest => do
    let (deps, values) ← componentArguments rest
    return ((← compDependencies value) ++ deps, compLiteral value :: values)
  | _, _ => throw "original-root-callee-pattern"

def binderType (binder : Binder) : Except String String :=
  match binder.slot with
  | .component ty => pure (app "Option" [Carriers.valueType (.uniform "F" "G") ty])
  | .tuple types => pure (app "Values" ["(Component (assignment F G))", typesText types])
  | _ => throw "original-root-binder-type"

/-- A complete signature has exactly one source catalogue association. -/
def uniqueIndex {α : Type} [BEq α] (candidates : List α) (selected : α) : Except String Nat := do
  let [(_, index)] := candidates.zipIdx.filter (fun pair => pair.1 == selected)
    | throw "original-root-unique-association"
  return index

def helperAlias (program : Program) (helper : Helper) : Except String String := do
  let index ← (uniqueIndex (program.payload.definitions.map (·.helper)) helper).mapError
    (fun _ => "original-root-helper-association")
  return "sourceHelper" ++ toString index ++ ".helper"

/-- Full nominal signatures select callees; no root names or compiled patterns
participate in selection. Duplicate exact candidates are refused. -/
def calleeIndex (program : Program) (signature : ProtocolSignature) : Except String Nat :=
  (uniqueIndex (program.payload.protocols.map (·.signature)) signature).mapError
    (fun _ => "original-root-callee-association")

/- Structural repeat observations retained for existing refusal controls.
Production library selection uses the typed static origin, not these bounds. -/
mutual
  def repeatBounds : {inputs outputs : List Ty} → Region protocolDialect inputs outputs → List Nat
    | _, _, .ret _ | _, _, .stop _ => []
    | _, _, .bind body next => repeatBounds body ++ repeatBounds next
    | _, _, .letOp op _ bodies next =>
      (match op with | .repeat spec _ => [spec.maximum] | _ => []) ++
        callbackBounds bodies ++ repeatBounds next
  def callbackBounds : {signatures : List (List Ty × List Ty)} → Regions protocolDialect signatures → List Nat
    | _, .nil => []
    | _, .cons body rest => repeatBounds body ++ callbackBounds rest
end

def selectMaximum (bounds : List Nat) : Except String Nat := do
  let [maximum] := bounds | throw "original-root-family-repeat"
  return maximum

def libraryMaximum (definition : CheckedProtocol) : Except String Nat :=
  selectMaximum (repeatBounds definition.body)

def naming (callees : List CalleeKey) (inputs : List Ty) : Naming [] callees ((Bindings.optionalPattern inputs).scope) :=
  { carriers := .uniform "F" "G", tables := "tables", context := "({} : ProtocolContext)" }

def selectParameters (binders : List Binder) (indices : List Nat) : Except String (List Binder) := do
  let selected ← indices.eraseDups.mapM (binderAt binders)
  return selected.mergeSort (fun left right => left.order ≤ right.order)

def parameterText (parameters : List Binder) : Except String String := do
  return " ".intercalate (← parameters.mapM fun binder => do
    return "(" ++ binder.name ++ " : " ++ (← binderType binder) ++ ")")

def isIdentity {Δ : Scope} {outputs : List Ty} (values : Values (Comp [] Δ) outputs) : Bool :=
  let rec positions {types : List Ty} (offset : Nat) : Values (Comp [] Δ) types → Bool
    | .nil => true
    | .cons (.read binder position) rest => binder.index == 0 && position.index == offset && positions (offset + 1) rest
    | _ => false
  positions 0 values

/-- Print only the structural application/helper spine supported by the selected
family. Other effects refuse instead of silently dropping them. The existing
normalizer handles marks, ownership, constants and optional input propagation. -/
def assemble (program : Program) (callees : List CalleeKey) (inputs : List Ty) :
    {Δ : Scope} → {outputs : List Ty} → List Binder → Form [] callees Δ outputs → Nat → Except String Assembly
  | _, _, binders, .done values, _ => do
    let _ ← selectParameters binders (← dependencies values)
    let names := binders.map (·.name)
    let returned := valuesText (compsText (naming callees inputs) names values)
    return { returned, identityReturn := isIdentity values }
  | _, _, _, .halt _, _ => throw "original-root-terminal"
  | _, _, binders, .owned owner helper args next, number => do
    let helperName ← helperAlias program helper
    let parameters ← selectParameters binders (← dependencies args)
    let arguments := valuesText (compsText (naming callees inputs) (binders.map (·.name)) args)
    let process := app "Participant.owned" ["1", toString owner, app "invoke" ["tables.closed", helperName], arguments]
    let step : Step := { name := "step" ++ toString number, parameters, arguments := "tables", process, realized := process, outputs := helper.outputs, helper := some helper }
    let tail ← assemble program callees inputs (⟨"out" ++ toString number, .tuple helper.outputs, inputs.length + number⟩ :: binders) next (number + 1)
    return { tail with steps := step :: tail.steps }
  | _, _, binders, .math helper args next, number => do
    let helperName ← helperAlias program helper
    let parameters ← selectParameters binders (← dependencies args)
    let arguments := valuesText (compsText (naming callees inputs) (binders.map (·.name)) args)
    let process := app "invoke" ["tables.components", helperName, arguments]
    let step : Step := { name := "step" ++ toString number, parameters, arguments := "tables", process, realized := process, outputs := helper.outputs, helper := some helper }
    let tail ← assemble program callees inputs (⟨"out" ++ toString number, .tuple helper.outputs, inputs.length + number⟩ :: binders) next (number + 1)
    return { tail with steps := step :: tail.steps }
  | _, _, binders, .apply callee signature roles site args next, number => do
    let index ← calleeIndex program signature
    unless (calleeAt callees callee).role == 1 && roles == [0, 1] do throw "original-root-callee-roles"
    let (deps, _) ← componentArguments args
    let parameters ← selectParameters binders deps
    let arguments := valuesText (argumentsText (naming callees inputs) (binders.map (·.name)) args)
    let context := app "ProtocolContext.enter" ["{}", quoted site, natsText roles]
    let process := app "invokeProtocol" ["protocols", "sourceProtocol" ++ toString index ++ ".signature", context, "1", arguments]
    let realized := app "realizeCall" ["(G := G)", "payload", "maximum" ++ toString index, context,
      "sourceProtocol" ++ toString index ++ ".outputScopes", arguments]
    let step : Step := { name := "step" ++ toString number, parameters, arguments := "protocols", process, realized, outputs := signature.outputs, context := some context, callee := some index }
    let tail ← assemble program callees inputs (⟨"out" ++ toString number, .tuple signature.outputs, inputs.length + number⟩ :: binders) next (number + 1)
    let declarations := "def callContext" ++ toString number ++ " : ProtocolContext := " ++ context ++ "\n" ++
      "theorem callContext" ++ toString number ++ "_roles : (callContext" ++ toString number ++ ").roles 0 ≠ (callContext" ++ toString number ++ ").roles 1 := by decide\n\n"
    return { tail with steps := step :: tail.steps, declarations := declarations ++ tail.declarations }
  | _, _, _, _, _ => throw "original-root-unsupported-form"

def spine (assembly : Assembly) (realized : Bool) : String := Id.run do
  let mut tail := ".done " ++ assembly.returned
  for (step, index) in assembly.steps.zipIdx.reverse do
    let expression := if realized && step.arguments == "protocols" then
      app (step.name ++ "Realized") ("(G := G)" :: step.parameters.map (·.name))
      else app step.name (step.arguments :: step.parameters.map (·.name))
    if realized && index + 1 == assembly.steps.length && assembly.identityReturn then tail := expression
    else
      let name := "out" ++ toString index
      let binder := if (expressionIdentifiers tail).contains name then name else "_" ++ name
      tail := expression ++ ".bind fun " ++ binder ++ " =>\n  " ++ tail
  return tail

/-- Congruence follows the normalized spine without unfolding a library call.
Explicit equality arguments also keep reducible generated aliases usable by
clients whose proofs expose the assembly with `simp only`. -/
def realizationProof (assembly : Assembly) : String := Id.run do
  let mut text := "  simp only [process, realized, singleton_eta, PIR.Process.bind_done]\n"
  let mut indent := "  "
  for (step, index) in assembly.steps.zipIdx do
    let proof := if step.callee.isSome then
      "exact " ++ app (step.name ++ "_binding") ("(G := G)" :: step.parameters.map (·.name))
      else "rfl"
    if index + 1 == assembly.steps.length then
      text := text ++ indent ++ proof ++ "\n"
    else
      text := text ++ indent ++ "apply congrArg₂ PIR.Process.bind\n" ++
        indent ++ "· " ++ proof ++ "\n" ++ indent ++ "· funext out" ++ toString index ++ "\n"
      indent := indent ++ "  "
  return text

/-- One generated module contains exact catalogue aliases, source-body equations,
typed continuations, library realization choices and checked root assembly. -/
def source (program : Program) (output : Output) : Except String String := do
  let protocols := program.payload.protocols
  unless (protocols.map (·.name)).eraseDups.length == protocols.length do throw "original-root-duplicate-protocol"
  unless (program.payload.definitions.map (·.name)).eraseDups.length == program.payload.definitions.length do
    throw "original-root-duplicate-helper"
  let [(root, rootIndex)] := protocols.zipIdx.filter (fun pair => pair.1.signature == program.payload.entry.signature)
    | throw "original-root-entry"
  unless rootIndex + 1 == protocols.length do throw "original-root-entry-prefix"
  unless rootIndex == 1 do throw "original-root-family-count"
  unless root.outputs == [.boolean] do throw "original-root-output"
  unless root.roles.length == 2 do throw "original-root-roster"
  let associations ← LibraryAssociation.bottomUp program.snapshot output.libraries (protocols.take rootIndex)
  let [association] := associations | throw "original-root-family-count"
  unless association.selected.domain == "bls12-381.fr" do
    throw "original-root-realization-domain"
  let keys := associations.map fun association =>
    CalleeKey.mk association.signature 1 (Bindings.optionalPattern association.signature.inputs) []
  let sig : Signature := ⟨[], false, true, program.payload.definitions.map (·.helper), keys⟩
  let form ← normalize sig root.body 1 root.roles.length (Bindings.optionalPattern root.inputs)
  unless NormalForms.callsMatch form do throw "original-root-call-identity"
  let inputBinders := root.inputs.zipIdx.map fun (ty, index) => Binder.mk ("input" ++ toString index) (.component ty) index
  let assembly ← assemble program keys root.inputs inputBinders form 0
  unless !assembly.steps.isEmpty && assembly.identityReturn do throw "original-root-return-layout"
  let mut text := "module\n\npublic import " ++ output.sourceModule ++ "\npublic import " ++ association.selected.familyModule ++
    "\npublic import ZkcExamples.Structured.OriginalSumcheckCalls\n\n@[expose] public section\n\n" ++
    "/-! Generated by checks/RunGenerators.lean bindings from admitted typed source.\n" ++
    "Catalogue positions are generated selectors, not human origins or mathematical laws.\n" ++
    "Every body association and process equation is checked by the kernel. -/\n" ++
    "set_option autoImplicit false\nset_option maxRecDepth 50000\nset_option maxHeartbeats 8000000\n" ++
    "set_option backward.isDefEq.respectTransparency false\nnoncomputable section\nnamespace " ++ output.moduleName ++ "\n" ++
    "open Zkc.Source Zkc.Source.Structured\nopen ZkcExamples.Structured.OriginalSumcheckLibrary ZkcExamples.Structured.SumcheckVerifierBodies\n" ++
    "open ZkcExamples.Structured.OriginalSumcheckCalls\n" ++
    "abbrev imported := " ++ output.sourceModule ++ ".imported\nabbrev payload := imported.program.payload\n\n"
  for (_, index) in program.payload.definitions.zipIdx do
    text := text ++ "abbrev sourceHelper" ++ toString index ++ " : CheckedDefinition := payload.definitions.get ⟨" ++ toString index ++ ", by decide +kernel⟩\n" ++
      "theorem sourceHelper" ++ toString index ++ "_body : sourceHelper" ++ toString index ++ ".body = " ++ output.sourceModule ++ ".helper" ++ toString index ++ "Body := by kernel_rfl\n"
  for (_, index) in protocols.zipIdx do
    let name := "sourceProtocol" ++ toString index
    text := text ++ "abbrev " ++ name ++ " : CheckedProtocol := payload.protocols.get ⟨" ++ toString index ++ ", by decide +kernel⟩\n" ++
      "theorem " ++ name ++ "_member : " ++ name ++ " ∈ payload.protocols := List.get_mem _ _\n"
    if index < rootIndex then
      let some associated := associations[index]? | throw "original-root-callee-association"
      let maximum := associated.selected.maximum
      text := text ++ "def maximum" ++ toString index ++ " : Nat := " ++ toString maximum ++ "\n" ++
        "theorem " ++ name ++ "_origin :\n" ++
        "    ((imported.program.snapshot.definitions.filterMap (fun | .function function => some function | _ => none)).find? (fun function => function.name == " ++ name ++ ".name)).bind\n" ++
        "      (fun function => function.origin) = some " ++ Root.originSource (.protocol associated.origin) ++ " := by kernel_rfl\n" ++
        "theorem " ++ name ++ "_body : " ++ name ++ ".body = reduceBody maximum" ++ toString index ++ " := by kernel_rfl\n"
  text := text ++ "abbrev root := sourceProtocol" ++ toString rootIndex ++ "\n" ++
    "def sourceBody : Region protocolDialect root.inputs root.outputs :=\n  " ++ regionText root.body ++ "\n" ++
    "theorem root_body : root.body = sourceBody := by kernel_rfl\n" ++
    "theorem source_body : sourceBody = " ++ output.sourceModule ++ ".protocol" ++ toString rootIndex ++ "Body := by kernel_rfl\n\n" ++
    "variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]\n\n"
  for (_, index) in protocols.zipIdx do
    let prefixName := "protocolPrefix" ++ toString index
    let previous := if index == 0 then "[]" else "protocolPrefix" ++ toString (index - 1)
    text := text ++ "def " ++ prefixName ++ " : ProtocolTable (assignment F G) (signature (F := F) (G := G)) :=\n  "
    if index == 0 then text := text ++ "[]\n"
    else text := text ++ "extendProtocolTableOn (ringModel F G) (.silent _) actions (helpers payload).toOn " ++ previous ++
      " sourceProtocol" ++ toString (index - 1) ++ " Occurrence.iterations\n"
  text := text ++ "\ntheorem protocols_eq : payload.protocols = [sourceProtocol0, root] := by kernel_rfl\n" ++
    "theorem reduce_lookup (context : ProtocolContext) (self : Nat)\n" ++
    "    (args : Values (Component (assignment F G)) sourceProtocol0.inputs) :\n" ++
    "    invokeProtocol (Occurrence.table (ringModel F G) payload) sourceProtocol0.signature context self args =\n" ++
    "      sourceProtocol0.denoteWithOn (ringModel F G) (.silent _) actions (helpers payload).toOn [] Occurrence.iterations context self args := by\n" ++
    "  unfold Occurrence.table\n  rw [← helpers_on, protocols_eq]\n" ++
    "  simp only [List.foldl_cons, List.foldl_nil, extendProtocolTableOn]\n" ++
    "  rw [invokeProtocol_cons_other _ _ _ (by change root.signature.name ≠ sourceProtocol0.signature.name; decide +kernel), invokeProtocol_cons_same]\n\n" ++
    "theorem root_lookup (args : Values (Component (assignment F G)) root.inputs) :\n" ++
    "    invokeProtocol (Occurrence.table (ringModel F G) payload) root.signature {} 1 args =\n" ++
    "      root.denoteWithOn (ringModel F G) (.silent _) actions (helpers payload).toOn protocolPrefix1 Occurrence.iterations {} 1 args := by\n" ++
    "  unfold Occurrence.table\n  rw [← helpers_on, protocols_eq]\n" ++
    "  simp only [List.foldl_cons, List.foldl_nil, extendProtocolTableOn]\n  rw [invokeProtocol_cons_same]\n  rfl\n"
  -- Prefix at callee declaration and prefix after installing it are distinct.
  -- Each source closure captures its earlier declarations exactly once.
  for step in assembly.steps do
    let parameters ← parameterText step.parameters
    text := text ++ "\nabbrev " ++ step.name ++ " (" ++ step.arguments ++ " : " ++
      (if step.arguments == "tables" then "Evaluation.ComponentTables F G (signature (F := F) (G := G))"
       else "ProtocolTable (assignment F G) (signature (F := F) (G := G))") ++ ") " ++ parameters ++ " : PIR.Process (signature (F := F) (G := G)) (Values (Component (assignment F G)) " ++ typesText step.outputs ++ ") :=\n  " ++ step.process ++ "\n"
    if step.arguments == "protocols" then
      text := text ++ "abbrev " ++ step.name ++ "Realized " ++ parameters ++ " : PIR.Process (signature (F := F) (G := G)) (Values (Component (assignment F G)) " ++ typesText step.outputs ++ ") :=\n  " ++ step.realized ++ "\n"
  text := text ++ assembly.declarations
  let callSteps := assembly.steps.filter (·.callee.isSome)
  let some firstCall := callSteps.head? | throw "original-root-no-call"
  let some lastCall := callSteps.getLast? | throw "original-root-no-call"
  let some firstContext := firstCall.context | throw "original-root-no-context"
  let some lastContext := lastCall.context | throw "original-root-no-context"
  text := text ++ "abbrev firstContext : ProtocolContext := " ++ firstContext ++ "\n" ++
    "abbrev lastContext : ProtocolContext := " ++ lastContext ++ "\n" ++
    "abbrev reduceDefinition := sourceProtocol0\nabbrev maximum := maximum0\nabbrev protocolPrefix := protocolPrefix1 (F := F) (G := G)\n"
  let checks := assembly.steps.filter (fun step => step.helper.any (fun helper => helper.kind == .local))
  let some firstCheck := checks.head? | throw "original-root-no-check"
  unless checks.all (fun step => step.helper == firstCheck.helper) do throw "original-root-check-association"
  text := text ++ "abbrev checkContinuation := " ++ firstCheck.name ++ " (F := F) (G := G)\n"
  let calculations := assembly.steps.filter (fun step => step.helper.any (fun helper => helper.kind == .math))
  if !calculations.isEmpty then
    let [terminal] := calculations | throw "original-root-terminal-calculation"
    let some helper := terminal.helper | throw "original-root-terminal-calculation"
    text := text ++ "abbrev terminalHelper : Helper := " ++ (← helperAlias program helper) ++ "\n" ++
      "abbrev terminalCalculation := " ++ terminal.name ++ " (F := F) (G := G)\n"
  for step in callSteps do
    let parameters ← parameterText step.parameters
    let arguments := " ".intercalate (step.parameters.map (·.name))
    text := text ++ "theorem " ++ step.name ++ "_binding " ++ parameters ++ " :\n" ++
      "    " ++ step.name ++ " (protocolPrefix (F := F) (G := G)) " ++ arguments ++ " = " ++ step.name ++ "Realized (G := G) " ++ arguments ++ " := by\n" ++
      "  unfold " ++ step.name ++ " protocolPrefix protocolPrefix1 protocolPrefix0 extendProtocolTableOn\n" ++
      "  rw [invokeProtocol_cons_same]\n  unfold CheckedProtocol.denoteWithOn\n" ++
      "  rw [sourceProtocol0_body]\n  rfl\n\n"
  text := text ++ "theorem library_call_binding (site : String) (claim : Option F) (count service : Option Nat) :\n" ++
    "    invokeProtocol (protocolPrefix (F := F) (G := G)) reduceDefinition.signature (({} : ProtocolContext).enter site [0, 1]) 1\n" ++
    "      (.cons none (.cons none (.cons none (.cons claim (.cons count (.cons service .nil)))))) =\n" ++
    "      realizeCall payload maximum (({} : ProtocolContext).enter site [0, 1]) reduceDefinition.outputScopes\n" ++
    "      (.cons none (.cons none (.cons none (.cons claim (.cons count (.cons service .nil)))))) := by\n" ++
    "  unfold protocolPrefix protocolPrefix1 protocolPrefix0 extendProtocolTableOn\n" ++
    "  rw [invokeProtocol_cons_same]\n  unfold CheckedProtocol.denoteWithOn\n  rw [sourceProtocol0_body]\n  rfl\n\n"
  let inputParameters ← parameterText inputBinders
  let inputNames := " ".intercalate (inputBinders.map (·.name))
  let inputValues := valuesText (inputBinders.map (·.name))
  text := text ++ "\ndef process (tables : Evaluation.ComponentTables F G (signature (F := F) (G := G)))\n" ++
    "    (protocols : ProtocolTable (assignment F G) (signature (F := F) (G := G))) " ++ inputParameters ++ " : PIR.Process (signature (F := F) (G := G)) (Values (Component (assignment F G)) root.outputs) :=\n  " ++ spine assembly false ++ "\n\n" ++
    "theorem body_binding (tables : Evaluation.ComponentTables F G (signature (F := F) (G := G)))\n" ++
    "    (protocols : ProtocolTable (assignment F G) (signature (F := F) (G := G))) " ++ inputParameters ++ " :\n" ++
    "    sourceBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) actions tables.toOn 1 protocols {} Occurrence.iterations)\n" ++
    "      (" ++ inputValues ++ " : Values (Component (assignment F G)) root.inputs).get = process tables protocols " ++ inputNames ++ " := by\n  derive_process\n\n" ++
    "abbrev realized " ++ inputParameters ++ " :=\n  let tables := helpers (F := F) (G := G) payload\n  " ++ spine assembly true ++ "\n\n" ++
    "theorem realization_binding " ++ inputParameters ++ " :\n" ++
    "    process (helpers (F := F) (G := G) payload) protocolPrefix " ++ inputNames ++ " = realized (G := G) " ++ inputNames ++ " := by\n" ++
    realizationProof assembly ++ "\n" ++
    "theorem participant_binding " ++ inputParameters ++ " :\n" ++
    "    Occurrence.participant (ringModel F G) imported.program 1 (" ++ inputValues ++ ") = realized (G := G) " ++ inputNames ++ " := by\n" ++
    "  change invokeProtocol (Occurrence.table (ringModel F G) payload) root.signature {} 1 (" ++ inputValues ++ ") = _\n" ++
    "  rw [root_lookup (F := F) (G := G)]\n  unfold CheckedProtocol.denoteWithOn\n" ++
    "  change (root.body.denote (participantMeaningWithOn (ringModel F G) (.silent _) actions (helpers payload).toOn 1 protocolPrefix {} Occurrence.iterations)\n" ++
    "    (" ++ inputValues ++ " : Values (Component (assignment F G)) root.inputs).get).bind _ = _\n" ++
    "  rw [root_body, body_binding, realization_binding]\n" ++
    "  rw [ProtocolContext.mapScopes_root]\n" ++
    "  change (realized (G := G) " ++ inputNames ++ ").bind (fun (out : Values (Component (assignment F G)) [.boolean]) => .done (maskValues 1 (List.replicate 1 [1]) out)) = _\n" ++
    "  exact bind_mask_single_role _ 1\n\nend " ++ output.moduleName ++ "\n"
  return text


/-- Selection for the same checked source/normal-form boundary at an arbitrary
nominal model. Mathematical helper results remain indexed checked arguments. -/
structure TemplateOutput where
  moduleName : String
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
    "namespace " ++ output.moduleName ++
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
    "def template : Template definition signature " ++ toString output.role ++ " " ++
      toString definition.roles.length ++ " where\n  form := " ++ formLiteral form ++
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
    "end\nend " ++ output.moduleName ++ "\n"

end ZkcTools.StructuredSource.OriginalRoot
