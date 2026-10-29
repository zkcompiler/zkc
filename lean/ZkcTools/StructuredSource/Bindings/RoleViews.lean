module

public import ZkcTools.StructuredSource.Bindings.Callbacks
public import Zkc.Source.Structured.InputVisibility
public import Zkc.Source.Structured.LoopPresentation
public import Zkc.Source.Structured.PlainHelpers
public import Zkc.Source.Structured.OccurrencePresentation
public import Zkc.Source.Structured.ProtocolPresentation

@[expose] public section

/-! Scope-derived callback presentations. Names only decorate declarations and
binders. State selection, optionality, return shape and every operation come
from the admitted typed region and its checked normal form. -/
namespace ZkcTools.StructuredSource.Bindings.RoleViews
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Source.Structured.Bindings
open ZkcTools.StructuredSource.Presentation

/-- One name per source coordinate, including coordinates hidden at this role.
There are no layout, visibility, law or semantic fields. -/
structure CallbackNames where
  body : String
  roles : List String
  inputs : List String

def roleFinish (role : Nat) : (types : List Ty) → List (List Nat) → Values (fun _ : Ty => Carried) types
  | [], _ => .nil
  | _ :: types, scopes => .cons (if (scopes.headD []).contains role then .optional else .absent)
      (roleFinish role types scopes.tail)

def appendPattern : {left right : List Ty} → InputPattern left → InputPattern right → InputPattern (left ++ right)
  | _, _, .nil, right => right
  | _, _, .cons input rest, right => .cons input (appendPattern rest right)

def patternNames : {types : List Ty} → InputPattern types → List String → List String
  | _, .nil, _ => []
  | _, .cons input rest, names => match input with
    | .absent => patternNames rest names.tail
    | _ => names.headD "missingName" :: patternNames rest names.tail

def params (scope : Scope) (names : List String) : String :=
  " ".intercalate ((scope.zip names).map fun (slot, name) =>
    "(" ++ name ++ " : " ++ slotType (laws := []) (callees := []) (initial := []) {carriers := .uniform "F" "G"} slot ++ ")")

def tupleParts (name : String) : Nat → List String
  | 0 => []
  | 1 => [name]
  | n + 2 => (name ++ ".1") :: tupleParts (name ++ ".2") (n + 1)

def stateValues : {types : List Ty} → Values (fun _ : Ty => Carried) types → List String → String
  | _, .nil, _ => ".nil"
  | _, .cons carried rest, names => match carried with
    | .absent => app ".cons" ["none", stateValues rest names]
    | .optional => app ".cons" [names.headD "missingState", stateValues rest names.tail]
    | .present => app ".cons" [app "some" [names.headD "missingState"], stateValues rest names.tail]

/-- Symbolic role callback and loop, including empty local state. The index is
present, state visibility is source-owned, captures remain optional, and nested
effects are retained. All emitted equations require ordinary kernel checking. -/
def callbackSource (program : Program) (protocolIndex callbackIndex role : Nat)
    (names : CallbackNames) (naming : {scope : Scope} → Naming [] (keys program) scope)
    (available availableHold : String) : Except String String := do
  let some definition := program.payload.protocols[protocolIndex]? | throw "role-view-protocol"
  let some callback := (callbacks definition.body)[callbackIndex]? | throw "role-view-callback"
  let some name := names.roles[role]? | throw "role-view-role-name"
  let inputs := .index :: (callback.spec.state ++ callback.spec.captures)
  unless names.inputs.length == inputs.length do throw "role-view-input-names"
  let statePattern := InputVisibility.rolePattern role callback.spec.state callback.spec.stateScopes
  let pattern : InputPattern inputs := .cons .present (appendPattern statePattern (optionalPattern callback.spec.captures))
  let finish := roleFinish role callback.spec.state callback.spec.stateScopes
  let signature : Signature := ⟨[], true, false, [], keys program⟩
  let (useNames, form) ← normalizeMatched signature callback.body role definition.roles.length pattern
  let naming := naming (scope := pattern.scope)
  let localNames := patternNames pattern names.inputs
  let process : String := (processText naming (.presented finish) localNames form 2).run' pattern.scope.length
  let references := expressionIdentifiers process
  let stateNames := patternNames statePattern ((names.inputs.drop 1).take callback.spec.state.length)
  let captures := names.inputs.drop (1 + callback.spec.state.length)
  let ordered := (localNames.take 1 ++ captures ++ stateNames).filter references.contains
  let processArgs := (if references.contains "ctx" then ["ctx"] else []) ++ ordered
  let processParams := " ".intercalate (processArgs.map fun input =>
    if input == "ctx" then "(ctx : ProtocolContext)" else
      let index := (localNames.zipIdx.find? (·.1 == input)).map Prod.snd |>.getD 0
      "(" ++ input ++ " : " ++ slotType naming (pattern.scope[index]?.getD (.value .index)) ++ ")")
  let applied := app (name ++ "Process (F := F) (G := G)") processArgs
  let state := app (name ++ "State (F := F) (G := G)") stateNames
  let tupleType := "Tuple (assignment F G) (carried " ++ name ++ "Finish)"
  let parts := tupleParts "result" stateNames.length
  let embedded := app (name ++ "State (F := F) (G := G)") parts
  let substitute := fun input =>
    if let some (_, index) := stateNames.zipIdx.find? (·.1 == input) then parts[index]!
    else if input == names.inputs.headD "index" then "index" else input
  let step := "fun result index => " ++ app (name ++ "Process (F := F) (G := G)") (processArgs.map substitute)
  let roster := toString definition.roles.length
  let fullParams := params pattern.scope localNames
  let stateParams := params statePattern.scope stateNames
  let capParams := params (optionalPattern callback.spec.captures).scope captures
  let rawInput := ".cons (some " ++ localNames.headD "index" ++ ") (" ++ state ++ ".append " ++ valuesText captures ++ ")"
  let body := names.body ++ "Body"
  let fn := names.body ++ "Fn"
  let distinct := "RosterDistinct ctx " ++ toString role ++ " " ++ roster
  return "def " ++ name ++ "Finish : Values (fun _ : Ty => Carried) " ++ typesText callback.spec.state ++ " :=\n  " ++ finishText finish ++ "\n\n" ++
    "def " ++ name ++ "State " ++ stateParams ++ " : Values (Component (assignment F G)) " ++ typesText callback.spec.state ++ " :=\n  " ++ stateValues finish stateNames ++ "\n\n" ++
    "theorem " ++ name ++ "State_masked (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles " ++ toString role ++ ") " ++ stateParams ++ " :\n  maskValues self (ctx.mapScopes " ++ scopesText callback.spec.stateScopes ++ ") " ++ state ++ " = " ++ state ++ " := by\n  subst self\n  exact maskValues_embed (Value := assignment F G) ctx " ++ toString role ++ " " ++ name ++ "Finish _ rfl " ++ valuesText stateNames ++ "\n\n" ++
    "def " ++ name ++ "Signature : Signature := " ++ "⟨[], true, " ++ toString useNames ++ ", [], calleeKeys⟩\n" ++
    "def " ++ name ++ "Pattern : InputPattern " ++ typesText inputs ++ " := " ++ patternText pattern ++ "\n" ++
    "noncomputable def " ++ name ++ "Form : Form " ++ name ++ "Signature.laws " ++ name ++ "Signature.callees " ++ name ++ "Pattern.scope " ++ typesText callback.spec.state ++ " :=\n  " ++ formLiteralWith naming.callbackBody form ++ "\n\n" ++
    "noncomputable def " ++ name ++ "Process " ++ processParams ++ " : " ++ processType naming (.presented finish) ++ " :=\n" ++ process ++ "\n\n" ++
    "theorem " ++ name ++ "_normalized : normalize " ++ name ++ "Signature " ++ body ++ " " ++ toString role ++ " " ++ roster ++ " " ++ name ++ "Pattern = .ok " ++ name ++ "Form := by kernel_rfl\n" ++
    "theorem " ++ name ++ "_calls : " ++ name ++ "Form.CallsMatch := by apply Prod.ext <;> kernel_rfl\n" ++
    "theorem " ++ name ++ "_finishes : " ++ name ++ "Form.finishes " ++ name ++ "Finish = true := by kernel_rfl\n\n" ++
    "theorem " ++ name ++ "_presentation (ctx : ProtocolContext) " ++ fullParams ++ " :\n  " ++
    denotation naming (.presented finish) (name ++ "Form") localNames ++ " = " ++ applied ++ " := by kernel_rfl\n\n" ++
    "theorem " ++ name ++ "_observed (ctx : ProtocolContext) (distinct : " ++ distinct ++ ")\n  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))\n  (masked : ProtocolPresentation.Masked protocols) " ++ fullParams ++ " :\n  " ++
    body ++ ".denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions\n    (Occurrence.helpers (ringModel F G) payload) (ctx.roles " ++ toString role ++ ") protocols ctx Occurrence.iterations)\n    ((" ++ name ++ "Pattern).environment (ringModel F G) " ++ valuesText localNames ++ ").get =\n  " ++ name ++ "Form.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)\n    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations\n      (Occurrence.helpers (ringModel F G) payload) protocols ctx " ++ toString role ++ ")\n    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) " ++ valuesText localNames ++ " :=\n  normalize_occurrence_sound " ++ name ++ "Signature " ++ body ++ " " ++ toString role ++ " " ++ roster ++ "\n    " ++ name ++ "Pattern " ++ name ++ "Form " ++ name ++ "_normalized " ++ name ++ "_calls distinct\n    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)\n\n" ++
    "theorem " ++ name ++ "_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles " ++ toString role ++ ")\n  (distinct : " ++ distinct ++ ") " ++ fullParams ++ " :\n  " ++ fn ++ " (F := F) (G := G) ctx self " ++ paren rawInput ++ " =\n    " ++ applied ++ ".bind (fun result => .done " ++ embedded ++ ") := by\n  subst self\n  exact (callback_sound_uniform " ++ name ++ "Signature " ++ body ++ " " ++ toString role ++ " " ++ roster ++ " " ++ name ++ "Pattern " ++ name ++ "Finish " ++ name ++ "Form\n    " ++ name ++ "_normalized " ++ name ++ "_calls " ++ name ++ "_finishes ctx distinct\n    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) " ++ paren available ++ "\n    " ++ valuesText localNames ++ " _ (by kernel_rfl) (emptyLaws _ _) (" ++ availableHold ++ " _)).trans\n    (congrArg₂ PIR.Process.bind (" ++ name ++ "_presentation ctx " ++ " ".intercalate localNames ++ ")\n      (by funext result; exact congrArg PIR.Process.done (by kernel_rfl)))\n\n" ++
    "theorem " ++ name ++ "_fold (ctx : ProtocolContext) (distinct : " ++ distinct ++ ")" ++ (if capParams.isEmpty then "" else " " ++ capParams) ++ "\n  (count : Nat) (bounded : count ≤ " ++ names.body ++ "Spec.maximum)\n  (state : Values (Component (assignment F G)) " ++ typesText callback.spec.state ++ ") (initial : " ++ tupleType ++ ")\n  (start : maskValues (ctx.roles " ++ toString role ++ ") (ctx.mapScopes " ++ names.body ++ "Spec.stateScopes) state = " ++
    app (name ++ "State (F := F) (G := G)") (tupleParts "initial" stateNames.length) ++ ") :\n  denoteRepeat " ++ names.body ++ "Spec ctx (ctx.roles " ++ toString role ++ ") (some count) state " ++ valuesText captures ++ " (" ++ fn ++ " ctx (ctx.roles " ++ toString role ++ ")) =\n    (Finite.fold (" ++ step ++ ") (List.range' 0 count) initial).bind (fun result => .done " ++ embedded ++ ") := by\n  exact LoopPresentation.presentUniform " ++ names.body ++ "Spec ctx (ctx.roles " ++ toString role ++ ") (by simp) _ _\n    (fun result => " ++ embedded ++ ") (fun result => " ++ name ++ "State_masked ctx _ rfl " ++ " ".intercalate parts ++ ")\n    (" ++ step ++ ") (fun result index => " ++ name ++ "_process ctx _ rfl distinct " ++ " ".intercalate (localNames.map substitute) ++ ") count bounded state initial start\n\n"

/-- A complete body view. The only normalizer is the source normalizer, and
invocation masks are fixed by the admitted declaration rather than the hints. -/
def protocolSource (program : Program) (protocolIndex role : Nat) (body name : String)
    (inputNames : List String) (naming : {scope : Scope} → Naming [] (keys program) scope)
    (available availableHold : String) : Except String String := do
  let some definition := program.payload.protocols[protocolIndex]? | throw "role-view-protocol"
  unless inputNames.length == definition.inputs.length do throw "role-view-input-names"
  let pattern := InputVisibility.rolePattern role definition.inputs definition.inputScopes
  let signature : Signature := ⟨[], true, false, [], keys program⟩
  let (useNames, form) ← normalizeMatched signature definition.body role definition.roles.length pattern
  let naming := naming (scope := pattern.scope)
  let localNames := patternNames pattern inputNames
  let process : String := (processText naming .outputs localNames form 2).run' pattern.scope.length
  let references := expressionIdentifiers process
  let processArgs := (if references.contains "ctx" then ["ctx"] else []) ++ localNames.filter references.contains
  let processParams := " ".intercalate (processArgs.map fun input =>
    if input == "ctx" then "(ctx : ProtocolContext)" else
      let index := (localNames.zipIdx.find? (·.1 == input)).map Prod.snd |>.getD 0
      "(" ++ input ++ " : " ++ slotType naming ((pattern.scope[index]?).getD (.value .index)) ++ ")")
  let applied := app (name ++ "Process (F := F) (G := G)") processArgs
  let fullParams := params pattern.scope localNames
  let environment := app (name ++ "Pattern.environment") ["(ringModel F G)", valuesText localNames]
  let roster := toString definition.roles.length
  let distinct := "RosterDistinct ctx " ++ toString role ++ " " ++ roster
  let definitionName := body ++ "Definition"
  let input := definition.inputs.zipIdx.map fun (_, i) => app "input.get" [positionText i]
  let localInput := patternNames pattern input
  let viewArgs := processArgs.map fun name =>
    if name == "ctx" then "ctx" else
      let index := (localNames.zipIdx.find? (·.1 == name)).map Prod.snd |>.getD 0
      localInput[index]!
  let staticOutputs := definition.outputs.zipIdx.map fun (_, i) =>
    if (definition.outputScopes[i]?.getD []).contains role then app "out.get" [positionText i] else "none"
  let mask := valuesText staticOutputs
  let view := "(" ++ app (name ++ "Process (F := F) (G := G)") viewArgs ++ ").bind fun out => .done " ++ mask
  return "def " ++ name ++ "Signature : Signature := " ++ "⟨[], true, " ++ toString useNames ++ ", [], calleeKeys⟩\n" ++
    "def " ++ name ++ "Pattern : InputPattern " ++ typesText definition.inputs ++ " := " ++ patternText pattern ++ "\n" ++
    "noncomputable def " ++ name ++ "Form : Form " ++ name ++ "Signature.laws " ++ name ++ "Signature.callees " ++ name ++ "Pattern.scope " ++ typesText definition.outputs ++ " :=\n  " ++ formLiteralWith naming.callbackBody form ++ "\n\n" ++
    "noncomputable def " ++ name ++ "Process " ++ processParams ++ " : " ++ processType naming (.outputs (out := definition.outputs)) ++ " :=\n" ++ process ++ "\n\n" ++
    "theorem " ++ name ++ "_normalized : normalize " ++ name ++ "Signature " ++ body ++ "Body " ++ toString role ++ " " ++ roster ++ " " ++ name ++ "Pattern = .ok " ++ name ++ "Form := by kernel_rfl\n" ++
    "theorem " ++ name ++ "_calls : " ++ name ++ "Form.CallsMatch := by apply Prod.ext <;> kernel_rfl\n\n" ++
    "theorem " ++ name ++ "_presentation (ctx : ProtocolContext) " ++ fullParams ++ " :\n  " ++
    denotation naming (.outputs (out := definition.outputs)) (name ++ "Form") localNames ++ " = " ++ applied ++ " := by kernel_rfl\n\n" ++
    "theorem " ++ name ++ "_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles " ++ toString role ++ ")\n  (distinct : " ++ distinct ++ ") " ++ fullParams ++ " :\n  " ++ body ++ "Fn (F := F) (G := G) ctx self " ++ paren environment ++ " = " ++ applied ++ " := by\n  subst self\n  exact (sound_uniform " ++ name ++ "Signature " ++ body ++ "Body " ++ toString role ++ " " ++ roster ++ " " ++ name ++ "Pattern " ++ name ++ "Form\n    " ++ name ++ "_normalized " ++ name ++ "_calls ctx distinct\n    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) " ++ paren available ++ "\n    " ++ valuesText localNames ++ " _ rfl (emptyLaws _ _) (" ++ availableHold ++ " _)).trans\n    (" ++ name ++ "_presentation ctx " ++ " ".intercalate localNames ++ ")\n\n" ++
    "theorem " ++ name ++ "_observed (ctx : ProtocolContext) (distinct : " ++ distinct ++ ")\n  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))\n  (masked : ProtocolPresentation.Masked protocols) " ++ fullParams ++ " :\n  " ++ body ++ "Body.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions\n    (Occurrence.helpers (ringModel F G) payload) (ctx.roles " ++ toString role ++ ") protocols ctx Occurrence.iterations)\n    (" ++ environment ++ ").get =\n  " ++ name ++ "Form.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)\n    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations\n      (Occurrence.helpers (ringModel F G) payload) protocols ctx " ++ toString role ++ ")\n    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) " ++ valuesText localNames ++ " :=\n  normalize_occurrence_sound " ++ name ++ "Signature " ++ body ++ "Body " ++ toString role ++ " " ++ roster ++ "\n    " ++ name ++ "Pattern " ++ name ++ "Form " ++ name ++ "_normalized " ++ name ++ "_calls distinct\n    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)\n\n" ++
    "noncomputable def " ++ name ++ "View (ctx : ProtocolContext) (input : Values (Component (assignment F G)) " ++ typesText definition.inputs ++ ") :\n    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) " ++ typesText definition.outputs ++ ") :=\n  " ++ view ++ "\n\n" ++
    "theorem " ++ name ++ "_invocation (ctx : ProtocolContext) (distinct : " ++ distinct ++ ")\n  (input : Values (Component (assignment F G)) " ++ typesText definition.inputs ++ ") :\n  invokeProtocol (payload.plainProtocolTable F G) " ++ definitionName ++ ".signature ctx (ctx.roles " ++ toString role ++ ") input = " ++ name ++ "View ctx input := by\n  have environment : " ++ name ++ "Pattern.environment (ringModel F G) " ++ valuesText localInput ++ " =\n      maskValues (ctx.roles " ++ toString role ++ ") (ctx.mapScopes " ++ definitionName ++ ".inputScopes) input := by\n    rw [InputVisibility.mask_context (model := ringModel F G) distinct " ++ definitionName ++ ".inputScopes (by decide +kernel)]\n    " ++ " ".intercalate (definition.inputs.map fun _ => "cases input with | cons _ input =>") ++ " cases input; rfl\n  have equation := invocation payload " ++ definitionName ++ " (List.get_mem _ _) " ++ name ++ "Signature " ++ toString role ++ " " ++ roster ++ " " ++ name ++ "Pattern " ++ name ++ "Form\n    " ++ name ++ "_normalized " ++ name ++ "_calls (emptyResults _) " ++ paren available ++ " ctx distinct input " ++ valuesText localInput ++ "\n    environment (emptyLaws _ _) (" ++ availableHold ++ " _)\n  rw [" ++ name ++ "_presentation] at equation\n  refine equation.trans ?_\n  apply congrArg (PIR.Process.bind _)\n  funext out\n  rw [InputVisibility.mask_context (model := ringModel F G) distinct " ++ definitionName ++ ".outputScopes (by decide +kernel)]\n  " ++ " ".intercalate (definition.outputs.map fun _ => "cases out with | cons _ out =>") ++ " cases out; rfl\n\n"

structure ProtocolNames where
  space : String
  body : String
  roles : List String
  inputs : List String
  callbacks : List CallbackNames

/-- An entirely source-derived spelling option, useful for clients that do not
need domain vocabulary in their generated presentations. -/
def ordinalNames (program : Program) : List ProtocolNames :=
  program.payload.protocols.zipIdx.map fun (definition, index) => {
    space := "Protocol" ++ toString index
    body := "body"
    roles := (List.range definition.roles.length).map (fun role => "role" ++ toString role)
    inputs := (List.range definition.inputs.length).map (fun input => "input" ++ toString input)
    callbacks := (callbacks definition.body).zipIdx.map fun (callback, index) => {
      body := "callback" ++ toString index
      roles := (List.range definition.roles.length).map (fun role => "role" ++ toString role ++ "Callback" ++ toString index)
      inputs := (List.range (1 + callback.spec.state.length + callback.spec.captures.length)).map
        (fun input => "input" ++ toString input) } }

/-- Assemble whole source views in declaration order. Prior checked invocations
replace actual callees once, preserving their complete optional return masks.
The catalogue supplies spelling only; the source supplies every layout. -/
def source (program : Program) (output : Output) (bindingModule : String)
    (names : List ProtocolNames) : Except String String := do
  unless names.length == program.payload.protocols.length do throw "role-view-protocol-names"
  let mut text := "module\n\npublic import " ++ output.sourceModule ++ "\npublic import Zkc.Source.Structured.LoopPresentation\npublic import Zkc.Source.Structured.InputVisibility\npublic import Zkc.Source.Structured.PlainHelpers\npublic import Zkc.Source.Structured.OccurrencePresentation\npublic import Zkc.Source.Structured.ProtocolPresentation\n\n@[expose] public section\n\n/-! Generated scope-derived source presentations. Regenerate with the Lean role-view printer. -/\nnamespace " ++ output.moduleName ++ "\nopen Zkc.Source Zkc.Source.Structured NormalForm Zkc.Source.Structured.Bindings\nset_option maxRecDepth 50000\nset_option maxHeartbeats 8000000\nset_option smartUnfolding false\nset_option backward.isDefEq.respectTransparency false\nset_option autoImplicit false\nset_option maxErrors 12\nset_option linter.unusedVariables false\nset_option linter.unusedSectionVars false\nset_option linter.unusedTactic false\nnoncomputable section\nvariable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]\n\nabbrev program : Program := " ++ output.programExpression ++ "\nabbrev payload := program.payload\nabbrev calleeKeys := " ++ bindingModule ++ ".calleeKeys\n\n"
  text := text ++ "theorem observedCallees_hold\n  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))\n  (masked : ProtocolPresentation.Masked protocols) {inputs : List Ty}\n  (input : Values (Component (assignment F G)) inputs) :\n  CalleesHold protocols (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) input := by\n  apply ProtocolPresentation.callees_hold _ _ _ masked\n  · intro entry binders others\n    fin_cases entry <;> exact optional_fill _ _ binders others\n  · intro entry\n    fin_cases entry <;> decide +kernel\n\n"
  let mut available := "actualCallees payload calleeKeys"
  let mut availableHold := bindingModule ++ ".callees_hold"
  let mut references : List (Nat × String) := []
  let mut keyOffset := 0
  for (definition, protocolIndex) in program.payload.protocols.zipIdx do
    let some named := names[protocolIndex]? | throw "role-view-protocol-names"
    unless named.roles.length == definition.roles.length && named.callbacks.length == (callbacks definition.body).length do
      throw "role-view-declaration-names"
    text := text ++ "namespace " ++ named.space ++ "\n\nabbrev " ++ named.body ++ "Definition : CheckedProtocol := payload.protocols.get ⟨" ++ toString protocolIndex ++ ", by decide +kernel⟩\nabbrev " ++ named.body ++ "Inputs : List Ty := " ++ typesText definition.inputs ++ "\nabbrev " ++ named.body ++ "Outputs : List Ty := " ++ typesText definition.outputs ++ "\nabbrev " ++ named.body ++ "Body := " ++ named.body ++ "Definition.body\ntheorem " ++ named.body ++ "Body_checked : " ++ named.body ++ "Definition.body = " ++ named.body ++ "Body := rfl\ntheorem " ++ named.body ++ "Body_raw : " ++ named.body ++ "Definition.raw = " ++ named.body ++ "Body.erase := by kernel_rfl\n\n"
    let functions := (named.body, definition.inputs, definition.outputs) ::
      ((callbacks definition.body).zip named.callbacks).map (fun (callback, names) =>
        (names.body, .index :: (callback.spec.state ++ callback.spec.captures), callback.spec.state))
    for ((callback, hints), callbackIndex) in ((callbacks definition.body).zip named.callbacks).zipIdx do
      let checked := bindingModule ++ "Callbacks." ++ roleName protocolIndex 0 ++ "Callback" ++ toString callbackIndex
      text := text ++ "abbrev " ++ hints.body ++ "State : List Ty := " ++ typesText callback.spec.state ++ "\nabbrev " ++ hints.body ++ "Captures : List Ty := " ++ typesText callback.spec.captures ++ "\nabbrev " ++ hints.body ++ "Maximum := " ++ toString callback.spec.maximum ++ "\nabbrev " ++ hints.body ++ "Spec : RepeatSpec := " ++ repeatText callback.spec ++ "\ndef " ++ hints.body ++ "Body := " ++ checked ++ "Body\ntheorem " ++ hints.body ++ "_selected : findRepeat " ++ quoted callback.site ++ " " ++ named.body ++ "Definition.body = some ⟨_, _, " ++ hints.body ++ "Body⟩ := " ++ checked ++ "_selected\n\n"
    for (body, inputs, outputs) in functions do
      text := text ++ "def " ++ body ++ "Fn (ctx : ProtocolContext) (self : Nat) : RegionFunction (Component (assignment F G)) (participantInterface F G) (" ++ typesText inputs ++ ", " ++ typesText outputs ++ ") :=\n  fun args => " ++ body ++ "Body.denote (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers payload) self (payload.plainProtocolTable F G) ctx) args.get\n\n"
    for (callback, hints) in (callbacks definition.body).zip named.callbacks do
      if callback.body.erase.operations.all OccurrencePresentation.contextFree then
        let body := hints.body ++ "Body"
        let fn := hints.body ++ "Fn"
        text := text ++ "theorem " ++ hints.body ++ "_occurrence (ctx : ProtocolContext) (self : Nat)\n  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))\n  (args : Values (Component (assignment F G)) (.index :: (" ++ hints.body ++ "Spec.state ++ " ++ hints.body ++ "Spec.captures))) :\n  " ++ body ++ ".denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions\n    (Occurrence.helpers (ringModel F G) payload) self protocols ctx Occurrence.iterations) args.get =\n    (" ++ fn ++ " (F := F) (G := G) ctx self args).interpret Occurrence.actions := by\n  simpa only [" ++ fn ++ "] using\n    (OccurrencePresentation.local_callback payload ctx self " ++ body ++ " (by kernel_rfl) protocols\n      (payload.plainProtocolTable F G) args)\n\n"
    for role in List.range definition.roles.length do
      let naming : {scope : Scope} → Naming [] (keys program) scope := fun {_} => {
        carriers := .uniform "F" "G", tables := "(plainHelpers (F := F) (G := G) payload).toOn"
        results := "emptyResults (ringModel F G)", context := "ctx"
        runs := "Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles " ++ toString role ++ ")"
        processes := available
        callee := fun entry => (references.find? (·.1 == entry.val)).map Prod.snd
        callback := fun spec body => do
          let (_, hints) ← ((callbacks definition.body).zip named.callbacks).find? fun (callback, _) =>
            repeatText callback.spec == repeatText spec && regionText callback.body == regionText body
          pure (hints.body ++ "Fn ctx (ctx.roles " ++ toString role ++ ")")
        callbackBody := fun spec body => do
          let (_, hints) ← ((callbacks definition.body).zip named.callbacks).find? fun (callback, _) =>
            repeatText callback.spec == repeatText spec && regionText callback.body == regionText body
          pure (hints.body ++ "Body")
        repeatHead := fun spec => some ("denoteRepeat " ++ repeatText spec ++ " ctx (ctx.roles " ++ toString role ++ ")") }
      for (_, callbackIndex) in (callbacks definition.body).zipIdx do
        let some hints := named.callbacks[callbackIndex]? | throw "role-view-callback-names"
        text := text ++ (← callbackSource program protocolIndex callbackIndex role hints naming available availableHold)
      let some name := named.roles[role]? | throw "role-view-role-name"
      text := text ++ (← protocolSource program protocolIndex role named.body name named.inputs naming available availableHold)
      if definition.name == program.payload.entry.name then
        text := text ++ "theorem " ++ name ++ "_participant (input : Values (Component (assignment F G)) payload.entry.inputs) :\n  program.participant F G " ++ toString role ++ " input = " ++ name ++ "View {} input := by\n  exact (payload.protocolTable_forgetSites (F := F) (G := G) payload.entry.signature {} " ++ toString role ++ " input).trans\n    (" ++ name ++ "_invocation {} (RosterDistinct.root _ _) input)\n\n"
      let qualified := named.space ++ "." ++ name
      let entry := "⟨" ++ toString (keyOffset + role) ++ ", by decide +kernel⟩"
      let replacement := "fun ctx binders => " ++ qualified ++ "View (F := F) (G := G) ctx ((optionalPattern " ++ typesText definition.inputs ++ ").environment (ringModel F G) binders)"
      let updated := "boundCallees" ++ toString (keyOffset + role)
      text := text ++ "end " ++ named.space ++ "\n\nnoncomputable def " ++ updated ++ " : CalleeProcesses (ringModel F G) calleeKeys :=\n  " ++ app "Function.update" [paren available, entry, paren replacement] ++ "\ntheorem " ++ updated ++ "_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :\n  CalleesHold (payload.plainProtocolTable F G) " ++ updated ++ " input := by\n  apply callees_update _ (actualCallees payload calleeKeys) " ++ paren available ++ " " ++ entry ++ " _ input (" ++ bindingModule ++ ".callees_hold input) (" ++ availableHold ++ " input)\n  intro ctx binders distinct\n  exact " ++ qualified ++ "_invocation ctx distinct _\n\nnamespace " ++ named.space ++ "\n\n"
      references := references ++ [(keyOffset + role, replacement)]
      available := updated
      availableHold := updated ++ "_hold"
    text := text ++ "end " ++ named.space ++ "\n\n"
    keyOffset := keyOffset + definition.roles.length
  return text ++ "end\nend " ++ output.moduleName ++ "\n"

end ZkcTools.StructuredSource.Bindings.RoleViews
