module

public import ZkcTools.StructuredSource.Bindings.Generate
public import ZkcTools.StructuredSource.Bindings.Inputs
public import Zkc.Source.Structured.Bindings.Selection

@[expose] public section

/-! Callback views are generated from admitted typed regions. Selection is
checked against the original declaration; the readable process is checked
against the existing normalizer, including all optional returned positions. -/

namespace ZkcTools.StructuredSource.Bindings
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open ZkcTools.StructuredSource.Presentation
open Zkc.Source.Structured.Bindings

/-- Use the same typed traversal as the generated selection certificate. -/
def callbacks {inputs outputs : List Ty} (body : Region protocolDialect inputs outputs) :
    List RepeatSite := repeatSites body

def callbackName (protocolIndex callbackIndex : Nat) : String :=
  "protocol" ++ toString protocolIndex ++ "Callback" ++ toString callbackIndex

/-- Keep the small typed header reducible without reevaluating admission at
every role equation. The entire suffix is projected, never serialized. The
complete descriptor equality below checks this header and the shared body. -/
def repeatSiteText (selected : RepeatSite) (name : String) : String :=
  let source := name ++ "Selection.repeatSite"
  let suffix := "Eq.mp (show Region protocolDialect (" ++ source ++ ".spec.state ++ " ++
    source ++ ".context) " ++ source ++ ".outputs = Region protocolDialect " ++
    typesText (selected.spec.state ++ selected.context) ++ " " ++ typesText selected.outputs ++
    " from by kernel_rfl) " ++ source ++ ".next"
  "⟨" ++ ", ".intercalate [typesText selected.context, typesText selected.outputs,
    repeatText selected.spec, quoted selected.site, operandsText selected.operands,
    name ++ "Body", paren suffix] ++ "⟩"

/-- Optional, explicitly selected checked library presentation. All emitted
law bodies and their use are kernel checked. The default keeps every helper
opaque and requires no installed example library. -/
structure CallbackLibrary where
  imports : List String := []
  laws : List LawKey := []
  declarations : String := "def callbackKeys : List LawKey := []\n\ndef callbackResults : LawResults (ringModel F G) callbackKeys where\n  result := fun entry => entry.elim0\n\ntheorem callbackLaws_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :\n    LawsHold (helpers payload).toOn (callbackResults (F := F) (G := G)) input := by\n  intro entry\n  exact entry.elim0\n\n"
  lawResult : Nat → Nat → Option String := fun _ _ => none

def callbacksSource (program : Program) (output : Output)
    (library : CallbackLibrary := {}) : Except String String := do
  let keys := keys program
  let laws := library.laws
  let mut text := "module\n\npublic import " ++ output.moduleName ++ "\npublic import Zkc.Source.Structured.Bindings.Selection\n" ++
    String.join (library.imports.map fun name => "public import " ++ name ++ "\n") ++
    "\n@[expose] public section\n\n/-! Generated complete callback views. -/\nnamespace " ++
    output.moduleName ++ "Callbacks\nopen Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm " ++
    "Zkc.Source.Structured.Bindings\nopen " ++ output.moduleName ++
    "\nset_option maxRecDepth 50000\nset_option maxHeartbeats 8000000\nset_option smartUnfolding false\nnoncomputable section\n" ++
    "variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]\n\n"
  text := text ++ library.declarations
  for (definition, index) in program.payload.protocols.zipIdx do
    if !output.protocols.isEmpty && !output.protocols.contains index then continue
    let inventory := repeatInventory definition.body
    let selectedCallbacks := inventory.map (·.repeatSite)
    for (selected, callbackIndex) in inventory.zipIdx do
      let callback := selected.repeatSite
      let name := callbackName index callbackIndex
      let locator := toString callbackIndex ++ " " ++ definitionName index ++ ".body"
      text := text ++ "def " ++ name ++ "Selection : RepeatOccurrence " ++ definitionName index ++
        ".body :=\n  checkedRepeat " ++ locator ++ " (by kernel_rfl)\n\n" ++
        "def " ++ name ++ "Body : Region protocolDialect " ++
        typesText (.index :: (callback.spec.state ++ callback.spec.captures)) ++ " " ++
        typesText callback.spec.state ++ " :=\n  " ++ regionText callback.body ++ "\n\n" ++
        "abbrev " ++ name ++ "Site : RepeatSite :=\n  " ++ repeatSiteText callback name ++ "\n\n" ++
        "theorem " ++ name ++ "_body : " ++ name ++ "Site.body = " ++ name ++
        "Body := rfl\n\n" ++
        "theorem " ++ name ++ "_selected : (selectRepeat " ++ locator ++
        ").map (·.repeatSite) = some " ++ name ++ "Site := by\n  kernel_rfl\n\n" ++
        "def " ++ name ++ "Occurrence : RepeatAt " ++ name ++ "Site " ++ definitionName index ++
        ".body :=\n  selectedRepeat " ++ name ++ "_selected\n\n" ++
        "theorem " ++ name ++ "_position : " ++ name ++ "Occurrence.position = " ++
        natsText selected.position ++ " := by\n  kernel_rfl\n\n"
    for role in List.range definition.roles.length do
      if !output.roles.isEmpty && !output.roles.contains role then continue
      for (selected, callbackIndex) in inventory.zipIdx do
        let callback := selected.repeatSite
        let name := roleName index role ++ "Callback" ++ toString callbackIndex
        let inputs := .index :: (callback.spec.state ++ callback.spec.captures)
        let pattern := optionalPattern inputs
        let signature : Signature := ⟨laws, false, false, program.payload.definitions.map (·.helper) |>.filter (fun helper => !(laws.any (·.helper == helper))), keys⟩
        let naming : Naming signature.laws signature.callees pattern.scope := {
          carriers := .uniform "F" "G"
          tables := "(helpers (F := F) (G := G) payload).toOn"
          results := "callbackResults (F := F) (G := G)"
          lawResult := fun entry position => library.lawResult entry.val position
          context := "ctx"
          runs := "Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles " ++ toString role ++ ")"
          processes := "actualCallees payload calleeKeys" }
        let (_, names, printed) ← request signature callback.body role definition.roles.length pattern naming
        let signature := {signature with names := names}
        let args := inputs.zipIdx.map fun (_, i) => paren ("input.get " ++ positionText i)
        let checked := callbackName index callbackIndex
        text := text ++ "abbrev " ++ name ++ "Body := " ++ checked ++ "Body\n" ++
          "abbrev " ++ name ++ "Site := " ++ checked ++ "Site\n" ++
          "abbrev " ++ name ++ "Occurrence := " ++ checked ++ "Occurrence\n" ++
          "theorem " ++ name ++ "_body : " ++ name ++ "Site.body = " ++ name ++ "Body := " ++ checked ++ "_body\n" ++
          "theorem " ++ name ++ "_selected : (selectRepeat " ++ toString callbackIndex ++ " " ++
          definitionName index ++ ".body).map (·.repeatSite) = some " ++ name ++ "Site :=\n  " ++ checked ++ "_selected\n\n" ++
          "theorem " ++ name ++ "_position : " ++ name ++ "Occurrence.position = " ++
          natsText selected.position ++ " := " ++ checked ++ "_position\n\n" ++
          "def " ++ name ++ "Signature : Signature := " ++ signatureLiteral signature ++ "\n" ++
          "def " ++ name ++ "Pattern : InputPattern " ++ typesText inputs ++ " := " ++ patternText pattern ++ "\n\n" ++
          declarations (out := callback.spec.state) naming .outputs printed ⟨name, "(ctx : ProtocolContext)", ["ctx"]⟩ ++ "\n" ++
          "theorem " ++ name ++ "_normalized : normalize " ++ name ++ "Signature " ++ name ++ "Body " ++
          toString role ++ " " ++ toString definition.roles.length ++ " " ++ name ++ "Pattern = .ok " ++
          name ++ "Form := by\n  kernel_rfl\n\n" ++
          "theorem " ++ name ++ "_source (ctx : ProtocolContext)\n" ++
          "    (distinct : RosterDistinct ctx " ++ toString role ++ " " ++ toString definition.roles.length ++ ")\n" ++
          "    (input : Values (Component (assignment F G)) " ++ typesText inputs ++ ") :\n" ++
          "    " ++ name ++ "Body.denote (participantMeaningWith (.silent _) (participantActions F G)\n" ++
          "      (helpers payload) (ctx.roles " ++ toString role ++ ") (payload.plainProtocolTable F G) ctx) input.get =\n" ++
          "      " ++ app (name ++ "Process") ("ctx" :: args) ++ " := by\n" ++
          "  have equation := sound_uniform " ++ name ++ "Signature " ++ name ++ "Body " ++ toString role ++ " " ++
          toString definition.roles.length ++ " " ++ name ++ "Pattern " ++ name ++ "Form " ++
          name ++ "_normalized " ++ name ++ "_calls ctx distinct\n" ++
          "    (helpers payload) (payload.plainProtocolTable F G) (callbackResults (F := F) (G := G))\n" ++
          "    (actualCallees payload calleeKeys) (optionalBinders (ringModel F G) input) input\n" ++
          "    (optional_environment _ _) (callbackLaws_hold _) (callees_hold _)\n" ++
          binderEta inputs "input" ++ "  rw [binderEta] at equation\n" ++
          "  exact equation.trans (" ++ name ++ "_presentation (F := F) (G := G) ctx " ++ " ".intercalate args ++ ")\n\n"
        text := text ++ "theorem " ++ name ++ "_function (ctx : ProtocolContext)\n" ++
          "    (distinct : RosterDistinct ctx " ++ toString role ++ " " ++ toString definition.roles.length ++ ") :\n" ++
          "    (Runs.uniform (helpers (F := F) (G := G) payload) (payload.plainProtocolTable F G) ctx (ctx.roles " ++
          toString role ++ ")).callback " ++ repeatText callback.spec ++ " " ++ name ++ "Body =\n" ++
          "      (fun (input : Values (Component (assignment F G)) " ++ typesText inputs ++ ") => " ++
          app (name ++ "Process") ("ctx" :: args) ++ ") := by\n" ++
          "  funext input\n  exact " ++ name ++ "_source ctx distinct input\n\n"
      let name := roleName index role
      let pattern := optionalPattern definition.inputs
      let signature : Signature := ⟨projectionLaws program, false, false,
        program.payload.definitions.map (·.helper), keys⟩
      let naming : Naming signature.laws signature.callees pattern.scope := {
        carriers := .uniform "F" "G"
        tables := "(helpers (F := F) (G := G) payload).toOn"
        results := "projectionResults (F := F) (G := G)"
        context := "ctx"
        runs := "Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles " ++ toString role ++ ")"
        processes := name ++ "Callees"
        -- These are function-body spelling hints, never occurrence selectors.
        -- Refuse a nonunique hint; exact association is carried by Selection.
        -- The full function and invocation equations check every replacement.
        callback := fun spec body => do
          let [(_, callbackIndex)] := selectedCallbacks.zipIdx.filter fun (callback, _) =>
            repeatText callback.spec == repeatText spec && regionText callback.body == regionText body
            | none
          let args := (.index :: (spec.state ++ spec.captures)).zipIdx.map fun (_, i) =>
            app "input.get" [positionText i]
          pure ("fun (input : Values (Component (assignment F G)) " ++ typesText (.index :: (spec.state ++ spec.captures)) ++
            ") => " ++ app (name ++ "Callback" ++ toString callbackIndex ++ "Process") ("ctx" :: args)) }
      let (_, _, printed) ← request signature definition.body role definition.roles.length pattern naming
      let references := expressionIdentifiers printed.process
      let usedCallbacks := selectedCallbacks.zipIdx.filter fun (_, i) =>
        references.contains (name ++ "Callback" ++ toString i ++ "Process")
      let params := " ".intercalate ((pattern.scope.zip printed.binders).map fun (slot, name) =>
        "(" ++ name ++ " : " ++ slotType naming slot ++ ")")
      let applied := app (name ++ "ReadableProcess (F := F) (G := G)") ("ctx" :: printed.binders)
      let readableParameters := explicitParameters ("(ctx : ProtocolContext) " ++ params)
        ("ctx" :: printed.binders) printed.process
      text := text ++ "noncomputable def " ++ name ++
        "ReadableProcess " ++ readableParameters ++ " :\n    " ++ processType naming (.outputs (out := definition.outputs)) ++
        " :=\n" ++ printed.process ++ "\n\n" ++
        "theorem " ++ name ++ "_readable (ctx : ProtocolContext)\n" ++
        "    (" ++ (if usedCallbacks.isEmpty then "_distinct" else "distinct") ++
        " : RosterDistinct ctx " ++ toString role ++ " " ++ toString definition.roles.length ++ ") " ++ params ++ " :\n" ++
        "    " ++ app (name ++ "Process (F := F) (G := G)") ("ctx" :: printed.binders) ++ " = " ++ applied ++ " := by\n"
      if usedCallbacks.isEmpty then
        text := text ++ "  unfold " ++ name ++ "Process " ++ name ++ "ReadableProcess\n  rfl\n\n"
      else
        -- Rewrite a local equation so simplification never consumes the goal
        -- before the remaining definitional equality is checked by `exact`.
        text := text ++ "  have equation := Eq.refl " ++
          app (name ++ "Process (F := F) (G := G)") ("ctx" :: printed.binders) ++ "\n"
        for (_, i) in usedCallbacks do
          text := text ++ "  have callback" ++ toString i ++ " := " ++ name ++ "Callback" ++ toString i ++
            "_function (F := F) (G := G) ctx distinct\n  unfold " ++ name ++ "Callback" ++ toString i ++
            "Body " ++ callbackName index i ++ "Body at callback" ++ toString i ++ "\n"
        let equations := ", ".intercalate (usedCallbacks.map fun (_, i) =>
          "callback" ++ toString i)
        text := text ++ "  conv_rhs at equation => unfold " ++ name ++ "Process; simp only [" ++
          equations ++ "]\n  exact equation\n\n"
      let masked := "maskValues (ctx.roles " ++ toString role ++ ") (ctx.mapScopes " ++ definitionName index ++ ".inputScopes) input"
      let args := definition.inputs.zipIdx.map fun (_, i) => app (paren masked ++ ".get") [positionText i]
      text := text ++ "noncomputable def " ++ name ++ "ReadableView (ctx : ProtocolContext)\n" ++
        "    (input : Values (Component (assignment F G)) " ++ definitionName index ++ ".inputs) :\n" ++
        "    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) " ++ definitionName index ++ ".outputs) :=\n  " ++
        app (name ++ "ReadableProcess") ("ctx" :: args) ++ ".bind fun out =>\n    .done (maskValues (ctx.roles " ++
        toString role ++ ") (ctx.mapScopes " ++ definitionName index ++ ".outputScopes) out)\n\n" ++
        "theorem " ++ name ++ "_readable_invocation (ctx : ProtocolContext)\n" ++
        "    (distinct : RosterDistinct ctx " ++ toString role ++ " " ++ toString definition.roles.length ++ ")\n" ++
        "    (input : Values (Component (assignment F G)) " ++ definitionName index ++ ".inputs) :\n" ++
        "    invokeProtocol (payload.plainProtocolTable F G) " ++ definitionName index ++ ".signature ctx\n" ++
        "      (ctx.roles " ++ toString role ++ ") input = " ++ name ++ "ReadableView ctx input := by\n" ++
        "  refine (" ++ name ++ "_invocation ctx distinct input).trans ?_\n" ++
        "  exact congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles " ++ toString role ++
        ") (ctx.mapScopes " ++ definitionName index ++ ".outputScopes) out))\n" ++
        "    (" ++ name ++ "_readable (F := F) (G := G) ctx distinct " ++ " ".intercalate args ++ ")\n\n"
  return text ++ "end\nend " ++ output.moduleName ++ "Callbacks\n"

end ZkcTools.StructuredSource.Bindings
