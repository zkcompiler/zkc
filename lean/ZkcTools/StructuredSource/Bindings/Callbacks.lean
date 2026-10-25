module

public import ZkcTools.StructuredSource.Bindings.Generate
public import ZkcTools.StructuredSource.Bindings.Inputs

@[expose] public section

/-! Callback views are generated from admitted typed regions. Selection is
checked against the original declaration; the readable process is checked
against the existing normalizer, including all optional returned positions. -/

namespace ZkcTools.StructuredSource.Bindings
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open ZkcTools.StructuredSource.Presentation
open Zkc.Source.Structured.Bindings

structure Callback where
  spec : RepeatSpec
  body : Region protocolDialect (.index :: (spec.state ++ spec.captures)) spec.state
  site : String

def callbacks {inputs outputs : List Ty} : Region protocolDialect inputs outputs → List Callback
  | .ret _ | .stop _ => []
  | .bind body next => callbacks body ++ callbacks next
  | .letOp op _ bodies next =>
    let inner := match op, bodies with
      | .repeat spec site, .cons body .nil => ⟨spec, body, site⟩ :: callbacks body
      | _, _ => []
    inner ++ callbacks next

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
    for role in List.range definition.roles.length do
      if !output.roles.isEmpty && !output.roles.contains role then continue
      for (callback, callbackIndex) in (callbacks definition.body).zipIdx do
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
        text := text ++ "def " ++ name ++ "Body : Region protocolDialect " ++ typesText inputs ++ " " ++
          typesText callback.spec.state ++ " :=\n  " ++ regionText callback.body ++ "\n\n" ++
          "theorem " ++ name ++ "_selected : Zkc.Source.Structured.Bindings.findRepeat " ++ quoted callback.site ++
          " " ++ definitionName index ++ ".body = some ⟨_, _, " ++ name ++ "Body⟩ := by\n  kernel_rfl\n\n" ++
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
        callback := fun spec body => do
          let (_, callbackIndex) ← (callbacks definition.body).zipIdx.find? fun (callback, _) =>
            repeatText callback.spec == repeatText spec && regionText callback.body == regionText body
          let args := (.index :: (spec.state ++ spec.captures)).zipIdx.map fun (_, i) =>
            app "input.get" [positionText i]
          pure ("fun (input : Values (Component (assignment F G)) " ++ typesText (.index :: (spec.state ++ spec.captures)) ++
            ") => " ++ app (name ++ "Callback" ++ toString callbackIndex ++ "Process") ("ctx" :: args)) }
      let (_, _, printed) ← request signature definition.body role definition.roles.length pattern naming
      let params := " ".intercalate ((pattern.scope.zip printed.binders).map fun (slot, name) =>
        "(" ++ name ++ " : " ++ slotType naming slot ++ ")")
      let applied := app (name ++ "ReadableProcess (F := F) (G := G)") ("ctx" :: printed.binders)
      text := text ++ "set_option linter.unusedVariables false in\nnoncomputable def " ++ name ++
        "ReadableProcess (ctx : ProtocolContext) " ++ params ++ " :\n    " ++ processType naming (.outputs (out := definition.outputs)) ++
        " :=\n" ++ printed.process ++ "\n\n" ++
        "-- Reflexivity is a fallback when simplification leaves a definitionally equal goal.\n" ++
        "set_option linter.unusedTactic false in\n" ++
        "set_option linter.unusedSimpArgs false in\n" ++
        "set_option linter.unreachableTactic false in\n" ++
        "theorem " ++ name ++ "_readable (ctx : ProtocolContext)\n" ++
        "    (" ++ (if (callbacks definition.body).isEmpty then "_distinct" else "distinct") ++
        " : RosterDistinct ctx " ++ toString role ++ " " ++ toString definition.roles.length ++ ") " ++ params ++ " :\n" ++
        "    " ++ app (name ++ "Process (F := F) (G := G)") ("ctx" :: printed.binders) ++ " = " ++ applied ++ " := by\n" ++
        "  unfold " ++ name ++ "Process " ++ name ++ "ReadableProcess\n"
      if (callbacks definition.body).isEmpty then
        text := text ++ "  rfl\n\n"
      else
        for (_, i) in (callbacks definition.body).zipIdx do
          text := text ++ "  have callback" ++ toString i ++ " := " ++ name ++ "Callback" ++ toString i ++
            "_function (F := F) (G := G) ctx distinct\n  unfold " ++ name ++ "Callback" ++ toString i ++
            "Body at callback" ++ toString i ++ "\n"
        let equations := ", ".intercalate ((callbacks definition.body).zipIdx.map fun (_, i) =>
          "callback" ++ toString i)
        text := text ++ "  simp only [" ++ equations ++ "]\n  all_goals rfl\n\n"
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
