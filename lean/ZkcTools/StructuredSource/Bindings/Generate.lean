module

public import ZkcTools.StructuredSource.Presentation
public import Zkc.Source.Structured.Bindings.Assembly

@[expose] public section

/-! Generated structural assembly from an admitted program. The printer is
untrusted. Its output contains exact normalizer, call identity, presentation
and whole invocation proofs; the kernel rechecks every emitted equation.
There is no source-name dispatch and no separate execution language. -/

namespace ZkcTools.StructuredSource.Bindings
open Lean Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open ZkcTools.StructuredSource.Presentation
open Zkc.Source.Structured.Bindings

structure Output where
  moduleName : String
  sourceModule : String
  programExpression : String
  importedExpression : String
  /-- Empty lists select every admitted declaration/role. These are selection
  data, never switches in the denotational semantics. -/
  protocols : List Nat := []
  roles : List Nat := []

def definitionName (index : Nat) := "definition" ++ toString index
def roleName (index role : Nat) := "protocol" ++ toString index ++ "Role" ++ toString role

def keys (program : Program) : List CalleeKey :=
  program.payload.protocols.flatMap fun definition =>
    (List.range definition.roles.length).map fun role =>
      ⟨definition.signature, role, optionalPattern definition.inputs, []⟩

def projectionIndices {inputs : List Ty} : {outputs : List Ty} → Operands inputs outputs → List Nat
  | _, .nil => []
  | _, .cons position rest => position.index :: projectionIndices rest

def projectionLaws (program : Program) : List LawKey :=
  program.payload.definitions.filterMap fun definition =>
    if definition.kind == .math then
      match definition.body with
      | .ret operands => some ⟨definition.helper, .passes (projectionIndices operands), []⟩
      | _ => none
    else none

def projectedValues {inputs : List Ty} (head : String) : {outputs : List Ty} → Operands inputs outputs → String
  | _, .nil => ".nil"
  | _, .cons position rest => app ".cons" [app (head ++ ".get") [positionText position.index], projectedValues head rest]

/-- Expose the constructor tuple before applying the curried presentation.
An inductive heterogeneous environment has no definitional eta rule. Keeping
this equality explicit also avoids unfolding the whole process to solve it. -/
def binderEta (types : List Ty) (environment : String) : String :=
  let entries := types.zipIdx.map fun (_, i) => app (paren environment ++ ".get") [positionText i]
  "  have binderEta : optionalBinders (ringModel F G) " ++ paren environment ++ " = " ++ valuesText entries ++ " := by\n    " ++
    " ".intercalate (types.map fun _ => "cases input with | cons _ input =>") ++ " cases input; rfl\n"

def source (program : Program) (output : Output) : Except String String := do
  let selectedKeys := keys program
  let laws := projectionLaws program
  let keyText := listText (selectedKeys.map calleeText)
  let mut text := "module\n\npublic import " ++ output.sourceModule ++
    "\npublic import Zkc.Source.Structured.Bindings.Assembly\npublic import Zkc.Source.Structured.NormalForm.Sites\npublic import Mathlib.Data.Fintype.Basic\n" ++
    "public import Mathlib.Tactic.FinCases\n\n@[expose] public section\n\n" ++
    "/-! Generated from admitted source by ZkcTools.StructuredSource.Bindings.Generate.\n" ++
    "Regenerate; every independent presentation is checked by the kernel. -/\n\n" ++
    "namespace " ++ output.moduleName ++ "\nopen Zkc.Source Zkc.Source.Structured " ++
    "Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings\n" ++
    "set_option maxRecDepth 50000\nset_option maxHeartbeats 8000000\n" ++
    "set_option smartUnfolding false\nnoncomputable section\n\n" ++
    "abbrev sourceImported := " ++ output.importedExpression ++ "\n" ++
    "abbrev program : Program := " ++ output.programExpression ++ "\n" ++
    "abbrev payload : UnitPayload := program.payload\n" ++
    "def sourceContracts := program.snapshot.contracts\n\n"
  for definition in program.payload.protocols.zipIdx do
    let (definition, index) := definition
    text := text ++ "abbrev " ++ definitionName index ++ " : CheckedProtocol :=\n  payload.protocols.get ⟨" ++
      toString index ++ ", by decide +kernel⟩\n" ++
      "theorem " ++ definitionName index ++ "_member : " ++ definitionName index ++
      " ∈ payload.protocols := List.get_mem _ _\n\n"
    unless definition.roles.length > 0 do throw "bindings-empty-roster"
  text := text ++ "def calleeKeys : List CalleeKey := " ++ keyText ++ "\n\n" ++
    "variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]\n\n" ++
    "theorem callees_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :\n" ++
    "    CalleesHold (payload.plainProtocolTable F G) (actualCallees payload calleeKeys) input := by\n" ++
    "  apply actualCallees_hold\n  · intro entry\n    fin_cases entry\n"
  for (definition, index) in program.payload.protocols.zipIdx do
    for _ in List.range definition.roles.length do
      text := text ++ "    · exact ⟨" ++ definitionName index ++ ", " ++ definitionName index ++ "_member, rfl⟩\n"
  text := text ++ "  · intro entry binders others\n    fin_cases entry <;> exact optional_fill _ _ binders others\n" ++
    "  · intro entry\n    fin_cases entry <;> simp [calleeKeys, calleeAt]\n\n"
  text := text ++ "def projectionKeys : List LawKey := " ++ listText (laws.map lawText) ++ "\n\n"
  let mut projectionBodies : List String := []
  for definition in program.payload.definitions do
    if definition.kind == .math then
      match definition.body with
      | .ret operands => projectionBodies := projectionBodies ++ ["fun args => " ++ projectedValues "args" operands]
      | _ => pure ()
  let projectionFunction := projectionBodies.foldr (fun body rest => app "Fin.cases" [paren body, rest])
    "(fun entry => entry.elim0)"
  text := text ++ "noncomputable def projectionResults : LawResults (ringModel F G) projectionKeys where\n" ++
    "  result := " ++ projectionFunction ++ "\n\ntheorem projectionLaws_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :\n" ++
    "    LawsHold (helpers payload).toOn (projectionResults (F := F) (G := G)) input := by\n" ++
    "  intro entry\n  fin_cases entry\n"
  for (definition, index) in program.payload.definitions.zipIdx do
    if definition.kind == .math then
      match definition.body with
      | .ret operands =>
        let values := paren (projectedValues "args" operands ++ " : Values (Component (assignment F G)) " ++ typesText definition.outputs)
        text := text ++ "  · intro args values passed\n" ++
          "    have body := helper_body payload (payload.definitions.get ⟨" ++ toString index ++ ", by decide +kernel⟩)\n" ++
          "      (List.get_mem _ _) args\n" ++
          "    change _ = PIR.Process.done " ++ values ++ " at body\n" ++
          "    have selected : passEntries args " ++ typesText definition.outputs ++ " " ++ natsText (projectionIndices operands) ++
          " = some " ++ paren values ++ " := by\n" ++
          "      " ++ (" ".intercalate ((List.range definition.inputs.length).map fun _ => "cases args with | cons _ args =>")) ++ " rfl\n" ++
          "    exact body.trans (congrArg PIR.Process.done (Option.some.inj (selected.symm.trans passed)))\n"
      | _ => pure ()
  text := text ++ "\n"
  -- Every role in a declaration sees the same earlier selected bindings.
  -- Publish each new entry once, only for subsequent declarations. This keeps
  -- unselected dependencies on the checked actual table and avoids cyclic views.
  let mut available := "actualCallees payload calleeKeys"
  let mut availableHold := "callees_hold"
  let mut keyOffset := 0
  for (definition, index) in program.payload.protocols.zipIdx do
    let current := available
    let currentHold := availableHold
    for role in List.range definition.roles.length do
      if !output.protocols.isEmpty && !output.protocols.contains index then continue
      if !output.roles.isEmpty && !output.roles.contains role then continue
      let name := roleName index role
      let processes := name ++ "Callees"
      text := text ++ "noncomputable def " ++ processes ++ " : CalleeProcesses (ringModel F G) calleeKeys :=\n  " ++
        current ++ "\n\ntheorem " ++ processes ++ "_hold {inputs : List Ty}\n" ++
        "    (input : Values (Component (assignment F G)) inputs) :\n" ++
        "    CalleesHold (payload.plainProtocolTable F G) " ++ processes ++ " input :=\n  " ++
        currentHold ++ " input\n\n"
      let pattern := optionalPattern definition.inputs
      let signature : Signature := ⟨laws, false, false, program.payload.definitions.map (·.helper), selectedKeys⟩
      let naming : Naming signature.laws signature.callees pattern.scope := {
        carriers := .uniform "F" "G"
        tables := "(helpers (F := F) (G := G) payload).toOn"
        results := "projectionResults (F := F) (G := G)"
        context := "ctx"
        runs := "Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles " ++ toString role ++ ")"
        processes := processes }
      let (_, names, printed) ← (request signature definition.body role definition.roles.length pattern naming).mapError
        (fun refusal => "protocol " ++ toString index ++ " role " ++ toString role ++ ": " ++ refusal)
      let decl : Presentation.Declaration := ⟨name, "(ctx : ProtocolContext)", ["ctx"]⟩
      text := text ++ "def " ++ name ++ "Signature : Signature := ⟨projectionKeys, false, " ++ boolText names ++
        ", program.payload.definitions.map (·.helper), calleeKeys⟩\n" ++
        "def " ++ name ++ "Pattern : InputPattern " ++ definitionName index ++ ".inputs := " ++ patternText pattern ++ "\n\n" ++
        declarations (out := definition.outputs) naming .outputs printed decl
          (some ("Form " ++ name ++ "Signature.laws calleeKeys " ++ name ++ "Pattern.scope " ++
            typesText definition.outputs)) ++ "\n" ++
        "theorem " ++ name ++ "_normalized : normalize " ++ name ++ "Signature " ++ definitionName index ++
        ".body " ++ toString role ++ " " ++ toString definition.roles.length ++ " " ++ name ++
        "Pattern = .ok " ++ name ++ "Form := by\n  kernel_rfl\n\n"
      let masked := "maskValues (ctx.roles " ++ toString role ++ ") (ctx.mapScopes " ++ definitionName index ++ ".inputScopes) input"
      let args := definition.inputs.zipIdx |>.map fun (_, i) => "(" ++ paren masked ++ ").get " ++ positionText i
      text := text ++ "noncomputable def " ++ name ++ "View (ctx : ProtocolContext)\n" ++
        "    (input : Values (Component (assignment F G)) " ++ definitionName index ++ ".inputs) :\n" ++
        "    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) " ++ definitionName index ++ ".outputs) :=\n  " ++
        app (name ++ "Process") ("ctx" :: args.map paren) ++ ".bind fun out =>\n    .done (maskValues (ctx.roles " ++
        toString role ++ ") (ctx.mapScopes " ++ definitionName index ++ ".outputScopes) out)\n\n" ++
        "theorem " ++ name ++ "_invocation (ctx : ProtocolContext)\n" ++
        "    (distinct : RosterDistinct ctx " ++ toString role ++ " " ++ toString definition.roles.length ++ ")\n" ++
        "    (input : Values (Component (assignment F G)) " ++ definitionName index ++ ".inputs) :\n" ++
        "    invokeProtocol (payload.plainProtocolTable F G) " ++ definitionName index ++ ".signature ctx\n" ++
        "      (ctx.roles " ++ toString role ++ ") input = " ++ name ++ "View ctx input := by\n" ++
        "  have equation := invocation (F := F) (G := G) payload " ++ definitionName index ++ " " ++ definitionName index ++ "_member\n" ++
        "    " ++ name ++ "Signature " ++ toString role ++ " " ++ toString definition.roles.length ++ " " ++ name ++ "Pattern\n" ++
        "    " ++ name ++ "Form " ++ name ++ "_normalized " ++ name ++ "_calls\n" ++
        "    (projectionResults (F := F) (G := G)) " ++ processes ++ " ctx distinct input\n" ++
        "    (optionalBinders (ringModel F G) (" ++ masked ++ "))\n" ++
        "    (optional_environment _ _) (projectionLaws_hold _) (" ++ processes ++ "_hold _)\n" ++
        binderEta definition.inputs masked ++ "  rw [binderEta] at equation\n" ++
        "  exact equation.trans (congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles " ++ toString role ++
        ") (ctx.mapScopes " ++ definitionName index ++ ".outputScopes) out))\n" ++
        "    (" ++ name ++ "_presentation (F := F) (G := G) ctx " ++ " ".intercalate (args.map paren) ++ "))\n\n" ++
        "theorem " ++ name ++ "_certificate :\n" ++
        "    Zkc.Verification.Certificate sourceImported\n" ++
        "      (fun p ctx input => invokeProtocol (p.payload.plainProtocolTable F G) " ++ definitionName index ++
        ".signature ctx (ctx.roles " ++ toString role ++ ") input)\n" ++
        "      (Zkc.Source.Structured.Bindings.Contract (fun ctx _ => RosterDistinct ctx " ++ toString role ++ " " ++
        toString definition.roles.length ++ ") (" ++ name ++ "View (F := F) (G := G))) := by\n" ++
        "  exact ⟨fun ctx input distinct => " ++ name ++ "_invocation ctx distinct input⟩\n\n"
      if definition.name == program.payload.entry.name then
        text := text ++ "theorem " ++ name ++ "_participant\n" ++
          "    (input : Values (Component (assignment F G)) program.payload.entry.inputs) :\n" ++
          "    program.participant F G " ++ toString role ++ " input = " ++ name ++ "View {} input := by\n" ++
          "  exact (payload.protocolTable_forgetSites (F := F) (G := G) payload.entry.signature {} " ++
          toString role ++ " input).trans (" ++ name ++ "_invocation {} (RosterDistinct.root _ _) input)\n\n"
      let updated := name ++ "BoundCallees"
      let entry := "⟨" ++ toString (keyOffset + role) ++ ", by decide +kernel⟩"
      let replacement := "fun ctx binders => " ++ name ++ "View (F := F) (G := G) ctx " ++
        "((optionalPattern " ++ typesText definition.inputs ++ ").environment (ringModel F G) binders)"
      text := text ++ "noncomputable def " ++ updated ++ " : CalleeProcesses (ringModel F G) calleeKeys :=\n  " ++
        app "Function.update" [paren available, entry, paren replacement] ++ "\n\n" ++
        "theorem " ++ updated ++ "_hold {inputs : List Ty}\n" ++
        "    (input : Values (Component (assignment F G)) inputs) :\n" ++
        "    CalleesHold (payload.plainProtocolTable F G) " ++ updated ++ " input := by\n" ++
        "  apply callees_update _ (actualCallees payload calleeKeys) " ++ paren available ++
        " " ++ entry ++ " _ input (callees_hold input) (" ++ availableHold ++ " input)\n" ++
        "  intro ctx binders distinct\n  exact " ++ name ++ "_invocation ctx distinct _\n\n"
      available := updated
      availableHold := updated ++ "_hold"
    keyOffset := keyOffset + definition.roles.length
  text := text ++ "end\nend " ++ output.moduleName ++ "\n"
  return text

end ZkcTools.StructuredSource.Bindings
