module

public import ZkcTools.StructuredSource.Bindings.Callbacks

@[expose] public section

/-! Untrusted printing of exact call and repeat continuations. The equations
are checked against the existing normal form; no execution evaluator is added.
Prefix selection retains existing effects, guards and stops. -/
namespace ZkcTools.StructuredSource.Bindings
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open ZkcTools.StructuredSource.Presentation

def headCallSource {laws : List LawKey} {callees : List CalleeKey} {scope : Scope}
    {outputs : List Ty} (naming : Naming laws callees scope)
    (form : Form laws callees scope outputs) (name : String) : Except String String := do
  let .apply callee _ roles site args next := form | throw "bindings-head-call-required"
  let names := inputNames naming.inputs 0
  let params := " ".intercalate ((scope.zip names).map fun (slot, name) =>
    "(" ++ name ++ " : " ++ slotType naming slot ++ ")")
  let key := calleeAt callees callee
  let outputType := valuesType naming key.signature.outputs true
  let inputType := "Values (Component (assignment F G)) " ++ typesText key.signature.inputs
  let arguments := valuesText (argumentsText naming names args)
  let continuation : String := (processText naming .outputs ("result" :: names) next 2).run' (scope.length + 1)
  let applied := " ".intercalate ("ctx" :: names)
  let inputParameters := explicitParameters ("(ctx : ProtocolContext) " ++ params)
    ("ctx" :: names) arguments
  let continuationParameters := explicitParameters
    ("(ctx : ProtocolContext) " ++ params ++ " (result : " ++ outputType ++ ")")
    ("ctx" :: "result" :: names) continuation
  return "noncomputable def " ++ name ++ "CallContext (ctx : ProtocolContext) : ProtocolContext :=\n  ctx.enter " ++ quoted site ++ " " ++ natsText roles ++ "\n\n" ++
    "noncomputable def " ++ name ++ "CallInput " ++ inputParameters ++ " : " ++ inputType ++ " :=\n  " ++ arguments ++ "\n\n" ++
    "noncomputable def " ++ name ++ "Continuation " ++ continuationParameters ++ " :\n  " ++ processType naming (.outputs (out := outputs)) ++ " :=\n" ++ continuation ++ "\n\n" ++
    "theorem " ++ name ++ "_call (ctx : ProtocolContext) " ++ params ++ " :\n  " ++ name ++ "Process (F := F) (G := G) " ++ applied ++ " =\n    (invokeProtocol (payload.plainProtocolTable F G) " ++ signatureText key.signature ++ "\n      (" ++ name ++ "CallContext ctx) ((" ++ name ++ "CallContext ctx).roles " ++ toString key.role ++ ")\n      (" ++ name ++ "CallInput " ++ applied ++ ")).bind (" ++ name ++ "Continuation " ++ applied ++ ") := by\n  kernel_rfl\n\n"

/-- A printer-side cursor through a prefix. The returned scope and residual
are the existing indexed Form; indentation locates the exact printed suffix. -/
structure RepeatCursor (laws : List LawKey) (callees : List CalleeKey) (outputs : List Ty) where
  scope : Scope
  names : List String
  form : Form laws callees scope outputs
  indent : Nat := 2

def repeatCursor {laws : List LawKey} {callees : List CalleeKey} {outputs : List Ty}
    (site : String) (indent : Nat := 2) : {scope : Scope} → List String → Form laws callees scope outputs →
      Option (RepeatCursor laws callees outputs)
  | scope, names, form@(.repeat _ found _ _ _ _ next) =>
      if found == site then some ⟨scope, names, form, indent⟩
      else repeatCursor site indent (binderName scope.length none :: names) next
  | scope, names, .owned _ _ _ next | scope, names, .math _ _ next |
      scope, names, .strict _ _ next | scope, names, .compute _ _ _ next =>
      repeatCursor site indent (binderName scope.length none :: names) next
  | _, names, .byLaw _ _ next => repeatCursor site indent names next
  | _, names, .guard _ _ _ next => repeatCursor site (indent + 4) names next
  | scope, names, .split _ (.halt _) present =>
      repeatCursor site (indent + 2) (binderName scope.length none :: names) present
  | _, _, _ => none

/-- Select an application after a pure linear prefix, refusing branches,
receives, repeats and earlier calls. Selection does not assert a helper law. -/
def applicationCursor {laws : List LawKey} {callees : List CalleeKey} {outputs : List Ty}
    (site : String) : {scope : Scope} → List String → Form laws callees scope outputs →
      Option (RepeatCursor laws callees outputs)
  | scope, names, form@(.apply _ _ _ found _ _) =>
      if found == site then some ⟨scope, names, form, 2⟩ else none
  | scope, names, .owned _ _ _ next | scope, names, .math _ _ next |
      scope, names, .strict _ _ next | scope, names, .compute _ _ _ next =>
      applicationCursor site (binderName scope.length none :: names) next
  | _, names, .byLaw _ _ next => applicationCursor site names next
  | _, _, _ => none

/-- Emit an exact setup/frame/call split, retaining the original continuation.
Only existing Form syntax is printed, followed by a kernel-checked equation. -/
def callSplitSource {laws : List LawKey} {callees : List CalleeKey} {scope : Scope}
    {outputs : List Ty} (naming : Naming laws callees scope)
    (form : Form laws callees scope outputs) (name site : String) : Except String String := do
  let initialNames := inputNames naming.inputs 0
  let some cursor := applicationCursor site initialNames form | throw "bindings-linear-call-required"
  let .apply callee _ roles found args next := cursor.form | throw "bindings-call-required"
  let key := calleeAt callees callee
  let params := " ".intercalate ((scope.zip initialNames).map fun (slot, n) =>
    "(" ++ n ++ " : " ++ slotType naming slot ++ ")")
  let frameType := "Binders (ringModel F G) " ++ listText (cursor.scope.map slotText)
  let frameParams := " ".intercalate ((cursor.scope.zip cursor.names).map fun (slot, n) =>
    "(" ++ n ++ " : " ++ slotType naming slot ++ ")")
  let frameNames := cursor.scope.zipIdx.map fun (_, i) => app "frame.get" [positionText i]
  let full : String := (processText naming .outputs initialNames form 2).run' scope.length
  let suffix : String := (processText naming .outputs cursor.names cursor.form 2).run' cursor.scope.length
  unless full.endsWith suffix do throw "bindings-call-prefix-print"
  let prefixText := (full.dropEnd suffix.length).toString ++ "  .done " ++ valuesText cursor.names
  let continuation : String := (processText naming .outputs ("result" :: frameNames) next 2).run' (cursor.scope.length + 1)
  let callInput := valuesText (argumentsText naming frameNames args)
  let applied := " ".intercalate ("ctx" :: initialNames)
  let setupParameters := explicitParameters ("(ctx : ProtocolContext) " ++ params)
    ("ctx" :: initialNames) prefixText
  let continuationParameters := explicitParameters
    ("(ctx : ProtocolContext) (frame : " ++ name ++ "SetupFrame (F := F) (G := G)) (result : " ++ valuesType naming key.signature.outputs true ++ ")")
    ["ctx", "frame", "result"] continuation
  return "abbrev " ++ name ++ "SetupFrame := " ++ frameType ++ "\n\n" ++
    "def " ++ name ++ "MakeSetupFrame " ++ frameParams ++ " : " ++ name ++ "SetupFrame (F := F) (G := G) :=\n  " ++ valuesText cursor.names ++ "\n\n" ++
    "noncomputable def " ++ name ++ "Setup " ++ setupParameters ++ " : PIR.Process (participantInterface F G) (" ++ name ++ "SetupFrame (F := F) (G := G)) :=\n" ++ prefixText ++ "\n\n" ++
    "def " ++ name ++ "SetupInput (frame : " ++ name ++ "SetupFrame (F := F) (G := G)) : " ++ valuesType naming key.signature.inputs true ++ " :=\n  " ++ callInput ++ "\n\n" ++
    "def " ++ name ++ "SetupContext (ctx : ProtocolContext) : ProtocolContext := ctx.enter " ++ quoted found ++ " " ++ natsText roles ++ "\n\n" ++
    "noncomputable def " ++ name ++ "SetupContinuation " ++ continuationParameters ++ " : " ++ processType naming (.outputs (out := outputs)) ++ " :=\n" ++ continuation ++ "\n\n" ++
    "theorem " ++ name ++ "_setup_split (ctx : ProtocolContext) " ++ params ++ " :\n  " ++ name ++ "Process (F := F) (G := G) " ++ applied ++ " =\n    (" ++ name ++ "Setup " ++ applied ++ ").bind (fun frame =>\n      (invokeProtocol (payload.plainProtocolTable F G) " ++ signatureText key.signature ++ " (" ++ name ++ "SetupContext ctx) ((" ++ name ++ "SetupContext ctx).roles " ++ toString key.role ++ ") (" ++ name ++ "SetupInput frame)).bind (" ++ name ++ "SetupContinuation ctx frame)) := by\n  unfold " ++ name ++ "Process " ++ name ++ "Setup " ++ name ++ "SetupInput " ++ name ++ "SetupContinuation " ++ name ++ "SetupContext\n  have bindValue {A B : Type} (value : A) (next : A → PIR.Process (participantInterface F G) B) :\n      (PIR.Process.done value).bind next = next value := rfl\n  simp only [PIR.Process.bind_assoc, bindValue]\n  all_goals kernel_rfl\n\n"

/-- Print a congruence proof along the selected existing prefix. Optional
components and guards are split symbolically; every stopping branch is retained. -/
def repeatPrefixProof {laws : List LawKey} {callees : List CalleeKey} {initial : Scope}
    {outputs : List Ty} (naming : Naming laws callees initial) (site : String) :
    {scope : Scope} → List String → Form laws callees scope outputs → Nat → Except String String
  | scope, names, .repeat _ found _ _ _ _ next, indent =>
      if found == site then pure (pad indent ++ "kernel_rfl\n")
      else bindPrefix scope names next indent
  | scope, names, .owned _ _ _ next, indent
  | scope, names, .math _ _ next, indent
  | scope, names, .strict _ _ next, indent
  | scope, names, .compute _ _ _ next, indent => bindPrefix scope names next indent
  | _, names, .byLaw _ _ next, indent => repeatPrefixProof naming site names next indent
  | scope, names, .split subject (.halt _) present, indent => do
      let name := binderName scope.length none
      let tail ← repeatPrefixProof naming site (name :: names) present (indent + 2)
      pure (pad indent ++ "cases " ++ compText naming names subject ++ " with\n" ++
        pad indent ++ "| none => kernel_rfl\n" ++
        pad indent ++ "| some " ++ name ++ " =>\n" ++ tail)
  | _, names, .guard _ left right next, indent => do
      let condition := paren (termText naming names left) ++ " = " ++ paren (termText naming names right)
      let tail ← repeatPrefixProof naming site names next (indent + 2)
      pure (pad indent ++ "by_cases guard : " ++ condition ++ "\n" ++
        pad indent ++ "· simp only [ite_eq_left guard]\n" ++ tail ++
        pad indent ++ "· simp only [ite_eq_right guard]\n" ++ pad (indent + 2) ++ "kernel_rfl\n")
  | _, _, _, _ => throw "bindings-repeat-proof-prefix"
where
  bindPrefix {slot : Slot} (scope : Scope) (names : List String)
      (next : Form laws callees (slot :: scope) outputs) (indent : Nat) : Except String String := do
    let name := binderName scope.length none
    let tail ← repeatPrefixProof naming site (name :: names) next indent
    pure (pad indent ++ "rw [PIR.Process.bind_assoc]\n" ++
      pad indent ++ "apply congrArg (PIR.Process.bind _)\n" ++
      pad indent ++ "funext " ++ name ++ "\n" ++ tail)

/-- Generate a full prefix/frame/loop/continuation equation. Guards and
absent-component stops remain in the prefix. Other branches are refused.
This is syntax printing followed by kernel checking of the existing denotation. -/
def repeatSplitSource {laws : List LawKey} {callees : List CalleeKey} {scope : Scope}
    {outputs : List Ty} (naming : Naming laws callees scope)
    (form : Form laws callees scope outputs) (role : Nat) (name site : String) : Except String String := do
  let initialNames := inputNames naming.inputs 0
  let some cursor := repeatCursor site 2 initialNames form | throw "bindings-repeat-prefix-required"
  let .repeat spec _ body count state captures next := cursor.form | throw "bindings-repeat-required"
  let params := " ".intercalate ((scope.zip initialNames).map fun (slot, name) =>
    "(" ++ name ++ " : " ++ slotType naming slot ++ ")")
  let frameType := "Binders (ringModel F G) " ++ listText (cursor.scope.map slotText)
  let frameNames := cursor.scope.zipIdx.map fun (_, i) => app "frame.get" [positionText i]
  let full : String := (processText naming .outputs initialNames form 2).run' scope.length
  let suffix : String := (processText naming .outputs cursor.names cursor.form cursor.indent).run' cursor.scope.length
  let [before, after] := full.splitOn suffix | throw "bindings-repeat-prefix-print"
  let prefixText := before ++ pad cursor.indent ++ ".done " ++ valuesText cursor.names ++ after
  let callback := app (paren naming.runs ++ ".callback") [repeatText spec, regionText body]
  let loop := app (paren naming.runs ++ ".run") [repeatText spec,
    paren (compText naming frameNames count), valuesText (compsText naming frameNames state),
    valuesText (compsText naming frameNames captures), callback]
  let continuation : String := (processText naming .outputs ("result" :: frameNames) next 2).run' (cursor.scope.length + 1)
  let applied := " ".intercalate ("ctx" :: initialNames)
  let frameParams := " ".intercalate ((cursor.scope.zip cursor.names).map fun (slot, n) =>
    "(" ++ n ++ " : " ++ slotType naming slot ++ ")")
  let stateText := valuesText (compsText naming frameNames state)
  let capturesText := valuesText (compsText naming frameNames captures)
  let inputType := valuesType naming (.index :: (spec.state ++ spec.captures)) true
  let stateType := valuesType naming spec.state true
  let prefixParameters := explicitParameters ("(ctx : ProtocolContext) " ++ params)
    ("ctx" :: initialNames) prefixText
  let afterParameters := explicitParameters
    ("(ctx : ProtocolContext) (frame : " ++ name ++ "Frame (F := F) (G := G)) (result : " ++ stateType ++ ")")
    ["ctx", "frame", "result"] continuation
  let resumeBody := "Repeat.loop " ++ repeatText spec ++ " ctx (ctx.roles " ++ toString role ++ ") " ++
    paren capturesText ++ " (" ++ name ++ "Callback ctx) 1 count (maskValues (ctx.roles " ++
    toString role ++ ") (ctx.mapScopes (" ++ repeatText spec ++ ").stateScopes) result)"
  let resumeParameters := explicitParameters
    ("(ctx : ProtocolContext) (frame : " ++ name ++ "Frame (F := F) (G := G)) (count : Nat) (result : " ++ stateType ++ ")")
    ["ctx", "frame", "count", "result"] resumeBody
  return "abbrev " ++ name ++ "Frame := " ++ frameType ++ "\n\n" ++
    "def " ++ name ++ "MakeFrame " ++ frameParams ++ " : " ++ name ++ "Frame (F := F) (G := G) :=\n  " ++ valuesText cursor.names ++ "\n\n" ++
    "def " ++ name ++ "Count (frame : " ++ name ++ "Frame (F := F) (G := G)) : Option Nat :=\n  " ++ compText naming frameNames count ++ "\n\n" ++
    "noncomputable def " ++ name ++ "Callback (ctx : ProtocolContext) : " ++ inputType ++ " → PIR.Process (participantInterface F G) " ++ stateType ++ " :=\n  " ++ callback ++ "\n\n" ++
    "def " ++ name ++ "FirstInput (ctx : ProtocolContext) (frame : " ++ name ++ "Frame (F := F) (G := G)) : " ++ inputType ++ " :=\n  .cons (some 0) ((maskValues (ctx.roles " ++ toString role ++ ") (ctx.mapScopes (" ++ repeatText spec ++ ").stateScopes) " ++ paren stateText ++ ").append " ++ paren capturesText ++ ")\n\n" ++
    "noncomputable def " ++ name ++ "First (ctx : ProtocolContext) (frame : " ++ name ++ "Frame (F := F) (G := G)) : PIR.Process (participantInterface F G) " ++ stateType ++ " :=\n  " ++ name ++ "Callback ctx (" ++ name ++ "FirstInput ctx frame)\n\n" ++
    "noncomputable def " ++ name ++ "Resume " ++ resumeParameters ++ " : PIR.Process (participantInterface F G) " ++ stateType ++ " :=\n  " ++ resumeBody ++ "\n\n" ++
    "noncomputable def " ++ name ++ "Prefix " ++ prefixParameters ++ " :\n  PIR.Process (participantInterface F G) (" ++ name ++ "Frame (F := F) (G := G)) :=\n" ++ prefixText ++ "\n\n" ++
    "noncomputable def " ++ name ++ "Loop (ctx : ProtocolContext) (frame : " ++ name ++ "Frame (F := F) (G := G)) :\n  PIR.Process (participantInterface F G) (" ++ valuesType naming spec.state true ++ ") :=\n  " ++ loop ++ "\n\n" ++
    "noncomputable def " ++ name ++ "After " ++ afterParameters ++ " :\n  " ++ processType naming (.outputs (out := outputs)) ++ " :=\n" ++ continuation ++ "\n\n" ++
    "theorem " ++ name ++ "_first (ctx : ProtocolContext) (frame : " ++ name ++ "Frame (F := F) (G := G)) (count : Nat)\n" ++
    "    (countEq : " ++ name ++ "Count (F := F) (G := G) frame = some (count + 1))\n" ++
    "    (inside : ((" ++ repeatText spec ++ ").roles.map ctx.roles).contains (ctx.roles " ++ toString role ++ ") = true)\n" ++
    "    (bounded : count + 1 ≤ (" ++ repeatText spec ++ ").maximum) :\n" ++
    "    " ++ name ++ "Loop (F := F) (G := G) ctx frame = (" ++ name ++ "First (F := F) (G := G) ctx frame).bind (" ++ name ++ "Resume ctx frame count) := by\n" ++
    "  unfold " ++ name ++ "Loop " ++ name ++ "First " ++ name ++ "FirstInput " ++ name ++ "Resume\n" ++
    "  change denoteRepeat _ _ _ _ _ _ _ = _\n" ++
    "  unfold " ++ name ++ "Count at countEq\n" ++
    "  rw [countEq, repeat_admitted _ _ _ _ _ _ _ inside bounded, Repeat.loop_succ, Repeat.step_equation]\n" ++
    "  simp only [PIR.Process.bind_assoc, maskValues_idempotent]\n  all_goals kernel_rfl\n\n" ++
    "theorem " ++ name ++ "_split (ctx : ProtocolContext) " ++ params ++ " :\n  " ++ name ++ "Process (F := F) (G := G) " ++ applied ++ " =\n    (" ++ name ++ "Prefix (F := F) (G := G) " ++ applied ++ ").bind (fun frame =>\n      (" ++ name ++ "Loop (F := F) (G := G) ctx frame).bind (" ++ name ++ "After (F := F) (G := G) ctx frame)) := by\n  unfold " ++ name ++ "Process " ++ name ++ "Prefix " ++ name ++ "Loop " ++ name ++ "After\n" ++ (← repeatPrefixProof naming site initialNames form 2) ++ "\n"

end ZkcTools.StructuredSource.Bindings
