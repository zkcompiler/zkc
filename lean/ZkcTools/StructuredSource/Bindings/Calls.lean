module

public import ZkcTools.StructuredSource.Bindings.Callbacks

@[expose] public section

/-! Untrusted printing of a call's exact captured continuation. The equations
are checked against the existing normal form; no execution evaluator is added.
Only a call at the head of a normalized callback is selected here. -/
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
  return "set_option linter.unusedVariables false in\n" ++
    "noncomputable def " ++ name ++ "CallContext (ctx : ProtocolContext) : ProtocolContext :=\n  ctx.enter " ++ quoted site ++ " " ++ natsText roles ++ "\n\n" ++
    "set_option linter.unusedVariables false in\nnoncomputable def " ++ name ++ "CallInput (ctx : ProtocolContext) " ++ params ++ " : " ++ inputType ++ " :=\n  " ++ arguments ++ "\n\n" ++
    "set_option linter.unusedVariables false in\nnoncomputable def " ++ name ++ "Continuation (ctx : ProtocolContext) " ++ params ++ " (result : " ++ outputType ++ ") :\n  " ++ processType naming (.outputs (out := outputs)) ++ " :=\n" ++ continuation ++ "\n\n" ++
    "theorem " ++ name ++ "_call (ctx : ProtocolContext) " ++ params ++ " :\n  " ++ name ++ "Process (F := F) (G := G) " ++ applied ++ " =\n    (invokeProtocol (payload.plainProtocolTable F G) " ++ signatureText key.signature ++ "\n      (" ++ name ++ "CallContext ctx) ((" ++ name ++ "CallContext ctx).roles " ++ toString key.role ++ ")\n      (" ++ name ++ "CallInput " ++ applied ++ ")).bind (" ++ name ++ "Continuation " ++ applied ++ ") := by\n  kernel_rfl\n\n"

/-- A printer-side cursor through a linear prefix. Branches are deliberately
refused. The returned scope and residual are the existing indexed Form. -/
structure RepeatCursor (laws : List LawKey) (callees : List CalleeKey) (outputs : List Ty) where
  scope : Scope
  names : List String
  form : Form laws callees scope outputs

def repeatCursor {laws : List LawKey} {callees : List CalleeKey} {outputs : List Ty}
    (site : String) : {scope : Scope} → List String → Form laws callees scope outputs →
      Option (RepeatCursor laws callees outputs)
  | scope, names, form@(.repeat _ found _ _ _ _ next) =>
      if found == site then some ⟨scope, names, form⟩
      else repeatCursor site (binderName scope.length none :: names) next
  | scope, names, .owned _ _ _ next | scope, names, .math _ _ next |
      scope, names, .strict _ _ next | scope, names, .compute _ _ _ next =>
      repeatCursor site (binderName scope.length none :: names) next
  | _, names, .byLaw _ _ next => repeatCursor site names next
  | _, _, _ => none

/-- Select an application after a pure linear prefix, refusing branches,
receives, repeats and earlier calls. Selection does not assert a helper law. -/
def applicationCursor {laws : List LawKey} {callees : List CalleeKey} {outputs : List Ty}
    (site : String) : {scope : Scope} → List String → Form laws callees scope outputs →
      Option (RepeatCursor laws callees outputs)
  | scope, names, form@(.apply _ _ _ found _ _) =>
      if found == site then some ⟨scope, names, form⟩ else none
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
  let frameNames := cursor.scope.zipIdx.map fun (_, i) => app "frame.get" [positionText i]
  let full : String := (processText naming .outputs initialNames form 2).run' scope.length
  let suffix : String := (processText naming .outputs cursor.names cursor.form 2).run' cursor.scope.length
  unless full.endsWith suffix do throw "bindings-call-prefix-print"
  let prefixText := (full.dropEnd suffix.length).toString ++ "  .done " ++ valuesText cursor.names
  let continuation : String := (processText naming .outputs ("result" :: frameNames) next 2).run' (cursor.scope.length + 1)
  let callInput := valuesText (argumentsText naming frameNames args)
  let applied := " ".intercalate ("ctx" :: initialNames)
  return "abbrev " ++ name ++ "SetupFrame := " ++ frameType ++ "\n\n" ++
    "set_option linter.unusedVariables false in\nnoncomputable def " ++ name ++ "Setup (ctx : ProtocolContext) " ++ params ++ " : PIR.Process (participantInterface F G) (" ++ name ++ "SetupFrame (F := F) (G := G)) :=\n" ++ prefixText ++ "\n\n" ++
    "def " ++ name ++ "SetupInput (frame : " ++ name ++ "SetupFrame (F := F) (G := G)) : " ++ valuesType naming key.signature.inputs true ++ " :=\n  " ++ callInput ++ "\n\n" ++
    "def " ++ name ++ "SetupContext (ctx : ProtocolContext) : ProtocolContext := ctx.enter " ++ quoted found ++ " " ++ natsText roles ++ "\n\n" ++
    "set_option linter.unusedVariables false in\nnoncomputable def " ++ name ++ "SetupContinuation (ctx : ProtocolContext) (frame : " ++ name ++ "SetupFrame (F := F) (G := G)) (result : " ++ valuesType naming key.signature.outputs true ++ ") : " ++ processType naming (.outputs (out := outputs)) ++ " :=\n" ++ continuation ++ "\n\n" ++
    "theorem " ++ name ++ "_setup_split (ctx : ProtocolContext) " ++ params ++ " :\n  " ++ name ++ "Process (F := F) (G := G) " ++ applied ++ " =\n    (" ++ name ++ "Setup " ++ applied ++ ").bind (fun frame =>\n      (invokeProtocol (payload.plainProtocolTable F G) " ++ signatureText key.signature ++ " (" ++ name ++ "SetupContext ctx) ((" ++ name ++ "SetupContext ctx).roles " ++ toString key.role ++ ") (" ++ name ++ "SetupInput frame)).bind (" ++ name ++ "SetupContinuation ctx frame)) := by\n  unfold " ++ name ++ "Process " ++ name ++ "Setup " ++ name ++ "SetupInput " ++ name ++ "SetupContinuation " ++ name ++ "SetupContext\n  simp only [PIR.Process.bind_assoc, PIR.Process.bind]\n  all_goals rfl\n\n"

/-- Generate a full prefix/frame/loop/continuation equation. This is syntax
printing followed by ordinary kernel checking, using the existing denotation. -/
def repeatSplitSource {laws : List LawKey} {callees : List CalleeKey} {scope : Scope}
    {outputs : List Ty} (naming : Naming laws callees scope)
    (form : Form laws callees scope outputs) (role : Nat) (name site : String) : Except String String := do
  let initialNames := inputNames naming.inputs 0
  let some cursor := repeatCursor site initialNames form | throw "bindings-linear-repeat-required"
  let .repeat spec _ body count state captures next := cursor.form | throw "bindings-repeat-required"
  let params := " ".intercalate ((scope.zip initialNames).map fun (slot, name) =>
    "(" ++ name ++ " : " ++ slotType naming slot ++ ")")
  let frameType := "Binders (ringModel F G) " ++ listText (cursor.scope.map slotText)
  let frameNames := cursor.scope.zipIdx.map fun (_, i) => app "frame.get" [positionText i]
  let full : String := (processText naming .outputs initialNames form 2).run' scope.length
  let suffix : String := (processText naming .outputs cursor.names cursor.form 2).run' cursor.scope.length
  unless full.endsWith suffix do throw "bindings-repeat-prefix-print"
  let prefixText :=  (full.dropEnd suffix.length).toString ++ "  .done " ++ valuesText cursor.names
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
  return "abbrev " ++ name ++ "Frame := " ++ frameType ++ "\n\n" ++
    "def " ++ name ++ "MakeFrame " ++ frameParams ++ " : " ++ name ++ "Frame (F := F) (G := G) :=\n  " ++ valuesText cursor.names ++ "\n\n" ++
    "def " ++ name ++ "Count (frame : " ++ name ++ "Frame (F := F) (G := G)) : Option Nat :=\n  " ++ compText naming frameNames count ++ "\n\n" ++
    "noncomputable def " ++ name ++ "Callback (ctx : ProtocolContext) : " ++ inputType ++ " → PIR.Process (participantInterface F G) " ++ stateType ++ " :=\n  " ++ callback ++ "\n\n" ++
    "def " ++ name ++ "FirstInput (ctx : ProtocolContext) (frame : " ++ name ++ "Frame (F := F) (G := G)) : " ++ inputType ++ " :=\n  .cons (some 0) ((maskValues (ctx.roles " ++ toString role ++ ") (ctx.mapScopes (" ++ repeatText spec ++ ").stateScopes) " ++ paren stateText ++ ").append " ++ paren capturesText ++ ")\n\n" ++
    "noncomputable def " ++ name ++ "First (ctx : ProtocolContext) (frame : " ++ name ++ "Frame (F := F) (G := G)) : PIR.Process (participantInterface F G) " ++ stateType ++ " :=\n  " ++ name ++ "Callback ctx (" ++ name ++ "FirstInput ctx frame)\n\n" ++
    "noncomputable def " ++ name ++ "Resume (ctx : ProtocolContext) (frame : " ++ name ++ "Frame (F := F) (G := G)) (count : Nat) (result : " ++ stateType ++ ") : PIR.Process (participantInterface F G) " ++ stateType ++ " :=\n  Repeat.loop " ++ repeatText spec ++ " ctx (ctx.roles " ++ toString role ++ ") " ++ paren capturesText ++ " (" ++ name ++ "Callback ctx) 1 count (maskValues (ctx.roles " ++ toString role ++ ") (ctx.mapScopes (" ++ repeatText spec ++ ").stateScopes) result)\n\n" ++
    "set_option linter.unusedVariables false in\nnoncomputable def " ++ name ++ "Prefix (ctx : ProtocolContext) " ++ params ++ " :\n  PIR.Process (participantInterface F G) (" ++ name ++ "Frame (F := F) (G := G)) :=\n" ++ prefixText ++ "\n\n" ++
    "noncomputable def " ++ name ++ "Loop (ctx : ProtocolContext) (frame : " ++ name ++ "Frame (F := F) (G := G)) :\n  PIR.Process (participantInterface F G) (" ++ valuesType naming spec.state true ++ ") :=\n  " ++ loop ++ "\n\n" ++
    "set_option linter.unusedVariables false in\nnoncomputable def " ++ name ++ "After (ctx : ProtocolContext) (frame : " ++ name ++ "Frame (F := F) (G := G)) (result : " ++ valuesType naming spec.state true ++ ") :\n  " ++ processType naming (.outputs (out := outputs)) ++ " :=\n" ++ continuation ++ "\n\n" ++
    "theorem " ++ name ++ "_first (ctx : ProtocolContext) (frame : " ++ name ++ "Frame (F := F) (G := G)) (count : Nat)\n" ++
    "    (countEq : " ++ name ++ "Count (F := F) (G := G) frame = some (count + 1))\n" ++
    "    (inside : ((" ++ repeatText spec ++ ").roles.map ctx.roles).contains (ctx.roles " ++ toString role ++ ") = true)\n" ++
    "    (bounded : count + 1 ≤ (" ++ repeatText spec ++ ").maximum) :\n" ++
    "    " ++ name ++ "Loop (F := F) (G := G) ctx frame = (" ++ name ++ "First (F := F) (G := G) ctx frame).bind (" ++ name ++ "Resume ctx frame count) := by\n" ++
    "  unfold " ++ name ++ "Loop " ++ name ++ "First " ++ name ++ "FirstInput " ++ name ++ "Resume\n" ++
    "  change denoteRepeat _ _ _ _ _ _ _ = _\n" ++
    "  unfold " ++ name ++ "Count at countEq\n" ++
    "  rw [countEq, repeat_admitted _ _ _ _ _ _ _ inside bounded, Repeat.loop_succ, Repeat.step_equation]\n" ++
    "  simp only [PIR.Process.bind_assoc, PIR.Process.bind, maskValues_idempotent]\n  all_goals rfl\n\n" ++
    "theorem " ++ name ++ "_split (ctx : ProtocolContext) " ++ params ++ " :\n  " ++ name ++ "Process (F := F) (G := G) " ++ applied ++ " =\n    (" ++ name ++ "Prefix (F := F) (G := G) " ++ applied ++ ").bind (fun frame =>\n      (" ++ name ++ "Loop (F := F) (G := G) ctx frame).bind (" ++ name ++ "After (F := F) (G := G) ctx frame)) := by\n  unfold " ++ name ++ "Process " ++ name ++ "Prefix " ++ name ++ "Loop " ++ name ++ "After\n  simp only [PIR.Process.bind_assoc, PIR.Process.bind]\n  all_goals rfl\n\n"

end ZkcTools.StructuredSource.Bindings
