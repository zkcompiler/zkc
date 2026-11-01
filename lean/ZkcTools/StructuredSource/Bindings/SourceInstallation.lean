module

public import ZkcTools.StructuredSource.Bindings.SourceSelection

@[expose] public section

/-! Printers for checked helper associations and exact callback/call seams.
Client modules choose names and query candidates using ordinary Lean functions.
Every printed equation uses the existing Helpers/Calls machinery. -/
namespace ZkcTools.StructuredSource.Bindings
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open Zkc.Source.Structured.Bindings
open ZkcTools.StructuredSource.Presentation

def helperTemplatesSource (program : Program) (templates : HelperTemplateOutput)
    (associations : List (String × Nat)) : Except String String := do
  let mut text := "module\n\npublic import Zkc.Source.Structured.ProtocolOperations\n\n" ++
    "@[expose] public section\n\n/-! Literal helper templates and collection layouts. -/\n" ++
    "namespace " ++ templates.namespaceName ++ "\nopen Zkc.Source Zkc.Source.Structured\n" ++
    "set_option smartUnfolding false\nnoncomputable section\n\n"
  for (name, index) in associations do
    text := text ++ (← helperTemplateSource program name index)
  return text ++ "end\nend " ++ templates.namespaceName ++ "\n"

def helperAssociationsSource (program : Program) (output : Output) (templates : HelperTemplateOutput)
    (namespaceSuffix : String) (associations : List (String × Nat)) : Except String String := do
  let namespaceName := output.moduleName ++ namespaceSuffix
  let mut text := "module\n\npublic import " ++ templates.moduleName ++ "\n" ++
    "public import " ++ output.moduleName ++ "Callbacks\n\n@[expose] public section\n\n" ++
    "/-! Generated full-body helper associations. -/\nnamespace " ++ namespaceName ++ "\n" ++
    "open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings\n" ++
    "open " ++ output.moduleName ++ "\n" ++
    (if templates.namespaceName == namespaceName then "" else "open " ++ templates.namespaceName ++ "\n") ++
    "set_option maxRecDepth 50000\nset_option maxHeartbeats 8000000\n" ++
    "set_option smartUnfolding false\nnoncomputable section\n" ++
    "variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]\n\n"
  for (name, index) in associations do
    text := text ++ (← helperAssociationSource program name index
      "(helpers payload).closed" ".silent (participantInterface F G)")
  return text ++ "end\nend " ++ namespaceName ++ "\n"

/-- Small output description, not a registry or a semantic installation record.
The client supplies selections and composes ordinary seam printers. -/
structure SourceInstallation where
  protocols : List Nat
  templates : HelperTemplateOutput
  namespaceSuffix : String
  associations : List (String × Nat)
  callerSource : Output → Except String String

def callerSourceHeader (output : Output) : String :=
  "module\n\npublic import " ++ output.moduleName ++ "Callbacks\npublic import Zkc.Source.Structured.RepeatLaws\n\n@[expose] public section\n\n" ++
  "/-! Generated actual call seams and retained continuations. -/\nnamespace " ++ output.moduleName ++ "Caller\n" ++
  "open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings\n" ++
  "open " ++ output.moduleName ++ " " ++ output.moduleName ++ "Callbacks\n" ++
  "set_option maxRecDepth 50000\nset_option maxHeartbeats 8000000\nnoncomputable section\n" ++
  "variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]\n\n"

def callbackAliasSource (selected : SelectedCallback) (role : Nat) (name : String) : String :=
  "abbrev " ++ name ++ "Spec : RepeatSpec := " ++ repeatText selected.callback.spec ++ "\n" ++
  "abbrev " ++ name ++ "Body := " ++ roleName selected.protocolIndex role ++ "Callback" ++
  toString selected.callbackIndex ++ "Body\n\n"

/-- Split a selected callback's actual call at every requested role, retaining
the complete setup, callee ABI, returned values and continuation. Optionally
expose the enclosing repeat split at the selected role. -/
def callbackCallSource (program : Program) (selected : SelectedCallback) (site : String)
    (roles : List Nat) (aliasRole : Nat) (callAlias repeatAlias : String)
    (splitRepeat : Bool := true) : Except String String := do
  let some definition := program.payload.protocols[selected.protocolIndex]?
    | throw "source-protocol-index"
  unless roles.contains aliasRole do throw "source-call-alias-role"
  let callback := selected.callback
  let inputs := .index :: (callback.spec.state ++ callback.spec.captures)
  let pattern := optionalPattern inputs
  let signature := sourceSignature program
  let mut text := ""
  for role in roles do
    unless role < definition.roles.length do throw "source-role-index"
    let naming : Naming signature.laws signature.callees pattern.scope := {
      carriers := .uniform "F" "G", tables := "(helpers (F := F) (G := G) payload).toOn"
      results := "callbackResults (F := F) (G := G)", context := "ctx"
      runs := "Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles " ++ toString role ++ ")"
      processes := "actualCallees payload calleeKeys" }
    let form ← normalize signature callback.body role definition.roles.length pattern
    text := text ++ (← callSplitSource naming form
      (roleName selected.protocolIndex role ++ "Callback" ++ toString selected.callbackIndex) site)
  let name := roleName selected.protocolIndex aliasRole ++ "Callback" ++ toString selected.callbackIndex
  text := text ++ "abbrev " ++ callAlias ++ " := @" ++ name ++ "Process\n" ++
    "abbrev " ++ callAlias ++ "Context := " ++ name ++ "SetupContext\n" ++
    "abbrev " ++ callAlias ++ "Input := @" ++ name ++ "SetupInput\n" ++
    "abbrev " ++ callAlias ++ "Continuation := @" ++ name ++ "SetupContinuation\n" ++
    callbackAliasSource selected aliasRole repeatAlias
  if splitRepeat then
    let wholePattern := optionalPattern definition.inputs
    let wholeSignature : Signature := ⟨projectionLaws program, false, false,
      program.payload.definitions.map (·.helper), keys program⟩
    let wholeNaming : Naming wholeSignature.laws wholeSignature.callees wholePattern.scope := {
      carriers := .uniform "F" "G", tables := "(helpers (F := F) (G := G) payload).toOn"
      results := "projectionResults (F := F) (G := G)", context := "ctx"
      runs := "Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles " ++ toString aliasRole ++ ")"
      processes := roleName selected.protocolIndex aliasRole ++ "Callees" }
    let (_, named, _) ← request wholeSignature definition.body aliasRole definition.roles.length wholePattern wholeNaming
    let whole ← normalize {wholeSignature with names := named} definition.body aliasRole definition.roles.length wholePattern
    text := text ++ (← repeatSplitSource wholeNaming whole aliasRole (roleName selected.protocolIndex aliasRole) callback.site)
  return text

end ZkcTools.StructuredSource.Bindings
