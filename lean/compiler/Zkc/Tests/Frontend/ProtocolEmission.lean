import Zkc.Frontend.Driver.SourcePhases
import Zkc.Frontend.Semantics.VocabularyTable
import Zkc.Frontend.Syntax.Parser
import Zkc.Frontend.Elab.Protocol
import Zkc.Frontend.Passes.Placement
import Zkc.Frontend.Typed.Number
import Zkc.Frontend.Emit.NamedProtocol
namespace Zkc.Tests.Frontend.ProtocolEmission
open Zkc.Frontend Static

private abbrev bindings : Zkc.Vocabulary.Project.Bindings := {}

private def input := "module delivery\ntype F = primitive(\"bls12-381.fr\")\nprotocol Share roles(P, V, W)(a: F @P, spec bound: nat) -> answer: F @(P, V, W):\n    m <- send a to V, W\n    c <- draw F from V to P, W\n    return m + c\nprotocol Caller roles(A, B, C)(a: F @C):\n    for i in 0..2:\n        answer <- Share(a, spec bound = i) @(P = C, V = A, W = B)\n        guard @A answer != 0\n"

private def emitAt (name : String) (earlier : Std.HashMap InstanceId Typed.ProtocolSignature) :
    CompileM (InstanceId × Typed.ProtocolSignature × Emit.Named.ProtocolEmission bindings × Typed.ProtocolBody) := do
  let s ← get
  let some (_, i) := s.program.declarations.zipIdx.find? (fun (d, _) => d.name.any (·.text == name))
    | throw (.defect "missing protocol")
  let inst ← instantiate i #[] ⟨name,default⟩
  let d := s.program.declarations[i]!
  let some lowered := s.env.modules.lowered? i | throw .abandoned
  let .protocol head stmts result := lowered.content | throw .abandoned
  let env := instanceEnv s.program d #[]
  let signature ← Elab.protocolSignatureIn head env
  let context : Elab.Context := {
    env, «instance» := inst, name, roster := some head.roster
    protocolBody := fun callee _ => unless earlier.contains callee do throw (.defect "unexpected protocol dependency")
  }
  let (tree, _) ← Elab.runElab context lowered.locals (Elab.elabProtocolBody name signature head stmts result[0]?)
  let .protocol body := (Typed.Body.protocol tree).numbered.1 | throw .abandoned
  let roles ← Passes.placeRoles {roster := body.roster, calleeStops := fun _ => false, signatureOf := (earlier[·]?)} body
  let b : Zkc.Vocabulary.Project.Bindings := {}
  let ctx : Emit.Named.Context b := {callees := default, apply := fun _ _ _ => Typing.defect "unexpected call"}
  match (Emit.Named.emitProtocol ctx ⟨roles,body.roster⟩ ⟨inst⟩ body).run (← get) with
  | .ok code => return (inst, signature, code, body)
  | .error e => throw (.defect s!"{repr e}")

/-- Recompile a three-role broadcast, uniform coin and a permuted call from a loop.
Check the exact instruction that owns the typed specification argument. -/
def check (root : System.FilePath) : IO Unit := do
  let assembly ← assemble #[⟨"delivery.zkc",Syntax.parseString "delivery.zkc" input⟩] fun segments => do
    let path := root / "libraries" / ((String.intercalate "/" segments.toList) ++ ".zkc")
    if ← path.pathExists then return some ⟨path.toString,Syntax.parse path.toString (← IO.FS.readBinFile path)⟩
    return none
  let mut s : Compile.State := {}
  for phase in Driver.sourcePhases assembly do
    let (report, next) := phase.runIn {vocabulary} s
    if let some why := report.interrupted then throw (IO.userError s!"{phase.name}: {why}")
    s := next
  let compile := do
    let (callee, signature, share, _) ← emitAt "Share" {}
    let (_, _, caller, body) ← emitAt "Caller" (({} : Std.HashMap _ _).insert callee signature)
    return (share, caller, body)
  let (r, final) := compile.run {vocabulary} s
  for e in final.log.entries do IO.println s!"{e.rule}: {Message.render Renderer.plain e.message}"
  unless !final.log.hasIncomplete && !final.log.hasErrors do throw (IO.userError "frontend diagnostics")
  let .ok (share, caller, body) := r | throw (IO.userError s!"protocol emission failed")
  let .protocol _ 3 _ _ (.mk _ steps _) := share.definition | throw (IO.userError "missing protocol")
  let messages := steps.filter fun step => match step with
    | .op _ _ (.event (.flow .message 0 [1,2]) _) [_] => true
    | _ => false
  let coins := steps.filter fun step => match step with
    | .op _ _ (.event (.given (.coin (.uniform _)) 1 [0,2]) _) [] => true
    | _ => false
  unless messages.length == 1 && coins.length == 1 do throw (IO.userError "message or coin shape changed")
  let .protocol _ _ _ _ (.mk _ callerSteps _) := caller.definition | throw (IO.userError "expected caller")
  let [(.loop _ _ (.fixed 2) _ _ (.mk _ inner _))] := callerSteps | throw (IO.userError "expected fixed loop")
  let [site] := inner.filterMap (fun step => match step with
    | .op k [_] (.apply ref [2,0,1]) [_] => if ref == share.definition.key then some k else none
    | _ => none) | throw (IO.userError "expected one call with the actual role map and one runtime operand")
  let #[attached] := caller.specification | throw (IO.userError "expected one specification attachment")
  unless attached.instruction == site do throw (IO.userError "wrong attachment instruction")
  let #[("bound", ghost)] := attached.arguments | throw (IO.userError "expected bound")
  let #[.for _ (.loop binder _ _ _) _] := body.statements | throw (IO.userError "missing source loop binder")
  let .local _ id := ghost | throw (IO.userError "expected a reference to the source loop")
  unless id == binder.id do throw (IO.userError "wrong loop binder")
  let package : SourcePackage := ⟨{},⟨[share.definition, caller.definition]⟩,⟨[],[],[],[],[]⟩⟩
  unless package.checkEvidence.isOk do throw (IO.userError s!"role admission refused the {steps.length} instructions")
  IO.println "Admitted the broadcast, uniform coin and role-mapped loop call with its source binder."

end Zkc.Tests.Frontend.ProtocolEmission
