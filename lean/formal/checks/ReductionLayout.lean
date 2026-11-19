import Zkc.Tools.Formal.DrawCharge
import Zkc.Tests.Formal.SourceProtocolRoots

open Zkc.Core Zkc.Frontend Zkc.Tools.Formal Zkc.Tests.Formal
open Zkc.Formal.Interactive.Sumcheck.ReductionRound

private def edited (root : System.FilePath) (edit : String → String) : IO Written.AdmittedRoot := do
  let entry ← SourceProtocolRoots.replaceOnce (root / "examples/sumcheck_example.zkc")
    "Proof = Sumcheck<10>" "Proof = Sumcheck<2>"
  SourceProtocolRoots.admitRoot entry fun parts => do
    if parts.back? != some "sumcheck" then return ← SourcePairReadback.loadModule root .original parts
    let path := root / "examples/sumcheck.zkc"
    let source := edit (← IO.FS.readFile path)
    return some ⟨path.toString,Syntax.parseString path.toString source⟩

private def withPrivate (src : String) : String :=
  src.replace "round <- send R::message(s)" (String.intercalate "\n        "
    ["spare = R::bind(s, running)", "payload = R::message(s)", "unused_end = R::boundary(payload)",
     "round <- send payload"])

/-- Check the extra call in the admitted body and the binding that survives projection. -/
private def retained {V : Zkc.Core.Vocabulary} {hs : Headers V} {t : V.Ty} {events : Events t}
    (round : IndexedRound hs events) : Bool := Id.run do
  let (steps,exit) := eraseBody (protocolRules hs).printOp id round.actual
  let before := steps.takeWhile fun step => !(step matches .op _ _ (.event (.flow ..) _) _)
  let some (.op key [spare] (.compute [0] op) [_,claim]) := before.find? (fun step =>
    step matches .op _ [_] (.compute [0] _) [_,_]) | return false
  unless op == round.checked.members.bindState.print && claim == round.running.name do return false
  let some (.op _ [payload] _ _) := before.find? (fun step => match step with
    | .op _ _ (.compute [0] raw) _ => raw == round.checked.members.sendValue.print
    | _ => false) | return false
  unless before.any (fun step => match step with
    | .op _ [_] (.compute [0] raw) [arg] => raw == round.checked.members.boundary.print && arg == payload
    | _ => false) do return false
  if exit.contains spare || steps.any (fun step => match step with
      | .op _ _ _ args => args.contains spare
      | .guard _ _ name _ => name == spare
      | _ => true) then return false
  let projected : List (Instruction (RoleRaw V) Holders) :=
    (eraseBody BodyAnalysis.roleWritten id (project 1 round.actual)).1
  return projected.any fun step => match step with
    | .op site [name] (RoleRaw.absent [_]) [] => site == key && name == spare
    | _ => false

-- Only correspondences to names rebound on the actual side leave scope.
example : StraightLine.forgetRight [(2,8),(3,9),(4,10)]
    (.cons 8 (.cons 10 .nil) : Names [Unit.unit, ()]) = [(3,9)] := rfl

-- A later binding of the same name cannot change the producer used by an earlier send.
example {V : Zkc.Core.Vocabulary} (code : LocalRaw V) (t : V.Ty) :
    ((RoundUses.read [.op ⟨7⟩ [3] (.compute [0] code) [0],
      .op ⟨9⟩ [4] (.event (.flow .message 0 [1]) t) [3], .op ⟨20⟩ [3] (.compute [0] code) [0]]).map
      fun uses => (uses.resolve 3, (uses.producer (.result ⟨9⟩)).map (·.args))) =
      some (.result ⟨20⟩,some [.result ⟨7⟩]) := rfl

#eval show IO Unit from do
  let root := (← IO.currentDir) / "../.."
  let plain ← edited root id
  let original ← IO.ofExcept (chargeSumcheck plain 2 "challenge")
  let c ← edited root withPrivate
  let approved ← IO.ofExcept (chargeSumcheck c 2 "challenge")
  let rounds := approved.verifier.linked.rounds.instances
  unless rounds.length == 2 && rounds.all retained do throw (IO.userError "missing retained private SSA call")
  let draws := approved.issued.charge.draws
  unless draws.length == 2 && draws != original.issued.charge.draws do
    throw (IO.userError "expected two relocated source draw addresses")
  let events := SourceProtocolRoots.sourceEvents c.emission.bindings
  let some first := locate c.evidence.admitted.program approved.keys.reduction events
    | throw (IO.userError "first-block recognition lost the private-step variant")
  unless draws.head? == some ([(first.first.block.key,first.first.block.index)],challengeSite first.first.sites) do
    throw (IO.userError "first block and written charge disagree on the draw")
  if standard : c.emission.bindings.rows = [] then
    let _ := approved.primeBound standard (σ := Unit)
  else throw (IO.userError "standard field model unavailable")
  for (label,edit) in [
      ("additional guard",fun (s : String) => s.replace "guard @V running ==" "guard @V running != 0\n        guard @V running =="),
      ("unused partial verifier call",fun s =>
        (s.replace "pub interface Round:" "pub def checked_value(x: F) -> F:\n    guard x != 0\n    return x\n\npub interface Round:").replace
          "guard @V running ==" "unused = checked_value(running)\n        guard @V running =="),
      ("previous claim as evaluation point",fun s => s.replace "R::evaluate(round, challenge)" "R::evaluate(round, running)"),
      ("previous claim as private bind point",fun s => s.replace "s := R::bind(s, challenge)" "s := R::bind(s, running)"),
      ("initial claim in second guard",fun s => s.replace "guard @V running ==" "guard @V claim ==")] do
    let variant ← edited root (edit ∘ withPrivate)
    let .error "uncertified Sumcheck verifier" := chargeSumcheck variant 2 "challenge"
      | throw (IO.userError s!"expected verifier refusal for {label}")
  IO.println "Retained private calls in both admitted rounds, issued the relocated charge and refused all verifier controls."
