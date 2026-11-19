import Zkc.Tests.Formal.SourcePairReadback
import Zkc.Tools.Formal.SumcheckCaller
import Zkc.Frontend.Written.Root
import Zkc.Frontend.Emit.Application
import Zkc.Formal.Interactive.EmptySumcheck
import Zkc.Formal.Interactive.PairSequence
import Zkc.Formal.Interactive.GateSequence
import Zkc.Formal.Interactive.SourceSumcheck

namespace Zkc.Tests.Formal.SourceProtocolRoots
open Zkc.Frontend
open Zkc.Core
open SourcePairReadback (Variant)
open SourcePairMembers (sourceRows)

private def load (root : System.FilePath) (variant : Variant) (fixedLayer : Bool)
    (segments : Array String) : IO (Option SourceInput) := do
  if fixedLayer && segments.back? == some "gkr" then
    let path := root / "examples/gkr.zkc"
    let src ← IO.FS.readFile path
    let needle := "spec p = summand(c, inputs, i, z)"
    unless (src.splitOn needle).length == 2 do throw (IO.userError "GKR layer control is ambiguous")
    return some ⟨path.toString, Syntax.parseString path.toString
      (src.replace needle "spec p = summand(c, inputs, 0, z)")⟩
  return ← SourcePairReadback.loadModule root variant segments

/-- Find the actual application instruction, even inside an enclosing block or loop. -/
private partial def applications {V : Zkc.Core.Vocabulary} (region : Region (ProtocolRaw V) (List Role)) :
    List (Key × Key × List Role × Nat) :=
  let .mk _ steps _ := region
  steps.flatMap fun step => match step with
    | .op key _ (.apply callee roles) args => [(key, callee, roles, args.length)]
    | .choose _ _ _ _ a b => applications a ++ applications b
    | .cases _ _ _ _ arms => arms.flatMap applications
    | .loop _ _ _ _ _ b | .block _ _ _ b | .attempt _ _ _ b => applications b
    | _ => []

private def instanceName (s : Compile.State) (id : InstanceId) : String :=
  (s.table.entries[id]?.map fun e => s.program.nameOf e.key.declaration).getD ""

abbrev CheckedRoot := Written.AdmittedRoot

/-- A Core readback control can intentionally change the emission being tested. Only
the normal compiler result carries source provenance and can enter a written issuer. -/
structure ReadbackFixture where
  id : InstanceId
  state : Compile.State
  emission : Emit.RootEmission
  evidence : (emission.package ⟨[],[],[],[],[]⟩).Admission

instance : Coe CheckedRoot ReadbackFixture where
  coe c := ⟨c.id,c.state,c.emission,c.evidence⟩

def admitRoot (entry : SourceInput) (loader : Array String → IO (Option SourceInput)) : IO CheckedRoot := do
  IO.ofExcept (Written.admitSource (← assemble #[entry] loader))

abbrev sourceEvents := Zkc.Formal.Written.SumcheckRows.sourceEvents

abbrev vectorRows := Zkc.Formal.Written.SumcheckRows.vectorRows

private def certifiedSumcheck (checked : CheckedRoot) (n : Nat := 10) : Option (Bool × Bool) := do
  let e := checked.emission
  let rows := sourceRows e.bindings
  let .protocol _ _ _ _ region ← e.named.definitions.find? (·.key.number == checked.id) | none
  let [(_,red,[0,1],3)] := applications region | none
  let checkedBody ← checked.state.results.checked? checked.id
  let .protocol caller := checkedBody.definition.body | none
  let [eval] := (Emit.protocolFunctions caller).toList.filter (fun k => instanceName checked.state k == "evaluate") | none
  let certify := Zkc.Formal.Interactive.Sumcheck.TableVerifier.certify rows (vectorRows e.bindings)
    checked.evidence.admitted.program ⟨checked.id⟩ red ⟨eval⟩ n (sourceEvents e.bindings)
  return ((certify rows.evaluationReadback).isSome,(certify rows.affineReadback).isSome)

private def checkedRounds (checked : ReadbackFixture) (callee : Key) (count : Nat) : Option (Bool × Bool × Bool) := do
  let rows := sourceRows checked.emission.bindings
  let events := sourceEvents checked.emission.bindings
  let cert ← Zkc.Formal.Interactive.Sumcheck.ReductionRound.locate checked.evidence.admitted.program callee events
  guard (cert.first.block.index == 0 && cert.first.block.key.number == 11)
  let sequence := Zkc.Formal.Interactive.Sumcheck.ReductionRound.readSequence
    (List.nodup_append.mp cert.first.entry.distinct).1 events (hs := cert.first.entry.earlier)
  let running : Var _ (Zkc.Formal.Interactive.Sumcheck.ReductionRound.shared rows.scalarTy) :=
    ⟨2, (rfl : (Ctx.empty.extend (Zkc.Formal.Interactive.Sumcheck.ReductionRound.names
      (state := cert.state) (point := cert.point) (t := rows.scalarTy))).find? 2 = _)⟩
  let some rounds := sequence count cert.state running cert.first.atNames.body | none
  let some (.protocol code) := checked.state.results.body? callee.number | none
  let addresses ← Emit.SiteAddresses.forProtocol checked.evidence.admitted.program callee
  let typedRounds := rounds.instances
  for (name, operation) in [("round", 1), ("challenge", 5)] do
    let source ← code.sites.find? (fun s => s.name == some name)
    let sites := Typing.SiteEntry.realizations code.sites source.event source.part
    let actual := (sites.extract 0 count).map addresses.resolve
    let expected := typedRounds.map fun r =>
      some ([(r.block, r.iteration)], r.checked.sites operation)
    guard (actual.toList == expected)
  guard (!(sequence (count+1) cert.state running cert.first.atNames.body).isSome)
  let test := Zkc.Formal.Interactive.Sumcheck.ReductionRound.checkPairSequence rows cert.first.entry.definitions
    (List.nodup_append.mp cert.first.entry.distinct).1
  let gate := Zkc.Formal.Written.SumcheckRows.checkGateMembers Zkc.Tools.Formal.gateRow cert.first.entry.definitions (List.nodup_append.mp cert.first.entry.distinct).1 rounds
  return ((test rows.evaluationReadback rounds).isSome,(test rows.affineReadback rounds).isSome,gate.isSome)

private def appliedGate (checked : CheckedRoot) (callee site : Key) (actualArgs : List Name) (loopKey : Key) : Bool := Id.run do
  let program := checked.evidence.admitted.program
  let [⟨_,root⟩] := Member.withKey ProtocolHeader.key ⟨checked.id⟩ program.headers.protocols | return false
  let [⟨hdr,_⟩] := Member.withKey ProtocolHeader.key callee program.headers.protocols | return false
  let [state,_,_] := hdr.ins | return false
  let [_,_,residual] := hdr.outs | return false
  let rows := sourceRows checked.emission.bindings
  let events := sourceEvents checked.emission.bindings
  let some located := Zkc.Formal.Interactive.Sumcheck.ReductionRound.atSite program root callee site state.ty rows.scalarTy residual.ty 0 4
    events actualArgs (Zkc.Formal.Interactive.Sumcheck.ReductionRound.loopRoute 4 loopKey 4 7) | return false
  return (Zkc.Formal.Written.SumcheckRows.checkGateMembers Zkc.Tools.Formal.gateRow located.linked.entry.definitions
    (List.nodup_append.mp located.linked.entry.distinct).1 located.linked.rounds).isSome

private def completeReduction (checked : ReadbackFixture) (callee : Key) (count : Nat) : Bool := Id.run do
  let program := checked.evidence.admitted.program
  let [⟨hdr,_⟩] := Member.withKey ProtocolHeader.key callee program.headers.protocols | return false
  let [state,_,_] := hdr.ins | return false
  let [_,_,residual] := hdr.outs | return false
  let rows := sourceRows checked.emission.bindings
  let events := sourceEvents checked.emission.bindings
  return (Zkc.Formal.Interactive.Sumcheck.ReductionRound.link program callee state.ty rows.scalarTy residual.ty 0 count events).isSome

/-- Swap the first two operands in the sequence construction following the rounds. -/
def swapDraws {V : Zkc.Core.Vocabulary} (callee : Key) (count : Nat) : Definition V → Definition V
  | .protocol k roles ins outs (.mk args steps exit) =>
    let changed := steps.modify count fun
      | .op site ns op (a::b::tail) => .op site ns op (b::a::tail)
      | other => other
    .protocol k roles ins outs (.mk args (if k == callee then changed else steps) exit)
  | other => other

private def checkReturnOrder (checked : CheckedRoot) (callee : Key) : IO Unit := do
  let e := checked.emission
  let changed := { e with named := ⟨e.named.definitions.map (swapDraws callee 10)⟩ }
  let .ok evidence := (changed.package ⟨[],[],[],[],[]⟩).checkEvidence
    | throw (IO.userError "Core refused the return-order control")
  let control : ReadbackFixture := ⟨checked.id,checked.state,changed,evidence⟩
  unless checkedRounds control callee 10 == some (true,false,false) && !completeReduction control callee 10 do
    throw (IO.userError "return-order control did not isolate the reduction exit")
  IO.println "Swapped returned coordinates admitted, all ten rounds certified, returned-point certificate refused"

/-- Redirect only the second emitted comparison to the initial claim. The first block and the
types of all operands are preserved. -/
def staleSecondClaim {V : Zkc.Core.Vocabulary} (callee : Key) : Definition V → Definition V
  | .protocol k roles ins outs (.mk args (first :: .block key index ns (.mk params code returns) :: rest) exit) =>
    let changed := code.modify 3 fun
      | .op site results op [_,boundary] => .op site results op [2,boundary]
      | other => other
    .protocol k roles ins outs (.mk args
      (first :: .block key index ns (.mk params (if k == callee then changed else code) returns) :: rest) exit)
  | other => other

private def checkStaleClaim (checked : CheckedRoot) (callee : Key) : IO Unit := do
  let e := checked.emission
  let changed := { e with named := ⟨e.named.definitions.map (staleSecondClaim callee)⟩ }
  let .ok evidence := (changed.package ⟨[],[],[],[],[]⟩).checkEvidence
    | throw (IO.userError "Core refused the stale-claim control")
  let control : ReadbackFixture := ⟨checked.id,checked.state,changed,evidence⟩
  unless checkedRounds control callee 1 == some (true,false,false) && (checkedRounds control callee 10).isNone do
    throw (IO.userError "the sequence certificate failed to distinguish using the initial claim in the second round")
  IO.println "Stale second claim admitted, first round certified, complete sequence refused"

/-- An event of a stepped reduction keeps one source identity and all of its physical sites.
Use the actual admitted Sumcheck and GKR callee; no fixed instruction numbering is assumed. -/
private def checkRoundSites {V : Zkc.Core.Vocabulary} (program : Zkc.Core.Typed V) (state : Compile.State) (callee : Key) (n : Nat) : IO Unit := do
  let some (.protocol code) := state.results.body? callee.number | throw (IO.userError "missing reduction")
  let some addresses := Emit.SiteAddresses.forProtocol program callee | throw (IO.userError "missing admitted callee")
  for name in ["round", "challenge"] do
    let some first := code.sites.find? (fun s => s.name == some name) | throw (IO.userError s!"missing {name}")
    let sites := Typing.SiteEntry.realizations code.sites first.event first.part
    let places := sites.filterMap addresses.resolve
    let keys := places.map (·.2)
    unless places.map (fun p => (p.1.map Prod.snd).toArray) == sites.map (·.iteration) do
      throw (IO.userError s!"{name} disagrees with its admitted block path")
    unless sites.map (·.iteration) == (Array.range n).map (fun i => #[i]) &&
        keys.size == n && keys.toList.eraseDups.length == n do
      throw (IO.userError s!"{name} lost a stepped realization or reused its instruction key")
    unless (Typing.SiteEntry.realizations code.sites first.event "nonexistent").isEmpty do
      throw (IO.userError "lookup ignored the event part")

private def checkExample (root : System.FilePath) (gkr : Bool) (variant : Variant)
    (fixedLayer : Bool := false) : IO Unit := do
  let file := if gkr then "examples/gkr_example.zkc" else "examples/sumcheck_example.zkc"
  let entry ← SourcePairReadback.source variant (root / file)
  let checked ← admitRoot entry (load root variant fixedLayer)
  let ⟨id,s,emission,_,evidence⟩ := checked
  let program := evidence.admitted.program
  let some origin := emission.origins.find? (·.definition.number == id)
    | throw (IO.userError "root location missing")
  let some (.protocol _ _ _ _ region) := emission.named.definitions.find? (·.key == origin.definition)
    | throw (IO.userError "missing executable root")
  let [(site, callee, [0,1], 3)] := applications region | throw (IO.userError "unexpected Reduce application ABI")
  if variant == .original then checkRoundSites program s callee (if gkr then 4 else 10)
  if gkr && variant == .original then
    let some (.protocol outer) := s.results.body? id | throw (IO.userError "missing GKR body")
    let some addresses := Emit.SiteAddresses.forProtocol program ⟨id⟩ | throw (IO.userError "missing admitted GKR")
    for name in ["q","t"] do
      let some event := outer.sites.find? (fun x => x.name == some name) | throw (IO.userError s!"missing {name}")
      let #[site] := Typing.SiteEntry.realizations outer.sites event.event event.part
        | throw (IO.userError s!"expected a single static site for {name}")
      unless site.iteration.isEmpty && (addresses.resolve site).any (·.1.isEmpty) do
        throw (IO.userError s!"ordinary GKR loop acquired a stepped address")
  let [_, _] := program.headers.protocols | throw (IO.userError "unexpected reachable protocol table")
  let [_] := Member.withKey (·.key) callee program.headers.protocols | throw (IO.userError "callee absent in admitted table")
  unless instanceName s callee.number == "Reduce" do throw (IO.userError "unexpected callee")
  let #[attached] := origin.specification | throw (IO.userError "expected one specification attachment")
  let #[("p", .apply _ (.instance target) _)] := attached.arguments
    | throw (IO.userError "expected a resolved specification function")
  let some (linear,affine,gate) := checkedRounds checked callee (if gkr then 4 else 10) | throw (IO.userError "missing emitted round block")
  unless gate == gkr && linear == (!gkr && (variant == .original || variant == .rename)) && affine == (!gkr && variant == .affine) do
    throw (IO.userError "round collision certificate disagrees with the applied instance")
  unless completeReduction checked callee (if gkr then 4 else 10) do
    throw (IO.userError "the returned point or claim disagrees with the source round trace")
  IO.println s!"Verified full reduction at callee {callee.number} with {if gkr then 4 else 10} ordered coordinates"
  if !gkr then
    unless certifiedSumcheck checked == some (linear,affine) do
      throw (IO.userError "full source verifier theorem disagrees with the round instance")
    IO.println s!"Full ten-variable source verifier soundness, original proof {linear}, affine proof {affine}"
  if !gkr && variant == .original then
    checkStaleClaim checked callee
    checkReturnOrder checked callee
  IO.println s!"Verified {if gkr then 4 else 10} consecutive rounds, original Pairs laws {linear}, affine Pairs laws {affine}"
  if gkr then
    IO.println "Verified gate boundary and project evaluation row in all four source rounds"
    let source := checked
    unless appliedGate source callee site [15,16,9] ⟨28⟩ && !appliedGate source callee site [15,16,8] ⟨28⟩ &&
        !appliedGate source callee site [15,16,9] ⟨27⟩ do throw (IO.userError "incorrect typed layer call site")
    IO.println "Gate theorem linked at layer loop 28, application 11; incorrect operand and enclosing loop refused"
  let some node := origin.nodes[site.number]? | throw (IO.userError "missing source node")
  let some checked := s.results.checked? id | throw (IO.userError "missing checked root")
  let .protocol body := checked.definition.body | throw (IO.userError "expected a protocol")
  let some (.stmt (.event _ _ (.apply _ sourceCallee _ _ roles ..))) := body.find? node
    | throw (IO.userError "application does not map to the source event")
  unless site == attached.instruction && callee.number == sourceCallee && roles == #[0,1] do
    throw (IO.userError "application source and emitted site disagree")
  let port (name : String) := (body.ports.find? (·.binder.name == name)).map (·.binder.id)
  if gkr then
    let some layer := body.statements.findSome? (fun
      | st@(.for _ (.loop binder _ _ _) _) => if (st.find? node).isSome then some binder.id else none
      | _ => none) | throw (IO.userError "Reduce call has no enclosing layer loop")
    let some point := body.statements.findSome? (fun
      | .bind _ binder _ _ => if binder.name == "z" then some binder.id else none
      | _ => none) | throw (IO.userError "missing layer point")
    let some circuit := port "c" | throw (IO.userError "missing circuit input")
    let some inputs := port "inputs" | throw (IO.userError "missing layer inputs")
    let requested : Emit.LocalApplication := ⟨target,[.binder circuit,.binder inputs,.bounded 4 layer,.binder point]⟩
    let fits := emission.externalApplicationAt? s ⟨id⟩ site callee [0,1] "p" "Zkc.Circuit.summand" == some requested
    unless instanceName s target == "summand" && fits == !fixedLayer do throw (IO.userError "incorrect summand attachment")
    IO.println s!"Checked source application to summand at the current layer {fits}"
  else
    let some values := port "values" | throw (IO.userError "missing public table")
    unless instanceName s target == "extension" &&
        emission.externalApplicationAt? s ⟨id⟩ site callee [0,1] "p" "Zkc.Polynomial.extension" ==
          some ⟨target,[.binder values]⟩ do
      throw (IO.userError "incorrect extension attachment")
    let some reduce := s.results.checked? callee.number | throw (IO.userError "missing Reduce")
    let .protocol rb := reduce.definition.body | throw (IO.userError "expected Reduce protocol")
    let calls := Emit.protocolFunctions rb
    let [boundary] := calls.toList.filter (fun k => instanceName s k == "boundary")
      | throw (IO.userError "ambiguous boundary member")
    let [evaluate] := calls.toList.filter (fun k => instanceName s k == "evaluate")
      | throw (IO.userError "ambiguous evaluation member")
    let rows := sourceRows emission.bindings
    let original := rows.locateMembers program ⟨boundary⟩ ⟨evaluate⟩ (rows.evaluationReadback ⟨evaluate⟩)
    let affine := rows.locateMembers program ⟨boundary⟩ ⟨evaluate⟩ (rows.affineReadback ⟨evaluate⟩)
    unless original.isSome == (variant == .original || variant == .rename) &&
        affine.isSome == (variant == .affine) do throw (IO.userError "unexpected round certificate")
  IO.println s!"Admitted {file} ({emission.named.definitions.length} definitions), member {repr variant}, fixed layer {fixedLayer}"

def replaceOnce (path : System.FilePath) (expected replacement : String) : IO SourceInput := do
  let text ← IO.FS.readFile path
  unless (text.splitOn expected).length == 2 do throw (IO.userError s!"ambiguous source edit in {path}")
  return ⟨path.toString, Syntax.parseString path.toString (text.replace expected replacement)⟩

/-- The verifier-side equality is checked on the referenced zero-round reduction. A
same-typed constant residual passes source and Core checking, then loses this certificate. -/
def checkEmpty (root : System.FilePath) (constantValue : Bool) (constantGuard : Bool := false) : IO Unit := do
  let source ← replaceOnce (root / "examples/sumcheck_example.zkc") "Proof = Sumcheck<10>" "Proof = Sumcheck<0>"
  let loader (parts : Array String) : IO (Option SourceInput) := do
    if constantValue && parts.back? == some "sumcheck" then
      return some (← replaceOnce (root / "examples/sumcheck.zkc")
        "return (prefix ++ challenges, running, s)" "return (prefix ++ challenges, 0, s)")
    if constantGuard && parts.back? == some "sumcheck" then
      return some (← replaceOnce (root / "examples/sumcheck.zkc")
        "guard @V reduced.value == evaluate(values, reduced.point)" "guard @V 0 == evaluate(values, reduced.point)")
    return ← SourcePairReadback.loadModule root .original parts
  let checked ← admitRoot source loader
  let some (.protocol _ _ _ _ region) := checked.emission.named.definitions.find? (·.key.number == checked.id)
    | throw (IO.userError "missing caller")
  let [(_,callee,[0,1],3)] := applications region | throw (IO.userError "missing applied reduction")
  let t := (sourceRows checked.emission.bindings).scalarTy
  let proof := Zkc.Formal.Interactive.Sumcheck.EmptyReduction.certify checked.evidence.admitted.program callee
    (.seq t (some 1)) t 0
  unless proof.isSome == !constantValue do throw (IO.userError "wrong empty-reduction law")
  IO.println s!"Zero-round source admitted, verifier result law {proof.isSome}, constant residual {constantValue}"
  let some body := checked.state.results.checked? checked.id | throw (IO.userError "missing checked Sumcheck")
  let .protocol sourceBody := body.definition.body | throw (IO.userError "expected protocol caller")
  let [evaluate] := (Emit.protocolFunctions sourceBody).toList.filter (fun k => instanceName checked.state k == "evaluate")
    | throw (IO.userError "expected terminal table evaluation")
  let whole := Zkc.Formal.Interactive.Sumcheck.EmptySumcheck.certify t (.inl (.field .equal .bls12381Fr .all)) rfl
    checked.evidence.admitted.program ⟨checked.id⟩ callee ⟨evaluate⟩ rfl
  unless whole.isSome == (!constantGuard && !constantValue) do throw (IO.userError "wrong source verifier law")
  IO.println s!"Zero-round Sumcheck law {whole.isSome}, constant guard {constantGuard}, constant residual {constantValue}"

private def checkRoundGuard (root : System.FilePath) : IO Unit := do
  let path := root / "examples/sumcheck_example.zkc"
  let entry : SourceInput := ⟨path.toString, Syntax.parse path.toString (← IO.FS.readBinFile path)⟩
  let loader (parts : Array String) : IO (Option SourceInput) := do
    if parts.back? == some "sumcheck" then
      return some (← replaceOnce (root / "examples/sumcheck.zkc")
        "guard @V running == R::boundary(round)" "guard @V 0 == R::boundary(round)")
    return ← SourcePairReadback.loadModule root .original parts
  let checked ← admitRoot entry loader
  let some (.protocol _ _ _ _ region) := checked.emission.named.definitions.find? (·.key.number == checked.id)
    | throw (IO.userError "missing root with changed round guard")
  let [(_,callee,[0,1],3)] := applications region | throw (IO.userError "missing reduction")
  if (checkedRounds checked callee 10).isSome then throw (IO.userError "changed guard acquired a round certificate")
  IO.println "Changed round guard admitted and round certificate refused"

private def checkGateBinding (root : System.FilePath) : IO Unit := do
  let entry ← SourcePairReadback.source .original (root / "examples/gkr_example.zkc")
  let loader (parts : Array String) : IO (Option SourceInput) := do
    if parts.back? == some "layered" then
      return some (← replaceOnce (root / "examples/support/circuits/layered.zkc")
        "circuit.gate_evaluate" "circuit.other_evaluate")
    return ← load root .original false parts
  let checked ← admitRoot entry loader
  let some (.protocol _ _ _ _ region) := checked.emission.named.definitions.find? (·.key.number == checked.id)
    | throw (IO.userError "missing GKR root with renamed primitive")
  let [(_,callee,[0,1],3)] := applications region | throw (IO.userError "missing applied reduction")
  unless checkedRounds checked callee 4 == some (false,false,false) do
    throw (IO.userError "wrong gate primitive acquired an evaluation certificate")
  IO.println "Alternative project row admitted, four round blocks recognized, gate certificate refused"

private def checkTerminalEdit (root : System.FilePath) (repeatFirst : Bool) : IO Unit := do
  let entry ← SourcePairReadback.source .original (root / "examples/sumcheck_example.zkc")
  let loader (parts : Array String) : IO (Option SourceInput) := do
    if repeatFirst && parts.back? == some "multilinear" then
      return some (← replaceOnce (root / "libraries/zkc/multilinear.zkc") "fix_first(rest, point[i])" "fix_first(rest, point[0])")
    if !repeatFirst && parts.back? == some "sumcheck" then
      return some (← replaceOnce (root / "examples/sumcheck.zkc") "guard @V reduced.value == evaluate(values, reduced.point)"
        "guard @V 0 == evaluate(values, reduced.point)")
    return ← SourcePairReadback.loadModule root .original parts
  let checked ← admitRoot entry loader
  let some (.protocol _ _ _ _ region) := checked.emission.named.definitions.find? (·.key.number == checked.id)
    | throw (IO.userError "missing caller")
  let [(_,callee,[0,1],3)] := applications region | throw (IO.userError "missing applied reduction")
  unless completeReduction checked callee 10 && certifiedSumcheck checked == some (false,false) do
    throw (IO.userError "terminal edit failed to isolate the outer source theorem")
  IO.println s!"Complete reduction retained, full verifier theorem refused, repeated first coordinate {repeatFirst}"

private def checkOneRound (root : System.FilePath) : IO Unit := do
  let source ← replaceOnce (root / "examples/sumcheck_example.zkc") "Proof = Sumcheck<10>" "Proof = Sumcheck<1>"
  let checked ← admitRoot source (SourcePairReadback.loadModule root .original)
  unless certifiedSumcheck checked 1 == some (true,false) do throw (IO.userError "one-round source verifier lost its bound")
  IO.println "Complete one-round source verifier certified"

def checkAll (root : System.FilePath) : IO Unit := do
  let site : Typing.SiteEntry := ⟨0, "value", none, default, #[1], some 7⟩
  let entries : List (List (Key × Nat) × Key) := [([(⟨2⟩,0)],⟨7⟩), ([(⟨3⟩,1)],⟨7⟩)]
  unless (Emit.SiteAddresses.ofAddresses entries).resolve site == some ([(⟨3⟩,1)],⟨7⟩) &&
      ((Emit.SiteAddresses.ofAddresses (([(⟨4⟩,1)],⟨7⟩) :: entries)).resolve site).isNone do
    throw (IO.userError "ambiguous or shared instruction address handled incorrectly")
  for variant in [Variant.original, .rename, .affine, .reversed] do checkExample root false variant
  checkExample root true .original
  checkExample root true .original true
  checkOneRound root
  checkEmpty root false
  checkEmpty root true
  checkEmpty root false true
  checkRoundGuard root
  checkGateBinding root
  checkTerminalEdit root true
  checkTerminalEdit root false

end Zkc.Tests.Formal.SourceProtocolRoots
