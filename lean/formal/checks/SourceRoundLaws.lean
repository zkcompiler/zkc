import Zkc.Tools.Formal.DrawCharge
import Zkc.Tests.Formal.SourceProtocolRoots

open Zkc.Core Zkc.Frontend Zkc.Tools.Formal Zkc.Tests.Formal
open Zkc.Formal.Interactive.Sumcheck Zkc.Formal.Interactive.Sumcheck.ReductionRound
open Zkc.Formal.Written.SumcheckRows

namespace SourceRoundLaws

private def modified (path : System.FilePath) (edits : List (String × String)) : IO SourceInput := do
  let mut text ← IO.FS.readFile path
  for (before, after) in edits do
    unless (text.splitOn before).length == 2 do throw (IO.userError s!"expected one occurrence of {before}")
    text := text.replace before after
  return ⟨path.toString, Syntax.parseString path.toString text⟩

private def shifted (root : System.FilePath) (edits : List (String × String) := []) : IO Written.AdmittedRoot := do
  let entry ← SourcePairReadback.source .original (root / "examples/shifted_sumcheck.zkc")
  SourceProtocolRoots.admitRoot entry fun parts => do
    if parts.back? == some "shifted_pairs" then
      return some (← modified (root / "examples/support/shifted_pairs.zkc") edits)
    SourcePairReadback.loadModule root .original parts

/-- Follow the emitted block and its SSA operands back to the source declaration and its
static argument. This also works on the swapped reduction, before any certificate exists. -/
private def membersAtBlocks (c : Written.AdmittedRoot) (swapped : Bool) : Option (List (List (Key × Nat) × Key)) := do
  let keys ← sumcheckCallKeys c.emission ⟨c.id⟩
  let .protocol _ _ _ _ (.mk _ steps _) ← c.emission.named.definitions.find? (·.key == keys.reduction) | none
  let blocks := steps.filterMap fun
    | .block key index _ (.mk _ ops _) => some (key,index,ops)
    | _ => none
  guard (blocks.map (·.2.1) == [0,1])
  blocks.mapM fun (key,index,ops) => do
    let [msg] := ops.filterMap (fun | .op _ [out] (.event (.flow .message 0 [1]) _) _ => some out | _ => none) | none
    let [(draw,coin)] := ops.filterMap (fun | .op site [out] (.event (.given (.coin _) 1 [0]) _) [] => some (site,out) | _ => none) | none
    let findCall (who : List Role) (args : List Name) := ops.filterMap fun
      | .op _ _ (.compute roles (.call fn)) xs => if roles == who && xs == args then some fn else none
      | _ => none
    let [b] := findCall [1] [msg] | none
    let [e] := findCall [0,1] [msg,coin] | none
    let d := if swapped then index else 1-index
    for (fn,expected) in [(b,"boundary"),(e,"interpolate")] do
      let some (.fn ..) := c.emission.named.definitions.find? (·.key == fn) | none
      let inst ← c.state.results.key? fn.number
      guard (c.state.program.nameOf inst.declaration == expected && inst.arguments == #[.natural d])
    return ([(key,index)],draw)

section Counterexample
open Zkc.Formal.Written
open scoped RoundCharge ArithmeticModel
local notation "rows" => ArithmeticModel.scalarRows

private abbrev offsets (d : Nat) := d == 1

/-- The two distinct challenges both correct the false claim at the wrong depth.
The local execution equations come from the admitted boundary and evaluator. -/
private theorem misplaced {hs : Headers Standard} (ds : Defs Standard hs) {msg st out}
    (ops : Members hs (rows).scalarTy msg st out) (inner : Bool)
    (impl : PairLaws rows ds ops inner (!inner)) :
    ¬ Nonempty (RoundInterpretationOn scalarModel (Defs.fnTable scalarModel ds) (encodedClaims offsets)
      ([0,1] : List Scalar) 1 ops (fun _ : Unit => if inner then 1 else 0)) := by
  let _ : DecidableEq (scalarModel.Val (rows).scalarTy) := inferInstanceAs (DecidableEq Scalar)
  rintro ⟨cross⟩
  obtain rfl := impl.aligned
  let m : scalarModel.Val (rows).pair := (0,0,())
  let math := (ArithmeticModel.reductionArithmetic Scalar Scalar 1).scalar (by decide)
  let output := functionResult (M := scalarModel) (t := (rows).scalarTy)
  have boundary : cross.boundary m = ScalarRows.encode inner ((0 : Scalar) + 0) :=
    Option.some.inj (congrArg output ((cross.ends m).symm.trans (impl.boundary scalarModel math m)))
  have evaluate (r : Scalar) : cross.evaluate m r = ScalarRows.encode (!inner) (line (0,0) r) :=
    Option.some.inj (congrArg output ((cross.atPoint m r).symm.trans (impl.evaluate scalarModel math m r)))
  cases inner with
  | false =>
    let x : Cube Scalar 1 := (1,1)
    have bad := cross.roots () x m (by rw [boundary]; change (0 : Scalar) ≠ 3; decide)
    change ([0,1] : List Scalar).countP (fun r : Scalar => @decide _ ((inferInstance : DecidableEq Scalar) (cross.evaluate m r) (Cube.restrict 0 x r))) ≤ 1 at bad
    simp only [evaluate] at bad
    revert bad
    decide
  | true =>
    let x : Cube Scalar 2 := ((-1,0),(-1,0))
    have bad := cross.roots () x m (by rw [boundary]; change (1 : Scalar) ≠ ((-1 + 0) + (-1 + 0)); decide)
    change ([0,1] : List Scalar).countP (fun r : Scalar => @decide _ ((inferInstance : DecidableEq Scalar) (cross.evaluate m r) (Cube.sum 1 (Cube.restrict 1 x r) + 1))) ≤ 1 at bad
    simp only [evaluate] at bad
    revert bad
    decide

private def checkCounterexamples {p : Zkc.Core.Typed Standard} {root red eval}
    (cert : TableVerifier.Certified rows ArithmeticModel.vectors p root red eval 2 ArithmeticModel.events) :=
  let ds := cert.linked.entry.definitions
  cert.linked.rounds.checkMembersAt
    (fun d {_ _ _} ops => ¬ Nonempty (RoundInterpretationOn scalarModel (Defs.fnTable scalarModel ds) (encodedClaims offsets)
      ([0,1] : List Scalar) 1 ops (fun _ : Unit => if d == 0 then 1 else 0)))
    fun d _ _ {_ _ _} ops => do
      let inner := d == 0
      let ⟨law⟩ ← certifyEncodedPairs rows ds (List.nodup_append.mp cert.linked.entry.distinct).1 ops inner
        (!inner) ((rows).encodedAffineReadback true (!inner))
      return ⟨misplaced ds ops inner law⟩

end Counterexample

private def checkSum (root : System.FilePath) : IO Unit := do
  let c ← shifted root
  let cert ← IO.ofExcept (chargeSumcheck c 2 "challenge")
  unless [0,1,2].map cert.verifier.shifted == [false,true,false] do
    throw (IO.userError "unexpected intermediate claim encoding")
  unless membersAtBlocks c false == some cert.issued.charge.draws do
    throw (IO.userError "charge and both pairs of source callees must resolve at the same paths")
  if plain : c.emission.bindings.rows = [] then
    unless (checkCounterexamples (cert.standardVerifier plain).1).isSome do
      throw (IO.userError "missing wrong-depth collision counterexamples on the actual source members")
  else throw (IO.userError "unexpected extra field rows")
  let exchanged ← shifted root [("boundary<remaining = 1 - i>", "boundary<remaining = i>"),
    ("interpolate<remaining = 1 - i>", "interpolate<remaining = i>")]
  unless (membersAtBlocks exchanged true).isSome do throw (IO.userError "the control did not exchange both callees")
  let .error "uncertified Sumcheck verifier" := chargeSumcheck exchanged 2 "challenge"
    | throw (IO.userError "issued a certificate with the intermediate encodings exchanged")
  for (before,after,reason) in [
      ("(∑ v ∈ values, v) == claim", "(∑ v ∈ values, v) == 0", "written sum relation"),
      ("(∑ v ∈ values, v) == claim", "(∑ v ∈ values, claim) == claim", "written sum relation"),
      ("m.1 - m.0) * r + 1", "m.0 - m.1) * r + 1", "uncertified Sumcheck"),
      ("if remaining == 1 then m.0 + (m.1 - m.0) * r + 1 else m.0 + (m.1 - m.0) * r",
       "gap = r - r\n    guard gap != 0\n    return m.0 + (m.1 - m.0) * r + 1 / gap", "uncertified Sumcheck"),
      ("reduced.value == evaluate", "0 == evaluate", "uncertified Sumcheck")] do
    let altered ← shifted root [(before,after)]
    let .error why := chargeSumcheck altered 2 "challenge" | throw (IO.userError s!"issued after {after}")
    unless why.contains reason do throw (IO.userError why)
  IO.println "Source Sumcheck issued at depths 1 and 0. Both wrong-depth collision laws refuted on its members. Exchanged callees and five admitted mutations refused."

private def checkEquivalentExpressions (root : System.FilePath) : IO Unit := do
  let entry ← SourceProtocolRoots.replaceOnce (root / "examples/sumcheck_example.zkc")
    "Proof = Sumcheck<10>" "Proof = Sumcheck<2>"
  for edit in [("claim == ∑ v ∈ values, v", "(∑ v ∈ values, v) == claim"),
      ("(1 - r) * m.0 + r * m.1", "m.0 + (m.1 - m.0) * r")] do
    let c ← SourceProtocolRoots.admitRoot entry fun parts => do
      if parts.back? == some "sumcheck" then return some (← modified (root / "examples/sumcheck.zkc") [edit])
      SourcePairReadback.loadModule root .original parts
    let _ ← IO.ofExcept (chargeSumcheck c 2 "challenge")
  IO.println "Ordinary Sumcheck issued with the reversed relation and commuted affine factors independently."

private def specializedGate (depth : Nat) := Emit.primitiveName
  ⟨"circuit.gate_evaluate", #[.type (StandardNames.fieldType .bls12381Fr),.nat depth]⟩

private def checkLayer (c : Written.AdmittedRoot) : Option Bool := do
  let b := c.emission.bindings
  let p := c.evidence.admitted.program
  let .protocol _ _ _ _ (.mk _ steps _) ← c.emission.named.definitions.find? (·.key == ⟨c.id⟩) | none
  let [(loopKey,count,before,inner)] := steps.zipIdx.filterMap (fun
    | (.loop key _ (.fixed count) _ _ (.mk _ inner _), pos) => some (key,count,pos,inner)
    | _ => none) | none
  let [(site,red,args,inside)] := inner.zipIdx.filterMap (fun
    | (.op site _ (.apply red [0,1]) args,pos) => some (site,red,args,pos)
    | _ => none) | none
  let ⟨hdr,member⟩ ← p.findProtocol ⟨c.id⟩
  let ⟨callee,_⟩ ← p.findProtocol red
  let [st,_,_] := callee.ins | none
  let [_,_,out] := callee.outs | none
  let call ← atSite p member red site st.ty (sourceRows b).scalarTy out.ty 0 4 (sourceEvents b)
    args (loopRoute before loopKey count inside)
  let summand ← c.emission.externalApplicationAt? c.state hdr.key site red [0,1] "p" "Zkc.Circuit.summand"
  let .ok cert := chargeGateFamily (c := c) call summand "challenge" specializedGate | none
  let .error "uncertified gate member at the selected depth" :=
    chargeGateFamily (c := c) call summand "challenge" (fun d => specializedGate (3-d)) | none
  return cert.issued.charge.draws.length == 4

private def checkGkr (root : System.FilePath) : IO Unit := do
  let entry ← SourcePairReadback.source .original (root / "examples/gkr_example.zkc")
  let c ← SourceProtocolRoots.admitRoot entry fun parts => do
    if parts.back? == some "sumcheck" then
      return some (← modified (root / "examples/sumcheck.zkc") [
        ("def evaluate(m: Message", "def evaluate<depth: nat>(m: Message"),
        ("law at_point(m:", "law at_point<depth: nat>(m:"),
        ("evaluate(m, r) == value", "evaluate<depth = depth>(m, r) == value"),
        ("R::evaluate(round, challenge)", "R::evaluate<depth = rounds - 1 - i>(round, challenge)")])
    SourcePairReadback.loadModule root .original parts
  unless checkLayer c == some true do throw (IO.userError "incorrect depth or gate primitive at the selected GKR call")
  IO.println "Source GKR issued with four depth-specialized primitives. Reversing the primitive selection failed."

#print axioms ChargedSumcheck.primeBoundOfRelation
#print axioms ChargedGateFamily.bound
#print axioms misplaced

#eval show IO Unit from do
  let root := (← IO.currentDir) / "../.."
  checkSum root
  checkEquivalentExpressions root
  checkGkr root

end SourceRoundLaws
