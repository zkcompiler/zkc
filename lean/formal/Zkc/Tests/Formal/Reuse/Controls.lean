import Zkc.Tests.Formal.Reuse.Manual
import Zkc.Tests.Formal.Reuse.Automatic

namespace Zkc.Tests.Formal.Reuse
open Core Frontend SourceProtocolRoots SourcePairReadback

private def shifted {V : Core.Vocabulary} (red : Key) (offset : Nat) : Definition V → Definition V
  | .protocol k roles ins outs (.mk names steps exit) =>
    let move := fun (site : Key) => Key.mk (offset + site.number)
    let step := fun (inst : Instruction (ProtocolRaw V) (List Role)) => match inst with
      | .op key ns op args => .op (move key) ns op args
      | .guard key who cond why => .guard (move key) who cond why
      | other => other
    let block := fun (inst : Instruction (ProtocolRaw V) (List Role)) => match inst with
      | .block key i ns (.mk params code result) => .block (move key) i ns (.mk params (code.map step) result)
      | other => other
    .protocol k roles ins outs (.mk names (if k == red then steps.map block else steps) exit)
  | other => other

private def modifyCore (c : CheckedRoot) (edit : Definition c.emission.bindings.vocabulary → Definition c.emission.bindings.vocabulary) :
    IO ReadbackFixture := do
  let e := { c.emission with named := ⟨c.emission.named.definitions.map edit⟩ }
  let .ok evidence := (e.package ⟨[],[],[],[],[]⟩).checkEvidence | throw (IO.userError "Core refused control")
  return ⟨c.id,c.state,e,evidence⟩

/-- Alternate installation order. Each timed call obtains its subject from an IO reference. -/
private def compare (label : String) (automatic manual : Unit → Bool) (expectedA expectedM : Bool) (samples : Nat) : IO Unit := do
  let a ← IO.mkRef automatic
  let m ← IO.mkRef manual
  for i in [:samples+1] do
    let order := if i % 2 == 0 then [("automatic",a,expectedA),("manual",m,expectedM)] else [("manual",m,expectedM),("automatic",a,expectedA)]
    for (method,f,expected) in order do
      let action ← f.get
      let start ← IO.monoNanosNow
      let observed := action ()
      unless observed == expected do throw (IO.userError s!"{label} {method} produced {observed}, expected {expected}")
      let stop ← IO.monoNanosNow
      if i > 0 then IO.println s!"REUSE,{label},{method},{i},{observed},{stop-start}"
  IO.println s!"VERDICT,{label},{expectedA},{expectedM}"

private def sumCase (label : String) (c : ReadbackFixture) (affine expected : Bool) (samples : Nat)
    (expectedManual : Bool := expected) (offset : Nat := 0) : IO Unit :=
  compare label (fun _ => (Automatic.sumcheck c ⟨7⟩ ⟨94⟩ affine).isSome)
    (fun _ => (Manual.sumcheck c affine offset).isSome) expected expectedManual samples

private def gkrCase (label : String) (c : CheckedRoot) (args : List Name) (loopKey : Key) (expected : Bool) (samples : Nat) : IO Unit :=
  let claim : Emit.LocalApplication := ⟨34,[.binder 0,.binder 1,.bounded 4 6,.binder 4]⟩
  compare label (fun _ => ((Automatic.gkr c ⟨17⟩ ⟨11⟩ args loopKey).bind (atSource (c := c) · claim)).isSome)
    (fun _ => ((Manual.gkr c args loopKey).bind (atSource (c := c) · claim)).isSome) expected expected samples

private def editModule (root : System.FilePath) (path suffix old newText : String) (parts : Array String) : IO (Option SourceInput) := do
  if parts.back? == some suffix then return some (← replaceOnce (root / path) old newText)
  SourcePairReadback.loadModule root .original parts

def run (root : System.FilePath) (samples : Nat) : IO Unit := do
  let entry ← source .original (root / "examples/sumcheck_example.zkc")
  for (variant,label,affine,expected) in [(Variant.original,"original",false,true),(.rename,"rename",false,true),
      (.affine,"affine-old-law",false,false),(.affine,"affine-new-law",true,true),(.reversed,"reversed",true,false)] do
    let c ← admitRoot entry (SourcePairReadback.loadModule root variant)
    sumCase label c affine expected samples
    if variant == .original then
      sumCase "stale-claim" (← modifyCore c (staleSecondClaim ⟨7⟩)) false false samples
      sumCase "swapped-coordinates" (← modifyCore c (swapDraws ⟨7⟩ 10)) false false samples
      let relabelled ← modifyCore c (shifted ⟨7⟩ 200)
      sumCase "new-site-keys" relabelled false true samples false
      sumCase "updated-manual-keys" relabelled false true samples true 200
  for (label,path,suffix,old,newText) in [
      ("terminal-coordinate","libraries/zkc/multilinear.zkc","multilinear","fix_first(rest, point[i])","fix_first(rest, point[0])"),
      ("terminal-guard","examples/sumcheck.zkc","sumcheck","guard @V reduced.value == evaluate(values, reduced.point)",
        "guard @V 0 == evaluate(values, reduced.point)")] do
    sumCase label (← admitRoot entry (editModule root path suffix old newText)) false false samples
  let gkr ← source .original (root / "examples/gkr_example.zkc")
  let c ← admitRoot gkr (SourcePairReadback.loadModule root .original)
  gkrCase "layer" c [15,16,9] ⟨28⟩ true samples
  gkrCase "layer-wrong-operand" c [15,16,8] ⟨28⟩ false samples
  gkrCase "layer-wrong-loop" c [15,16,9] ⟨27⟩ false samples
  let changed ← admitRoot gkr (editModule root "examples/support/circuits/layered.zkc" "layered"
    "circuit.gate_evaluate" "circuit.other_evaluate")
  gkrCase "layer-wrong-primitive" changed [15,16,9] ⟨28⟩ false samples
  let fixed ← admitRoot gkr (editModule root "examples/gkr.zkc" "gkr"
    "spec p = summand(c, inputs, i, z)" "spec p = summand(c, inputs, 0, z)")
  compare "constant-layer-executable" (fun _ => (Automatic.gkr fixed ⟨17⟩ ⟨11⟩ [15,16,9] ⟨28⟩).isSome)
    (fun _ => (Manual.gkr fixed [15,16,9] ⟨28⟩).isSome) true true samples
  gkrCase "constant-layer-source-claim" fixed [15,16,9] ⟨28⟩ false samples
  let rebound ← admitRoot gkr (editModule root "examples/support/circuits/layered.zkc" "layered"
    "external(\"Zkc.Circuit.summand\")" "external(\"Example.otherSummand\")")
  compare "rebound-layer-executable" (fun _ => (Automatic.gkr rebound ⟨17⟩ ⟨11⟩ [15,16,9] ⟨28⟩).isSome)
    (fun _ => (Manual.gkr rebound [15,16,9] ⟨28⟩).isSome) true true samples
  gkrCase "rebound-layer-source-claim" rebound [15,16,9] ⟨28⟩ false samples

end Zkc.Tests.Formal.Reuse
