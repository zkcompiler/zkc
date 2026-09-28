import Tools.Mathematical.PlacementCheck
import Tools.Mathematical.SchemaEncoding
import Tools.Mathematical.Json

/-! One retained source/target pair for mathematical placement checking.

Hash requests encode the independently reconstructed bytes. The host must hash
them and compare their expected digests before accepting this correspondence.
The returned common target is the exact value checked here and is passed on to
common admission and participant correspondence, without replacement.
-/

set_option autoImplicit false
namespace Tools.Mathematical.Placement
open Zkc.Source.Mathematical

structure HashObligation where
  bytes : ByteArray
  expected : String

structure Checked where
  located : Lean.Json
  hashes : List HashObligation

def check (capture : Raw.Attribute) : Except String Checked := do
  let field ← PlacementWitness.record ["format", "mathematical", "located", "witness"] capture
  PlacementWitness.ensure ((← PlacementWitness.string (← field "format")) == "zkc.mathematical-placement/1")
  let rawSource ← field "mathematical"
  let source ← Schema.decode rawSource
  let admitted ← (BlsAdmission.admit source 10000000).mapError
    (fun reason => "math-admission-refused: " ++ reprStr reason)
  let [view] := PlacementView.history admitted.header admitted.assembly.table.history
    | throw "math-placement-instance-subset"
  let witness ← PlacementWitness.decode (← field "witness")
  let (body, graphWork) ← (PlacementGraph.build admitted.header view).run {}
  let (demand, graphWork) ← (PlacementGraph.demand body).run graphWork
  let located ← field "located"
  let _ ← (PlacementCheck.check admitted.header body demand witness located).run {remaining := graphWork.remaining}
  let sourceBytes ← Codec.encode (← SchemaEncoding.encode source)
  let targetBytes ← Codec.encode located
  let mut hashes := [HashObligation.mk ("zkc.math.subject.v1".toUTF8.push 0 ++ sourceBytes) witness.sourceDigest,
    HashObligation.mk ("zkc.math.placement.target.v1".toUTF8.push 0 ++ targetBytes) witness.targetDigest]
  for (identity, descriptor) in InstallationDescriptors.descriptors do
    hashes := hashes ++ [⟨"zkc.math.installation.v1".toUTF8.push 0 ++ (← Codec.encode descriptor), identity.digest⟩]
  return ⟨← Json.common 65 located, hashes⟩

end Tools.Mathematical.Placement
