module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.UnitStateData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:83b0a853bded25681859e568f26270520f738476a712243e951a2c2218a85c3e"
  entry := "main"
  role := "P"
  domains := [⟨"items", [.vector "bls12-381.fr"], .elements 0⟩]
  definitions := [.function ⟨"step", .local, .privateDef, [.field "bls12-381.fr", .vector "bls12-381.fr", .boolean], [], [], some ("step", []), (.block [] (.stop .abort "body_stop"))⟩, .function ⟨"predicate", .local, .privateDef, [.field "bls12-381.fr", .vector "bls12-381.fr", .boolean], [.boolean], [], some ("predicate", []), (.block [] (.ret [2]))⟩, .finite ⟨"fold", .publicDef, [.vector "bls12-381.fr", .boolean], [], "items", "step", "predicate"⟩, .function ⟨"work", .local, .publicDef, [.vector "bls12-381.fr", .boolean], [.boolean], [], some ("work", []), (.block [.instruction (.apply "fold") [0, 1] [] [] "fold"] (.ret [1]))⟩, .function ⟨"main", .protocol, .publicDef, [.vector "bls12-381.fr", .boolean], [.boolean], [], none, (.block [.instruction (.localCall "work" "P") [0, 1] [.boolean] [] "work"] (.ret [0]))⟩]

end ZkcExamples.Structured.UnitStateData
