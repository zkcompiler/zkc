module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.ApplicationData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:5054785ea5a11ddf05ec13ca971c1f8dd1ec5e851890fc6c6521f49dab965611"
  entry := "s6h73616d706c653h52756e"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s6h73616d706c653h52756e", .protocol, .publicDef, [.field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000000", "role00000001"], ["role00000000", "role00000001"]], [["role00000000"], ["role00000001"]]⟩, [], none, (.block [.instruction (.protocolApply "zkl_1029dffd30597bc82f81c8cfdb80d2ccd06b8fc9301525510f4cb8960568b1b0" ["role00000000", "role00000001"]) [0, 1] [.field "bls12-381.fr", .field "bls12-381.fr"] [] "s0"] (.ret [0, 1]))⟩, .function ⟨"zkl_1029dffd30597bc82f81c8cfdb80d2ccd06b8fc9301525510f4cb8960568b1b0", .protocol, .publicDef, [.field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000000", "role00000001"], ["role00000000", "role00000001"]], [["role00000000"], ["role00000001"]]⟩, [], none, (.block [.instruction (.protocolApply "zkl_f39ed99e9ca380a5675dcf66974ff8ba662cf37425e869e7bb6fe866ef82d479" ["role00000001", "role00000000"]) [0, 1] [.field "bls12-381.fr", .field "bls12-381.fr"] [] "s0", .instruction (.protocolApply "s6h73616d706c657h4f627365727665" ["role00000000", "role00000001"]) [] [] [] "s3"] (.ret [1, 0]))⟩, .function ⟨"zkl_f39ed99e9ca380a5675dcf66974ff8ba662cf37425e869e7bb6fe866ef82d479", .protocol, .publicDef, [.field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"], some ⟨["role00000000", "role00000001"], [["role00000000", "role00000001"], ["role00000000", "role00000001"]], [["role00000000"], ["role00000001"]]⟩, [], none, (.block [.instruction (.fieldAdd "bls12-381.fr") [0, 1] [.field "bls12-381.fr"] [] "", .instruction (.fieldMultiply "bls12-381.fr") [1, 2] [.field "bls12-381.fr"] [] ""] (.ret [1, 0]))⟩, .function ⟨"s6h73616d706c657h4f627365727665", .protocol, .publicDef, [], [], some ⟨["role00000000", "role00000001"], [], []⟩, [], none, (.block [] (.ret []))⟩]
  contracts := [⟨"s6h73616d706c653h52756e", []⟩, ⟨"zkl_1029dffd30597bc82f81c8cfdb80d2ccd06b8fc9301525510f4cb8960568b1b0", []⟩, ⟨"zkl_f39ed99e9ca380a5675dcf66974ff8ba662cf37425e869e7bb6fe866ef82d479", []⟩, ⟨"s6h73616d706c657h4f627365727665", []⟩]

end ZkcExamples.Structured.ApplicationData
