module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Structured.TableIndexedReadData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:cb0ae672788867050e5b3751cfb9586695a30d040623b2c67eef55b3fc9e47ed"
  entry := "zkl_4597680e78fa47047d8f8fcedcf8fe295ebd02cf0856991e260e9130a8d2ea87"
  domains := [⟨"finite_zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a_s4_domain", [.vector "koala-bear"], .indices 0 0⟩]
  relations := [⟨"zkl_4a7527ef14d9b3ec64519e018a58da326ed309327b8561291731722a15176757", .publicDef, "zkc.language.formula/0", "zkl_4a7527ef14d9b3ec64519e018a58da326ed309327b8561291731722a15176757", "ae9fe16a4a5ff9b0b0dea1491f4b761b2cb11e19451a102fb23355c2e24c644d", [.vector "koala-bear", .index, .field "koala-bear"], [.boolean], ["parameter", "statement", "statement"], some ("zkf_eeb8bf15a7659bce5aa909302f5a359e054778ba70f159e4c02088dc98b55444")⟩]
  bindings := []
  definitions := [.realization ⟨"zkl_realization_f23e2cf91e13194bc53b5a53cc8b12fd546c4daae64d3751bb30899d04fa3be4", [.vector "koala-bear", .index, .field "koala-bear"], [.boolean], "zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a"⟩, .function ⟨"zkl_4597680e78fa47047d8f8fcedcf8fe295ebd02cf0856991e260e9130a8d2ea87", .protocol, .publicDef, [.vector "koala-bear", .index, .field "koala-bear"], [.boolean], some ⟨["role00000000", "role00000001"], [["role00000001"], ["role00000001"], ["role00000001"]], [["role00000001"]]⟩, [], none, (.block [.instruction (.localCall "zkl_f1d7fac3d3ce489e30442c70b43fb2fd1ecf6ba206d6f59492b3f75b72249a66" "role00000001") [0, 1, 2] [.boolean] [] "s0"] (.ret [0]))⟩, .function ⟨"zkf_eeb8bf15a7659bce5aa909302f5a359e054778ba70f159e4c02088dc98b55444", .math, .privateDef, [.vector "koala-bear", .index, .field "koala-bear"], [.boolean], none, [], none, (.block [.instruction (.call "zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a") [0, 1, 2] [.boolean] [] ""] (.ret [0]))⟩, .function ⟨"zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a", .math, .privateDef, [.vector "koala-bear", .index, .field "koala-bear"], [.boolean], none, [], none, (.block [.instruction (.booleanConstant false) [] [.boolean] [] "", .instruction (.fold "finite_zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a_s4_domain" "finite_zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a_s4_body" "") [1, 0, 2, 3] [.boolean] [] ""] (.ret [0]))⟩, .function ⟨"finite_zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a_s4_body", .math, .privateDef, [.boolean, .index, .vector "koala-bear", .index, .field "koala-bear"], [.boolean], none, [⟨1, 2, 0⟩], none, (.block [.instruction (.call "zkl_b495e0ed1417c211869f7fedf6d130630630d8ae869a74d3e0edf61af30302b3") [0, 1, 3, 2, 4] [.boolean] [] ""] (.ret [0]))⟩, .function ⟨"zkl_b495e0ed1417c211869f7fedf6d130630630d8ae869a74d3e0edf61af30302b3", .math, .privateDef, [.boolean, .index, .index, .vector "koala-bear", .field "koala-bear"], [.boolean], none, [⟨1, 3, 0⟩], none, (.block [.instruction (.indexEqual) [1, 2] [.boolean] [] "", .instruction (.boundedAt "koala-bear") [4, 2] [.field "koala-bear"] [] "", .instruction (.fieldEqual "koala-bear") [0, 6] [.boolean] [] "", .instruction (.booleanAnd) [2, 0] [.boolean] [] "", .instruction (.booleanOr) [4, 0] [.boolean] [] ""] (.ret [0]))⟩, .function ⟨"zkl_f1d7fac3d3ce489e30442c70b43fb2fd1ecf6ba206d6f59492b3f75b72249a66", .local, .publicDef, [.vector "koala-bear", .index, .field "koala-bear"], [.boolean], none, [], some ("s14h7461626c655f72656c6174696f6e10h636865636b5f72656164", []), (.block [.instruction (.apply "zkl_realization_f23e2cf91e13194bc53b5a53cc8b12fd546c4daae64d3751bb30899d04fa3be4") [0, 1, 2] [.boolean] [] "s0"] (.ret [0]))⟩]
  contracts := [⟨"zkl_4597680e78fa47047d8f8fcedcf8fe295ebd02cf0856991e260e9130a8d2ea87", [⟨.target, "selected_read", ⟨"zkl_4a7527ef14d9b3ec64519e018a58da326ed309327b8561291731722a15176757", [⟨.input, 0, "role00000001"⟩, ⟨.input, 1, "role00000001"⟩, ⟨.input, 2, "role00000001"⟩]⟩, none, some (⟨.output, 0, "role00000001"⟩)⟩]⟩]
  catalogue := { nominals := [⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩], services := [] }

end ZkcExamples.Structured.TableIndexedReadData
