module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace ZkcExamples.Construction.EmbeddingEqualityData
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:fc9a282a5ab377d24c58983c7b3c8fdef4361068612f63462deef5318fbb7510"
  entry := "s7h6578616d706c6517h456d62656464696e67457175616c697479"
  domains := []
  relations := [⟨"s7h6578616d706c655h457175616c", .publicDef, "zkc.language.formula/0", "s7h6578616d706c655h457175616c", "237d2e6879805fdf2f4805f16beaf704b37a14a4f9d46f02f6b58f4e0a11983e", [.field "koala-bear", .field "koala-bear"], [.boolean], ["statement", "statement"], some ("zkf_fe5e2a3c5bbade8b5ce48ffd090142e127cc04ea947d1766a7f847161f657190")⟩]
  bindings := [⟨"zkl_binding_0", "field.embed", ["koala-bear.ext8-binomial3"], ""⟩]
  definitions := [.function ⟨"s7h6578616d706c6517h456d62656464696e67457175616c697479", .protocol, .publicDef, [.field "koala-bear", .field "koala-bear", .service "random.koala-bear.ext8-binomial3/0"], [.boolean], some ⟨["role00000000", "role00000001"], [["role00000000", "role00000001"], ["role00000001"], ["role00000001"]], [["role00000001"]]⟩, [], none, (.block [.instruction (.localCall "s7h6578616d706c655h656d626564" "role00000000") [0] [.field "koala-bear.ext8-binomial3"] [] "s0", .instruction (.exchange "role00000000" "role00000001") [0] [.field "koala-bear.ext8-binomial3"] [] "label_6d657373616765_0", .instruction (.restrict ["role00000001"]) [0] [.field "koala-bear.ext8-binomial3"] [] "", .instruction (.draw "role00000001" "koala-bear.ext8-binomial3") [5] [.field "koala-bear.ext8-binomial3"] [] "label_6368616c6c656e6765", .instruction (.exchange "role00000001" "role00000000") [0] [.field "koala-bear.ext8-binomial3"] [] "label_64656c6976657279_0", .instruction (.restrict ["role00000000"]) [0] [.field "koala-bear.ext8-binomial3"] [] "", .instruction (.fieldAdd "koala-bear.ext8-binomial3") [3, 2] [.field "koala-bear.ext8-binomial3"] [] "", .instruction (.localCall "s7h6578616d706c655h656d626564" "role00000001") [7] [.field "koala-bear.ext8-binomial3"] [] "s9", .instruction (.fieldAdd "koala-bear.ext8-binomial3") [0, 4] [.field "koala-bear.ext8-binomial3"] [] "", .instruction (.fieldEqual "koala-bear.ext8-binomial3") [2, 0] [.boolean] [] "", .instruction (.fieldAdd "koala-bear.ext8-binomial3") [7, 6] [.field "koala-bear.ext8-binomial3"] [] "", .instruction (.localCall "s7h6578616d706c655h656d626564" "role00000001") [12] [.field "koala-bear.ext8-binomial3"] [] "s14", .instruction (.fieldAdd "koala-bear.ext8-binomial3") [0, 8] [.field "koala-bear.ext8-binomial3"] [] "", .instruction (.fieldEqual "koala-bear.ext8-binomial3") [2, 0] [.boolean] [] "", .instruction (.booleanAnd) [4, 0] [.boolean] [] ""] (.ret [0]))⟩, .function ⟨"zkf_fe5e2a3c5bbade8b5ce48ffd090142e127cc04ea947d1766a7f847161f657190", .math, .privateDef, [.field "koala-bear", .field "koala-bear"], [.boolean], none, [], none, (.block [.instruction (.fieldEqual "koala-bear") [0, 1] [.boolean] [] ""] (.ret [0]))⟩, .function ⟨"s7h6578616d706c655h656d626564", .local, .publicDef, [.field "koala-bear"], [.field "koala-bear.ext8-binomial3"], none, [], some ("s7h6578616d706c655h656d626564", []), (.block [.instruction (.exec "algebra.exec.field_embed" "zkl_binding_0" []) [0] [.field "koala-bear.ext8-binomial3"] [] "s0"] (.ret [0]))⟩]
  contracts := [⟨"s7h6578616d706c6517h456d62656464696e67457175616c697479", [⟨.target, "equality", ⟨"s7h6578616d706c655h457175616c", [⟨.input, 0, "role00000001"⟩, ⟨.input, 1, "role00000001"⟩]⟩, none, some (⟨.output, 0, "role00000001"⟩)⟩]⟩]
  catalogue := { nominals := [⟨"koala-bear.ext8-binomial3", .field, [("BaseField", "koala-bear")], ["IndexRandomness", "ExtensionField", "TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo"], (some 2130706433)⟩, ⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "PrimeField", "CharacteristicNotTwo"], (some 2130706433)⟩], services := [⟨"random.koala-bear.ext8-binomial3/0", "koala-bear.ext8-binomial3", ["draw", "index"]⟩] }

end ZkcExamples.Construction.EmbeddingEqualityData
