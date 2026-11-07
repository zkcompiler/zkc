module

public import ZkcExamples.Structured.FriSourceData

@[expose] public section

/-! Complete native export of the two-call test root. The native regression
checks all shared declarations byte-for-byte as structured data. -/
namespace Tests.FriBindingSitesData
open Zkc.Source.Structured
abbrev single := ZkcExamples.Structured.FriSourceData.snapshot

def entry : Definition :=
  .function ⟨"s7h6578616d706c653h467269", .protocol, .publicDef, [.vector "koala-bear.ext8-binomial3", .field "koala-bear.ext8-binomial3", .index, .index, .service "random.koala-bear.ext8-binomial3/0"], [.boolean, .boolean], some ⟨["role00000000", "role00000001"], [["role00000000"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000000", "role00000001"], ["role00000001"]], [["role00000001"], ["role00000001"]]⟩, [], some (.protocol ⟨"example::Fri", []⟩), (.block [.instruction (.protocolApply "zkl_5be81258fbd44da038012fc7680dce446a9d3c1f187a820b4a63d44cd345c871" ["role00000000", "role00000001"]) [0, 1, 1, 2, 3, 4] [.boolean, .indices, .indices, .vector "koala-bear.ext8-binomial3"] [] "label_6c656674", .instruction (.protocolApply "zkl_5be81258fbd44da038012fc7680dce446a9d3c1f187a820b4a63d44cd345c871" ["role00000000", "role00000001"]) [4, 5, 5, 6, 7, 8] [.boolean, .indices, .indices, .vector "koala-bear.ext8-binomial3"] [] "label_7269676874"] (.ret [4, 0]))⟩

def ports : SourceProtocol :=
  ⟨"s7h6578616d706c653h467269", [⟨"word", (.builtin "vector" [(.field "koala-bear.ext8-binomial3")]), ["role00000000"], 0, 1, (.data ["role00000000"])⟩, ⟨"shift", (.field "koala-bear.ext8-binomial3"), ["role00000000", "role00000001"], 1, 1, (.data ["role00000000", "role00000001"])⟩, ⟨"round_count", .index, ["role00000000", "role00000001"], 2, 1, (.data ["role00000000", "role00000001"])⟩, ⟨"query_count", .index, ["role00000000", "role00000001"], 3, 1, (.data ["role00000000", "role00000001"])⟩], [⟨"left", .boolean, ["role00000001"], 0, 1, (.data ["role00000001"])⟩, ⟨"right", .boolean, ["role00000001"], 1, 1, (.data ["role00000001"])⟩]⟩

def snapshot : Snapshot := {single with
  source := "sha256:0ee8506b78354925dc38186111fc621071f911ccfe0d5bd85b00db834c6268ca"
  definitions := single.definitions.set 0 entry
  sourceDeclarations := {single.sourceDeclarations with
    protocols := single.sourceDeclarations.protocols.set 0 ports}}

end Tests.FriBindingSitesData
