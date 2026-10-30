module

public import Zkc.Protocols.Multilinear.Source.CollectBodies
public import Zkc.Protocols.Multilinear.Source.PrefixBodies

@[expose] public section

/-! Private mathematical realizations selected by the current Sumcheck exports.
Each source association checks these names against that source's complete body. -/
namespace ZkcExamples.Structured.SumcheckMathBindings

abbrev collection : MultilinearCollectBodies.Bindings where
  collection := "_finite_admission_0"
  domain := "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain"
  callback := "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body"
  computation := "_mathematical_admission_1"

abbrev prefixBindings : MultilinearPrefixBodies.Bindings :=
  ⟨"_finite_admission_3", "_mathematical_admission_2"⟩

end ZkcExamples.Structured.SumcheckMathBindings
