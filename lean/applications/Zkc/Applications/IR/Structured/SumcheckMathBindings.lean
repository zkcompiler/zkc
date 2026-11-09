module

public import Zkc.Verification.Installations.Multilinear.Source.CollectBodies
public import Zkc.Verification.Installations.Multilinear.Source.PrefixBodies

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
  ⟨"_finite_admission_3", "_mathematical_admission_2", ⟨"zkl_c22ca043f56e31ae33fc04b669755c76f6f9db03b95b1cc7733fde9f3c08b402",
    "finite_zkl_c22ca043f56e31ae33fc04b669755c76f6f9db03b95b1cc7733fde9f3c08b402_s0_domain",
    "finite_zkl_c22ca043f56e31ae33fc04b669755c76f6f9db03b95b1cc7733fde9f3c08b402_s0_body"⟩⟩

end ZkcExamples.Structured.SumcheckMathBindings
