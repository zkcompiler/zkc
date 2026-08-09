// This is the largest exact, current-carrier slice of the original PLONK
// verifier schedule.  Challenges retain fresh origin while carrying the field
// payload class consumed by the eventual verifier.  The schedule stops before
// the final check because the live vocabulary does not yet content-pin an
// opaque predicate or admit the monolithic PLONK verifier contract.
pir.protocol "plonk_kzg_boundary" kappa {codecs = {fr = "fr_be32", g1 = "bls_g1_be48"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %at_zeta = pir.instantiate "opening_at_zeta" anchors {commitment = "sha256:1010101010101010101010101010101010101010101010101010101010101010", point = "sha256:2020202020202020202020202020202020202020202020202020202020202020", value = "sha256:3030303030303030303030303030303030303030303030303030303030303030"} : !pir.claim<"single_opening">
  %at_zeta_omega = pir.instantiate "opening_at_zeta_omega" anchors {commitment = "sha256:4040404040404040404040404040404040404040404040404040404040404040", point = "sha256:5050505050505050505050505050505050505050505050505050505050505050", value = "sha256:6060606060606060606060606060606060606060606060606060606060606060"} : !pir.claim<"single_opening">

  %t0 = pir.begin
  // A real preprocessing commitment is absorbed.  Today this is a generic
  // public bind: no ReductionContract can require that it came from a bind
  // rather than a prover slot, so this fixture makes no index-channel claim.
  %t1, %vk = pir.bind %t0 "vk" : "g1" stage instance
  %t2, %public_input = pir.bind %t1 "public_input" : "fr" stage instance

  %t3, %a = pir.slot %t2 "a_commitment" : "g1"
  %t4, %b = pir.slot %t3 "b_commitment" : "g1"
  %t5, %c = pir.slot %t4 "c_commitment" : "g1"
  %t6, %beta = pir.chal %t5 deps(%vk, %public_input, %a, %b, %c : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"g1">, !pir.val<"g1">, !pir.val<"g1">) "beta" : "fr" domain "plonk.permutation.beta" space "52435875175126190479447740508185965837690552500527637822603658699938581184513"
  %t7, %gamma = pir.chal %t6 deps(%vk, %public_input, %a, %b, %c, %beta : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"g1">, !pir.val<"g1">, !pir.val<"g1">, !pir.val<"fr">) "gamma" : "fr" domain "plonk.permutation.gamma" space "52435875175126190479447740508185965837690552500527637822603658699938581184513"
  %t8, %z = pir.slot %t7 "permutation_commitment" : "g1"
  %t9, %alpha = pir.chal %t8 deps(%vk, %public_input, %a, %b, %c, %beta, %gamma, %z : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"g1">, !pir.val<"g1">, !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"g1">) "alpha" : "fr" domain "plonk.quotient.alpha" space "52435875175126190479447740508185965837690552500527637822603658699938581184513"
  %t10, %t_lo = pir.slot %t9 "quotient_commitment_0" : "g1"
  %t11, %t_mid = pir.slot %t10 "quotient_commitment_1" : "g1"
  %t12, %t_hi = pir.slot %t11 "quotient_commitment_2" : "g1"
  %t13, %zeta = pir.chal %t12 deps(%vk, %public_input, %a, %b, %c, %beta, %gamma, %z, %alpha, %t_lo, %t_mid, %t_hi : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"g1">, !pir.val<"g1">, !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"g1">, !pir.val<"fr">, !pir.val<"g1">, !pir.val<"g1">, !pir.val<"g1">) "zeta" : "fr" domain "plonk.evaluation.zeta" space "52435875175126190479447740508185965837690552500527637822603658699938581184513"

  %t14, %a_zeta = pir.slot %t13 "a_at_zeta" : "fr"
  %t15, %b_zeta = pir.slot %t14 "b_at_zeta" : "fr"
  %t16, %c_zeta = pir.slot %t15 "c_at_zeta" : "fr"
  %t17, %sigma1_zeta = pir.slot %t16 "sigma1_at_zeta" : "fr"
  %t18, %sigma2_zeta = pir.slot %t17 "sigma2_at_zeta" : "fr"
  %t19, %z_shifted_eval = pir.slot %t18 "z_at_zeta_omega" : "fr"
  %t20, %v = pir.chal %t19 deps(%vk, %public_input, %a, %b, %c, %beta, %gamma, %z, %alpha, %t_lo, %t_mid, %t_hi, %zeta, %a_zeta, %b_zeta, %c_zeta, %sigma1_zeta, %sigma2_zeta, %z_shifted_eval : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"g1">, !pir.val<"g1">, !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"g1">, !pir.val<"fr">, !pir.val<"g1">, !pir.val<"g1">, !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"fr">) "v" : "fr" domain "plonk.opening.aggregate" space "52435875175126190479447740508185965837690552500527637822603658699938581184513"
  %t21, %w_zeta = pir.slot %t20 "opening_proof_at_zeta" : "g1"
  %t22, %w_zeta_omega = pir.slot %t21 "opening_proof_at_zeta_omega" : "g1"
  %t23, %u = pir.chal %t22 deps(%vk, %public_input, %a, %b, %c, %beta, %gamma, %z, %alpha, %t_lo, %t_mid, %t_hi, %zeta, %a_zeta, %b_zeta, %c_zeta, %sigma1_zeta, %sigma2_zeta, %z_shifted_eval, %v, %w_zeta, %w_zeta_omega : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"g1">, !pir.val<"g1">, !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"g1">, !pir.val<"fr">, !pir.val<"g1">, !pir.val<"g1">, !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"g1">, !pir.val<"g1">) "u" : "fr" domain "plonk.opening.batch" space "52435875175126190479447740508185965837690552500527637822603658699938581184513"
  pir.end %t23

  // These are obligations, not false discharges.  The future exact predicate
  // receives fresh `%zeta : fr` and computes zeta * omega internally.
  pir.residual %at_zeta : !pir.claim<"single_opening"> route "unsupported.digest-covered-check-predicate"
  pir.residual %at_zeta_omega : !pir.claim<"single_opening"> route "unsupported.closed-plonk-verifier-contract"
}
