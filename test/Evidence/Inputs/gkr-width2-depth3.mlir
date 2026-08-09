// A fixed width-two, depth-three GKR semantic stress witness.  Each layer
// proves the exact add/multiply wiring endpoint, then folds its two child-MLE
// evaluations to one claim.  The final claim is checked against the public
// two-element input MLE.  The next-point/value slots are redundant proof
// fields constrained to the verifier-derived affine folds; this is an exact
// acceptance-relation projection, not byte-level implementation conformance.
pir.protocol "gkr_width2_depth3" kappa {codecs = {scalar = "ts_be8"}, constants = {one = {class = "scalar", value = "1"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %root = pir.instantiate "root_evaluation" anchors {oracle = "sha256:51629dcbf4528ccf05cb3d5e3cfb1026f89b1898ab16af9c11412f0d9b72da8e", point = "sha256:42b2b9246fd828c1512fe789ea645fb0ed2af780117574cf3bd3685633f509e7", value = "sha256:b803d6105862f82ba72107d14aea25fb684db905080323c09ab3019f255c1a24"} : !pir.claim<"mle_evaluation">

  %t0 = pir.begin
  %t1, %root_point = pir.bind %t0 "root_point" : "scalar" stage instance
  %t2, %root_value = pir.bind %t1 "root_value" : "scalar" stage instance
  %t3, %input0 = pir.bind %t2 "input0" : "scalar" stage instance
  %t4, %input1 = pir.bind %t3 "input1" : "scalar" stage instance

  // Layer 0: W_0(root_point) -> W_1(layer1_point).
  %t5, %l0_a0 = pir.slot %t4 "l0_a0" : "scalar" in "layer0" as "first_poly"
  %t6, %l0_a1 = pir.slot %t5 "l0_a1" : "scalar" in "layer0" as "first_poly" idx 1
  %t7, %l0_a2 = pir.slot %t6 "l0_a2" : "scalar" in "layer0" as "first_poly" idx 2
  %t8, %l0_rho = pir.chal %t7 "l0_rho" : "scalar" domain "gkr.layer0.rho" space "2305843009213693951"
  %t9, %l0_b0 = pir.slot %t8 "l0_b0" : "scalar" in "layer0" as "second_poly"
  %t10, %l0_b1 = pir.slot %t9 "l0_b1" : "scalar" in "layer0" as "second_poly" idx 1
  %t11, %l0_b2 = pir.slot %t10 "l0_b2" : "scalar" in "layer0" as "second_poly" idx 2
  %t12, %l0_sigma = pir.chal %t11 "l0_sigma" : "scalar" domain "gkr.layer0.sigma" space "2305843009213693951"
  %t13, %l0_left = pir.slot %t12 "l0_left" : "scalar" in "layer0" as "child_values"
  %t14, %l0_right = pir.slot %t13 "l0_right" : "scalar" in "layer0" as "child_values" idx 1
  %t15, %l0_tau = pir.chal %t14 "l0_tau" : "scalar" domain "gkr.layer0.tau" space "2305843009213693951"
  %t16, %l1_point = pir.slot %t15 "l1_point" : "scalar"
  %t17, %l1_value = pir.slot %t16 "l1_value" : "scalar"
  pir.check "l0_round1" contract "zkc.check.sumcheck-round1" (%root_value, %l0_a0, %l0_a1, %l0_a2 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["f_add", ["f_add", ["f_add", ["in", 1], ["in", 1]], ["in", 2]], ["in", 3]], ["in", 0]]
  pir.check "l0_round2" contract "zkc.check.sumcheck-round2" (%l0_a0, %l0_a1, %l0_a2, %l0_rho, %l0_b0, %l0_b1, %l0_b2 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["f_add", ["f_add", ["f_add", ["in", 4], ["in", 4]], ["in", 5]], ["in", 6]], ["f_add", ["in", 0], ["f_add", ["f_mul", ["in", 1], ["in", 3]], ["f_mul", ["in", 2], ["f_mul", ["in", 3], ["in", 3]]]]]]
  pir.check "l0_endpoint" contract "zkc.check.gkr-width2-addmul-endpoint" (%l0_b0, %l0_b1, %l0_b2, %l0_rho, %l0_sigma, %root_point, %l0_left, %l0_right : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["f_add", ["in", 0], ["f_add", ["f_mul", ["in", 1], ["in", 4]], ["f_mul", ["in", 2], ["f_mul", ["in", 4], ["in", 4]]]]], ["f_mul", ["f_mul", ["f_add", ["const", "one"], ["f_neg", ["in", 3]]], ["in", 4]], ["f_add", ["f_mul", ["f_add", ["const", "one"], ["f_neg", ["in", 5]]], ["f_add", ["in", 6], ["in", 7]]], ["f_mul", ["in", 5], ["f_mul", ["in", 6], ["in", 7]]]]]]
  pir.check "l0_point_fold" contract "zkc.check.affine-fold-challenge-points" (%l0_rho, %l0_sigma, %l0_tau, %l1_point : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["in", 3], ["f_add", ["in", 0], ["f_mul", ["in", 2], ["f_add", ["in", 1], ["f_neg", ["in", 0]]]]]]
  pir.check "l0_value_fold" contract "zkc.check.affine-fold-scalars" (%l0_left, %l0_right, %l0_tau, %l1_value : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["in", 3], ["f_add", ["in", 0], ["f_mul", ["in", 2], ["f_add", ["in", 1], ["f_neg", ["in", 0]]]]]]

  // Layer 1: the output descriptor above is the exact input descriptor here.
  %t18, %l1_a0 = pir.slot %t17 "l1_a0" : "scalar" in "layer1" as "first_poly"
  %t19, %l1_a1 = pir.slot %t18 "l1_a1" : "scalar" in "layer1" as "first_poly" idx 1
  %t20, %l1_a2 = pir.slot %t19 "l1_a2" : "scalar" in "layer1" as "first_poly" idx 2
  %t21, %l1_rho = pir.chal %t20 "l1_rho" : "scalar" domain "gkr.layer1.rho" space "2305843009213693951"
  %t22, %l1_b0 = pir.slot %t21 "l1_b0" : "scalar" in "layer1" as "second_poly"
  %t23, %l1_b1 = pir.slot %t22 "l1_b1" : "scalar" in "layer1" as "second_poly" idx 1
  %t24, %l1_b2 = pir.slot %t23 "l1_b2" : "scalar" in "layer1" as "second_poly" idx 2
  %t25, %l1_sigma = pir.chal %t24 "l1_sigma" : "scalar" domain "gkr.layer1.sigma" space "2305843009213693951"
  %t26, %l1_left = pir.slot %t25 "l1_left" : "scalar" in "layer1" as "child_values"
  %t27, %l1_right = pir.slot %t26 "l1_right" : "scalar" in "layer1" as "child_values" idx 1
  %t28, %l1_tau = pir.chal %t27 "l1_tau" : "scalar" domain "gkr.layer1.tau" space "2305843009213693951"
  %t29, %l2_point = pir.slot %t28 "l2_point" : "scalar"
  %t30, %l2_value = pir.slot %t29 "l2_value" : "scalar"
  pir.check "l1_round1" contract "zkc.check.sumcheck-round1" (%l1_value, %l1_a0, %l1_a1, %l1_a2 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["f_add", ["f_add", ["f_add", ["in", 1], ["in", 1]], ["in", 2]], ["in", 3]], ["in", 0]]
  pir.check "l1_round2" contract "zkc.check.sumcheck-round2" (%l1_a0, %l1_a1, %l1_a2, %l1_rho, %l1_b0, %l1_b1, %l1_b2 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["f_add", ["f_add", ["f_add", ["in", 4], ["in", 4]], ["in", 5]], ["in", 6]], ["f_add", ["in", 0], ["f_add", ["f_mul", ["in", 1], ["in", 3]], ["f_mul", ["in", 2], ["f_mul", ["in", 3], ["in", 3]]]]]]
  pir.check "l1_endpoint" contract "zkc.check.gkr-width2-addmul-endpoint" (%l1_b0, %l1_b1, %l1_b2, %l1_rho, %l1_sigma, %l1_point, %l1_left, %l1_right : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["f_add", ["in", 0], ["f_add", ["f_mul", ["in", 1], ["in", 4]], ["f_mul", ["in", 2], ["f_mul", ["in", 4], ["in", 4]]]]], ["f_mul", ["f_mul", ["f_add", ["const", "one"], ["f_neg", ["in", 3]]], ["in", 4]], ["f_add", ["f_mul", ["f_add", ["const", "one"], ["f_neg", ["in", 5]]], ["f_add", ["in", 6], ["in", 7]]], ["f_mul", ["in", 5], ["f_mul", ["in", 6], ["in", 7]]]]]]
  pir.check "l1_point_fold" contract "zkc.check.affine-fold-challenge-points" (%l1_rho, %l1_sigma, %l1_tau, %l2_point : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["in", 3], ["f_add", ["in", 0], ["f_mul", ["in", 2], ["f_add", ["in", 1], ["f_neg", ["in", 0]]]]]]
  pir.check "l1_value_fold" contract "zkc.check.affine-fold-scalars" (%l1_left, %l1_right, %l1_tau, %l2_value : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["in", 3], ["f_add", ["in", 0], ["f_mul", ["in", 2], ["f_add", ["in", 1], ["f_neg", ["in", 0]]]]]]

  // Layer 2 and the deterministic public-input terminal equality.
  %t31, %l2_a0 = pir.slot %t30 "l2_a0" : "scalar" in "layer2" as "first_poly"
  %t32, %l2_a1 = pir.slot %t31 "l2_a1" : "scalar" in "layer2" as "first_poly" idx 1
  %t33, %l2_a2 = pir.slot %t32 "l2_a2" : "scalar" in "layer2" as "first_poly" idx 2
  %t34, %l2_rho = pir.chal %t33 "l2_rho" : "scalar" domain "gkr.layer2.rho" space "2305843009213693951"
  %t35, %l2_b0 = pir.slot %t34 "l2_b0" : "scalar" in "layer2" as "second_poly"
  %t36, %l2_b1 = pir.slot %t35 "l2_b1" : "scalar" in "layer2" as "second_poly" idx 1
  %t37, %l2_b2 = pir.slot %t36 "l2_b2" : "scalar" in "layer2" as "second_poly" idx 2
  %t38, %l2_sigma = pir.chal %t37 "l2_sigma" : "scalar" domain "gkr.layer2.sigma" space "2305843009213693951"
  %t39, %l2_left = pir.slot %t38 "l2_left" : "scalar" in "layer2" as "child_values"
  %t40, %l2_right = pir.slot %t39 "l2_right" : "scalar" in "layer2" as "child_values" idx 1
  %t41, %l2_tau = pir.chal %t40 "l2_tau" : "scalar" domain "gkr.layer2.tau" space "2305843009213693951"
  %t42, %input_point = pir.slot %t41 "input_point" : "scalar"
  %t43, %input_value = pir.slot %t42 "input_value" : "scalar"
  pir.check "l2_round1" contract "zkc.check.sumcheck-round1" (%l2_value, %l2_a0, %l2_a1, %l2_a2 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["f_add", ["f_add", ["f_add", ["in", 1], ["in", 1]], ["in", 2]], ["in", 3]], ["in", 0]]
  pir.check "l2_round2" contract "zkc.check.sumcheck-round2" (%l2_a0, %l2_a1, %l2_a2, %l2_rho, %l2_b0, %l2_b1, %l2_b2 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["f_add", ["f_add", ["f_add", ["in", 4], ["in", 4]], ["in", 5]], ["in", 6]], ["f_add", ["in", 0], ["f_add", ["f_mul", ["in", 1], ["in", 3]], ["f_mul", ["in", 2], ["f_mul", ["in", 3], ["in", 3]]]]]]
  pir.check "l2_endpoint" contract "zkc.check.gkr-width2-addmul-endpoint" (%l2_b0, %l2_b1, %l2_b2, %l2_rho, %l2_sigma, %l2_point, %l2_left, %l2_right : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["f_add", ["in", 0], ["f_add", ["f_mul", ["in", 1], ["in", 4]], ["f_mul", ["in", 2], ["f_mul", ["in", 4], ["in", 4]]]]], ["f_mul", ["f_mul", ["f_add", ["const", "one"], ["f_neg", ["in", 3]]], ["in", 4]], ["f_add", ["f_mul", ["f_add", ["const", "one"], ["f_neg", ["in", 5]]], ["f_add", ["in", 6], ["in", 7]]], ["f_mul", ["in", 5], ["f_mul", ["in", 6], ["in", 7]]]]]]
  pir.check "l2_point_fold" contract "zkc.check.affine-fold-challenge-points" (%l2_rho, %l2_sigma, %l2_tau, %input_point : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["in", 3], ["f_add", ["in", 0], ["f_mul", ["in", 2], ["f_add", ["in", 1], ["f_neg", ["in", 0]]]]]]
  pir.check "l2_value_fold" contract "zkc.check.affine-fold-scalars" (%l2_left, %l2_right, %l2_tau, %input_value : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["in", 3], ["f_add", ["in", 0], ["f_mul", ["in", 2], ["f_add", ["in", 1], ["f_neg", ["in", 0]]]]]]
  pir.check "public_input_evaluation" contract "zkc.check.mle-width2-public-input" semantic_args {oracle = "sha256:1fe543b3845ed3f7f475b6bf6cba1140d4444a5ab38d26d721889ab58fb41810"} (%input_point, %input_value, %input0, %input1 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["in", 1], ["f_add", ["in", 2], ["f_mul", ["in", 0], ["f_add", ["in", 3], ["f_neg", ["in", 2]]]]]]
  pir.end %t43

  %layer1 = pir.reduce "layer0" contract "gkr_width2_addmul_layer" (%root : !pir.claim<"mle_evaluation">) deps(%l0_rho, %l0_sigma, %l0_tau, %l1_point, %l1_value : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) checks {endpoint = "l0_endpoint", point_fold = "l0_point_fold", round1 = "l0_round1", round2 = "l0_round2", value_fold = "l0_value_fold"} params {child_oracle = "sha256:aa7bf38396fa39250375fe66f4fe426c4238845d624fe91895ffacb3dcedb658"} anchors [{oracle = "sha256:aa7bf38396fa39250375fe66f4fe426c4238845d624fe91895ffacb3dcedb658", point = "sha256:a06b870b513764aa38f7c299ab407a16b9cb25de3d077746b52b2178c7235a06", value = "sha256:251db8954e587580b1d1db7da3108ad477bfdeef3ced5b2c1156ffef51604dee"}] -> !pir.claim<"mle_evaluation">
  %layer2 = pir.reduce "layer1" contract "gkr_width2_addmul_layer" (%layer1 : !pir.claim<"mle_evaluation">) deps(%l1_rho, %l1_sigma, %l1_tau, %l2_point, %l2_value : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) checks {endpoint = "l1_endpoint", point_fold = "l1_point_fold", round1 = "l1_round1", round2 = "l1_round2", value_fold = "l1_value_fold"} params {child_oracle = "sha256:165eb76118dfea981815a48cdb6bce3d673b3600305d0afa6fc01e8f308db079"} anchors [{oracle = "sha256:165eb76118dfea981815a48cdb6bce3d673b3600305d0afa6fc01e8f308db079", point = "sha256:f36af60d2c804b93542d4b3a965e7431c31b27bc09474a17d2016916d009549c", value = "sha256:4b6937cbec332fd94b6a58484db86620aafc5332c11b0d92d1ceda91f579cc2f"}] -> !pir.claim<"mle_evaluation">
  %input_eval = pir.reduce "layer2" contract "gkr_width2_addmul_layer" (%layer2 : !pir.claim<"mle_evaluation">) deps(%l2_rho, %l2_sigma, %l2_tau, %input_point, %input_value : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) checks {endpoint = "l2_endpoint", point_fold = "l2_point_fold", round1 = "l2_round1", round2 = "l2_round2", value_fold = "l2_value_fold"} params {child_oracle = "sha256:1fe543b3845ed3f7f475b6bf6cba1140d4444a5ab38d26d721889ab58fb41810"} anchors [{oracle = "sha256:1fe543b3845ed3f7f475b6bf6cba1140d4444a5ab38d26d721889ab58fb41810", point = "sha256:3718687b5a6e049be4d07858abbca68ad5ab5487adc6b36c0806c9bede4c9ce9", value = "sha256:164eaba18d8aef08003e37b422f37150c80d1b587013d90a8f2dda112d4d0380"}] -> !pir.claim<"mle_evaluation">

  pir.material_bind %root_point to "sha256:42b2b9246fd828c1512fe789ea645fb0ed2af780117574cf3bd3685633f509e7" : !pir.val<"scalar">
  pir.material_bind %root_value to "sha256:b803d6105862f82ba72107d14aea25fb684db905080323c09ab3019f255c1a24" : !pir.val<"scalar">
  pir.material_bind %l1_point to "sha256:a06b870b513764aa38f7c299ab407a16b9cb25de3d077746b52b2178c7235a06" : !pir.val<"scalar">
  pir.material_bind %l1_value to "sha256:251db8954e587580b1d1db7da3108ad477bfdeef3ced5b2c1156ffef51604dee" : !pir.val<"scalar">
  pir.material_bind %l2_point to "sha256:f36af60d2c804b93542d4b3a965e7431c31b27bc09474a17d2016916d009549c" : !pir.val<"scalar">
  pir.material_bind %l2_value to "sha256:4b6937cbec332fd94b6a58484db86620aafc5332c11b0d92d1ceda91f579cc2f" : !pir.val<"scalar">
  pir.material_bind %input_point to "sha256:3718687b5a6e049be4d07858abbca68ad5ab5487adc6b36c0806c9bede4c9ce9" : !pir.val<"scalar">
  pir.material_bind %input_value to "sha256:164eaba18d8aef08003e37b422f37150c80d1b587013d90a8f2dda112d4d0380" : !pir.val<"scalar">
  pir.discharge %input_eval : !pir.claim<"mle_evaluation"> rule "zkc.terminal.mle-width2-public-input" checks {evaluation = "public_input_evaluation"}
}
