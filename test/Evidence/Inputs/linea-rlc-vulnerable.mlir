// Vulnerable ordering witness: u is sampled before the two complete equation
// materials whose random coefficients it determines.
pir.protocol "linea_rlc_vulnerable" kappa {codecs = {fr = "fr_be32", equation = "fr_be32"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %eq0 = pir.instantiate "equation0" anchors {material = "sha256:45a164347a1fdb1b2c0d42be4a93210f73b7c680a493b9cb27673515f6a1f50e"} : !pir.claim<"kzg_verification_equation">
  %eq1 = pir.instantiate "equation1" anchors {material = "sha256:319abfe29a80e14f52a92fcf12d02bc138667a9753c93e81d78daef009f45158"} : !pir.claim<"kzg_verification_equation">
  %t0 = pir.begin
  %t1, %u = pir.chal %t0 "u" : "fr" domain "linea.kzg-equation-rlc.u" space "21888242871839275222246405745257275088548364400416034343698204186575808495617"
  %t2, %m0 = pir.slot %t1 "equation0_material" : "equation" in "equation_rlc" as "equations"
  %t3, %m1 = pir.slot %t2 "equation1_material" : "equation" in "equation_rlc" as "equations" idx 1
  pir.end %t3
  %combined = pir.reduce "equation_rlc" contract "kzg_equation_rlc" (%eq0, %eq1 : !pir.claim<"kzg_verification_equation">, !pir.claim<"kzg_verification_equation">) deps(%u : !pir.val<"fr">) checks {} anchors [{coefficient = "sha256:a06ad058694b50c2db9aa05bd248fe73db07687040e1b383907d4d94625c5ba2", members = "sha256:5fdbc8f10d18e5944a92ca4588696bcfff08e75e0af64e28f6fe2d1b99cc5abf"}] -> !pir.claim<"kzg_equation_rlc">
  pir.material_bind %m0 to "sha256:45a164347a1fdb1b2c0d42be4a93210f73b7c680a493b9cb27673515f6a1f50e" : !pir.val<"equation">
  pir.material_bind %m1 to "sha256:319abfe29a80e14f52a92fcf12d02bc138667a9753c93e81d78daef009f45158" : !pir.val<"equation">
  pir.material_bind %u to "sha256:a06ad058694b50c2db9aa05bd248fe73db07687040e1b383907d4d94625c5ba2" : !pir.val<"fr">
  pir.residual %combined : !pir.claim<"kzg_equation_rlc"> route "kzg-equation-verification-not-evaluated"
}
