// Abstract SP1/Plonky3 opening-value RLC: every claimed value is observed
// before alpha.  This represents the repaired local schedule and ordered
// reduction only; FRI, PCS execution, and AIR correctness remain residual.
pir.protocol "sp1_rlc_patched" kappa {codecs = {ext_field = "plonky3_bb31_ext4_tuple", fr = "fr_be32"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %open0 = pir.instantiate "open0" anchors {commitment = "sha256:f1f26eb6b69f225749921b8d0aba4a1b2f1a7dcbeb5b094888a80fc8758f1449", point = "sha256:bb841dc4d43823795fe62eaa30c910cc3ea3c54b1afac2d91d7d7f44adb98bbf", value = "sha256:aeb2f59852dc774ec0bc96bbd26b2391759b9d3c59dbe350d283761513a8f53c"} : !pir.claim<"single_opening">
  %open1 = pir.instantiate "open1" anchors {commitment = "sha256:fa248e84204d634e1fcf3ba0bdb0abbf252cc19a4c30a5ecfa27a0042a655065", point = "sha256:7aefa2d4a3ee7e2d1696cddf7f2532e01a5cc973ec766128ef183fea9b5ee34b", value = "sha256:b68a862a777bf0eb557d81bfc632a0e8c0cd18e63fb11ea0ad2f267759295bf2"} : !pir.claim<"single_opening">
  %open2 = pir.instantiate "open2" anchors {commitment = "sha256:8f5a18a2fce3bf9b8773cfae20e4d437505b6763a0800b78ca272a0cafadeb9a", point = "sha256:2bd989aa5bbe41505c3df8448dd7304c17d33d9ec2873a308c40eafae232a73b", value = "sha256:4cc19f4e3fb1e65c57904336df94478cbc73d6972f35bca180f495cc2c9e9ba9"} : !pir.claim<"single_opening">
  %t0 = pir.begin
  %t1, %v0 = pir.slot %t0 "value0" : "ext_field" in "opening_rlc" as "values"
  %t2, %v1 = pir.slot %t1 "value1" : "ext_field" in "opening_rlc" as "values" idx 1
  %t3, %v2 = pir.slot %t2 "value2" : "ext_field" in "opening_rlc" as "values" idx 2
  %t4, %alpha = pir.chal %t3 deps(%v0, %v1, %v2 : !pir.val<"ext_field">, !pir.val<"ext_field">, !pir.val<"ext_field">) "alpha" : "ext_field" domain "sp1.opening-value-rlc.alpha" space "16428751811598850197311699254593454081"
  pir.end %t4
  %combined = pir.reduce "opening_rlc" contract "opening_value_rlc" (%open0, %open1, %open2 : !pir.claim<"single_opening">, !pir.claim<"single_opening">, !pir.claim<"single_opening">) deps(%alpha : !pir.val<"ext_field">) checks {} anchors [{coefficient = "sha256:4429298bf4f75eadcda459d9d83cb5ea1e18cfed4f244abb4238d2c1565edd2b", members = "sha256:b2e2a88c5b0544c5d433de525b4cf65da01c2fc0b41b1d27962bd65d2a21834f"}] -> !pir.claim<"opening_value_rlc">
  pir.material_bind %v0 to "sha256:aeb2f59852dc774ec0bc96bbd26b2391759b9d3c59dbe350d283761513a8f53c" : !pir.val<"ext_field">
  pir.material_bind %v1 to "sha256:b68a862a777bf0eb557d81bfc632a0e8c0cd18e63fb11ea0ad2f267759295bf2" : !pir.val<"ext_field">
  pir.material_bind %v2 to "sha256:4cc19f4e3fb1e65c57904336df94478cbc73d6972f35bca180f495cc2c9e9ba9" : !pir.val<"ext_field">
  pir.material_bind %alpha to "sha256:4429298bf4f75eadcda459d9d83cb5ea1e18cfed4f244abb4238d2c1565edd2b" : !pir.val<"ext_field">
  pir.residual %combined : !pir.claim<"opening_value_rlc"> route "plonky3-fri-pcs-not-evaluated"
}
