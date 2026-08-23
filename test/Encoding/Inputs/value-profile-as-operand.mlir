// A commitment offered where a check declares one element of a class.
//
// Driven by value-profile-resolution.mlir. A commitment is not an element of
// the class its content is drawn from — it stands for a whole sequence of
// them — so it satisfies no operand slot, and a value profile spelled like a
// payload class must not slip through on the name.
pir.protocol "profile_as_operand" kappa {codecs = {scalar = "ts_be8"}, constants = {one = {class = "scalar", value = "1"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "air" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %column = pir.slot %t0 "column" : profile "logup_committed_column"
  %t2, %beta = pir.chal %t1 deps(%column : !pir.val<profile "logup_committed_column">) "beta" : "scalar" domain "operand.beta" space "2305843009213693951"
  %t3, %left = pir.slot %t2 "left" : "scalar"
  %t4, %right = pir.slot %t3 "right" : "scalar"
  // The fourth operand is the commitment, where the contract declares one
  // scalar. Every other operand is well typed, so the refusal below is about
  // the commitment alone.
  pir.check "fold" contract "zkc.check.affine-fold-scalars" (%left, %right, %beta, %column : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<profile "logup_committed_column">) expr ["eq", ["f_add", ["in", 0], ["f_mul", ["in", 2], ["in", 1]]], ["in", 3]]
  pir.end %t4
  pir.residual %relation : !pir.claim<"opaque_relation"> route "unmodeled"
}
