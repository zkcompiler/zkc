// A hand-crafted artifact that absorbs a pinned constant wider than the
// low-bits codec frames. The codec writes four bytes, so a value above
// 2^32 would absorb as its low half — two distinct constants entering
// the transcript identically, which is what the framing-width gate
// (zkc-E411) exists to prevent. Hand-authored because no family
// generator emits an out-of-range constant; the artifact is adversarial.
oir.artifact "lowbits" id "d6aef4784af6e70b6a8110d0d042056c0e18e5a10158034858c5df4969926571" source "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc" endpoint "verifier" {
  oir.program attributes {codecs = {pow_value = "plonky3_bb31_low_bits"}, statement_labels = []} {
  ^bb0(%arg0: !oir.stream):
    %0 = oir.transcript_init sponge "plonky3_bb31_poseidon2_w16_r8_lenpad" iv "zero"
    %1 = oir.constant "4294967296" : "pow_value" src []
    %2 = oir.absorb %0, %1 : <"pow_value", "pinned"> src []
    oir.expect_end %arg0
    oir.decide %2
  }
}
