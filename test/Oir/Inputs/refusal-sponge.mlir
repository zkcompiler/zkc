// A real sponge construction with no supplier in the executing profile.
// The stored id is a placeholder; the driving test mints the real one.
oir.artifact "refusal-sponge" id "0000000000000000000000000000000000000000000000000000000000000000" source "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" endpoint "verifier" {
  oir.program attributes {codecs = {}, statement_labels = []} {
  ^bb0(%s: !oir.stream):
    %t = oir.transcript_init sponge "plonky3_bb31_poseidon2_w16_r8_lenpad" iv "artifact-id"
    oir.expect_end %s
    oir.decide %t
  }
}
