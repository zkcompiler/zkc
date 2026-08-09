// A pinned construction digest the supplier does not implement: the
// artifact was sealed against different registry bytes, so this profile
// cannot judge it — a refusal, never a proof verdict.
oir.artifact "refusal-pin-mismatch" id "0000000000000000000000000000000000000000000000000000000000000000" source "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" endpoint "verifier" {
  oir.program attributes {codecs = {}, param_digests = ["sponge:toy_duplex=sha256:0000000000000000000000000000000000000000000000000000000000000000"], statement_labels = []} {
  ^bb0(%s: !oir.stream):
    %t = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.expect_end %s
    oir.decide %t
  }
}
