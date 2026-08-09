// An opaque check contract with no executable implementation in the profile.
oir.artifact "refusal-check" id "0000000000000000000000000000000000000000000000000000000000000000" source "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" endpoint "verifier" {
  oir.program attributes {codecs = {}, statement_labels = []} {
  ^bb0(%s: !oir.stream):
    %t = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.check_call "m" kind "zkc.check.merkle-path" digest "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    oir.expect_end %s
    oir.decide %t
  }
}
