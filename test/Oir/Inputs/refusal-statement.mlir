// A statement label the run supplies no value for.
oir.artifact "refusal-statement" id "0000000000000000000000000000000000000000000000000000000000000000" source "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" endpoint "verifier" {
  oir.program attributes {codecs = {}, statement_labels = ["x"]} {
  ^bb0(%x: !oir.val<"scalar", "public">, %s: !oir.stream):
    %t = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.expect_end %s
    oir.decide %t
  }
}
