// A counted independent vector squeeze the profile's sampling does not supply.
oir.artifact "refusal-sampling" id "0000000000000000000000000000000000000000000000000000000000000000" source "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" endpoint "verifier" {
  oir.program attributes {codecs = {rs = "ts_be8"}, statement_labels = []} {
  ^bb0(%s: !oir.stream):
    %t = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    %t2, %v = oir.squeeze %t "query" : "rs" count "4" domain "d" rule "uniform_independent" space "16" src [0]
    oir.expect_end %s
    oir.decide %t2
  }
}
