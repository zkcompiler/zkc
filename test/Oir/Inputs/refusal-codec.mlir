// A codec named by the artifact with no supplier in the executing profile.
oir.artifact "refusal-codec" id "0000000000000000000000000000000000000000000000000000000000000000" source "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" endpoint "verifier" {
  oir.program attributes {codecs = {rs = "plonky3_bb31_ext4_tuple"}, statement_labels = []} {
  ^bb0(%s: !oir.stream):
    %t = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    %t2, %v = oir.squeeze %t "fold" : "rs" count "1" domain "d" rule "uniform" space "16" src [0]
    oir.expect_end %s
    oir.decide %t2
  }
}
