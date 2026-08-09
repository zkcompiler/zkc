// An algebra op under a profile that declares no moduli: the pure ops
// precede the transcript init so the algebra refusal is what fires, and
// computing in another profile's field is exactly what must not happen.
oir.artifact "refusal-no-algebra" id "0000000000000000000000000000000000000000000000000000000000000000" source "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" endpoint "verifier" {
  oir.program attributes {codecs = {}, statement_labels = []} {
  ^bb0(%s: !oir.stream):
    %1 = oir.constant "1" : "scalar" src [0]
    %2 = oir.constant "2" : "scalar" src [0]
    %3 = oir.f_add %1, %2 : <"scalar", "pinned">, <"scalar", "pinned"> src [0]
    %t = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.expect_end %s
    oir.decide %t
  }
}
