// A hand-crafted artifact whose pinned constants exceed the field
// modulus: constants are decoded as decimal uint64 without a range
// gate (only wire reads are canonical-or-reject), so field addition
// must reduce each operand before summing — the reference oracle
// computes the sum with exact integers and the two must agree on
// every representable input, not only canonical ones.
oir.artifact "wide" id "9dc7be012046ca03849ec06aaa6c8bc6e106213ec8e314ce4784ab6aaa6c458b" source "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd" endpoint "verifier" {
  oir.program attributes {codecs = {}, statement_labels = []} {
  ^bb0(%arg0: !oir.stream):
    %0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    %1 = oir.constant "9223372036854775808" : "scalar" src [0]
    %2 = oir.constant "9223372036854775808" : "scalar" src [0]
    %3 = oir.f_add %1, %2 : <"scalar", "pinned">, <"scalar", "pinned"> src [0]
    %4 = oir.constant "2305843009213670873" : "scalar" src [0]
    oir.assert_eq %3, %4 : <"scalar", "derived">, <"scalar", "pinned"> as "sum" src [0]
    oir.expect_end %arg0
    oir.decide %0
  }
}
