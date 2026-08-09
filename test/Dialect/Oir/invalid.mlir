// RUN: zkc-opt %s -split-input-file -verify-diagnostics

// The artifact id has one spelling (E141).
// expected-error @below {{[zkc-E141] id must be a 64-lowercase-hex SHA-256 digest}}
oir.artifact "a" id "nope"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  oir.program {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.expect_end %proof
    oir.decide %sp0
  }
}

// -----

// A source citation without its algorithm prefix (E141).
// expected-error @below {{[zkc-E141] source citation must be an algorithm-prefixed sealed artifact id}}
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  oir.program {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.expect_end %proof
    oir.decide %sp0
  }
}

// -----

// A program whose decision is not last (E142).
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  // expected-error @below {{[zkc-E142] the decision must be the final operation}}
  oir.program {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.decide %sp0
    oir.expect_end %proof
  }
}

// -----

// A doubly-absorbed sponge state is a transcript fork (E143).
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  oir.program attributes {statement_labels = ["x"]} {
  ^bb0(%x: !oir.val<"tg", "public">, %proof: !oir.stream):
    // expected-error @below {{[zkc-E143] sponge state must be consumed exactly once}}
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    %sp1 = oir.absorb %sp0, %x : !oir.val<"tg", "public">
    %sp2 = oir.absorb %sp0, %x : !oir.val<"tg", "public">
    oir.expect_end %proof
    oir.decide %sp1
  }
}

// -----

// The entry ABI is exact: labels, witness handles, and one stream (E144).
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  // expected-error @below {{[zkc-E144] the program's arguments are exactly the labeled statement values, the declared witness handles, and one final stream: expected 4, got 2}}
  oir.program attributes {statement_labels = ["x", "y", "z"]} {
  ^bb0(%x: !oir.val<"tg", "public">, %proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.expect_end %proof
    oir.decide %sp0
  }
}

// -----

oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  // expected-error @below {{[zkc-E144] statement label #1 does not name a value argument}}
  oir.program attributes {statement_labels = ["x", "y"]} {
  ^bb0(%x: !oir.val<"tg", "public">, %y: !oir.stream, %proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.expect_end %proof
    oir.decide %sp0
  }
}

// -----

// Count is identity-bearing endpoint semantics: it is always an explicit,
// canonical positive decimal string (E146).
oir.artifact "bad-count"
    id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  oir.program attributes {codecs = {scalar = "ts_be8"}} {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    // expected-error @below {{[zkc-E146] count must be a canonical decimal from 1 through 2^20 (1 for scalar, 2..2^20 for vector), got "01"}}
    %sp1, %c = oir.squeeze %sp0 "c" : "scalar" count "01" domain "test.c" rule "uniform" space "17"
    oir.expect_end %proof
    oir.decide %sp1
  }
}

// -----

oir.artifact "oversized-count"
    id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  oir.program attributes {codecs = {query_index = "ts_be8"}} {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    // expected-error @below {{[zkc-E146] count must be a canonical decimal from 1 through 2^20}}
    %sp1, %q = oir.squeeze %sp0 "q" : "query_index" count "1048577" domain "test.q" rule "uniform_independent" space "1024"
    oir.expect_end %proof
    oir.decide %sp1
  }
}

// -----

oir.artifact "empty-class"
    id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  oir.program {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    // expected-error @below {{[zkc-E146] payload class must be non-empty}}
    %sp1, %q = oir.squeeze %sp0 "q" : "" count "1" domain "test.q" rule "uniform" space "1024"
    oir.expect_end %proof
    oir.decide %sp1
  }
}

// -----

oir.artifact "empty-domain"
    id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  oir.program attributes {codecs = {scalar = "ts_be8"}} {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    // expected-error @below {{[zkc-E146] domain must be a non-empty printable-ASCII string}}
    %sp1, %c = oir.squeeze %sp0 "c" : "scalar" count "1" domain "" rule "uniform" space "17"
    oir.expect_end %proof
    oir.decide %sp1
  }
}

// -----

oir.artifact "empty-rule"
    id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  oir.program attributes {codecs = {scalar = "ts_be8"}} {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    // expected-error @below {{[zkc-E146] sampling rule must be a non-empty printable-ASCII string}}
    %sp1, %c = oir.squeeze %sp0 "c" : "scalar" count "1" domain "test.c" rule "" space "17"
    oir.expect_end %proof
    oir.decide %sp1
  }
}

// -----

oir.artifact "noncanonical-scalar-rule"
    id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  oir.program attributes {codecs = {scalar = "ts_be8"}} {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    // expected-error @below {{[zkc-E146] sampling rule must be 'uniform' for count 1 and 'uniform_independent' for count 2 through 2^20; got rule 'uniform_independent' with count 1}}
    %sp1, %c = oir.squeeze %sp0 "c" : "scalar" count "1" domain "test.c" rule "uniform_independent" space "17"
    oir.expect_end %proof
    oir.decide %sp1
  }
}

// -----

oir.artifact "noncanonical-vector-rule"
    id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  oir.program attributes {codecs = {query_index = "ts_be8"}} {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    // expected-error @below {{[zkc-E146] sampling rule must be 'uniform' for count 1 and 'uniform_independent' for count 2 through 2^20; got rule 'uniform' with count 4}}
    %sp1, %q = oir.squeeze %sp0 "q" : "query_index" count "4" domain "test.q" rule "uniform" space "1024"
    oir.expect_end %proof
    oir.decide %sp1
  }
}

// -----

oir.artifact "noncanonical-space"
    id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  oir.program attributes {codecs = {scalar = "ts_be8"}} {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    // expected-error @below {{[zkc-E146] space must be an exact positive cardinality in minimal decimal form, got "01"}}
    %sp1, %c = oir.squeeze %sp0 "c" : "scalar" count "1" domain "test.c" rule "uniform" space "01"
    oir.expect_end %proof
    oir.decide %sp1
  }
}

// -----

// Origin is represented by the sampled result and producing op, not by a
// payload pseudo-class (E146).
oir.artifact "retired-class"
    id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  oir.program attributes {codecs = {scalar = "ts_be8"}} {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    // expected-error @below {{[zkc-E146] payload class 'chal' is retired: a squeeze must name its semantic payload class}}
    %sp1, %c = oir.squeeze %sp0 "c" : "chal" count "1" domain "test.c" rule "uniform" space "17"
    oir.expect_end %proof
    oir.decide %sp1
  }
}

// -----

// Opaque endpoint dispatch is authorized by resolved content, not by a
// human-readable contract id alone (E147).
oir.artifact "bad-check-digest"
    id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  oir.program {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    // expected-error @below {{[zkc-E147] contract_digest must be a sha256:-prefixed 64-lowercase-hex CheckContract content digest}}
    oir.check_call "predicate" kind "zkc.check.relation-predicate" digest "not-a-digest"
    oir.expect_end %proof
    oir.decide %sp0
  }
}

// -----

// The endpoint-kind vocabulary is closed (E148).
// expected-error @below {{[zkc-E148] unknown endpoint kind 'prover'}}
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "prover" {
  oir.program {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.expect_end %proof
    oir.decide %sp0
  }
}

// -----

// The gadget kind is reserved without carrier semantics (E148).
// expected-error @below {{[zkc-E148] endpoint kind 'verifier_gadget' is reserved}}
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier_gadget" {
  oir.program {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.expect_end %proof
    oir.decide %sp0
  }
}

// -----

// A prover op inside a verifier program (E148).
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  oir.program {
  ^bb0(%x: !oir.val<"tg", "public">, %proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    // expected-error @below {{[zkc-E148] operation is outside the verifier endpoint's admitted operation set}}
    %st1 = oir.write %proof, %x : !oir.val<"tg", "public"> as "s" class "tg"
    oir.expect_end %st1
    oir.decide %sp0
  }
}

// -----

// A verifier decision sink inside a prover program (E148).
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "prover_skeleton" {
  oir.program attributes {counterparty = [], witness_labels = [["w", "wc"]]} {
  ^bb0(%w: !oir.handle<"wc">, %proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    %a = oir.hole_call "h" kind "commit" digest "sha256:1111111111111111111111111111111111111111111111111111111111111111" (%w : !oir.handle<"wc">) -> !oir.val<"tg", "hole">
    %st1 = oir.write %proof, %a : !oir.val<"tg", "hole"> as "s" class "tg"
    %sp1 = oir.absorb %sp0, %a : !oir.val<"tg", "hole">
    // expected-error @below {{[zkc-E148] operation is outside the prover_skeleton endpoint's admitted operation set}}
    oir.decide %sp1
    oir.end_stream %st1
  }
}

// -----

// witness_labels is prover-endpoint ABI and must be present there (E148).
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "prover_skeleton" {
  // expected-error @below {{[zkc-E148] witness_labels is present exactly when the endpoint kind is prover_skeleton}}
  oir.program {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.end_stream %proof
    oir.finish %sp0
  }
}

// -----

// ... and must be absent on a verifier program (E148).
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  // expected-error @below {{[zkc-E148] witness_labels is present exactly when the endpoint kind is prover_skeleton}}
  oir.program attributes {counterparty = [], witness_labels = [["w", "wc"]]} {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.expect_end %proof
    oir.decide %sp0
  }
}

// -----

// The witness argument's handle class matches its declaration (E148).
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "prover_skeleton" {
  // expected-error @below {{[zkc-E148] witness argument #0 must be !oir.handle<declared-class> per its witness_labels declaration}}
  oir.program attributes {counterparty = [], witness_labels = [["w", "declared-class"]]} {
  ^bb0(%w: !oir.handle<"other-class">, %proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    %a = oir.hole_call "h" kind "commit" digest "sha256:1111111111111111111111111111111111111111111111111111111111111111" (%w : !oir.handle<"other-class">) -> !oir.val<"tg", "hole">
    %st1 = oir.write %proof, %a : !oir.val<"tg", "hole"> as "s" class "tg"
    oir.end_stream %st1
    oir.finish %sp0
  }
}

// -----

// finish is the prover frame's terminal operation (E149).
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "prover_skeleton" {
  // expected-error @below {{[zkc-E149] finish must be the final operation of a prover program}}
  oir.program attributes {counterparty = [], witness_labels = [["w", "wc"]]} {
  ^bb0(%w: !oir.handle<"wc">, %proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    %a = oir.hole_call "h" kind "commit" digest "sha256:1111111111111111111111111111111111111111111111111111111111111111" (%w : !oir.handle<"wc">) -> !oir.val<"tg", "hole">
    %st1 = oir.write %proof, %a : !oir.val<"tg", "hole"> as "s" class "tg"
    oir.finish %sp0
    oir.end_stream %st1
  }
}

// -----

// An unconsumed handle is a committed tree nobody opened (E149).
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "prover_skeleton" {
  oir.program attributes {counterparty = [], witness_labels = [["w", "wc"]]} {
  ^bb0(%w: !oir.handle<"wc">, %proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    // expected-error @below {{[zkc-E149] handle state must be consumed exactly once}}
    %a, %w1 = oir.hole_call "h" kind "commit" digest "sha256:1111111111111111111111111111111111111111111111111111111111111111" (%w : !oir.handle<"wc">) -> !oir.val<"tg", "hole">, !oir.handle<"wc">
    %st1 = oir.write %proof, %a : !oir.val<"tg", "hole"> as "s" class "tg"
    oir.end_stream %st1
    oir.finish %sp0
  }
}

// -----

// Only a pow_search hole may see the transcript (E149).
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "prover_skeleton" {
  oir.program attributes {counterparty = [], witness_labels = [["w", "wc"]]} {
  ^bb0(%w: !oir.handle<"wc">, %proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    // expected-error @below {{[zkc-E149] only a pow_search hole may take the sponge}}
    %a, %sp1 = oir.hole_call "h" kind "commit" digest "sha256:1111111111111111111111111111111111111111111111111111111111111111" (%w, %sp0 : !oir.handle<"wc">, !oir.sponge) -> !oir.val<"tg", "hole">, !oir.sponge
    %st1 = oir.write %proof, %a : !oir.val<"tg", "hole"> as "s" class "tg"
    oir.end_stream %st1
    oir.finish %sp1
  }
}

// -----

// A challenge is never a write operand directly (E149).
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "prover_skeleton" {
  oir.program attributes {counterparty = [], witness_labels = []} {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    %sp1, %c = oir.squeeze %sp0 "c" : "scalar" count "1" domain "d" rule "uniform" space "7"
    // expected-error @below {{[zkc-E149] a write operand's origin must be hole, derived, public, or pinned; got 'sampled'}}
    %st1 = oir.write %proof, %c : !oir.val<"scalar", "sampled"> as "s" class "scalar"
    oir.end_stream %st1
    oir.finish %sp1
  }
}

// -----

// The hole-kind vocabulary is closed (E149).
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "prover_skeleton" {
  oir.program attributes {counterparty = [], witness_labels = [["w", "wc"]]} {
  ^bb0(%w: !oir.handle<"wc">, %proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    // expected-error @below {{[zkc-E149] hole kind must be one of commit | extend | evaluate | fold | open | pow_search}}
    %a = oir.hole_call "h" kind "merkleize" digest "sha256:1111111111111111111111111111111111111111111111111111111111111111" (%w : !oir.handle<"wc">) -> !oir.val<"tg", "hole">
    %st1 = oir.write %proof, %a : !oir.val<"tg", "hole"> as "s" class "tg"
    oir.end_stream %st1
    oir.finish %sp0
  }
}

// -----

oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "prover_skeleton" {
  // expected-error @below {{[zkc-E148] counterparty row #0 must be a [position, discharge] pair}}
  oir.program attributes {counterparty = [[0]], witness_labels = []} {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.end_stream %proof
    oir.finish %sp0
  }
}

// -----

oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "prover_skeleton" {
  // expected-error @below {{[zkc-E148] counterparty row #0 cites a negative event position}}
  oir.program attributes {counterparty = [[-1, "assert_eq"]], witness_labels = []} {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.end_stream %proof
    oir.finish %sp0
  }
}

// -----

oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "prover_skeleton" {
  // expected-error @below {{[zkc-E148] counterparty rows cite event position 0 more than once}}
  oir.program attributes {counterparty = [[0, "assert_eq"], [0, "check_call"]], witness_labels = []} {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.end_stream %proof
    oir.finish %sp0
  }
}

// -----

oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  // expected-error @below {{[zkc-E148] malformed pinned-parameter entry 'toy_duplex': rows are sponge:<name>=<digest> or codec:<name>=<digest>}}
  oir.program attributes {param_digests = ["toy_duplex"]} {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.expect_end %proof
    oir.decide %sp0
  }
}

// -----

// A hole with no result did nothing the program can use. The whole point of a
// hole is the value it produces, so an empty result list is not a degenerate
// hole — it is a row with no reason to exist.
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "prover_skeleton" {
  oir.program attributes {witness_labels = [], counterparty = []} {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    // expected-error @below {{[zkc-E149] a hole declares at least one result}}
    "oir.hole_call"() <{label = "h", kind = "commit", contract_digest = "sha256:0000000000000000000000000000000000000000000000000000000000000000"}> : () -> ()
    oir.end_stream %proof
    oir.finish %sp0
  }
}

// -----

// Only a pow_search hole may take the transcript. The converse — a
// non-pow_search hole holding the sponge — is tested above; this is a
// grinding hole with no transcript access at all, which is the same
// invariant read from its other side.
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "prover_skeleton" {
  oir.program attributes {witness_labels = [], counterparty = []} {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    // expected-error @below {{[zkc-E149] a pow_search hole peeks the transcript}}
    %v = "oir.hole_call"() <{label = "h", kind = "pow_search", contract_digest = "sha256:0000000000000000000000000000000000000000000000000000000000000000"}> : () -> !oir.val<"scalar", "hole">
    %sp1 = oir.absorb %sp0, %v : !oir.val<"scalar", "hole">
    oir.end_stream %proof
    oir.finish %sp1
  }
}

// -----

// A hole result nothing consumes is a hole that silently did nothing. The
// linearity discipline covers sponges, streams, and handles; this is the same
// rule for the values a hole produces.
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "prover_skeleton" {
  oir.program attributes {witness_labels = [], counterparty = []} {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    // expected-error @below {{[zkc-E149] every hole result has at least one use}}
    %v = "oir.hole_call"() <{label = "h", kind = "commit", contract_digest = "sha256:0000000000000000000000000000000000000000000000000000000000000000"}> : () -> !oir.val<"scalar", "hole">
    oir.end_stream %proof
    oir.finish %sp0
  }
}

// -----

// A hole's value results carry origin `hole`. Origin is how a consumer knows
// where a value came from without trusting a label, so a hole announcing its
// output as sampled would be claiming provenance it does not have.
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "prover_skeleton" {
  oir.program attributes {witness_labels = [], counterparty = []} {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    // expected-error @below {{[zkc-E149] a hole's value results carry origin 'hole'}}
    %v = "oir.hole_call"() <{label = "h", kind = "commit", contract_digest = "sha256:0000000000000000000000000000000000000000000000000000000000000000"}> : () -> !oir.val<"scalar", "sampled">
    %sp1 = oir.absorb %sp0, %v : !oir.val<"scalar", "sampled">
    oir.end_stream %proof
    oir.finish %sp1
  }
}

// -----

// Exactly one transcript_init. Two would be two transcripts, and the sponge
// each event threads would be a choice rather than a fact.
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  // expected-error @below {{[zkc-E142] exactly one transcript_init required, got 2}}
  oir.program {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    %sp1 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.expect_end %proof
    oir.decide %sp0
    oir.decide %sp1
  }
}

// -----

// The "exactly one expect_end" and "exactly one end_stream" counts are not
// reachable: a second one consumes the stream a second time, and linearity
// (zkc-E143) owns that first. They are a backstop behind a stronger rule
// rather than an independent boundary, which is why neither has a test.

// -----

// An artifact packages exactly one program. Identity is per-artifact, so two
// programs would be one id naming two endpoints.
// expected-error @below {{[zkc-E141] artifact packages exactly one oir.program}}
oir.artifact "a" id "0000000000000000000000000000000000000000000000000000000000000000"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  oir.program {
  ^bb0(%proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.expect_end %proof
    oir.decide %sp0
  }
  oir.program {
  ^bb0(%proof: !oir.stream):
    %sp1 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    oir.expect_end %proof
    oir.decide %sp1
  }
}
