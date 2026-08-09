// RUN: zkc-opt %pir-recheck-full %s -split-input-file -verify-diagnostics
//
// Recheck is the consumer-side seal battery, not a trust in the `sealed`
// spelling.  It re-derives BIND and requires one exact six-section citation
// stamp; empty input and invented citations fail closed.

pir.sealed "late-binding" id "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"}
    vocab {check_contracts = {}, claim_profiles = {}, construction_profiles = {"codec:tg_be8" = "sha256:3350aaa6e9a9a99ed351e5da7429dc552e32597eef3990c26e7d414b8683c8aa", "codec:ts_be8" = "sha256:3350aaa6e9a9a99ed351e5da7429dc552e32597eef3990c26e7d414b8683c8aa", "sponge:toy_duplex" = "sha256:35aefee5b893ded95c3a1397e67477204f5f53711c9e7dc60d17efb6b2e26407"}, reduction_contracts = {}, terminal_rules = {}} {
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "x" : "tg" stage instance
  %t2, %challenge = pir.chal %t1 deps(%x : !pir.val<"tg">) "challenge" : "scalar" domain "late.challenge" space "2305843009213693952"
  // expected-error @below {{[zkc-E214] statement binding 'y' follows challenge 'challenge': every public binding precedes its segment's first challenge}}
  %t3, %y = pir.bind %t2 "y" : "tg" stage instance
  pir.end %t3
}

// -----

// expected-error @below {{pir-recheck found no sealed artifact to re-judge}}
module {
}

// -----

// expected-error @below {{[zkc-E248] carries no resolved-vocabulary table: the seal stamps cited content digests}}
pir.sealed "missing-stamp" id "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" {
  %t0 = pir.begin
  pir.end %t0
}

// -----

// The stamp is the exact cited subset, not a registry environment snapshot.
// expected-error @below {{[zkc-E248] vocabulary section 'check_contracts' stamps a digest for 'zkc.check.relation-predicate', which this body never cites}}
pir.sealed "extra-citation" id "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    vocab {check_contracts = {"zkc.check.relation-predicate" = "sha256:ed29670b8353a955e1b8432dc6cec85b515fead053e14e3ecf586919c41b2c7a"}, claim_profiles = {}, construction_profiles = {}, reduction_contracts = {}, terminal_rules = {}} {
  %t0 = pir.begin
  pir.end %t0
}

// -----

// An empty optional section is still an extra authority claim.
// expected-error @below {{[zkc-E248] resolved-vocabulary table carries hole_contracts exactly when routes cite hole contracts}}
pir.sealed "empty-hole-citation" id "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    vocab {check_contracts = {}, claim_profiles = {}, construction_profiles = {}, hole_contracts = {}, reduction_contracts = {}, terminal_rules = {}} {
  %t0 = pir.begin
  pir.end %t0
}
