// The link boundary rejects unresolved operands, colliding face namespaces,
// and construction-profile conflicts before it creates a composite.

// RUN: not zkc-opt '-pir-link=producer=nope consumer=cons' %s 2>&1 | FileCheck --check-prefix=RESOLVE %s
// RESOLVE: [zkc-E701] pir-link resolves exactly one distinct open protocol for each name

// RUN: not zkc-opt '-pir-link=producer=prod consumer=cons producer-prefix=left consumer-prefix=left %pir-link-authorities' %s 2>&1 | FileCheck --check-prefix=PREFIX %s
// PREFIX: [zkc-E703] face prefixes namespace labels and challenge domains

// RUN: not zkc-opt '-pir-link=producer=prod consumer=cons producer-prefix=p consumer-prefix=p.x %pir-link-authorities' %s 2>&1 | FileCheck --check-prefix=DOTTED %s
// DOTTED: [zkc-E703] {{.*}}neither equal nor a dotted prefix of the other, got 'p' and 'p.x'

// RUN: not zkc-opt '-pir-link=producer=prod consumer=cons_iv %pir-link-authorities' %s 2>&1 | FileCheck --check-prefix=KAPPA %s
// KAPPA: [zkc-E702] kappa axis 'iv' conflicts

// RUN: not zkc-opt '-pir-link=producer=prod consumer=cons_codec %pir-link-authorities' %s 2>&1 | FileCheck --check-prefix=CODEC %s
// CODEC: [zkc-E702] kappa axis 'codecs' conflicts at key 'tg'

// Stable semantic references are single-valued across the linked composite.
// RUN: not zkc-opt '-pir-link=producer=prod_bind consumer=cons_bind %pir-link-authorities' %s 2>&1 | FileCheck --check-prefix=MATERIAL %s
// MATERIAL: [zkc-E704] semantic reference 'sha256:1111111111111111111111111111111111111111111111111111111111111111' reaches two distinct value endpoints after link

// Protocol names are selectors, so ambiguous selectors refuse rather than
// choosing one body by iteration order.
// RUN: not zkc-opt '-pir-link=producer=dup consumer=cons %pir-link-authorities' %s 2>&1 | FileCheck --check-prefix=AMBIGUOUS %s
// AMBIGUOUS: [zkc-E701] {{.*}}producer 'dup' (2 matches)

// The current carrier has no sound composition algebra for global theorem-hop
// citations; link never drops or guesses them.

pir.protocol "prod" kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "X" : "tg" stage instance
  pir.end %t1
}

pir.protocol "cons" kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "Y" : "tg" stage instance
  pir.end %t1
}

pir.protocol "cons_iv" kappa {codecs = {tg = "tg_be8"}, iv = "other-iv", sponge = "toy_duplex"} {
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "Y" : "tg" stage instance
  pir.end %t1
}

pir.protocol "cons_codec" kappa {codecs = {tg = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "Y" : "tg" stage instance
  pir.end %t1
}

pir.protocol "prod_bind" kappa {codecs = {fr = "fr_be32", g1 = "bls_g1_be48"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %opening = pir.instantiate "opening" anchors {commitment = "sha256:1111111111111111111111111111111111111111111111111111111111111111", point = "sha256:2222222222222222222222222222222222222222222222222222222222222222", value = "sha256:3333333333333333333333333333333333333333333333333333333333333333"} : !pir.claim<"single_opening">
  %t0 = pir.begin
  %t1, %commitment = pir.bind %t0 "commitment" : "g1" stage instance
  %t2, %point = pir.bind %t1 "point" : "fr" stage instance
  %t3, %value = pir.bind %t2 "value" : "fr" stage instance
  %t4, %challenge = pir.chal %t3 deps(%commitment, %point, %value : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">) "challenge" : "fr" domain "prod.material.challenge" space "52435875175126190479447740508185965837690552500527637822603658699938581184513"
  %t5, %proof = pir.slot %t4 "proof" : "g1"
  pir.check "opening_check" contract "zkc.check.kzg-opening" params {suite = "kzg-bls12-381"} (%commitment, %point, %value, %proof : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"g1">)
  pir.end %t5
  pir.material_bind %commitment to "sha256:1111111111111111111111111111111111111111111111111111111111111111" : !pir.val<"g1">
  pir.material_bind %point to "sha256:2222222222222222222222222222222222222222222222222222222222222222" : !pir.val<"fr">
  pir.material_bind %value to "sha256:3333333333333333333333333333333333333333333333333333333333333333" : !pir.val<"fr">
  pir.discharge %opening : !pir.claim<"single_opening"> rule "zkc.terminal.kzg-opening" checks {opening = "opening_check"}
}

pir.protocol "cons_bind" kappa {codecs = {fr = "fr_be32", g1 = "bls_g1_be48"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %opening = pir.instantiate "opening" anchors {commitment = "sha256:1111111111111111111111111111111111111111111111111111111111111111", point = "sha256:4444444444444444444444444444444444444444444444444444444444444444", value = "sha256:5555555555555555555555555555555555555555555555555555555555555555"} : !pir.claim<"single_opening">
  %t0 = pir.begin
  %t1, %commitment = pir.bind %t0 "commitment" : "g1" stage instance
  %t2, %point = pir.bind %t1 "point" : "fr" stage instance
  %t3, %value = pir.bind %t2 "value" : "fr" stage instance
  %t4, %challenge = pir.chal %t3 deps(%commitment, %point, %value : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">) "challenge" : "fr" domain "cons.material.challenge" space "52435875175126190479447740508185965837690552500527637822603658699938581184513"
  %t5, %proof = pir.slot %t4 "proof" : "g1"
  pir.check "opening_check" contract "zkc.check.kzg-opening" params {suite = "kzg-bls12-381"} (%commitment, %point, %value, %proof : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"g1">)
  pir.end %t5
  pir.material_bind %commitment to "sha256:1111111111111111111111111111111111111111111111111111111111111111" : !pir.val<"g1">
  pir.material_bind %point to "sha256:4444444444444444444444444444444444444444444444444444444444444444" : !pir.val<"fr">
  pir.material_bind %value to "sha256:5555555555555555555555555555555555555555555555555555555555555555" : !pir.val<"fr">
  pir.discharge %opening : !pir.claim<"single_opening"> rule "zkc.terminal.kzg-opening" checks {opening = "opening_check"}
}

pir.protocol "dup" {
  %t0 = pir.begin
  pir.end %t0
}

pir.protocol "dup" {
  %t0 = pir.begin
  pir.end %t0
}

pir.protocol "prod_hops" {
  %t0 = pir.begin
  pir.end %t0
}

// The consumer's declared producer face is checked, not inferred: an export
// whose exact descriptor no consumer source declares refuses rather than
// re-cloning as an assumed statement of the composite.  This is the mis-link
// reproduction: a discrete-log conclusion offered to a protocol that authored
// its source for a sumcheck endpoint, refused for the descriptor reason now
// that evaluation profiles are split per family.
// RUN: not zkc-opt '-pir-link=producer=misprod consumer=miscons %pir-link-authorities' %s 2>&1 | FileCheck --check-prefix=MISS %s
// MISS: [zkc-E705] exported claim with profile 'schnorr_evaluation' finds no consumer source with its exact descriptor

// Two consumer sources with one descriptor leave no fact deciding which face
// receives the export; authored order is not a semantic input.
// RUN: not zkc-opt '-pir-link=producer=ambprod consumer=ambcons %pir-link-authorities' %s 2>&1 | FileCheck --check-prefix=TWOFACES %s
// TWOFACES: [zkc-E706] exported claim with profile 'single_opening' matches 2 consumer sources with one descriptor

pir.protocol "misprod" kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %evaluation = pir.instantiate "ev" anchors {statement = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"} : !pir.claim<"schnorr_evaluation">
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "X" : "tg" stage instance
  pir.end %t1
  pir.export %evaluation : !pir.claim<"schnorr_evaluation"> route "to.consumer"
}

pir.protocol "miscons" kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %evaluation = pir.instantiate "ev" anchors {statement = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"} : !pir.claim<"sumcheck_evaluation">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "Y" : "tg" stage instance
  pir.end %t1
  pir.residual %evaluation : !pir.claim<"sumcheck_evaluation"> route "sumcheck-terminal-not-modeled"
}

pir.protocol "ambprod" kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %opening = pir.instantiate "opening" anchors {commitment = "sha256:c9256a263eaf9251bb2b10ec702ab192f7661351c8be76e0341503de862776a4", point = "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64", value = "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd9fc7cfa04d4ca35c89025b10c379"} : !pir.claim<"single_opening">
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "X" : "tg" stage instance
  pir.end %t1
  pir.export %opening : !pir.claim<"single_opening"> route "to.consumer"
}

pir.protocol "ambcons" kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %left = pir.instantiate "left" anchors {commitment = "sha256:c9256a263eaf9251bb2b10ec702ab192f7661351c8be76e0341503de862776a4", point = "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64", value = "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd9fc7cfa04d4ca35c89025b10c379"} : !pir.claim<"single_opening">
  %right = pir.instantiate "right" anchors {commitment = "sha256:c9256a263eaf9251bb2b10ec702ab192f7661351c8be76e0341503de862776a4", point = "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64", value = "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd9fc7cfa04d4ca35c89025b10c379"} : !pir.claim<"single_opening">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "Y" : "tg" stage instance
  pir.end %t1
  pir.residual %left : !pir.claim<"single_opening"> route "opening-terminal-not-modeled"
  pir.residual %right : !pir.claim<"single_opening"> route "opening-terminal-not-modeled"
}
