// RUN: zkc-opt '-pir-link=producer=prod consumer=cons %pir-link-authorities' %s | FileCheck %s --check-prefix=LINK
// RUN: zkc-opt '-pir-link=producer=prod consumer=cons %pir-link-authorities' %pir-seal-full %s | FileCheck %s --check-prefix=SEALED
// RUN: zkc-opt '-pir-link=producer=empty-routes consumer=no-routes %pir-link-authorities' %s | FileCheck %s --check-prefix=EMPTY
// RUN: zkc-opt '-pir-link=producer=unused-handle consumer=no-routes %pir-link-authorities' %s | FileCheck %s --check-prefix=UNUSED
// RUN: zkc-opt '-pir-link=producer=empty-spine-a consumer=no-routes %pir-link-authorities' %s | FileCheck %s --check-prefix=EMPTY-PRODUCER
// RUN: zkc-opt '-pir-link=producer=no-routes consumer=empty-spine-a %pir-link-authorities' %s | FileCheck %s --check-prefix=EMPTY-CONSUMER
// RUN: zkc-opt '-pir-link=producer=empty-spine-a consumer=empty-spine-b %pir-link-authorities' %s | FileCheck %s --check-prefix=EMPTY-BOTH

// Static linking re-authors both typed construction graphs under the same
// face namespaces as the transcript. Constants retain their kappa names;
// every face-local reference is qualified; witness ABI order is producer then
// consumer. The source protocols remain unchanged, and the composed routes
// pass the same open judgment used by sealing.

// LINK: pir.protocol "prod"
// LINK-SAME: routes {instances = {local.commit =
// LINK-SAME: witnesses = {{\[\[}}"w", "sigma-witness"]]
// LINK: binding "local.commit.0"
// LINK: pir.protocol "cons"
// LINK-SAME: routes {instances = {local.commit =
// LINK: pir.protocol "link(prod,cons)"
// LINK-SAME: routes {instances = {left.local.commit = {contract = "zkc.hole.sigma-commit", inputs = ["slot:left.generator", "witness:left.w"]}
// LINK-SAME: left.local.response = {contract = "zkc.hole.sigma-response", inputs = ["chal:left.c", "left.local.commit.1"]}
// LINK-SAME: right.local.commit = {contract = "zkc.hole.sigma-commit", inputs = ["slot:right.generator", "witness:right.w"]}
// LINK-SAME: right.local.response = {contract = "zkc.hole.sigma-response", inputs = ["chal:right.c", "right.local.commit.1"]}
// LINK-SAME: witnesses = {{\[\[}}"left.w", "sigma-witness"], ["right.w", "sigma-witness"]]
// LINK: pir.bind {{.*}} "left.y"
// LINK: pir.slot {{.*}} "left.echo" : "tg" binding "bind:left.y"
// LINK: pir.slot {{.*}} "left.generator" : "tg" binding "const:g"
// LINK: pir.slot {{.*}} "left.commitment" : "tg" binding "left.local.commit.0"
// LINK: domain "left.challenge"
// LINK: pir.slot {{.*}} "left.response" : "scalar" binding "left.local.response.0"
// LINK: pir.bind {{.*}} "right.y"
// LINK: pir.slot {{.*}} "right.echo" : "tg" binding "bind:right.y"
// LINK: pir.slot {{.*}} "right.generator" : "tg" binding "const:g"
// LINK: pir.slot {{.*}} "right.commitment" : "tg" binding "right.local.commit.0"
// LINK: domain "right.challenge"
// LINK: pir.slot {{.*}} "right.response" : "scalar" binding "right.local.response.0"

// SEALED: pir.sealed "link(prod,cons)"
// SEALED-SAME: hole_contracts = {"zkc.hole.sigma-commit" = "sha256:
// SEALED-SAME: "zkc.hole.sigma-response" = "sha256:
// SEALED-SAME: routes {instances = {left.local.commit =

// An authored empty route graph remains an explicit route graph after link;
// absence on the other face does not silently erase that distinction.
// EMPTY: pir.protocol "link(empty-routes,no-routes)"
// EMPTY-SAME: routes {instances = {}}

// Handle linearity is at-most-one reader, not an exact-use requirement.
// UNUSED: pir.protocol "link(unused-handle,no-routes)"
// UNUSED-SAME: routes {instances = {}, witnesses = {{\[\[}}"left.unused", "sigma-witness"]]}

// Empty event runs add no segment boundary: segment starts must denote a
// non-empty later run strictly inside the composite spine.
// EMPTY-PRODUCER: pir.protocol "link(empty-spine-a,no-routes)"
// EMPTY-PRODUCER-SAME: sponge = "toy_duplex"} {
// EMPTY-CONSUMER: pir.protocol "link(no-routes,empty-spine-a)"
// EMPTY-CONSUMER-SAME: sponge = "toy_duplex"} {
// EMPTY-BOTH: pir.protocol "link(empty-spine-a,empty-spine-b)"
// EMPTY-BOTH-SAME: sponge = "toy_duplex"} {

pir.protocol "prod"
    kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"}
    routes {instances = {local.commit = {contract = "zkc.hole.sigma-commit", inputs = ["slot:generator", "witness:w"]}, local.response = {contract = "zkc.hole.sigma-response", inputs = ["chal:c", "local.commit.1"]}}, witnesses = [["w", "sigma-witness"]]} {
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %echo = pir.slot %t1 "echo" : "tg" binding "bind:y"
  %t3, %generator = pir.slot %t2 "generator" : "tg" binding "const:g"
  %t4, %commitment = pir.slot %t3 "commitment" : "tg" binding "local.commit.0"
  %t5, %challenge = pir.chal %t4 deps(%y, %echo, %generator, %commitment : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "challenge" space "2305843009213693952"
  %t6, %response = pir.slot %t5 "response" : "scalar" binding "local.response.0"
  pir.end %t6
}

pir.protocol "cons"
    kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"}
    routes {instances = {local.commit = {contract = "zkc.hole.sigma-commit", inputs = ["slot:generator", "witness:w"]}, local.response = {contract = "zkc.hole.sigma-response", inputs = ["chal:c", "local.commit.1"]}}, witnesses = [["w", "sigma-witness"]]} {
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %echo = pir.slot %t1 "echo" : "tg" binding "bind:y"
  %t3, %generator = pir.slot %t2 "generator" : "tg" binding "const:g"
  %t4, %commitment = pir.slot %t3 "commitment" : "tg" binding "local.commit.0"
  %t5, %challenge = pir.chal %t4 deps(%y, %echo, %generator, %commitment : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "challenge" space "2305843009213693952"
  %t6, %response = pir.slot %t5 "response" : "scalar" binding "local.response.0"
  pir.end %t6
}

pir.protocol "empty-routes"
    kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"}
    routes {instances = {}} {
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "x" : "tg" stage instance
  pir.end %t1
}

pir.protocol "no-routes" kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "x" : "tg" stage instance
  pir.end %t1
}

pir.protocol "unused-handle"
    kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"}
    routes {instances = {}, witnesses = [["unused", "sigma-witness"]]} {
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "x" : "tg" stage instance
  pir.end %t1
}

pir.protocol "empty-spine-a"
    kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  pir.end %t0
}

pir.protocol "empty-spine-b"
    kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  pir.end %t0
}
