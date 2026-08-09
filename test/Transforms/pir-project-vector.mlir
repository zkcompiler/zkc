// RUN: zkc-opt %pir-seal-full %pir-project-full %s | FileCheck %s
//
// Count is carried, not unrolled: one vector challenge capability projects to
// one typed endpoint squeeze with the exact semantic class, multiplicity, and
// independent-sampling rule.  Nothing here executes the construction.

// CHECK: oir.program attributes {codecs = {query_index = "ts_be8", rs = "ts_be8"}, param_digests = {{.*}}, statement_labels = ["root"]}
// CHECK: %[[SP:.+]], %[[QUERY:.+]] = oir.squeeze {{.*}} "query" : "query_index" count "2" domain "fri.query" rule "uniform_independent" space "1024" src [1]
// CHECK: oir.check_call "predicate" kind "zkc.check.relation-predicate" digest "sha256:{{[0-9a-f]+}}"

pir.protocol "vector-challenge" kappa {codecs = {query_index = "ts_be8", rs = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  %t1, %root = pir.bind %t0 "root" : "rs" stage instance
  %t2, %query = pir.chal %t1 deps(%root : !pir.val<"rs">) "query" : "query_index" domain "fri.query" space "1024" mode ["vector", "2", "uniform_independent"]
  pir.check "predicate" contract "zkc.check.relation-predicate" semantic_args {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"}
  pir.end %t2
}
