#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringSet.h"

using namespace llvm;
namespace zkc::protocol {
ArrayRef<Kernel> kernels() {
  static const std::vector<Kernel> table = {
      {"resource_unit.create", {}, {"resource_unit"}},
      {"resource_unit.pass", {"resource_unit"}, {"resource_unit"}},
      {"resource_unit.consume", {"resource_unit"}, {}},
      {"external.monero.init", {"indices"}, {"indices"}},
      {"external.monero.hash", {"indices"}, {"indices"}},
      {"external.monero.update",
       {"indices", "indices"},
       {"indices", "indices"}},
      {"external.openvm.init", {}, {"indices"}},
      {"external.openvm.observe", {"indices", "indices"}, {"indices"}},
      {"external.openvm.sample", {"indices"}, {"indices", "index"}},
      {"external.openvm.sample_ext", {"indices"}, {"indices", "indices"}},
      {"external.openvm.sample_bits",
       {"indices", "index"},
       {"indices", "index"}},
      {"external.openvm.check_witness",
       {"indices", "index", "index"},
       {"indices", "bool"}},
      {"index.constant",
       {},
       {"index"},
       OperationContracts::exactDomainValue(DomainValueRule::Constant, true)},
      {"index.add", {"index", "index"}, {"index"}},
      {"index.sub", {"index", "index"}, {"index"}},
      {"index.mul", {"index", "index"}, {"index"}},
      {"index.div",
       {"index", "index"},
       {"index"},
       OperationContracts::exactDomainValue(DomainValueRule::Divide)},
      {"index.mod", {"index", "index"}, {"index"}},
      {"index.equal", {"index", "index"}, {"bool"}},
      {"index.less", {"index", "index"}, {"bool"}},
      {"indices.empty", {}, {"indices"}},
      {"indices.append", {"indices", "index"}, {"indices"}},
      {"indices.at", {"indices", "index"}, {"index"}},
      {"indices.length", {"indices"}, {"index"}},
      {"vector.get", {"vector", "index"}, {"field"}},
      {"vector.slice", {"vector", "index", "index"}, {"vector"}},
      {"vector.length",
       {"vector"},
       {"index"},
       OperationContracts::exactDomainValue(DomainValueRule::Length)},
      {"vector.rotate", {"vector", "index"}, {"vector"}},
      {"vector.interleave", {"vector", "vector"}, {"vector"}},
      {"vector.prefix_product", {"vector"}, {"vector"}},
      {"vector.prefix_sum", {"vector"}, {"vector"}},
      {"vector.inverse", {"vector"}, {"vector"}},
      {"vector.embed", {"vector"}, {"vector"}},
      {"vector.fill", {"field", "index"}, {"vector"}},
      {"vector.geometric", {"field", "index"}, {"vector"}},
      {"field.from_index", {"index"}, {"field"}},
      {"poly.coefficient_count", {"polynomial"}, {"index"}},
      {"poly.coset_evaluate",
       {"polynomial", "field", "index"},
       {"vector"},
       OperationContracts::onCoset({1, 2, false, 0, false})},
      {"poly.coset_interpolate",
       {"vector", "field"},
       {"polynomial"},
       OperationContracts::onCoset({1, 0, true, {}, false})},
      {"poly.domain_point",
       {"field", "index", "index"},
       {"field"},
       OperationContracts::onCoset({0, 1, false, {}, false})},
      {"poly.domain_root", {"index"}, {"field"}},
      {"poly.domain_points",
       {"field", "index"},
       {"vector"},
       OperationContracts::onCoset({0, 1, false, 0, false})},
      {"poly.even_odd_fold",
       {"vector", "field", "field"},
       {"vector"},
       OperationContracts::onCoset({1, 0, true, 0, true})},
      {"poly.divide_opening", {"polynomial", "field", "field"}, {"polynomial"}},
      {"poly.opening_quotient",
       {"vector", "field", "field", "field"},
       {"vector"},
       OperationContracts::onCoset({1, 0, true, 0, false})},
      {"field.sub", {"field", "field"}, {"field"}},
      {"field.neg", {"field"}, {"field"}},
      {"field.inverse", {"field"}, {"field"}},
      {"field.embed", {"field"}, {"field"}},
      {"matrix.mul_vector", {"matrix", "vector"}, {"vector"}},
      {"matrix.transpose_mul_vector", {"matrix", "vector"}, {"vector"}},
      {"matrix.bilinear", {"matrix", "vector", "vector"}, {"field"}},
      {"matrix.shape_check", {"matrix"}, {"bool"}},
      {"matrix.identity_check", {"matrix"}, {"bool"}},
      {"vector.constant", {}, {"vector"}},
      {"vector.scatter_sum", {"vector"}, {"vector"}},
      {"vector.empty", {}, {"vector"}},
      {"vector.append", {"vector", "field"}, {"vector"}},
      {"vector.splat", {"field"}, {"vector"}},
      {"vector.powers", {"field"}, {"vector"}},
      {"vector.add", {"vector", "vector"}, {"vector"}},
      {"vector.sub", {"vector", "vector"}, {"vector"}},
      {"vector.mul",
       {"vector", "vector"},
       {"vector"},
       OperationContracts::diagonal()},
      {"vector.dot",
       {"vector", "vector"},
       {"field"},
       OperationContracts::contraction()},
      {"vector.concat", {"vector", "vector"}, {"vector"}},
      {"vector.kronecker", {"vector", "vector"}, {"vector"}},
      {"vector.matvec", {"vector", "vector"}, {"vector"}},
      {"vector.scale", {"vector", "field"}, {"vector"}},
      {"vector.sum", {"vector"}, {"field"}},
      {"vector.split", {"vector"}, {"vector", "vector"}},
      {"vector.at", {"vector"}, {"field"}},
      {"vector.length_check", {"vector"}, {"bool"}},
      {"vector.gather", {"vector"}, {"vector"}},
      {"vector.from_point", {"point"}, {"vector"}},
      {"vector.from_table", {"table"}, {"vector"}},
      {"vector.to_point", {"vector"}, {"point"}},
      {"vector.to_table", {"vector"}, {"table"}},
      {"poly.equality_weights", {"point"}, {"vector"}},
      {"poly.from_coefficients", {"vector"}, {"polynomial"}},
      {"poly.coefficients", {"polynomial"}, {"vector"}},
      {"poly.degree_check", {"polynomial"}, {"bool"}},
      {"poly.univariate_evaluate", {"polynomial", "field"}, {"field"}},
      {"poly.univariate_boundary", {"polynomial"}, {"field"}},
      {"random.vector",
       {"rng"},
       {"vector", "rng"},
       OperationContracts::sample(RandomnessProvider::Entropy,
                                  SampleDomain::FieldVector)},
      {"curve.neg", {"group"}, {"group"}},
      {"curve.nonidentity", {"group"}, {"bool"}},
      {"curve.msm",
       {"vector", "groups"},
       {"group"},
       OperationContracts::contraction()},
      {"curve.scale_each",
       {"vector", "groups"},
       {"groups"},
       OperationContracts::diagonal()},
      {"curve.vector_add", {"groups", "groups"}, {"groups"}},
      {"curve.vector_scale", {"groups", "field"}, {"groups"}},
      {"curve.split", {"groups"}, {"groups", "groups"}},
      {"curve.concat", {"groups", "groups"}, {"groups"}},
      {"pairing.check", {"groups", "groups"}, {"bool"}},
      {"field.constant",
       {},
       {"field"},
       OperationContracts::exactDomainValue(DomainValueRule::Constant, true)},
      {"field.add",
       {"field", "field"},
       {"field"},
       OperationContracts::replay()},
      {"field.mul",
       {"field", "field"},
       {"field"},
       OperationContracts::exactDomainValue(DomainValueRule::Multiply, true)},
      {"field.equal",
       {"field", "field"},
       {"bool"},
       OperationContracts::replay()},
      {"bool.and",
       {"bool", "bool"},
       {"bool"},
       OperationContracts::booleanConjunction()},
      {"bool.not", {"bool"}, {"bool"}, OperationContracts::replay()},
      {"bool.or", {"bool", "bool"}, {"bool"}, OperationContracts::replay()},
      {"control.require", {"bool"}, {}, OperationContracts::guard()},
      {"poly.product_sum", {"table", "table"}, {"field"}},
      {"poly.product_round", {"table", "table"}, {"round"}},
      {"poly.boundary", {"round"}, {"field"}, OperationContracts::replay()},
      {"poly.round_evaluate",
       {"round", "field"},
       {"field"},
       OperationContracts::replay()},
      {"poly.fold", {"table", "field"}, {"table"}},
      {"poly.evaluate", {"table", "point"}, {"field"}},
      {"poly.empty_point", {}, {"point"}, OperationContracts::replay()},
      {"poly.append_point",
       {"point", "field"},
       {"point"},
       OperationContracts::replay()},
      {"oracle.commit", {"vector", "index"}, {"commitment", "opening_state"}},
      {"oracle.open", {"opening_state", "index"}, {"vector", "proof"}},
      {"oracle.check",
       {"commitment", "index", "index", "index", "vector", "proof"},
       {"bool"}},
      {"commitments.empty", {}, {"commitments"}},
      {"commitments.append", {"commitments", "commitment"}, {"commitments"}},
      {"commitments.at", {"commitments", "index"}, {"commitment"}},
      {"commitments.length", {"commitments"}, {"index"}},
      {"opening_states.empty", {}, {"opening_states"}},
      {"opening_states.append",
       {"opening_states", "opening_state"},
       {"opening_states"}},
      {"opening_states.at", {"opening_states", "index"}, {"opening_state"}},
      {"opening_states.length", {"opening_states"}, {"index"}},
      {"pcs.commit", {"prover_key", "table"}, {"commitment", "opening_state"}},
      {"pcs.open", {"opening_state", "point"}, {"field", "proof"}},
      {"pcs.check",
       {"verifier_key", "commitment", "point", "field", "proof"},
       {"bool"}},
      {"random.index",
       {"rng", "index"},
       {"index", "rng"},
       OperationContracts::sample(RandomnessProvider::Entropy,
                                  SampleDomain::BoundedIndex, 1,
                                  "transcript.draw_index")},
      {"transcript.draw_index",
       {"transcript", "index"},
       {"index", "transcript"},
       OperationContracts::sample(RandomnessProvider::Transcript,
                                  SampleDomain::BoundedIndex, 1)},
      {"random.draw",
       {"rng"},
       {"field", "rng"},
       OperationContracts::sample(RandomnessProvider::Entropy,
                                  SampleDomain::Field, {},
                                  "transcript.challenge")},
  };
  static const std::vector<Kernel> installed = [&] {
    auto all = table;
    all.insert(
        all.end(),
        {{"pcs.equal",
          {"commitment", "commitment"},
          {"bool"},
          OperationContracts::replay()},
         {"curve.generator", {}, {"group"}, OperationContracts::replay()},
         {"curve.add",
          {"group", "group"},
          {"group"},
          OperationContracts::replay()},
         {"curve.scale",
          {"group", "field"},
          {"group"},
          OperationContracts::replay()},
         {"curve.equal",
          {"group", "group"},
          {"bool"},
          OperationContracts::replay()},
         {"curve.empty", {}, {"groups"}, OperationContracts::replay()},
         {"curve.append",
          {"groups", "group"},
          {"groups"},
          OperationContracts::replay()},
         {"curve.at", {"groups"}, {"group"}, OperationContracts::replay()},
         {"curve.get",
          {"groups", "index"},
          {"group"},
          OperationContracts::replay()},
         {"curve.length", {"groups"}, {"index"}, OperationContracts::replay()},
         {"curve.commit", {"groups", "nonce"}, {"groups", "nonce"}},
         {"curve.response", {"field", "field", "nonce"}, {"field"}},
         {"transcript.challenge",
          {"transcript"},
          {"field", "transcript"},
          OperationContracts::sample(RandomnessProvider::Transcript,
                                     SampleDomain::Field)}});
    // Owned strings below have static lifetime, including their StringRefs.
    static const std::vector<std::string> kinds = {
        "bool",       "field",      "table", "point",   "round",
        "commitment", "proof",      "group", "groups",  "matrix",
        "vector",     "polynomial", "index", "indices", "commitments"};
    static const std::vector<std::string> keys = [] {
      std::vector<std::string> out;
      for (const auto &kind : kinds)
        out.push_back("transcript.observe." + kind);
      return out;
    }();
    for (size_t i = 0; i < kinds.size(); ++i)
      all.push_back({keys[i],
                     {"transcript", kinds[i]},
                     {"transcript"},
                     OperationContracts::transcriptObservation()});
    return all;
  }();
  return installed;
}
StringRef fieldModulus(StringRef identity) {
  const auto *domain = installedDomains().domain(identity);
  return domain && domain->sort == "Field" ? StringRef(domain->modulus)
                                           : StringRef{};
}

Error checkParameters(StringRef key, llvm::ArrayRef<std::string> parameters,
                      StringRef field) {
  unsigned count = 0;
  if (key.starts_with("transcript."))
    count = 5;
  else if (key == "matrix.shape_check")
    count = 2;
  else if (key == "vector.matvec")
    count = 3;
  else if (key == "index.constant" || key == "field.constant" ||
           key == "curve.at" || key == "vector.splat" ||
           key == "vector.powers" || key == "vector.at" ||
           key == "vector.length_check" || key == "poly.degree_check" ||
           key == "random.vector" || key == "matrix.identity_check")
    count = 1;
  if (key == "vector.scatter_sum" && parameters.empty())
    return error("interactive-kernel-parameters");
  if (key != "vector.gather" && key != "vector.constant" &&
      key != "vector.scatter_sum" && parameters.size() != count)
    return error("interactive-kernel-parameters");
  if (key == "matrix.identity_check") {
    StringRef digest = parameters.front();
    if (digest.size() != 64 || !all_of(digest, [](char c) {
          return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f');
        }))
      return error("interactive-kernel-parameters");
    return Error::success();
  }
  if (key.starts_with("transcript.")) {
    for (const auto &p : parameters)
      if (p.empty() || p.size() > 128 || !all_of(p, [](char c) {
            return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
                   (c >= '0' && c <= '9') || c == '_' || c == '.' || c == '-';
          }))
        return error("interactive-transcript-origin");
    return Error::success();
  }
  for (const auto &parameter : parameters) {
    StringRef n = parameter;
    auto code = (key == "field.constant" || key == "vector.constant")
                    ? "interactive-constant"
                : key == "curve.at" ? "interactive-index"
                                    : "interactive-kernel-parameters";
    if (n.empty() || !all_of(n, [](char c) { return c >= '0' && c <= '9'; }))
      return error("expected-natural");
    if (n.size() > 1 && n.front() == '0')
      return error("noncanonical-natural");
    if (key == "field.constant" || key == "vector.constant") {
      StringRef modulus = fieldModulus(field);
      if (modulus.empty() || n.size() > modulus.size() ||
          (n.size() == modulus.size() && n >= modulus))
        return error(code);
    } else {
      // Curve indices and vector sizes, positions and degrees share one
      // bound: no vector the runtimes provide is longer.
      static const llvm::StringSet<> extents{
          "curve.at",      "vector.splat",        "vector.powers",
          "vector.at",     "vector.length_check", "poly.degree_check",
          "random.vector", "vector.gather",       "vector.matvec"};
      uint64_t natural;
      if (n.getAsInteger(10, natural) ||
          (extents.contains(key) && natural > 1048576) ||
          (key == "matrix.shape_check" && natural > 65536))
        return error(code);
    }
  }
  if (key == "vector.matvec" && parameters[2] != "0" && parameters[2] != "1")
    return error("interactive-kernel-parameters");
  return Error::success();
}
} // namespace zkc::protocol
