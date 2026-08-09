//===- TestHoleParameters.cpp - hole parameter transport ---------*- C++ -*-===//
// Observe what a hole supplier is actually handed. A contract's static and
// semantic parameter bindings travel authored route -> sealed protocol ->
// projected endpoint -> admission -> supplier, and every stage of that could
// drop or reorder them while the suite stayed green, because the production
// contracts declare no parameters at all. This pass puts a supplier at the end
// of the chain that reports its arguments instead of filling, so the test can
// read the bindings that arrived.
//===----------------------------------------------------------------------===//

#include "mlir/IR/BuiltinOps.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Dialect/Oir/OirOps.h"
#include "zkc/Interpreter/ExecutionProfile.h"
#include "zkc/Interpreter/Interpreter.h"
#include "llvm/Support/raw_ostream.h"

using namespace mlir;

namespace {

/// Fills nothing; states what it was given. A supplier that answered would
/// prove only that execution completed, which is what the existing coverage
/// already shows.
class ReportingSupplier : public zkc::interpreter::HoleSupplier {
public:
  ReportingSupplier(llvm::StringRef digest) : digest(digest) {}

  llvm::StringRef contractDigest() const override { return digest; }

  llvm::Error
  fill(llvm::ArrayRef<llvm::StringRef> params,
       llvm::ArrayRef<llvm::StringRef> semanticParams,
       llvm::ArrayRef<llvm::APInt> values,
       llvm::ArrayRef<llvm::SmallVector<uint8_t, 32>> handles,
       llvm::SmallVectorImpl<llvm::APInt> &valueResults,
       llvm::SmallVectorImpl<llvm::SmallVector<uint8_t, 32>> &handleResults)
      const override {
    (void)values;
    (void)handles;
    (void)valueResults;
    (void)handleResults;
    std::string report;
    llvm::raw_string_ostream os(report);
    os << "received static [";
    llvm::interleaveComma(params, os);
    os << "] semantic [";
    llvm::interleaveComma(semanticParams, os);
    os << "]";
    return llvm::createStringError(report);
  }

private:
  std::string digest;
};

/// The toy supplier set with one hole rerouted to the reporting supplier.
class ReportingProfile : public zkc::interpreter::ExecutionProfile {
public:
  ReportingProfile(llvm::StringRef digest)
      : inner(zkc::interpreter::toyProfile()), supplier(digest) {}

  llvm::StringRef name() const override { return "test-reporting"; }
  const zkc::interpreter::CodecSupplier *
  codec(llvm::StringRef codecName) const override {
    return inner.codec(codecName);
  }
  const zkc::interpreter::SpongeSupplier *
  sponge(llvm::StringRef construction, llvm::StringRef ivPolicy) const override {
    return inner.sponge(construction, ivPolicy);
  }
  std::optional<zkc::interpreter::SamplingPlan>
  admitSampling(llvm::StringRef rule, llvm::StringRef count,
                llvm::StringRef space) const override {
    return inner.admitSampling(rule, count, space);
  }
  std::optional<llvm::APInt>
  canonicalModulus(llvm::StringRef valueClass) const override {
    return inner.canonicalModulus(valueClass);
  }
  std::optional<AlgebraModuli> algebraModuli() const override {
    return inner.algebraModuli();
  }
  std::optional<llvm::StringRef>
  constructionDigest(llvm::StringRef taggedName) const override {
    return inner.constructionDigest(taggedName);
  }
  const zkc::interpreter::HoleSupplier *
  hole(llvm::StringRef contractDigest) const override {
    if (contractDigest == supplier.contractDigest())
      return &supplier;
    return inner.hole(contractDigest);
  }

private:
  const zkc::interpreter::ExecutionProfile &inner;
  ReportingSupplier supplier;
};

struct TestHoleParametersPass
    : public PassWrapper<TestHoleParametersPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(TestHoleParametersPass)

  TestHoleParametersPass() = default;
  TestHoleParametersPass(const TestHoleParametersPass &other)
      : PassWrapper(other) {}

  StringRef getArgument() const override {
    return "test-hole-parameter-transport";
  }
  StringRef getDescription() const override {
    return "report the parameter bindings a hole supplier is handed";
  }

  Option<std::string> witness{
      *this, "witness", llvm::cl::desc("prover witness, hex")};
  Option<std::string> statementValue{
      *this, "statement", llvm::cl::desc("statement binding, name=value")};

  void runOnOperation() override {
    // The hole to report on is the one carrying bindings: naming it by digest
    // would put a derived value in the test text, and there is exactly one
    // thing here worth reporting on.
    std::string digest;
    getOperation().walk([&](zkc::oir::HoleCallOp hole) {
      if (digest.empty() &&
          (!hole.getParams().empty() || !hole.getSemanticParams().empty()))
        digest = hole.getContractDigest().str();
    });
    if (digest.empty()) {
      getOperation().emitError("no hole_call carries a parameter binding");
      return signalPassFailure();
    }

    ReportingProfile profile(digest);
    llvm::StringMap<std::string> statement;
    StringRef binding(statementValue);
    auto [name, value] = binding.split('=');
    if (!name.empty())
      statement[name] = value.str();
    llvm::StringMap<std::string> witnesses;
    if (!witness.empty())
      witnesses["w"] = witness;

    for (zkc::oir::ArtifactOp artifact :
         getOperation().getOps<zkc::oir::ArtifactOp>()) {
      auto result =
          zkc::interpreter::prove(artifact, profile, statement, witnesses);
      if (!result) {
        artifact.emitOpError() << llvm::toString(result.takeError());
        return signalPassFailure();
      }
    }
  }
};

} // namespace

namespace zkc {
namespace test {
void registerTestHoleParametersPass() {
  PassRegistration<TestHoleParametersPass>();
}
} // namespace test
} // namespace zkc
