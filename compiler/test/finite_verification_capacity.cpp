#include "../lib/Transforms/FiniteVerification.h"
#include "../lib/Transforms/MathematicalComparison.h"
#include "../lib/Transforms/RecipeRealizations.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Dialect/IR.h"
#include <fstream>
#include <sstream>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;

namespace {
OwningOpRef<ModuleOp> fixture(MLIRContext &context, StringRef name) {
  std::ifstream input(std::string(ZKC_FINITE_FIXTURES) + "/" + name.str() +
                      ".mlir");
  require(bool(input), "missing fixture");
  std::ostringstream text;
  text << input.rdbuf();
  auto module = parseSourceString<ModuleOp>(text.str(), &context);
  require(bool(module) && succeeded(verify(*module)), "fixture refused");
  return module;
}
OwningOpRef<ModuleOp> clone(ModuleOp source) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
}
bool same(ModuleOp left, ModuleOp right) {
  return OperationEquivalence::isEquivalentTo(
      left, right, OperationEquivalence::IgnoreLocations);
}
local::FuncOp function(ModuleOp module, StringRef name) {
  return SymbolTable(&module.getBody()->front()).lookup<local::FuncOp>(name);
}
Operation *payload(local::FuncOp target, SymbolTable &symbols) {
  for (auto &op : target.getBody().front())
    if (mathematical::hasFinitePayloadContract(&op, symbols))
      return &op;
  return nullptr;
}
bool hasLoop(ModuleOp module, StringRef name) {
  bool result = false;
  function(module, name).walk([&](local::LocalForOp) { result = true; });
  return result;
}
// Extend the ordinary square into x^(multiplications + 1). Both scalar and
// vector operations stay well formed, and the two actual formulas agree.
void extendProduct(local::FuncOp target, unsigned multiplications) {
  auto &block = target.getBody().front();
  auto *prototype = block.back().getOperand(0).getDefiningOp();
  require(prototype && prototype->getNumOperands() == 2,
          "missing multiplication prototype");
  OpBuilder builder(&block.back());
  Value result = prototype->getResult(0);
  for (unsigned i = 1; i < multiplications; ++i) {
    auto *next = builder.clone(*prototype);
    next->setOperands({result, target.getArgument(0)});
    next->setAttr("site",
                  builder.getStringAttr("product_" + std::to_string(i)));
    result = next->getResult(0);
  }
  block.back().setOperand(0, result);
}
// Probe the actual comparator independently of the producer's operation order.
FailureOr<Value> compare(ModuleOp source, ModuleOp candidate, StringRef name,
                         uint64_t &work,
                         mathematical::ComparisonCapacity &capacity) {
  SymbolTable before(&source.getBody()->front());
  finite::Computation computation;
  require(succeeded(finite::describe(before.lookup(name), computation)),
          "finite description failed");
  SymbolTable symbols(&candidate.getBody()->front());
  auto target = function(candidate, name);
  Operation *cursor = payload(target, symbols);
  require(cursor, "candidate has no bulk payload");
  auto *saved = cursor;
  llvm::DenseSet<Operation *> bindings;
  auto result = mathematical::compareFinitePayload(
      computation, target.getArguments(),
      target.getBody().front().front().getResult(0), cursor, symbols, bindings,
      work, &target.getBody().front().back(), &capacity);
  if (failed(result))
    require(cursor == saved && bindings.empty(),
            "failed comparison published cursor or bindings");
  else
    require(cursor == &target.getBody().front().back() &&
                *result == cursor->getOperand(0),
            "comparison did not verify the actual returned value");
  return result;
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  for (StringRef name : {"collect", "dot", "matrix-row", "matrix-column",
                         "bilinear", "msm-direct"}) {
    StringRef declaration = name == "collect" ? "collect" : "fold";
    cases.run(name + " precise independent comparison boundary", [&] {
      auto source = fixture(context, name);
      auto candidate = clone(*source);
      require(succeeded(finite::realizeLocals(*candidate)),
              "bulk realization failed");
      auto target = function(*candidate, declaration);
      auto *result =
          target.getBody().front().back().getOperand(0).getDefiningOp();
      require(result && result->getNumOperands() == 2,
              "fixture no longer returns a binary bulk result");
      Value left = result->getOperand(0), right = result->getOperand(1);
      result->setOperands({right, left});
      require(succeeded(verify(*candidate)) &&
                  succeeded(finite::verifyRealizations(*source, *candidate)),
              "commuted valid candidate was refused");
      uint64_t work = 100000;
      mathematical::ComparisonCapacity capacity;
      require(succeeded(
                  compare(*source, *candidate, declaration, work, capacity)) &&
                  capacity == mathematical::ComparisonCapacity::None,
              "ample comparison refused");
      uint64_t cost = 100000 - work;
      require(cost > 1, "missing comparator charges");
      work = cost;
      require(succeeded(
                  compare(*source, *candidate, declaration, work, capacity)) &&
                  work == 0 &&
                  capacity == mathematical::ComparisonCapacity::None,
              "successful exact allowance was classified as capacity");
      work = cost - 1;
      require(
          failed(compare(*source, *candidate, declaration, work, capacity)) &&
              capacity == mathematical::ComparisonCapacity::Work && work == 0,
          "failed final charge did not report work capacity");
      auto checked =
          finite::checkRealizations(*source, *candidate, {100000, 1});
      require(checked.status == finite::VerificationStatus::OptionalCapacity &&
                  checked.detail == "finite comparison work",
              "optional capacity was reported as semantic mismatch");
      llvm::outs() << name << " comparison work: " << cost << '\n';
    });
    cases.run(name + " changed result remains a hard refusal", [&] {
      auto source = fixture(context, name);
      auto candidate = clone(*source);
      require(succeeded(finite::realizeLocals(*candidate)),
              "bulk realization failed");
      auto target = function(*candidate, declaration);
      target.getBody().front().back().setOperand(
          0, name == "collect" ? target.getArgument(0)
                               : target.getArguments().back());
      require(succeeded(verify(*candidate)),
              "changed result was not an ordinary well-formed candidate");
      auto checked = finite::checkRealizations(*source, *candidate);
      require(checked.status == finite::VerificationStatus::Mismatch,
              "changed result was downgraded to capacity");
      std::string diagnostic;
      ScopedDiagnosticHandler capture(&context, [&](Diagnostic &d) {
        diagnostic += d.str();
        return success();
      });
      require(failed(checked.diagnose(*candidate)) &&
                  namesIdentifier(diagnostic, "finite-correspondence"),
              "mismatch lost its refusal identifier");
    });
    cases.run(name + " optional capacity retries checked ordered source", [&] {
      auto source = fixture(context, name);
      auto fallback = clone(*source), ordered = clone(*source);
      mathematical::RealizationWork work;
      const auto initial = work;
      std::string diagnostic;
      ScopedDiagnosticHandler capture(&context, [&](Diagnostic &d) {
        diagnostic += d.str();
        return success();
      });
      require(succeeded(finite::realizeLocalsWithLimits(
                  *fallback, {}, &work, mathematical::mathematicalRecipes(),
                  {100000, 1})) &&
                  diagnostic.empty(),
              "transient capacity did not retry silently");
      require(
          succeeded(finite::realizeLocals(*ordered, {false, false})) &&
              hasLoop(*fallback, declaration) && same(*fallback, *ordered) &&
              succeeded(finite::verifyRealizations(*source, *fallback)),
          "fallback differs from independently checked ordered realization");
      if (name == "collect")
        require(work.lanes < initial.lanes,
                "discarded candidate replenished optional lane work");
      require(work.matching.structural < initial.matching.structural,
              "discarded candidate replenished optional matching work");
    });
    cases.run(name + " required reader boundary and atomic refusal", [&] {
      auto source = fixture(context, name);
      auto original = clone(*source), ordered = clone(*source);
      require(succeeded(finite::realizeLocals(*ordered, {false, false})),
              "ordered realization failed");
      uint64_t cost = 0;
      for (; cost < 1000; ++cost) {
        auto checked = finite::checkRealizations(*source, *ordered, {cost, 0});
        if (checked.status == finite::VerificationStatus::Verified)
          break;
        require(checked.status ==
                        finite::VerificationStatus::RequiredCapacity &&
                    checked.detail == "finite reader work",
                "required reader exhaustion became a mismatch");
      }
      require(cost > 1 && cost < 1000, "missing ordered reader boundary");
      std::string diagnostic;
      ScopedDiagnosticHandler capture(&context, [&](Diagnostic &d) {
        diagnostic += d.str();
        return success();
      });
      require(failed(finite::realizeLocalsWithLimits(
                  *source, {}, nullptr, mathematical::mathematicalRecipes(),
                  {cost - 1, 1})) &&
                  same(*source, *original) &&
                  namesIdentifier(diagnostic, "finite-verification-capacity") &&
                  diagnostic.find("finite reader work") != std::string::npos,
              "required refusal published a partial source or lost its budget");
      llvm::outs() << name << " ordered reader work: " << cost << '\n';
    });
  }
  cases.run("ordinary valid formula reaches independent term depth limit", [&] {
    auto source = fixture(context, "collect");
    auto candidate = clone(*source);
    require(succeeded(finite::realizeLocals(*candidate)),
            "initial collect realization failed");
    extendProduct(function(*source, "square"), ring::Limits::depth);
    extendProduct(function(*candidate, "square"), ring::Limits::depth);
    extendProduct(function(*candidate, "collect"), ring::Limits::depth);
    require(succeeded(verify(*source)) && succeeded(verify(*candidate)),
            "deep equivalent formulas were not admitted");
    uint64_t work = 100000;
    mathematical::ComparisonCapacity capacity;
    require(failed(compare(*source, *candidate, "collect", work, capacity)) &&
                work > 0 && capacity == mathematical::ComparisonCapacity::Depth,
            "term depth failure was conflated with work or mismatch");
    auto checked = finite::checkRealizations(*source, *candidate);
    require(checked.status == finite::VerificationStatus::OptionalCapacity &&
                checked.detail == "finite comparison term depth",
            "depth exhaustion did not reach the transaction boundary");
    auto ordered = clone(*source);
    require(
        succeeded(finite::realizeLocals(*ordered, {false, false})) &&
            succeeded(finite::verifyRealizations(*source, *ordered)),
        "admitted deep formula lost its independently checked ordered path");
  });
  return cases.result();
}
