#include "mlir/IR/OperationSupport.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/NestedContractions.h"
#include <fstream>
#include <sstream>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
std::string fixture() {
  std::ifstream stream(ZKC_NESTED_SOURCE);
  require(bool(stream), "missing nested source fixture");
  std::ostringstream result;
  result << stream.rdbuf();
  return result.str();
}
std::string replace(std::string text, StringRef from, StringRef to) {
  size_t position = 0;
  require(text.find(from.str()) != std::string::npos, "missing fixture edit");
  while ((position = text.find(from.str(), position)) != std::string::npos) {
    text.replace(position, from.size(), to.str());
    position += to.size();
  }
  return text;
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  for (bool columns : {false, true})
    for (StringRef seed : {"seed", "0", "19"})
      cases.run(llvm::Twine(columns ? "columns " : "rows ") + seed, [&] {
        std::string text =
            replace(fixture(), ",seed,fn", ("," + seed + ",fn").str());
        if (columns)
          text = replace(replace(text, "indices.rows", "indices.columns"),
                         "matrix.row", "matrix.column");
        auto captured =
            take(language::capture({{"sample", text, "nested-matrix.zkc"}}));
        auto checked = take(language::analyze(captured).checkedProject());
        auto entry = take(language::closeEntry(checked, "sample::Demo"));
        auto original = take(language::prepareOriginal(entry));
        auto prepared = parseSourceString<ModuleOp>(original.bytes(), &context);
        require(bool(prepared), "original source IR refused");
        require(succeeded(mathematical::expandMathRealizations(*prepared)),
                "math helper realization failed");
        protocol::AlgorithmExpansionState expansion;
        require(succeeded(protocol::expandAlgorithms(
                    *prepared, protocol::AlgorithmExpansionPhase::RetainMaps,
                    expansion)),
                "transparent helper expansion failed");
        OwningOpRef<ModuleOp> before(cast<ModuleOp>((*prepared)->clone()));
        require(succeeded(nested::rewriteFiniteCollections(*prepared)),
                "nested source rewrite failed");
        require(succeeded(nested::verifyFiniteCollections(*before, *prepared)),
                "nested source comparison failed");
        unsigned matvecs = 0, loops = 0;
        prepared->walk([&](Operation *op) {
          auto name = op->getName().getStringRef();
          matvecs += name == "algebra.exec.matrix_mul_vector" ||
                     name == "algebra.exec.matrix_transpose_mul_vector";
          loops += isa<local::LocalForOp>(op);
        });
        require(matvecs == 1 && !loops,
                "source spelling missed whole collection strategy");
        // Exercise the parent preparation slot and the compiler's independent
        // composed correspondence, including the retained original closure.
        take(language::compileEntry(original));
        take(language::compileEntry(original, {false, false}));
      });
  cases.run("effectful callback keeps ordered fallback", [&] {
    auto text = replace(fixture(), "=>s+a*b", "=>{require true;s+a*b}");
    auto captured =
        take(language::capture({{"sample", text, "nested-effect.zkc"}}));
    auto checked = take(language::analyze(captured).checkedProject());
    auto entry = take(language::closeEntry(checked, "sample::Demo"));
    auto original = take(language::prepareOriginal(entry));
    auto prepared = parseSourceString<ModuleOp>(original.bytes(), &context);
    require(bool(prepared), "effectful source refused");
    require(succeeded(mathematical::expandMathRealizations(*prepared)),
            "math realization failed");
    protocol::AlgorithmExpansionState expansion;
    require(succeeded(protocol::expandAlgorithms(
                *prepared, protocol::AlgorithmExpansionPhase::RetainMaps,
                expansion)),
            "helper expansion failed");
    OwningOpRef<ModuleOp> before(cast<ModuleOp>((*prepared)->clone()));
    require(succeeded(nested::rewriteFiniteCollections(*prepared)),
            "effectful fallback failed");
    require(OperationEquivalence::isEquivalentTo(
                before->getOperation(), prepared->getOperation(),
                OperationEquivalence::IgnoreLocations),
            "effectful source was replaced");
    take(language::compileEntry(original));
  });
  return cases.result();
}
