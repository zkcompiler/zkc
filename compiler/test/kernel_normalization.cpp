#include "../lib/Transforms/HelperNormalization.h"
#include "../lib/Transforms/Kernel/NormalizationVerification.h"
#include "../lib/Transforms/Kernel/Support.h"
#include "../lib/Transforms/MathematicalSupport.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Dialect/IR.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/Support/MemoryBuffer.h"
#include <functional>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
OwningOpRef<mlir::ModuleOp> fixture(MLIRContext &context, StringRef name) {
  auto buffer = llvm::MemoryBuffer::getFile(
      (Twine(ZKC_NORMALIZATION_FIXTURES) + "/" + name + ".mlir").str());
  require(bool(buffer), "normalization fixture unavailable");
  auto result =
      parseSourceString<mlir::ModuleOp>((*buffer)->getBuffer(), &context);
  require(bool(result), "normalization fixture refused");
  return result;
}
protocol_ir::ProtocolModuleOp unit(mlir::ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
func::FuncOp function(mlir::ModuleOp module, StringRef name) {
  auto result = SymbolTable(unit(module)).lookup<func::FuncOp>(name);
  require(bool(result), "missing normalization helper");
  return result;
}
OwningOpRef<mlir::ModuleOp> makeKernelUnit(mlir::ModuleOp module,
                                           StringRef entryName,
                                           ArrayRef<StringRef> dependencies) {
  OpBuilder builder(module.getContext());
  OwningOpRef<mlir::ModuleOp> result(
      mlir::ModuleOp::create(builder, module.getLoc(), "numerical"));
  result->getOperation()->setAttr("exec.computation", builder.getUnitAttr());
  builder.setInsertionPointToEnd(result->getBody());
  SymbolTable declarations(unit(module));
  for (auto name : dependencies) {
    auto *dependency = declarations.lookup(name);
    require(bool(dependency), "missing Kernel dependency fixture");
    builder.clone(*dependency);
  }
  auto entry = cast<func::FuncOp>(builder.clone(*function(module, entryName)));
  entry->setAttr("sym_visibility", builder.getStringAttr("public"));
  entry->setAttr("data.preconditions", builder.getArrayAttr({}));
  return result;
}
OwningOpRef<func::FuncOp> copy(func::FuncOp source) {
  return OwningOpRef<func::FuncOp>(cast<func::FuncOp>(source->clone()));
}
SmallVector<Operation *> operations(func::FuncOp function) {
  SmallVector<Operation *> result;
  for (auto &op : function.front().without_terminator())
    result.push_back(&op);
  return result;
}
void provenanceRefusal(MLIRContext &context,
                       llvm::function_ref<LogicalResult()> action,
                       StringRef code = "kernel-normalization-provenance") {
  std::string diagnostic;
  ScopedDiagnosticHandler handler(&context, [&](Diagnostic &value) {
    diagnostic += value.str();
    return success();
  });
  require(failed(action()), "invalid normalization provenance was accepted");
  require(namesIdentifier(diagnostic, code),
          "unexpected refusal: " + diagnostic);
}
OwningOpRef<func::FuncOp> normalize(func::FuncOp source) {
  auto result = copy(source);
  uint64_t work = 100000;
  require(succeeded(poly::eliminatePolynomials(result->front(), work)),
          "polynomial fixture did not normalize");
  require(succeeded(verify(*result)), "normalization is malformed");
  return result;
}
} // namespace

int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();

  cases.run("owned Kernel normalization preserves metadata and origins", [&] {
    auto module = fixture(context, "provenance");
    auto source = makeKernelUnit(*module, "mixed_raw", {"mixed_leaf"});
    auto entry = mathematical::getComputationEntry(*source);
    auto helper = SymbolTable(*source).lookup<func::FuncOp>("mixed_leaf");
    require(succeeded(verify(*source)) &&
                succeeded(mathematical::verifyComputationUnit(*source)),
            "computation source is malformed");
    uint64_t remaining = 1000000;
    llvm::DenseSet<Operation *> generated;
    auto candidate = kernel::normalizeUnit(*source, remaining, generated);
    require(bool(candidate) && succeeded(verify(*candidate)) &&
                succeeded(mathematical::verifyComputationUnit(*candidate)),
            "owned Kernel normalization refused");
    auto normalized = mathematical::getComputationEntry(*candidate);
    require((*source)->getAttrDictionary() ==
                    (*candidate)->getAttrDictionary() &&
                entry->getAttrDictionary() == normalized->getAttrDictionary(),
            "normalization changed unit or entry declaration metadata");
    auto retained = SymbolTable(*candidate).lookup<func::FuncOp>("mixed_leaf");
    require(retained &&
                OperationEquivalence::isEquivalentTo(
                    helper, retained, OperationEquivalence::IgnoreLocations),
            "normalization changed an original helper dependency");
    auto returned = cast<func::ReturnOp>(normalized.front().back());
    auto *first = returned.getOperand(0).getDefiningOp();
    auto *second = returned.getOperand(2).getDefiningOp();
    require(first && second && first != second,
            "normalization lost distinct concrete result coordinates");
    require(!generated.empty() && !generated.contains(first) &&
                !generated.contains(second) &&
                generated.contains(returned.getOperand(1).getDefiningOp()),
            "normalization confused concrete and polynomial origins");
    for (auto *op : generated)
      require(op->getBlock() == &normalized.front(),
              "generated identity does not belong to the returned Kernel");
    for (auto &op : normalized.front().without_terminator())
      require(!isa<func::CallOp>(op) &&
                  op.getName().getDialectNamespace() != "poly",
              "normalized entry retained unexpanded mathematics");
    mathematical::HelperNormalizationChecker checker(*source);
    require(succeeded(checker.check(entry, normalized.front())),
            "direct Kernel copy lost checked mathematical meaning");
  });

  cases.run(
      "owned Kernel normalization retains finite dependency identities", [&] {
        auto module = fixture(context, "callback");
        auto source = makeKernelUnit(*module, "fold", {"items", "step"});
        require(succeeded(verify(*source)) &&
                    succeeded(mathematical::verifyComputationUnit(*source)),
                "computation source is malformed");
        uint64_t remaining = 1000000;
        llvm::DenseSet<Operation *> generated;
        auto candidate = kernel::normalizeUnit(*source, remaining, generated);
        require(bool(candidate) && succeeded(verify(*candidate)) &&
                    succeeded(mathematical::verifyComputationUnit(*candidate)),
                "finite Kernel normalization refused");
        SymbolTable original(*source), normalized(*candidate);
        auto *domain = normalized.lookup("items");
        require(domain && OperationEquivalence::isEquivalentTo(
                              original.lookup("items"), domain,
                              OperationEquivalence::IgnoreLocations),
                "finite domain dependency changed");
        auto step = normalized.lookup<func::FuncOp>("step");
        require(step && step->getAttrDictionary() ==
                            original.lookup("step")->getAttrDictionary(),
                "finite callback lost its signature or preconditions");
        for (auto &op : step.front().without_terminator())
          require(op.getName().getDialectNamespace() != "poly",
                  "finite callback was not normalized");
        auto entry = mathematical::getComputationEntry(*candidate);
        require(entry.front().front().getAttrDictionary() ==
                        mathematical::getComputationEntry(*source)
                            .front()
                            .front()
                            .getAttrDictionary() &&
                    generated.empty(),
                "finite dependency symbols or entry origins changed");
      });

  cases.run("owned Kernel copy exhaustion is cumulative and read-only", [&] {
    auto module = fixture(context, "provenance");
    auto source = makeKernelUnit(*module, "mixed_raw", {"mixed_leaf"});
    uint64_t remaining = 1000000;
    llvm::DenseSet<Operation *> generated;
    auto candidate = kernel::normalizeUnit(*source, remaining, generated);
    require(bool(candidate), "reference normalization refused");
    uint64_t spent = 1000000 - remaining;
    require(spent > 1, "normalization did not charge copying");
    std::string before, after;
    llvm::raw_string_ostream(before) << *source;
    for (uint64_t allowance : {uint64_t(0), spent - 1}) {
      llvm::DenseSet<Operation *> evidence{source->getOperation()};
      remaining = allowance;
      auto refused = kernel::normalizeUnit(*source, remaining, evidence);
      require(!refused, "exhausted normalization was accepted");
      require(evidence.size() == 1 && evidence.contains(source->getOperation()),
              "refused normalization published destroyed identities");
      require(!allowance || remaining < allowance,
              "refused normalization refunded spent copying work");
    }
    llvm::raw_string_ostream(after) << *source;
    require(before == after, "refused normalization mutated its source");
  });

  cases.run("handwritten helper substitution includes every invocation", [&] {
    auto module = fixture(context, "provenance");
    auto expanded = function(*module, "expanded");
    kernel::NormalizationProvenanceChecker checker(unit(*module));
    require(succeeded(checker.checkExpansion(function(*module, "raw"),
                                             expanded.front())),
            "exact positional helper substitution refused");
    require(succeeded(checker.checkNormalization(expanded, expanded.front())),
            "unchanged concrete work refused");
  });

  cases.run(
      "mixed helper results retain their exact concrete coordinates", [&] {
        auto module = fixture(context, "provenance");
        auto expanded = function(*module, "mixed_expanded");
        auto candidate = normalize(expanded);
        kernel::NormalizationProvenanceChecker checker(unit(*module));
        require(succeeded(checker.checkExpansion(function(*module, "mixed_raw"),
                                                 expanded.front())),
                "mixed positional helper expansion refused");
        require(
            succeeded(checker.checkNormalization(expanded, candidate->front())),
            "mixed helper normalization refused");
        auto ops = operations(*candidate);
        candidate->front().back().setOperand(2, ops[1]->getResult(0));
        mathematical::HelperNormalizationChecker values(unit(*module));
        require(
            succeeded(values.check(expanded, candidate->front())),
            "mixed control does not expose equal-valued concrete coordinates");
        provenanceRefusal(context, [&] {
          return checker.checkNormalization(expanded, candidate->front());
        });
      });

  struct Mutation {
    StringRef name;
    bool sameMeaning;
    std::function<void(func::FuncOp)> mutate;
  };
  SmallVector<Mutation> mutations{
      {"delete unused concrete multiplication", true,
       [](func::FuncOp candidate) { candidate.front().front().erase(); }},
      {"merge identical concrete occurrences", true,
       [](func::FuncOp candidate) {
         auto ops = operations(candidate);
         ops[2]->getResult(0).replaceAllUsesWith(ops[1]->getResult(0));
         ops[2]->erase();
       }},
      {"replace equal-valued distinct concrete SSA operand", true,
       [](func::FuncOp candidate) {
         auto ops = operations(candidate);
         ops[3]->setOperand(0, ops[1]->getResult(0));
       }},
      {"duplicate helper work", true,
       [](func::FuncOp candidate) {
         OpBuilder builder(&candidate.front().front());
         builder.clone(candidate.front().front());
       }},
      {"change equal-valued return coordinate", true,
       [](func::FuncOp candidate) {
         auto ops = operations(candidate);
         candidate.front().back().setOperand(1, ops[5]->getResult(0));
       }},
      {"move concrete work across source cut", true,
       [](func::FuncOp candidate) {
         auto ops = operations(candidate);
         ops[4]->moveBefore(ops[3]);
       }},
      {"permute positional inputs", false,
       [](func::FuncOp candidate) {
         auto ops = operations(candidate);
         ops[0]->setOperand(0, candidate.getArgument(0));
       }},
      {"change concrete occurrence attributes", true,
       [](func::FuncOp candidate) {
         candidate.front().front().setAttr(
             "site", StringAttr::get(candidate.getContext(), "invented"));
       }},
  };
  for (bool expansion : {true, false})
    for (auto &mutation : mutations)
      cases.run(
          (expansion ? "expansion: " : "normalization: ") + mutation.name, [&] {
            auto module = fixture(context, "provenance");
            auto expanded = function(*module, "expanded");
            auto source = expansion ? function(*module, "raw") : expanded;
            auto candidate = copy(expanded);
            mutation.mutate(*candidate);
            require(succeeded(verify(*candidate)),
                    "negative control is malformed");
            if (mutation.sameMeaning) {
              mathematical::HelperNormalizationChecker values(unit(*module));
              require(succeeded(values.check(source, candidate->front())),
                      "negative control does not expose the value-only gap");
            }
            kernel::NormalizationProvenanceChecker checker(unit(*module));
            SmallVector<Operation *> generated{source.getOperation()};
            provenanceRefusal(context, [&] {
              return expansion
                         ? checker.checkExpansion(source, candidate->front())
                         : checker.checkNormalization(
                               source, candidate->front(), &generated);
            });
            require(generated.size() == 1 &&
                        generated.front() == source.getOperation(),
                    "failed checker published generated identities");
          });

  cases.run(
      "handwritten polynomial expansion separates generated identities", [&] {
        auto module = fixture(context, "provenance");
        auto source = function(*module, "polynomial");
        auto candidate = function(*module, "normalized");
        kernel::NormalizationProvenanceChecker checker(unit(*module));
        SmallVector<Operation *> generated;
        require(succeeded(checker.checkNormalization(source, candidate.front(),
                                                     &generated)),
                "supported handwritten polynomial expansion refused");
        auto ops = operations(candidate);
        require(generated == SmallVector<Operation *>({ops[2], ops[3], ops[4]}),
                "generated identity set includes concrete work or omits "
                "polynomial work");
        llvm::DenseSet<Operation *> unique(generated.begin(), generated.end());
        require(unique.size() == generated.size(),
                "one instruction was consumed twice");
      });

  for (StringRef name : {"polynomial", "reconstruct", "cache", "tables",
                         "coefficients", "convolution"})
    cases.run("supported polynomial laws: " + name, [&] {
      auto module = fixture(context, "provenance");
      auto source = function(*module, name);
      auto candidate = normalize(source);
      kernel::NormalizationProvenanceChecker checker(unit(*module));
      require(succeeded(checker.checkNormalization(source, candidate->front())),
              "supported normalizer trace refused");
    });

  cases.run("duplicated helper work cannot reconstruct a formal result", [&] {
    auto module = fixture(context, "provenance");
    auto source = function(*module, "reconstruct");
    auto candidate = copy(function(*module, "reconstructed"));
    auto &ret = candidate->front().back();
    OpBuilder builder(&ret);
    auto *duplicate = builder.clone(candidate->front().front());
    ret.setOperand(0, duplicate->getResult(0));
    require(succeeded(verify(*candidate)),
            "duplicate reconstruction is malformed");
    mathematical::HelperNormalizationChecker values(unit(*module));
    require(succeeded(values.check(source, candidate->front())),
            "duplicate reconstruction does not expose the value-only gap");
    kernel::NormalizationProvenanceChecker checker(unit(*module));
    provenanceRefusal(context, [&] {
      return checker.checkNormalization(source, candidate->front());
    });
  });

  for (StringRef mutation :
       {"missing concrete work", "early polynomial work",
        "duplicate polynomial work", "invented polynomial site",
        "changed polynomial result"})
    cases.run("polynomial authorization: " + mutation, [&] {
      auto module = fixture(context, "provenance");
      auto source = function(*module, "polynomial");
      auto candidate = copy(function(*module, "normalized"));
      auto ops = operations(*candidate);
      if (mutation == "missing concrete work")
        ops[0]->erase();
      else if (mutation == "early polynomial work")
        ops[2]->moveBefore(ops[1]);
      else if (mutation == "duplicate polynomial work") {
        OpBuilder builder(ops[3]);
        builder.clone(*ops[2]);
      } else if (mutation == "invented polynomial site")
        ops[2]->setAttr("site", StringAttr::get(&context, "concrete"));
      else
        candidate->front().back().setOperand(0, ops[3]->getResult(0));
      require(succeeded(verify(*candidate)), "polynomial control is malformed");
      kernel::NormalizationProvenanceChecker checker(unit(*module));
      provenanceRefusal(context, [&] {
        return checker.checkNormalization(source, candidate->front());
      });
    });

  cases.run("ordinary array folding requires its own checked edge", [&] {
    auto module = fixture(context, "provenance");
    auto source = function(*module, "projection");
    auto candidate = copy(source);
    uint64_t work = 1000;
    require(
        succeeded(mathematical::foldArrayProjections(candidate->front(), work)),
        "projection fixture did not fold");
    mathematical::HelperNormalizationChecker values(unit(*module));
    require(succeeded(values.check(source, candidate->front())),
            "folded arrays lost their mathematical meaning");
    kernel::NormalizationProvenanceChecker checker(unit(*module));
    provenanceRefusal(context, [&] {
      return checker.checkNormalization(source, candidate->front());
    });
  });

  for (StringRef mutation :
       {"unchanged", "delete dead multiplication", "replace equal-valued SSA",
        "replace equal-valued polynomial input", "merge occurrences",
        "swap returned state"})
    cases.run("total finite callback: " + mutation, [&] {
      auto module = fixture(context, "callback");
      auto source = function(*module, "step");
      auto candidate = normalize(source);
      kernel::NormalizationProvenanceChecker checker(unit(*module));
      require(succeeded(checker.checkExpansion(source, source.front())),
              "callback exact identity refused");
      auto ops = operations(*candidate);
      if (mutation == "unchanged") {
        require(
            succeeded(checker.checkNormalization(source, candidate->front())),
            "normalized finite callback refused");
        return;
      }
      if (mutation == "delete dead multiplication")
        ops[0]->erase();
      else if (mutation == "replace equal-valued SSA")
        ops[4]->setOperand(1, ops[1]->getResult(0));
      else if (mutation == "replace equal-valued polynomial input")
        ops[5]->setOperand(0, ops[1]->getResult(0));
      else if (mutation == "merge occurrences") {
        ops[2]->getResult(0).replaceAllUsesWith(ops[1]->getResult(0));
        ops[2]->erase();
      } else {
        auto &ret = candidate->front().back();
        Value first = ret.getOperand(0), second = ret.getOperand(1);
        ret.setOperand(0, second);
        ret.setOperand(1, first);
      }
      require(succeeded(verify(*candidate)),
              "finite callback control is malformed");
      if (mutation != "swap returned state") {
        mathematical::HelperNormalizationChecker values(unit(*module));
        require(succeeded(values.check(source, candidate->front())),
                "callback control does not expose the value-only gap");
      }
      provenanceRefusal(context, [&] {
        return checker.checkNormalization(source, candidate->front());
      });
    });

  cases.run(
      "multi-result concrete operation coordinates remain positional", [&] {
        auto module = fixture(context, "callback");
        auto source = function(*module, "fold");
        auto candidate = copy(source);
        kernel::NormalizationProvenanceChecker checker(unit(*module));
        require(
            succeeded(checker.checkNormalization(source, candidate->front())),
            "unchanged concrete finite operation refused");
        auto &ret = candidate->front().back();
        Value first = ret.getOperand(0), second = ret.getOperand(1);
        ret.setOperand(0, second);
        ret.setOperand(1, first);
        provenanceRefusal(context, [&] {
          return checker.checkNormalization(source, candidate->front());
        });
      });

  cases.run("work exhaustion is named, cumulative and read-only", [&] {
    auto module = fixture(context, "provenance");
    auto source = function(*module, "raw");
    auto candidate = function(*module, "expanded");
    std::string before, after;
    llvm::raw_string_ostream(before) << *module;
    kernel::NormalizationProvenanceChecker checker(unit(*module), 200);
    require(succeeded(checker.checkExpansion(source, candidate.front())),
            "first bounded expansion refused");
    provenanceRefusal(
        context,
        [&] { return checker.checkExpansion(source, candidate.front()); },
        "kernel-normalization-limit");
    provenanceRefusal(
        context,
        [&] { return checker.checkExpansion(source, candidate.front()); },
        "kernel-normalization-limit");
    llvm::raw_string_ostream(after) << *module;
    require(before == after, "checker mutated its subjects");
    kernel::NormalizationProvenanceChecker independent(unit(*module));
    require(succeeded(independent.checkExpansion(source, candidate.front())),
            "exhaustion corrupted an independent reader");
  });
  cases.run("total simplification removes only dead concrete work", [&] {
    auto module = fixture(context, "provenance");
    auto source = function(*module, "leaf");
    auto candidate = copy(source);
    candidate->front().front().erase();
    kernel::NormalizationProvenanceChecker checker(unit(*module));
    require(succeeded(checker.checkSimplification(source, candidate->front())),
            "dead total arithmetic refused");
  });
  for (StringRef mutation : {"coalesce", "operand", "extra"})
    cases.run("total simplification refuses " + mutation, [&] {
      auto module = fixture(context, "provenance");
      auto source = function(*module, "leaf");
      auto candidate = copy(source);
      candidate->front().front().erase();
      auto ops = operations(*candidate);
      if (mutation == "coalesce") {
        ops[1]->getResult(0).replaceAllUsesWith(ops[0]->getResult(0));
        ops[1]->erase();
      } else if (mutation == "operand") {
        ops[0]->setOperand(1, ops[0]->getOperand(0));
      } else {
        OpBuilder builder(ops[0]);
        builder.clone(*ops[0]);
      }
      kernel::NormalizationProvenanceChecker checker(unit(*module));
      provenanceRefusal(context, [&] {
        return checker.checkSimplification(source, candidate->front());
      });
    });
  return cases.result();
}
