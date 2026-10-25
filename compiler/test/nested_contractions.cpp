#include "../lib/Transforms/AlgorithmSupport.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/detail/Builders.h"
#include "zkc/Transforms/Finite.h"
#include "zkc/Transforms/NestedContractions.h"
#include <fstream>
#include <sstream>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
using State = protocol::AlgorithmExpansionState;
using Access = protocol::detail::AlgorithmStateAccess;

std::string fixture() {
  std::ifstream input(std::string(ZKC_FINITE_FIXTURES) + "/nested-matrix.mlir");
  require(bool(input), "missing nested matrix fixture");
  std::ostringstream result;
  result << input.rdbuf();
  return result.str();
}
std::string replace(std::string text, StringRef from, StringRef to) {
  auto position = text.find(from.str());
  require(position != std::string::npos, "fixture edit missing");
  text.replace(position, from.size(), to.str());
  return text;
}
OwningOpRef<ModuleOp> clone(ModuleOp source) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(source->clone()));
}
Operation *lookup(ModuleOp module, StringRef name) {
  return SymbolTable::lookupSymbolIn(&module.getBody()->front(), name);
}
Operation *findKernel(Operation *root, StringRef contract) {
  Operation *found = nullptr;
  root->walk([&](Operation *operation) {
    if (!operation->hasAttr("binding"))
      return;
    auto binding = protocol::operationBinding(operation);
    if (!binding) {
      consumeError(binding.takeError());
      return;
    }
    if (binding->application.contract == contract && !found)
      found = operation;
  });
  require(found, "missing candidate kernel " + contract);
  return found;
}
local::FuncOp outer(ModuleOp module) {
  auto function = dyn_cast_or_null<local::FuncOp>(lookup(module, "all_rows"));
  require(bool(function), "collection was not replaced");
  return function;
}
void refusesLifecycle(MLIRContext &context,
                      llvm::function_ref<LogicalResult()> action) {
  bool named = false;
  ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
    for (const auto &refusal : diagnostics::refusals(diagnostic))
      named |= refusal.code == "nested-contraction-correspondence";
    return success();
  });
  require(failed(action()), "invalid nested preparation state accepted");
  require(named, "missing nested lifecycle refusal identifier");
}
void checkStructure(ModuleOp source, ModuleOp candidate, bool columns) {
  auto function = outer(candidate);
  unsigned matvecs = 0, loops = 0, scalar = 0;
  function.walk([&](Operation *op) {
    loops += isa<local::LocalForOp>(op);
    auto name = op->getName().getStringRef();
    matvecs +=
        name == protocol::boundOperationName("matrix.mul_vector") ||
        name == protocol::boundOperationName("matrix.transpose_mul_vector");
    scalar += name == protocol::boundOperationName("matrix.row_dot") ||
              name == protocol::boundOperationName("matrix.column_dot");
  });
  require(
      matvecs == 1 && !loops && !scalar,
      "whole collection requires exactly one matvec and no loop/contraction");
  auto *bulk = findKernel(function, columns ? "matrix.transpose_mul_vector"
                                            : "matrix.mul_vector");
  auto branch = bulk->getParentOfType<local::LocalIfOp>();
  require(bool(branch), "matvec was speculated outside outer admission");
  require(bulk->getParentRegion() == &branch->getRegion(0),
          "matvec not in nonempty branch");
  auto &empty = branch->getRegion(1).front();
  require(std::distance(empty.begin(), empty.end()) == 2 &&
              empty.front().getName().getStringRef() ==
                  protocol::boundOperationName("vector.empty"),
          "empty outer executes inner admission");
  require(isa<local::FiniteFoldOp>(lookup(candidate, "inner")),
          "inner declaration was prematurely lowered");
  for (StringRef name : {"body", "step", "work", "inner", "outer_domain",
                         "inner_domain", "main"})
    require(OperationEquivalence::isEquivalentTo(
                lookup(source, name), lookup(candidate, name),
                OperationEquivalence::IgnoreLocations),
            "surrounding definition changed " + name);
  require(succeeded(nested::verifyFiniteCollections(source, candidate)),
          "independent collection correspondence failed");
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler quiet(&context,
                                [](Diagnostic &) { return success(); });
  Cases cases;
  auto source = parseSourceString<ModuleOp>(fixture(), &context);
  require(bool(source), "source fixture refused");
  for (bool columns : {false, true})
    cases.run(columns ? "all columns" : "all rows", [&] {
      auto text = columns ? replace(replace(fixture(), "domain_matrix_row",
                                            "domain_matrix_column"),
                                    "axis=0:i64", "axis=1:i64")
                          : fixture();
      auto original = parseSourceString<ModuleOp>(text, &context);
      require(bool(original), "oriented fixture refused");
      auto candidate = clone(*original);
      require(succeeded(nested::rewriteFiniteCollections(*candidate)),
              "nested rewrite failed");
      checkStructure(*original, *candidate, columns);
      auto accepted = clone(*candidate);
      require(succeeded(finite::realizeLocals(*candidate)),
              "remaining inner realization failed");
      require(succeeded(finite::verifyRealizations(*accepted, *candidate)),
              "ordinary finite stage lost accepted nested computation");
    });
  for (bool reverseSum : {false, true})
    for (bool reverseProduct : {false, true})
      cases.run(
          llvm::Twine("commutative callback ") +
              (reverseSum ? "sum/" : "state/") +
              (reverseProduct ? "vector" : "matrix"),
          [&] {
            auto original = clone(*source);
            auto function = cast<local::FuncOp>(lookup(*original, "step"));
            auto &product = function.getBody().front().front();
            auto &sum = *product.getNextNode();
            for (auto entry : {std::make_pair(reverseSum, &sum),
                               std::make_pair(reverseProduct, &product)})
              if (entry.first) {
                Value first = entry.second->getOperand(0);
                entry.second->setOperand(0, entry.second->getOperand(1));
                entry.second->setOperand(1, first);
              }
            auto candidate = clone(*original);
            require(succeeded(nested::rewriteFiniteCollections(*candidate)),
                    "commutative callback rewrite failed");
            checkStructure(*original, *candidate, false);
          });
  cases.run("disabled family is exact identity", [&] {
    auto candidate = clone(*source);
    require(
        succeeded(nested::rewriteFiniteCollections(*candidate, {false, false})),
        "disabled rewrite failed");
    require(OperationEquivalence::isEquivalentTo(
                source->getOperation(), candidate->getOperation(),
                OperationEquivalence::IgnoreLocations),
            "disabled policy mutated source");
    require(succeeded(nested::verifyFiniteCollections(*source, *candidate)),
            "identity correspondence failed");
  });
  for (StringRef seed : {"0", "19"})
    cases.run("uniform constant seed " + seed, [&] {
      auto text = replace(
          fixture(), "   %out = local.apply @inner(",
          ("   %constant = \"algebra.exec.field_constant\"() "
           "{binding=@constant,parameters=[\"" +
           seed + "\"],site=\"seed\"} : ()->!F\n   %out = local.apply @inner(")
              .str());
      text = replace(text, "@inner(%m,%r,%xs,%ignored,%seed)",
                     "@inner(%m,%r,%xs,%ignored,%constant)");
      auto original = parseSourceString<ModuleOp>(text, &context);
      require(bool(original), "constant seed fixture refused");
      auto candidate = clone(*original);
      require(succeeded(nested::rewriteFiniteCollections(*candidate)),
              "constant seed rewrite failed");
      checkStructure(*original, *candidate, false);
      auto *constant = findKernel(outer(*candidate), "field.constant");
      Builder builder(&context);
      constant->setAttr("parameters",
                        builder.getArrayAttr({builder.getStringAttr("23")}));
      require(failed(nested::verifyFiniteCollections(*original, *candidate)),
              "changed uniform constant seed accepted");
    });
  auto accepted = clone(*source);
  require(succeeded(nested::rewriteFiniteCollections(*accepted)),
          "baseline rewrite failed");
  auto mutation = [&](StringRef name,
                      llvm::function_ref<void(ModuleOp)> change) {
    cases.run(name, [&] {
      SmallVector<std::string> codes;
      ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
        for (auto &refusal : diagnostics::refusals(diagnostic))
          codes.push_back(refusal.code);
        return success();
      });
      auto candidate = clone(*accepted);
      change(*candidate);
      require(failed(nested::verifyFiniteCollections(*source, *candidate)),
              "mutated candidate accepted");
      require(llvm::is_contained(
                  codes, std::string("nested-contraction-correspondence")),
              "missing nested correspondence refusal identifier");
    });
  };
  mutation("wrong matrix", [&](ModuleOp candidate) {
    auto *op = findKernel(outer(candidate), "matrix.mul_vector");
    op->setOperand(0, op->getBlock()->getArgument(3));
  });
  mutation("wrong vector", [&](ModuleOp candidate) {
    auto *op = findKernel(outer(candidate), "matrix.mul_vector");
    op->setOperand(1, op->getBlock()->getArgument(4));
  });
  mutation("wrong seed capture", [&](ModuleOp candidate) {
    auto *op = findKernel(outer(candidate), "vector.fill");
    op->setOperand(0, op->getBlock()->getArgument(6));
  });
  mutation("wrong capture at branch", [&](ModuleOp candidate) {
    auto *op = findKernel(outer(candidate), "matrix.mul_vector");
    auto branch = op->getParentOfType<local::LocalIfOp>();
    branch->setOperand(2, outer(candidate).getArgument(4));
  });
  mutation("wrong orientation", [&](ModuleOp candidate) {
    auto *op = findKernel(outer(candidate), "matrix.dimension");
    Builder builder(&context);
    op->setAttr("parameters",
                builder.getArrayAttr({builder.getStringAttr("1")}));
  });
  mutation("wrong matvec orientation", [&](ModuleOp candidate) {
    auto *op = findKernel(outer(candidate), "matrix.mul_vector");
    auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    auto *binding = lookup(candidate, reference.getValue());
    binding->setAttr("contract",
                     StringAttr::get(&context, "matrix.transpose_mul_vector"));
    OperationState state(op->getLoc(), protocol::boundOperationName(
                                           "matrix.transpose_mul_vector"));
    state.addOperands(op->getOperands());
    state.addTypes(op->getResultTypes());
    state.addAttributes(op->getAttrs());
    OpBuilder builder(op);
    auto *replacement = builder.create(state);
    op->getResult(0).replaceAllUsesWith(replacement->getResult(0));
    op->erase();
    require(succeeded(verify(candidate)),
            "orientation mutation must remain valid IR");
  });
  mutation("strict zip guard order", [&](ModuleOp candidate) {
    SmallVector<Operation *> guards;
    outer(candidate).walk([&](local::RequireOp op) { guards.push_back(op); });
    require(guards.size() == 3, "expected row admission and two zip guards");
    Value first = guards[1]->getOperand(0);
    // Move the second comparison earlier so both swapped guards remain valid.
    auto *second = guards[2]->getOperand(0).getDefiningOp();
    second->moveBefore(guards[1]);
    guards[1]->setOperand(0, guards[2]->getOperand(0));
    guards[2]->setOperand(0, first);
    require(succeeded(verify(candidate)),
            "reordered guard mutation must remain valid IR");
  });
  mutation("missing ignored strict zip guard", [&](ModuleOp candidate) {
    auto *first = findKernel(outer(candidate), "control.require");
    Operation *last = first;
    outer(candidate).walk([&](local::RequireOp op) { last = op; });
    last->erase();
  });
  mutation("changed inner guard identity", [&](ModuleOp candidate) {
    findKernel(outer(candidate), "control.require")
        ->setAttr("site", StringAttr::get(&context, "changed_guard"));
  });
  mutation("changed inner guard location", [&](ModuleOp candidate) {
    findKernel(outer(candidate), "control.require")
        ->setLoc(FileLineColLoc::get(&context, "wrong-fold.zkc", 9, 2));
  });
  mutation("inner admission moved before empty outer branch",
           [&](ModuleOp candidate) {
             auto *op = findKernel(outer(candidate), "matrix.mul_vector");
             auto branch = op->getParentOfType<local::LocalIfOp>();
             auto &block = branch->getRegion(0).front();
             auto *first = &block.front();
             require(first->getName().getStringRef() ==
                         protocol::boundOperationName("matrix.dimension"),
                     "unexpected first inner admission");
             auto *comparison = first->getNextNode();
             auto *guard = comparison->getNextNode();
             for (Operation *moved : {first, comparison, guard}) {
               for (OpOperand &operand : moved->getOpOperands()) {
                 auto argument = dyn_cast<BlockArgument>(operand.get());
                 if (argument && argument.getOwner() == &block)
                   operand.set(branch->getOperand(argument.getArgNumber() + 1));
               }
               moved->moveBefore(branch);
             }
             require(succeeded(verify(candidate)),
                     "hoisted guard mutation must remain valid IR");
           });
  mutation("surrounding helper body change", [&](ModuleOp candidate) {
    auto function = cast<local::FuncOp>(lookup(candidate, "step"));
    function.getBody().front().back().setOperand(0, function.getArgument(0));
  });
  mutation("source-domain mapping change", [&](ModuleOp candidate) {
    auto function = cast<local::FuncOp>(lookup(candidate, "body"));
    auto &call = function.getBody().front().front();
    call.setOperand(2, function.getArgument(5));
  });
  mutation("changed surrounding return", [&](ModuleOp candidate) {
    auto function = cast<local::FuncOp>(lookup(candidate, "work"));
    function.getBody().front().back().setOperand(0, function.getArgument(1));
  });
  for (StringRef mapping : {"vector", "seed", "product"})
    cases.run("rereads actual source " + mapping, [&] {
      auto changedSource = clone(*source);
      auto staleCandidate = clone(*accepted);
      for (ModuleOp module : {*changedSource, *staleCandidate}) {
        if (mapping == "product") {
          auto function = cast<local::FuncOp>(lookup(module, "step"));
          function.getBody().front().front().setOperand(
              1, function.getArgument(3));
        } else {
          auto function = cast<local::FuncOp>(lookup(module, "body"));
          auto &call = function.getBody().front().front();
          call.setOperand(mapping == "vector" ? 2 : 4,
                          function.getArgument(mapping == "vector" ? 5 : 7));
        }
      }
      require(succeeded(verify(*changedSource)) &&
                  succeeded(verify(*staleCandidate)),
              "source mutation must retain admitted IR");
      require(failed(nested::verifyFiniteCollections(*changedSource,
                                                     *staleCandidate)),
              "stale computation was accepted after source mapping changed");
    });
  cases.run("same-name replacement and shared helper lifetime", [&] {
    auto original = clone(*source);
    auto *declaration = lookup(*original, "all_rows");
    auto *second = declaration->clone();
    second->setAttr("sym_name", StringAttr::get(&context, "second_collection"));
    declaration->getBlock()->getOperations().insert(declaration->getIterator(),
                                                    second);
    auto candidate = clone(*original);
    require(succeeded(nested::rewriteFiniteCollections(*candidate)),
            "shared helper rewrite failed");
    require(isa<local::FuncOp>(lookup(*candidate, "second_collection")),
            "second collection was not realized");
    require(succeeded(nested::verifyFiniteCollections(*original, *candidate)),
            "two collections failed correspondence");
    require(succeeded(finite::realizeLocals(*candidate)),
            "shared inner declaration lifetime failed");
  });
  for (StringRef implementation : {"field.add", "field.mul"})
    cases.run("explicit implementation fallback " + implementation, [&] {
      auto original = clone(*source);
      auto binding = cast<runtime::BindingOp>(
          lookup(*original, implementation == "field.add" ? "add" : "mul"));
      auto info = protocol::readBinding(binding);
      require(bool(info), "binding unavailable");
      auto chosen = protocol::defaultImplementation(info->application);
      require(bool(chosen), "native implementation unavailable");
      binding->setAttr("implementation", StringAttr::get(&context, *chosen));
      require(succeeded(verify(*original)), "explicit binding refused");
      auto candidate = clone(*original);
      require(succeeded(nested::rewriteFiniteCollections(*candidate)),
              "explicit fallback failed");
      require(OperationEquivalence::isEquivalentTo(
                  original->getOperation(), candidate->getOperation(),
                  OperationEquivalence::IgnoreLocations),
              "explicit binding was replaced");
    });
  cases.run("opaque callback fallback", [&] {
    auto original = clone(*source);
    auto function = cast<local::FuncOp>(lookup(*original, "step"));
    function.getBody().front().back().setOperand(0, function.getArgument(0));
    auto candidate = clone(*original);
    require(succeeded(nested::rewriteFiniteCollections(*candidate)),
            "unsupported callback fallback failed");
    require(OperationEquivalence::isEquivalentTo(
                original->getOperation(), candidate->getOperation(),
                OperationEquivalence::IgnoreLocations),
            "unsupported callback was replaced");
  });
  auto retained = clone(*source);
  State initialState, retainedState;
  require(succeeded(protocol::expandAlgorithms(
              *retained, protocol::AlgorithmExpansionPhase::RetainMaps,
              retainedState)),
          "lifecycle source retention failed");
  auto finished = clone(*retained);
  State finishedState = retainedState;
  require(succeeded(finite::realizeLocals(*finished)) &&
              succeeded(protocol::expandAlgorithms(
                  *finished, protocol::AlgorithmExpansionPhase::Finish,
                  finishedState)),
          "lifecycle source completion failed");
  for (bool afterFinish : {false, true}) {
    StringRef lifecycle = afterFinish ? "finished" : "missing retain";
    const State &invalidState = afterFinish ? finishedState : initialState;
    for (bool enabled : {false, true})
      cases.run(
          llvm::Twine("rewrite refuses ") + lifecycle +
              (enabled ? " with enabled policy" : " with disabled policy"),
          [&] {
            auto original = clone(afterFinish ? *finished : *source);
            auto candidate = clone(*original);
            State state = invalidState;
            refusesLifecycle(context, [&] {
              return nested::rewriteFiniteCollections(*candidate, state,
                                                      {enabled, false});
            });
            require(OperationEquivalence::isEquivalentTo(
                        original->getOperation(), candidate->getOperation(),
                        OperationEquivalence::Flags{}) &&
                        &Access::get(state) == &Access::get(invalidState),
                    "invalid lifecycle rewrite changed IR or state");
          });
    for (StringRef invalid : {"source", "candidate", "both"})
      cases.run(llvm::Twine("verifier refuses ") + lifecycle + " in " + invalid,
                [&] {
                  auto original = clone(*retained);
                  auto candidate = clone(*retained);
                  const State &beforeSourceState =
                      invalid == "candidate" ? retainedState : invalidState;
                  const State &beforeCandidateState =
                      invalid == "source" ? retainedState : invalidState;
                  State sourceState = beforeSourceState;
                  State candidateState = beforeCandidateState;
                  refusesLifecycle(context, [&] {
                    return nested::verifyFiniteCollections(
                        *original, *candidate, sourceState, candidateState);
                  });
                  for (ModuleOp module : {*original, *candidate})
                    require(OperationEquivalence::isEquivalentTo(
                                retained->getOperation(), module.getOperation(),
                                OperationEquivalence::Flags{}),
                            "invalid lifecycle verifier changed IR");
                  require(&Access::get(sourceState) ==
                                  &Access::get(beforeSourceState) &&
                              &Access::get(candidateState) ==
                                  &Access::get(beforeCandidateState),
                          "invalid lifecycle verifier changed expansion state");
                });
  }
  cases.run("disabled staged family preserves retained state", [&] {
    auto candidate = clone(*retained);
    State state = retainedState;
    require(succeeded(nested::rewriteFiniteCollections(*candidate, state,
                                                       {false, false})) &&
                succeeded(nested::verifyFiniteCollections(
                    *retained, *candidate, retainedState, state)),
            "disabled staged rewrite or identity correspondence failed");
    require(OperationEquivalence::isEquivalentTo(
                retained->getOperation(), candidate->getOperation(),
                OperationEquivalence::Flags{}) &&
                &Access::get(state) == &Access::get(retainedState),
            "disabled staged rewrite changed IR or state");
  });
  cases.run("nested origin budget refusal is transactional", [&] {
    auto original = clone(*retained);
    State state = retainedState;
    auto record = Access::get(state);
    record.originBytes = 0;
    Access::set(state, record);
    const auto *beforeRecord = &Access::get(state);
    auto candidate = clone(*original);
    bool named = false;
    ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
      for (const auto &refusal : diagnostics::refusals(diagnostic))
        named |= refusal.code == "algorithm-origin-limit";
      return success();
    });
    require(failed(nested::rewriteFiniteCollections(*candidate, state)) &&
                named,
            "nested guard naming did not honor the cumulative origin limit");
    require(OperationEquivalence::isEquivalentTo(
                original->getOperation(), candidate->getOperation(),
                OperationEquivalence::Flags{}) &&
                &Access::get(state) == beforeRecord,
            "failed nested rewrite published candidate IR or origins");
  });
  for (bool hashed : {false, true})
    cases.run(
        hashed ? "hashed nested guard provenance through Finish"
               : "nested guard provenance through Finish",
        [&] {
          auto original = clone(*source);
          auto innerLocation =
              FileLineColLoc::get(&context, "inner-fold.zkc", 17, 3);
          lookup(*original, "inner")->setLoc(innerLocation);
          lookup(*original, "all_rows")
              ->setLoc(FileLineColLoc::get(&context, "outer-fold.zkc", 41, 5));
          std::string innerSite = hashed ? std::string(120, 'i') : "inner";
          auto body = cast<local::FuncOp>(lookup(*original, "body"));
          body.getBody().front().front().setAttr(
              "site", StringAttr::get(&context, innerSite));
          State beforeState;
          require(succeeded(protocol::expandAlgorithms(
                      *original, protocol::AlgorithmExpansionPhase::RetainMaps,
                      beforeState)),
                  "retained nested source failed");
          auto candidate = clone(*original);
          State state = beforeState;
          require(
              succeeded(nested::rewriteFiniteCollections(*candidate, state)),
              "nested provenance rewrite failed");
          require(succeeded(nested::verifyFiniteCollections(
                      *original, *candidate, beforeState, state)),
                  "nested provenance correspondence failed");

          // Compare leaves and locations against ordinary realization of the
          // actual retained inner declaration, independently of the nested
          // emitter.
          auto ordinary = clone(*original);
          require(succeeded(finite::realizeLocals(*ordinary, {false, false})),
                  "ordered finite origin reference failed");
          SmallVector<Operation *> referenceGuards, guards;
          lookup(*ordinary, "inner")->walk([&](local::RequireOp op) {
            referenceGuards.push_back(op);
          });
          outer(*candidate).walk([&](local::RequireOp op) {
            guards.push_back(op);
          });
          require(guards.size() == 3 && guards.size() == referenceGuards.size(),
                  "unexpected inner guard inventory");
          auto record = Access::get(state);
          for (auto [guard, reference] : llvm::zip(guards, referenceGuards)) {
            auto site = protocol::attr(guard, "site");
            auto origin =
                protocol::detail::occurrence(record, "all_rows", site);
            require(origin && origin->definition == "inner" &&
                        origin->declaration == "inner" &&
                        origin->originalSite ==
                            protocol::attr(reference, "site") &&
                        origin->path ==
                            protocol::Assignments{{innerSite, "inner"}} &&
                        guard->getLoc() == reference->getLoc() &&
                        guard->getLoc() == innerLocation,
                    "nested guard lost the actual inner admission origin");
            require(site.starts_with("lc_h_") == hashed,
                    "unexpected guard name encoding");
          }
          for (StringRef mutation : {"leaf", "path", "definition", "missing"}) {
            auto changed = record;
            auto key = protocol::detail::OccurrenceKey{
                "all_rows", protocol::attr(guards.front(), "site").str()};
            if (mutation == "missing")
              changed.occurrences.erase(key);
            else {
              auto &origin = changed.occurrences.at(key);
              if (mutation == "leaf")
                origin.originalSite = "finite_999";
              else if (mutation == "path")
                origin.path.front().first = "wrong_call";
              else
                origin.definition = "all_rows";
            }
            State changedState;
            Access::set(changedState, std::move(changed));
            require(failed(nested::verifyFiniteCollections(
                        *original, *candidate, beforeState, changedState)),
                    "changed nested guard record accepted: " + mutation);
          }
          require(succeeded(finite::realizeLocals(*candidate)),
                  "remaining finite realization failed");
          auto beforeFinish = clone(*candidate);
          State finishInput = state;
          std::vector<protocol::AlgorithmOrigin> origins;
          require(succeeded(protocol::expandAlgorithms(
                      *candidate, protocol::AlgorithmExpansionPhase::Finish,
                      state, &origins)),
                  "Finish lost nested guard records");
          auto *workGuard =
              findKernel(lookup(*candidate, "work"), "control.require");
          require(
              workGuard->getLoc() == innerLocation &&
                  llvm::any_of(origins,
                               [&](const auto &origin) {
                                 return origin.function == "work" &&
                                        origin.site ==
                                            protocol::attr(workGuard, "site") &&
                                        origin.definition == "inner" &&
                                        origin.originalSite == "finite_2" &&
                                        origin.path ==
                                            protocol::Assignments{
                                                {"collect", "all_rows"},
                                                {innerSite, "inner"}};
                               }),
              "Finish replaced the original guard path with an encoded leaf");
          workGuard->setAttr("site",
                             StringAttr::get(&context, "changed_finish"));
          require(failed(protocol::verifyStagedAlgorithmExpansionPreserved(
                      *beforeFinish, *candidate,
                      protocol::AlgorithmExpansionPhase::Finish, finishInput,
                      state)),
                  "Finish accepted a changed nested guard site");
        });
  return cases.result();
}
