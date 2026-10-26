#include "../lib/Transforms/ComputationSelection.h"
#include "../lib/Transforms/ScopedCandidate.h"
#include "../lib/Transforms/ScopedNestedContraction.h"
#include "../lib/Transforms/ScopedPreparation.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Finite.h"
#include "zkc/Transforms/NestedContractions.h"
#include <fstream>
#include <sstream>
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
std::string fixture(StringRef name) {
  std::ifstream input(std::string(ZKC_FINITE_FIXTURES) + "/" + name.str() +
                      ".mlir");
  require(bool(input), "missing finite fixture");
  std::ostringstream text;
  text << input.rdbuf();
  return text.str();
}
struct AdmittedComputation : finite::Computation {
  std::shared_ptr<protocol::SourceExecutionClosure> source;
};
AdmittedComputation computation(ModuleOp module) {
  AdmittedComputation result;
  result.source = std::make_shared<protocol::SourceExecutionClosure>(
      take(protocol::readSourceExecutionClosure(&module.getBody()->front())));
  Operation *found = nullptr;
  module.walk([&](Operation *op) {
    if (finite::isComputation(op))
      found = op;
  });
  require(found, "missing computation");
  require(succeeded(finite::describe(found, result)), "invalid computation");
  result.scopedSource = result.source.get();
  return result;
}
LogicalResult realize(ModuleOp module, MathematicalSelectionPolicy policy = {},
                      mathematical::RealizationWork *shared = nullptr,
                      const mathematical::MathematicalRecipes &recipes =
                          mathematical::mathematicalRecipes()) {
  mathematical::RealizationWork standalone;
  auto &work = shared ? *shared : standalone;
  uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
  std::optional<CapacityCause> capacity;
  auto result =
      protocol::prepareScopedFinite(module, work, copy, bytes, capacity, policy,
                                    nullptr, nullptr, nullptr, recipes);
  if (!result)
    return failure();
  module->setAttrs(result->getOperation()->getAttrs());
  module.getBodyRegion().takeBody(result->getBodyRegion());
  return success();
}
LogicalResult compare(ModuleOp source, ModuleOp candidate) {
  mathematical::RealizationWork work;
  return protocol::verifyScopedFinitePreparation(source, candidate, work);
}
func::FuncOp function(ModuleOp module, StringRef name) {
  auto result =
      SymbolTable(&module.getBody()->front()).lookup<func::FuncOp>(name);
  require(bool(result), "missing scoped fixture function");
  return result;
}
Value apply(OpBuilder &builder, exec::ScopedExecutionBuilder &control,
            StringRef binding, ValueRange inputs, Type output, StringRef site,
            ArrayRef<StringRef> parameters = {}, Block *stop = nullptr) {
  SmallVector<Attribute> values;
  for (auto value : parameters)
    values.push_back(builder.getStringAttr(value));
  return control
      .invoke(
          "exec.apply", output, control.scoped(inputs),
          {builder.getNamedAttr("binding", FlatSymbolRefAttr::get(
                                               builder.getContext(), binding)),
           builder.getNamedAttr("site", builder.getStringAttr(site)),
           builder.getNamedAttr("parameters", builder.getArrayAttr(values))},
          stop)
      .front();
}
OwningOpRef<ModuleOp> clone(ModuleOp module) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
}
bool equivalent(ModuleOp left, ModuleOp right) {
  return OperationEquivalence::isEquivalentTo(
      left, right, OperationEquivalence::IgnoreLocations);
}
bool hasKernel(ModuleOp module, StringRef contract) {
  bool found = false;
  module.walk([&](exec::ApplyOp op) {
    auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
        op, op.getBindingAttr());
    found |= binding && binding.getContract() == contract;
  });
  return found;
}
exec::ApplyOp findKernel(ModuleOp module, StringRef contract) {
  exec::ApplyOp found;
  module.walk([&](exec::ApplyOp op) {
    auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
        op, op.getBindingAttr());
    if (!found && binding && binding.getContract() == contract)
      found = op;
  });
  require(bool(found), "missing candidate contract " + contract);
  return found;
}
void eraseInvocation(exec::ApplyOp operation) {
  auto dispatch = cast<exec::DispatchOp>(operation->getNextNode());
  auto *next = dispatch.getReturned();
  require(next->getNumArguments() == 0, "expected no invocation payload");
  auto *before = operation->getBlock();
  dispatch.erase();
  operation.erase();
  IRRewriter rewriter(before->getParentOp()->getContext());
  rewriter.mergeBlocks(next, before);
}
bool hasStatefulLoop(ModuleOp module, StringRef name) {
  auto closure =
      take(protocol::readSourceExecutionClosure(&module.getBody()->front()));
  auto body = closure.bodies.find(name.str());
  require(body != closure.bodies.end(), "missing selected source body");
  return llvm::any_of(body->second, [](const auto &step) {
    return isa<exec::RangeOp>(step.operation) && !step.outputs.empty();
  });
}
llvm::SmallVector<mathematical::MatrixContractionRecipe>
withoutMatrixForm(mathematical::MatrixContractionForm form) {
  llvm::SmallVector<mathematical::MatrixContractionRecipe> result;
  for (const auto &recipe :
       mathematical::mathematicalRecipes().matrixContractions)
    if (recipe.form != form)
      result.push_back(recipe);
  return result;
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  using namespace mathematical;
  const MathematicalRecipes absent{{}, {}};
  cases.run("malformed scoped invocation has no mathematical meaning", [&] {
    auto source =
        parseSourceString<ModuleOp>(fixture("nested-matrix"), &context);
    require(bool(source), "nested fixture refused");
    auto operation = findKernel(*source, "field.mul");
    require(finite::semantics(operation), "missing admitted field meaning");
    operation->setOperand(0, operation.getInputs().front());
    require(!finite::semantics(operation),
            "non-scope operand acquired meaning");
    operation->eraseOperands(0, operation->getNumOperands());
    require(!finite::semantics(operation), "absent scope acquired meaning");
  });
  cases.run("lane emission retains the selected inventory", [&] {
    auto source = parseSourceString<ModuleOp>(fixture("collect"), &context);
    require(bool(source), "collection fixture refused");
    auto square = function(*source, "square");
    OpBuilder builder(square);
    runtime::BindingOp::create(
        builder, square.getLoc(), "constant", "field.constant",
        builder.getStrArrayAttr({"bls12-381.fr"}), "", ArrayAttr());
    square.getBody().dropAllReferences();
    square.getBody().getBlocks().clear();
    square.addEntryBlock();
    builder.setInsertionPointToStart(&square.front());
    exec::ScopedExecutionBuilder control(builder, square);
    auto field = square.getArgument(1).getType();
    auto two = apply(builder, control, "constant", {}, field, "two", {"2"});
    auto product = apply(builder, control, "mul", {square.getArgument(1), two},
                         field, "square");
    control.returned(product);
    require(succeeded(verify(*source)), "scalar/lane fixture refused");
    const auto &installed = mathematicalRecipes();
    llvm::SmallVector<LaneRecipe> lanes(installed.lanes);
    for (auto &recipe : lanes)
      if (recipe.identity == MathematicalIdentity::FieldMultiply)
        recipe.mixed = {};
    // Both recipes implement multiplication. With no mixed scalar/vector
    // recipe, the supplied inventory requires a broadcast and packed multiply.
    const MathematicalRecipes broadcast{lanes, installed.reductions,
                                        installed.matrixContractions};
    auto direct = clone(*source), expanded = clone(*source);
    MathematicalSelectionPolicy vectorPolicy;
    vectorPolicy.numericalExpressions = NumericalExpressionMode::VectorOnly;
    require(succeeded(realize(*direct, vectorPolicy, nullptr, installed)) &&
                succeeded(realize(*expanded, vectorPolicy, nullptr, broadcast)),
            "valid selected lane recipe did not pass independent checking");
    require(
        hasKernel(*direct, "vector.scale") &&
            !hasKernel(*expanded, "vector.scale") &&
            hasKernel(*expanded, "vector.fill") &&
            hasKernel(*expanded, "vector.mul"),
        "lane emission replaced the selected inventory with global recipes");
    require(succeeded(compare(*source, *expanded)),
            "broadcast realization changed the source meaning");
  });
  cases.run("two-member inventory has no implicit matrix recipes", [&] {
    const auto &installed = mathematicalRecipes();
    const MathematicalRecipes original{installed.lanes, installed.reductions};
    require(original.matrixContractions.empty() &&
                original.lane(MathematicalIdentity::FieldAdd) &&
                original.reduction(MathematicalIdentity::FieldAdd,
                                   MathematicalIdentity::FieldMultiply,
                                   ReductionForm::Contraction),
            "two-member inventory silently installed additional recipes");
    require(installed.matrixContractions.size() == 3,
            "installed matrix inventory is incomplete");
  });
  cases.run("bilinear withheld recipe retains checked ordered fallback", [&] {
    auto source = parseSourceString<ModuleOp>(fixture("bilinear"), &context);
    require(bool(source) && succeeded(verify(*source)),
            "bilinear fixture refused");
    auto c = computation(*source);
    const auto &installed = mathematicalRecipes();
    auto matrices = withoutMatrixForm(MatrixContractionForm::Bilinear);
    const MathematicalRecipes withheld{installed.lanes, installed.reductions,
                                       matrices};
    auto selected = selectComputation(c, {});
    auto missing = selectComputation(c, {}, withheld);
    require(selected.kind == RealizationKind::Bilinear && selected.matrix &&
                selected.outcome() == OptimizationStatus::Succeeded &&
                selected.matrix->target == "matrix.bilinear" &&
                selected.matrix->seedCombiner == "field.add" &&
                missing.kind == RealizationKind::Ordered && !missing.matrix &&
                missing.outcome() == OptimizationStatus::MissingRecipe &&
                missing.equations.bilinear &&
                missing.equations.bilinear->matrix ==
                    selected.equations.bilinear->matrix &&
                missing.equations.bilinear->left ==
                    selected.equations.bilinear->left &&
                missing.equations.bilinear->right ==
                    selected.equations.bilinear->right,
            "missing bilinear recipe changed recognition or selected a target");
    auto present = clone(*source), fallback = clone(*source);
    auto defaultInventory = clone(*source);
    require(succeeded(realize(*present, {}, nullptr, installed)) &&
                succeeded(realize(*defaultInventory)),
            "installed bilinear recipe realization failed");
    require(equivalent(*present, *defaultInventory),
            "explicit installed inventory changed default bilinear output");
    require(succeeded(compare(*source, *present)),
            "installed bilinear recipe failed independent correspondence");
    require(hasKernel(*present, "matrix.bilinear") &&
                !hasStatefulLoop(*present, "work"),
            "installed bilinear recipe did not replace payload iteration");
    require(
        succeeded(realize(*fallback, {}, nullptr, withheld)) &&
            succeeded(verify(*fallback)) &&
            succeeded(compare(*source, *fallback)) &&
            hasStatefulLoop(*fallback, "work") &&
            !hasKernel(*fallback, "matrix.bilinear"),
        "withheld bilinear recipe failed independently checked ordered path");
  });
  for (bool columns : {false, true})
    cases.run(
        columns ? "withheld column matvec recipe"
                : "withheld row matvec recipe",
        [&] {
          auto text = fixture("nested-matrix");
          if (columns)
            for (auto [before, after] :
                 {std::pair{"domain_matrix_row", "domain_matrix_column"},
                  {"axis = 0 : i64", "axis = 1 : i64"}}) {
              auto position = text.find(before);
              require(position != std::string::npos,
                      "column fixture edit missing");
              text.replace(position, StringRef(before).size(), after);
            }
          auto source = parseSourceString<ModuleOp>(text, &context);
          require(bool(source) && succeeded(verify(*source)),
                  "matvec fixture refused");
          auto c = computation(*source);
          auto view = finite::analyzeComputation(c);
          require(bool(view), "nested structural view missing");
          auto form = columns ? MatrixContractionForm::Columns
                              : MatrixContractionForm::Rows;
          const auto &installed = mathematicalRecipes();
          auto matrices = withoutMatrixForm(form);
          const MathematicalRecipes withheld{installed.lanes,
                                             installed.reductions, matrices};
          auto selected = selectNestedContraction(*view);
          auto missing = selectNestedContraction(*view, withheld);
          StringRef target =
              columns ? "matrix.transpose_mul_vector" : "matrix.mul_vector";
          require(
              selected.recipe && selected.recipe->target == target &&
                  selected.outcome() == OptimizationStatus::Succeeded &&
                  selected.recipe->seedCombiner == "vector.add" &&
                  selected.equation && missing.equation && !missing.recipe &&
                  missing.outcome() == OptimizationStatus::MissingRecipe &&
                  missing.equation->axis == unsigned(columns) &&
                  missing.equation->matrix == selected.equation->matrix &&
                  missing.equation->vector == selected.equation->vector &&
                  missing.equation->seed.input ==
                      selected.equation->seed.input &&
                  missing.equation->seed.constant ==
                      selected.equation->seed.constant,
              "withheld matvec recipe changed equation or selected a target");
          auto present = clone(*source), fallback = clone(*source);
          auto defaultInventory = clone(*source);
          require(succeeded(realize(*present, {}, nullptr, installed)) &&
                      succeeded(realize(*defaultInventory)) &&
                      equivalent(*present, *defaultInventory) &&
                      succeeded(compare(*source, *present)) &&
                      hasKernel(*present, target),
                  "installed matvec recipe changed default output or "
                  "correspondence");
          require(succeeded(realize(*fallback, {}, nullptr, withheld)) &&
                      succeeded(verify(*fallback)) &&
                      succeeded(compare(*source, *fallback)) &&
                      hasStatefulLoop(*fallback, "work") &&
                      !hasKernel(*fallback, "matrix.mul_vector") &&
                      !hasKernel(*fallback, "matrix.transpose_mul_vector"),
                  "withheld matvec recipe failed independently checked ordered "
                  "path");
        });
  auto nestedSource =
      parseSourceString<ModuleOp>(fixture("nested-matrix"), &context);
  auto nestedCandidate = clone(*nestedSource);
  require(succeeded(realize(*nestedCandidate)) &&
              succeeded(compare(*nestedSource, *nestedCandidate)),
          "nested mutation baseline failed");
  for (bool reverseSum : {false, true})
    for (bool reverseProduct : {false, true})
      cases.run("nested commutative operand order " + Twine(reverseSum) + "/" +
                    Twine(reverseProduct),
                [&] {
                  auto source = clone(*nestedSource);
                  for (auto [reverse, name] :
                       {std::pair{reverseSum, "field.add"},
                        std::pair{reverseProduct, "field.mul"}})
                    if (reverse) {
                      auto call = findKernel(*source, name);
                      auto first = call->getOperand(1);
                      call->setOperand(1, call->getOperand(2));
                      call->setOperand(2, first);
                    }
                  auto candidate = clone(*source);
                  require(
                      succeeded(realize(*candidate)) &&
                          succeeded(compare(*source, *candidate)) &&
                          hasKernel(*candidate, "matrix.mul_vector"),
                      "commutative nested source lost checked bulk selection");
                });
  for (StringRef seed : {"0", "19"})
    cases.run("nested uniform constant seed " + seed, [&] {
      auto source = clone(*nestedSource);
      auto body = function(*source, "body");
      auto fold = cast<exec::FoldOp>(body.front().front());
      auto stop = cast<exec::DispatchOp>(fold->getNextNode()).getStopped();
      IRRewriter rewriter(&context);
      auto *tail = rewriter.splitBlock(&body.front(), fold->getIterator());
      OpBuilder builder(&context);
      builder.setInsertionPointToEnd(&body.front());
      exec::ScopedExecutionBuilder control(builder, body);
      Value value = apply(builder, control, "constant", {},
                          body.getArgument(7).getType(), "seed", {seed}, stop);
      fold->setOperand(5, value);
      rewriter.mergeBlocks(tail, builder.getInsertionBlock());
      require(succeeded(verify(*source)), "constant source must remain formed");
      auto candidate = clone(*source);
      require(succeeded(realize(*candidate)) &&
                  succeeded(compare(*source, *candidate)) &&
                  hasKernel(*candidate, "matrix.mul_vector"),
              "constant seed lost checked nested selection");
      auto bulk = findKernel(*candidate, "matrix.mul_vector");
      auto owner = bulk->getParentOfType<func::FuncOp>();
      bool changed = false;
      owner.walk([&](exec::ApplyOp op) {
        if (SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                op, op.getBindingAttr())
                .getContract() == "field.constant") {
          op.setParametersAttr(builder.getStrArrayAttr({"23"}));
          changed = true;
        }
      });
      require(changed && succeeded(verify(*candidate)) &&
                  failed(compare(*source, *candidate)),
              "changed bulk seed accepted");
    });
  cases.run("nested optional comparison exhaustion keeps checked order", [&] {
    auto candidate = clone(*nestedSource);
    mathematical::RealizationWork work;
    work.optionalFiniteChecking = 0;
    require(
        succeeded(realize(*candidate, {}, &work)) &&
            succeeded(compare(*nestedSource, *candidate)) &&
            hasStatefulLoop(*candidate, "work") &&
            !hasKernel(*candidate, "matrix.mul_vector") &&
            work.optionalFiniteChecking == 0,
        "comparison exhaustion published bulk work or refilled its allowance");
  });
  auto mutation = [&](StringRef name, llvm::function_ref<void(ModuleOp)> edit) {
    cases.run("nested candidate rejects " + name, [&] {
      auto changed = clone(*nestedCandidate);
      edit(*changed);
      require(succeeded(verify(*changed)),
              "mutation must retain formed scoped IR");
      require(failed(compare(*nestedSource, *changed)),
              "independent reader accepted changed candidate");
    });
  };
  mutation("matrix mapping", [&](ModuleOp module) {
    auto call = findKernel(module, "matrix.mul_vector");
    auto owner = call->getParentOfType<func::FuncOp>();
    call->setOperand(1, owner.getArgument(4));
  });
  mutation("vector mapping", [&](ModuleOp module) {
    auto call = findKernel(module, "matrix.mul_vector");
    auto owner = call->getParentOfType<func::FuncOp>();
    call->setOperand(2, owner.getArgument(5));
  });
  mutation("seed mapping", [&](ModuleOp module) {
    auto call = findKernel(module, "vector.fill");
    auto owner = call->getParentOfType<func::FuncOp>();
    call->setOperand(1, owner.getArgument(7));
  });
  mutation("bulk orientation", [&](ModuleOp module) {
    auto call = findKernel(module, "matrix.mul_vector");
    auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
        call, call.getBindingAttr());
    binding.setContract("matrix.transpose_mul_vector");
  });
  mutation("missing ignored zip guard", [&](ModuleOp module) {
    auto call = findKernel(module, "matrix.mul_vector");
    auto owner = call->getParentOfType<func::FuncOp>();
    exec::ApplyOp last;
    unsigned count = 0;
    owner.walk([&](exec::ApplyOp op) {
      auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
          op, op.getBindingAttr());
      if (binding.getContract() == "control.require") {
        last = op;
        ++count;
      }
    });
    require(count == 3,
            "expected selected-row guard and two strict zip guards");
    eraseInvocation(last);
  });
  mutation("guard identity", [&](ModuleOp module) {
    auto call = findKernel(module, "matrix.mul_vector");
    auto owner = call->getParentOfType<func::FuncOp>();
    auto closure =
        take(protocol::readSourceExecutionClosure(&module.getBody()->front()));
    for (const auto &step : closure.bodies.at(owner.getSymName().str())) {
      auto op = dyn_cast<exec::ApplyOp>(step.operation);
      if (op && SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                    op, op.getBindingAttr())
                        .getContract() == "control.require") {
        op.setSite("changed_guard");
        return;
      }
    }
    require(false, "missing nested guard");
  });
  mutation("guard source location", [&](ModuleOp module) {
    auto call = findKernel(module, "matrix.mul_vector");
    auto owner = call->getParentOfType<func::FuncOp>();
    owner.walk([&](exec::ApplyOp op) {
      if (SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
              op, op.getBindingAttr())
              .getContract() == "control.require")
        op->setLoc(FileLineColLoc::get(&context, "wrong-fold.zkc", 9, 2));
    });
  });
  for (StringRef mapping : {"vector", "seed", "product"})
    cases.run("nested source is reread for " + mapping, [&] {
      auto changed = clone(*nestedSource);
      if (mapping == "product") {
        auto call = findKernel(*changed, "field.mul");
        call->setOperand(2, function(*changed, "step").getArgument(4));
      } else {
        auto owner = function(*changed, "body");
        auto call = cast<exec::FoldOp>(owner.front().front());
        call->setOperand(mapping == "vector" ? 3 : 5,
                         owner.getArgument(mapping == "vector" ? 6 : 8));
      }
      require(succeeded(verify(*changed)),
              "source mutation must remain formed");
      require(failed(compare(*changed, *nestedCandidate)),
              "stale candidate accepted against changed source");
    });
  for (bool hashed : {false, true})
    cases.run(
        hashed ? "nested guard hashed source coordinates"
               : "nested guard source coordinates",
        [&] {
          auto source = clone(*nestedSource);
          auto body = function(*source, "body");
          auto call = cast<exec::FoldOp>(body.front().front());
          std::string site = hashed ? std::string(120, 'i') : "inner";
          call.setSite(site);
          auto location =
              FileLineColLoc::get(&context, "inner-fold.zkc", 17, 3);
          call->setLoc(location);
          auto candidate = clone(*source);
          require(succeeded(realize(*candidate)) &&
                      succeeded(compare(*source, *candidate)),
                  "qualified nested candidate failed");
          auto bulk = findKernel(*candidate, "matrix.mul_vector");
          auto owner = bulk->getParentOfType<func::FuncOp>();
          SmallVector<exec::ApplyOp> guards;
          owner.walk([&](exec::ApplyOp op) {
            if (SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                    op, op.getBindingAttr())
                    .getContract() == "control.require")
              guards.push_back(op);
          });
          require(guards.size() == 3, "missing nested admission guards");
          const unsigned admissionLeaves[] = {2, 7, 9};
          for (auto [guard, index] : llvm::zip(guards, admissionLeaves)) {
            uint64_t bytes = 16 * 1024 * 1024;
            auto expected = take(protocol::algorithmSite(
                {{"collect", "body"}, {site, "step"}},
                "finite_" + std::to_string(index), bytes));
            require(
                guard.getSite() == expected && guard->getLoc() == location &&
                    guard.getSite().starts_with("lc_h_") == hashed,
                "guard lost inner source coordinates or diagnostic location: " +
                    guard.getSite() + " expected " + expected);
          }
          auto snapshot = clone(*source);
          mathematical::RealizationWork work;
          uint64_t copy = 1000000, bytes = 0;
          std::optional<CapacityCause> capacity;
          auto refused = protocol::prepareScopedFinite(*source, work, copy,
                                                       bytes, capacity);
          require(!refused && capacity &&
                      capacity->owner == WorkOwner::AlgorithmOriginBytes &&
                      equivalent(*source, *snapshot),
                  "site-budget refusal published a changed source");
        });
  cases.run("nested source work limit is explicit", [&] {
    auto c = computation(*nestedSource);
    uint64_t work = 100000;
    bool exhausted = false;
    auto source = nested::readScopedSource(c, work, exhausted);
    require(source && !exhausted && work < 100000,
            "source reader did no bounded work");
    uint64_t exact = 100000 - work;
    auto remaining = exact;
    require(nested::readScopedSource(c, remaining, exhausted) && !exhausted &&
                remaining == 0,
            "exact source-reader allowance refused");
    remaining = exact - 1;
    require(!nested::readScopedSource(c, remaining, exhausted) && exhausted,
            "exhausted source-reader allowance was not distinguished");
  });
  for (auto [name, target] : {std::pair{"sum", "vector.sum"},
                              {"product", "vector.product"},
                              {"dot", "vector.dot"},
                              {"msm-direct", "curve.msm"},
                              {"matrix-row", "matrix.row_dot"},
                              {"matrix-column", "matrix.column_dot"}})
    cases.run(name, [&, name = name, target = target] {
      auto module = parseSourceString<ModuleOp>(fixture(name), &context);
      require(bool(module), "fixture refused");
      auto c = computation(*module);
      auto selected = selectComputation(c, {});
      require(selected.kind == RealizationKind::Reduction &&
                  selected.reduction &&
                  selected.reduction->recipe->target == target,
              "native reduction recipe not selected");
      auto withheld = selectComputation(c, {}, absent);
      require(withheld.kind == RealizationKind::Ordered &&
                  withheld.outcome() == OptimizationStatus::MissingRecipe &&
                  !withheld.reduction && withheld.view &&
                  withheld.equations.reduction &&
                  withheld.equations.reduction->combine ==
                      selected.equations.reduction->combine &&
                  withheld.equations.reduction->inputs ==
                      selected.equations.reduction->inputs,
              "withheld recipe erased mathematical recognition or invented a "
              "target");
      if (StringRef(name) == "msm-direct")
        require(selected.equations.reduction->inputs ==
                        SmallVector<unsigned>({0, 1}) &&
                    selected.reduction->inputs ==
                        SmallVector<unsigned>({1, 0}) &&
                    selected.reduction->staticSourceInput == 0,
                "group/scalar semantic roles confused with native MSM order");
      if (StringRef(name).starts_with("matrix-")) {
        auto *term = selected.view->sourceOperation(
            selected.equations.reduction->term.getDefiningOp());
        auto applied = dyn_cast_or_null<exec::ApplyOp>(term);
        require(bool(applied), "missing actual scalar product");
        Value left = applied.getInputs()[0], right = applied.getInputs()[1];
        term->setOperand(1, right);
        term->setOperand(2, left);
        c = computation(*module);
        selected = selectComputation(c, {});
        require(selected.kind == RealizationKind::Reduction &&
                    selected.equations.reduction->inputs ==
                        SmallVector<unsigned>({1, 0}) &&
                    selected.equations.reduction->matrixOperand == 1 &&
                    selected.reduction->inputs ==
                        SmallVector<unsigned>({0, 1}) &&
                    selected.reduction->selectedIndex == 3 &&
                    selected.reduction->staticSourceInput == 0,
                "matrix semantic role or selected native mapping changed");
      }
    });
  cases.run("disabled selection preserves recipe-free equations", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("dot"), &context);
    auto c = computation(*module);
    auto disabled = selectComputation(c, {false, false}, absent);
    require(disabled.view && disabled.equations.reduction &&
                disabled.outcome() == OptimizationStatus::PolicyDisabled &&
                disabled.kind == RealizationKind::Ordered &&
                !disabled.reduction &&
                disabled.equations.reduction->witness.yielded ==
                    disabled.view->result &&
                disabled.equations.reduction->witness.seed.formal ==
                    disabled.view->seeds[0].formal,
            "selection policy erased source equation or exact witness");
  });
  cases.run("lane recognition with withheld recipes", [&] {
    auto module =
        parseSourceString<ModuleOp>(fixture("total-collect"), &context);
    require(bool(module), "collect refused");
    auto c = computation(*module);
    auto present = selectComputation(c, {});
    auto withheld = selectComputation(c, {}, absent);
    require(present.kind == RealizationKind::Elementwise &&
                present.outcome() == OptimizationStatus::Succeeded &&
                withheld.outcome() == OptimizationStatus::MissingRecipe &&
                withheld.kind == RealizationKind::Ordered && withheld.view &&
                withheld.equations.elementwise &&
                withheld.view->result == present.view->result,
            "withheld lane recipe changed semantic formula recognition");
  });
  cases.run("pinned meaning is recognized and retained", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("sum"), &context);
    require(bool(module), "sum refused");
    auto c = computation(*module);
    auto &operation = c.helper->getRegion(0).front().front();
    auto binding = operation.getAttrOfType<FlatSymbolRefAttr>("binding");
    auto declaration = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
        &operation, binding);
    require(bool(declaration), "missing scalar binding");
    declaration.setImplementation("arkworks/field.add");
    require(succeeded(verify(*module)),
            "pinned scalar binding is not admitted");
    c = computation(*module);
    auto selected = selectComputation(c, {});
    require(
        selected.view && selected.equations.reduction &&
            selected.outcome() == OptimizationStatus::ReplacementRestricted &&
            !canReplacePayload(*selected.view) &&
            selected.kind == RealizationKind::Ordered &&
            finite::semantics(&operation) && !finite::replaceable(&operation),
        "explicit implementation erased meaning or permitted replacement");
    OwningOpRef<ModuleOp> candidate(cast<ModuleOp>((*module)->clone()));
    require(succeeded(realize(*candidate)) &&
                succeeded(compare(*module, *candidate)),
            "pinned ordered fallback failed independent checking");
    bool retained = false;
    candidate->walk([&](runtime::BindingOp op) {
      retained |= op.getContract() == "field.add" &&
                  op.getImplementation() == "arkworks/field.add";
    });
    require(retained, "pinned implementation disappeared");
    // An unavailable pin is still mathematically identifiable, but ordinary
    // binding admission rejects it. Analysis is not physical admission.
    declaration.setImplementation("withheld/field.add");
    require(finite::semantics(&operation) && !finite::replaceable(&operation),
            "unavailable provider erased meaning");
    auto physical = protocol::operationBinding(&operation);
    require(!physical, "unknown physical implementation gained admission");
    llvm::consumeError(physical.takeError());
  });
  cases.run(
      "nested equation recognition preserves implementation constraints", [&] {
        auto module =
            parseSourceString<ModuleOp>(fixture("nested-matrix"), &context);
        auto c = computation(*module);
        auto view = finite::analyzeComputation(c);
        require(view && matchNestedContraction(*view) &&
                    canReplaceNestedContraction(*view),
                "nested equation missing");
        Operation *add =
            view->nested[0].sourceOperation(view->nested[0].payload.back());
        auto declaration =
            SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                add, add->getAttrOfType<FlatSymbolRefAttr>("binding"));
        declaration.setImplementation("arkworks/field.add");
        require(succeeded(verify(*module)), "nested pin is not admitted");
        c = computation(*module);
        view = finite::analyzeComputation(c);
        require(view && matchNestedContraction(*view) &&
                    !canReplaceNestedContraction(*view),
                "nested pin erased the equation or permitted replacement");
        auto selected = selectNestedContraction(*view);
        require(selected.equation && !selected.recipe &&
                    selected.outcome() ==
                        OptimizationStatus::ReplacementRestricted,
                "nested pin did not explain its selection restriction");
      });
  cases.run("indexed group access retains ordered fallback", [&] {
    auto module = parseSourceString<ModuleOp>(fixture("msm-direct"), &context);
    require(bool(module), "indexed group fixture refused");
    auto step = function(*module, "step");
    auto domain = SymbolTable(&module->getBody()->front())
                      .lookup<data::DomainOp>("items");
    auto index = IntegerType::get(&context, 64, IntegerType::Unsigned);
    auto field = step.getArgument(3).getType();
    auto group = step.getArgument(2).getType();
    auto &elements = domain.getBody().front().front();
    OpBuilder builder(&elements);
    auto positions = data::DomainIndicesOp::create(
        builder, elements.getLoc(), data::DomainType::get(&context, {index}),
        elements.getOperand(0), builder.getI64IntegerAttr(0));
    elements.getResult(0).replaceAllUsesWith(positions.getResult());
    elements.erase();
    auto zip = *domain.getBody().front().getOps<data::DomainZipOp>().begin();
    auto domainType = data::DomainType::get(&context, {index, field});
    zip.getResult().setType(domainType);
    domain.setFunctionType(FunctionType::get(
        &context, domain.getFunctionType().getInputs(), {domainType}));
    builder.setInsertionPoint(step);
    runtime::BindingOp::create(builder, step.getLoc(), "get", "curve.get",
                               builder.getStrArrayAttr({"bls12-381.g1"}), "",
                               ArrayAttr());
    SmallVector<Type> inputs(step.getArgumentTypes());
    inputs[2] = index;
    step.setFunctionType(
        FunctionType::get(&context, inputs, step.getResultTypes()));
    step.getBody().dropAllReferences();
    step.getBody().getBlocks().clear();
    step.addEntryBlock();
    builder.setInsertionPointToStart(&step.front());
    exec::ScopedExecutionBuilder control(builder, step);
    auto point =
        apply(builder, control, "get",
              {step.getArgument(4), step.getArgument(2)}, group, "get");
    auto term = apply(builder, control, "scale", {point, step.getArgument(3)},
                      group, "term");
    auto result = apply(builder, control, "add", {step.getArgument(1), term},
                        group, "add");
    control.returned(result);
    require(succeeded(verify(*module)), "indexed group control not admitted");
    auto c = computation(*module);
    auto selected = selectComputation(c, {});
    // curve.get has no total mathematical facet. The scoped reader may decline
    // a scalar view; both that outcome and an opaque view must remain ordered.
    require(!selected.equations.reduction &&
                selected.outcome() == OptimizationStatus::Unsupported &&
                selected.kind == RealizationKind::Ordered,
            "indexed group access acquired an unsupported bulk equation");
    OwningOpRef<ModuleOp> candidate(cast<ModuleOp>((*module)->clone()));
    require(succeeded(realize(*candidate)) &&
                succeeded(compare(*module, *candidate)),
            "indexed group fallback failed independent correspondence");
    require(hasStatefulLoop(*candidate, "work") &&
                hasKernel(*candidate, "curve.get"),
            "indexed group fallback lost ordered iteration or group lookup");
  });
  cases.run(
      "recognized group sum has no direct recipe and executes fallback", [&] {
        auto module =
            parseSourceString<ModuleOp>(fixture("msm-direct"), &context);
        require(bool(module), "group fixture refused");
        auto c = computation(*module);
        auto function = cast<func::FuncOp>(c.helper);
        auto scale = cast<exec::ApplyOp>(function.front().front());
        auto dispatch = cast<exec::DispatchOp>(scale->getNextNode());
        auto *continuation = dispatch.getReturned();
        Value point = scale.getInputs()[0];
        dispatch.erase();
        scale.erase();
        IRRewriter rewriter(&context);
        rewriter.mergeBlocks(continuation, &function.front(), point);
        require(succeeded(verify(*module)), "group sum control not admitted");
        c = computation(*module);
        auto selected = selectComputation(c, {});
        require(selected.view && selected.equations.reduction &&
                    selected.equations.reduction->combine ==
                        MathematicalIdentity::GroupAdd &&
                    !selected.equations.reduction->termIdentity &&
                    selected.kind == RealizationKind::Ordered &&
                    !selected.reduction,
                "group sum was not recognized independently of missing direct "
                "recipe");
        OwningOpRef<ModuleOp> candidate(cast<ModuleOp>((*module)->clone()));
        require(succeeded(realize(*candidate)) &&
                    succeeded(compare(*module, *candidate)),
                "missing-recipe ordered fallback failed independent checking");
        require(hasStatefulLoop(*candidate, "work"),
                "missing direct group recipe did not retain an ordered loop");
      });
  return cases.result();
}
