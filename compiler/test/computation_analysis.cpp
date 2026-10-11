#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/Computation.h"
#include "zkc/Dialect/IR.h"
#include <fstream>
#include <sstream>
#include <type_traits>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
// This executable links only IR. Reintroducing equation/strategy fields is an
// API regression even when every installed realization still happens to work.
#define ABSENT_MEMBER(member)                                                  \
  template <class T, class = void> struct Has_##member : std::false_type {};   \
  template <class T>                                                           \
  struct Has_##member<T, std::void_t<decltype(std::declval<T>().member)>>      \
      : std::true_type {};                                                     \
  static_assert(!Has_##member<finite::ComputationView>::value)
ABSENT_MEMBER(reduction);
ABSENT_MEMBER(elementwise);
ABSENT_MEMBER(bilinear);
ABSENT_MEMBER(demand);
ABSENT_MEMBER(replaceable);
#undef ABSENT_MEMBER

std::string fixture(StringRef name) {
  std::ifstream input(std::string(ZKC_FINITE_FIXTURES) + "/" + name.str() +
                      ".mlir");
  require(bool(input), "missing fixture");
  std::ostringstream text;
  text << input.rdbuf();
  return text.str();
}
finite::Computation computation(ModuleOp module) {
  Operation *found = nullptr;
  module.walk([&](Operation *op) {
    if (finite::isComputation(op))
      found = op;
  });
  require(found, "missing computation");
  finite::Computation result;
  require(succeeded(finite::describe(found, result)), "invalid computation");
  return result;
}
void checkBindings(const finite::ComputationView &view) {
  auto c = view.computation;
  require(view.environment.inputs.size() == c.signature.getNumInputs(),
          "missing signature input environment");
  for (const auto &input : view.environment.inputs) {
    require(view.environment.inputPosition(input.formal) == input.input,
            "helper argument does not map to exact signature input");
    if (input.input < c.arguments)
      require(input.domainFormal ==
                      c.domain.getBody().front().getArgument(input.input) &&
                  view.environment.inputPosition(input.domainFormal) ==
                      input.input,
              "domain formal mapping lost");
    else
      require(!input.domainFormal, "seed/capture invented a domain formal");
    require(input.formal.getType() == c.signature.getInput(input.input),
            "helper input type changed");
    if (input.actual)
      require(input.actual == view.occurrence->getOperand(input.input),
              "actual occurrence input changed");
  }
  for (const auto &mapping : view.resultMappings) {
    require(mapping.yielded == view.results[mapping.output],
            "yield result mapping changed");
    require(mapping.type == c.signature.getResult(mapping.output),
            "result shape/type observation changed");
    if (c.collect)
      require(
          mapping.cardinality ==
              (c.predicate ? std::nullopt : std::optional<unsigned>(view.root)),
          "collect cardinality ignored predicate or domain identity");
    else
      require(mapping.seedInput == view.seeds[mapping.output].input,
              "declaration zero-trip seed mapping omitted");
    if (mapping.actual)
      require(mapping.actual == view.occurrence->getResult(mapping.output),
              "actual occurrence result changed");
  }
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  for (auto name :
       {"sum", "dot", "msm-direct", "matrix-row", "matrix-column", "bilinear",
        "total-collect", "total-state", "total-predicate", "nested-total",
        "nested-matrix", "dead-domain"})
    cases.run(name, [&, name] {
      auto module = parseSourceString<ModuleOp>(fixture(name), &context);
      require(bool(module) && succeeded(verify(*module)), "fixture refused");
      auto c = computation(*module);
      auto view = finite::analyzeComputation(c);
      require(bool(view), "structural view missing");
      checkBindings(*view);
      require(view->admission.size() == view->iteration.size(),
              "admission constructor omitted");
      for (auto [operation, recorded] :
           llvm::zip(c.domain.getBody().front().without_terminator(),
                     view->admission))
        require(&operation == recorded, "ordered admission changed");
      require(view->items.size() == view->axes.size(), "item axis omitted");
      for (const auto &item : view->items) {
        const auto &axis = view->axes[item.axis];
        require(axis.identity.constructor ==
                        view->iteration[item.iteration].operation &&
                    axis.identity.occurrence == view->occurrencePath,
                "item axis lost constructor or invocation identity");
      }
      require(!finite::analyzeComputation(c, 0), "structural budget ignored");
    });
  cases.run(
      "unused constructors retain admission but add no traversed axes", [&] {
        auto module =
            parseSourceString<ModuleOp>(fixture("dead-domain"), &context);
        auto view = finite::analyzeComputation(computation(*module));
        require(
            view && view->admission.size() == 4 && view->axes.size() == 1 &&
                view->root == 0 && view->seeds.size() == 1 &&
                !view->seeds.front().actual,
            "unused admission became traversal or fabricated an invocation");
      });
  for (auto name : {"coordinates-row", "coordinates-column"})
    cases.run(name, [&, name] {
      auto module = parseSourceString<ModuleOp>(fixture(name), &context);
      auto view = finite::analyzeComputation(computation(*module));
      require(view && view->axes.size() == 2 &&
                  view->axes[0].identity.constructor ==
                      view->axes[1].identity.constructor &&
                  view->axes[0].identity != view->axes[1].identity &&
                  view->axes[0].identity.coordinate == 0 &&
                  view->axes[1].identity.coordinate == 1 &&
                  view->axes[0].containerAxis == 0 &&
                  view->axes[1].containerAxis == 1,
              "matrix coordinate order or identity collapsed");
      auto order =
          view->iteration[0].operation->getAttrOfType<StringAttr>("order");
      require(order && order.getValue() == (StringRef(name) == "coordinates-row"
                                                ? "row_major"
                                                : "column_major"),
              "enumeration order lost");
    });
  cases.run(
      "reused descriptor has distinct product coordinate occurrences", [&] {
        auto text = fixture("dot");
        auto at = text.find("data.domain_zip");
        require(at != std::string::npos, "dot zip missing");
        text.replace(at, std::string("data.domain_zip").size(),
                     "data.domain_product");
        auto module = parseSourceString<ModuleOp>(text, &context);
        require(bool(module), "product fixture refused");
        auto c = computation(*module);
        auto *product =
            c.domain.getBody().front().back().getOperand(0).getDefiningOp();
        product->setOperand(1, product->getOperand(0));
        require(succeeded(verify(*module)),
                "reused descriptor is not admitted");
        auto view = finite::analyzeComputation(c);
        require(
            view && view->axes.size() == 3 && view->admission.size() == 4 &&
                view->axes[0].identity.constructor ==
                    view->axes[1].identity.constructor &&
                view->axes[0].identity != view->axes[1].identity &&
                view->axes[0].identity.path == SmallVector<unsigned>({0}) &&
                view->axes[1].identity.path == SmallVector<unsigned>({1}),
            "descriptor reuse collapsed independent axes or unused admission");
      });
  cases.run(
      "nested occurrences resolve captures but retain recurrence state", [&] {
        auto module =
            parseSourceString<ModuleOp>(fixture("nested-total"), &context);
        auto c = computation(*module);
        auto &body = c.helper->getRegion(0).front();
        OpBuilder builder(&body.back());
        builder.clone(body.front());
        require(succeeded(verify(*module)),
                "reused nested helper fixture refused");
        auto view = finite::analyzeComputation(c);
        require(view && view->nested.size() == 2, "nested occurrences omitted");
        const auto &first = view->nested[0], &second = view->nested[1];
        checkBindings(first);
        checkBindings(second);
        require(first.computation.helper == second.computation.helper &&
                    first.axes[0].identity != second.axes[0].identity &&
                    first.occurrencePath.size() == 2 &&
                    first.occurrencePath[0] == c.operation,
                "shared helper declaration collapsed distinct occurrence axes");
        require(
            first.captures[0].actual == view->captures[0].formal &&
                first.captures[0].resolved == view->captures[0].actual &&
                first.seeds[0].actual == view->seeds[0].formal &&
                first.seeds[0].resolved == view->seeds[0].formal &&
                first.environment.resolveCapture(first.seeds[0].formal) ==
                    first.seeds[0].formal,
            "capture composition replaced recurrence state with initial seed");
        require(view->admission.size() == 1 && first.admission.size() == 1,
                "nested admission was hoisted into outer empty case");
      });
  cases.run(
      "multiple state and zero-trip results retain exact correspondence", [&] {
        auto module =
            parseSourceString<ModuleOp>(fixture("total-state"), &context);
        auto c = computation(*module);
        auto view = finite::analyzeComputation(c);
        require(view && view->seeds.size() == 2 &&
                    view->resultMappings.size() == 2 && !view->result &&
                    view->results[0] == view->seeds[1].formal,
                "multiple state result relationship changed");
        for (unsigned i = 0; i < 2; ++i)
          require(view->seeds[i].input == i + 1 &&
                      view->resultMappings[i].initial ==
                          c.operation->getOperand(i + 1),
                  "zero-trip result is not its corresponding initial state");
      });
  cases.run("predicate may reuse an inactive acyclic step callback", [&] {
    auto text = fixture("nested-total");
    auto begin = text.find(" func.func private @outside");
    auto end = text.find(" \"protocol.func\"", begin);
    require(begin != std::string::npos && end != std::string::npos,
            "predicate fixture edit missing");
    text.replace(begin, end - begin, R"mlir(
 func.func private @predicate(%x:!F,%xs:!V) -> i1 {
   %r = "algebra.finite_fold"(%xs,%x) {domain=@items,step=@inside} : (!V,!F)->!F
   %ok = algebra.field_equal %r,%x : (!F,!F)->i1
   func.return %ok : i1
 }
)mlir");
    auto step = text.find("step=@outside");
    require(step != std::string::npos, "outer step missing");
    text.replace(step, StringRef("step=@outside").size(),
                 "step=@inside,predicate=@predicate");
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module) && succeeded(verify(*module)),
            "shared step predicate closure is not admitted");
    auto c = computation(*module);
    auto view = finite::analyzeComputation(c);
    require(view && view->nested.size() == 1 && view->payload.size() == 1 &&
                view->predicatePayload.size() == 2 &&
                view->predicateArguments.size() == 2,
            "acyclic predicate fold was mistaken for recursion");
    const auto &child = view->nested.front();
    checkBindings(*view);
    checkBindings(child);
    require(
        child.computation.helper == c.helper &&
            child.occurrence == view->predicatePayload.front() &&
            child.axes[0].identity != view->axes[0].identity &&
            child.occurrencePath.size() == 2 &&
            view->predicateArguments[0].source == view->items[0].formal &&
            view->predicateArguments[1].source == view->captures[0].formal &&
            child.seeds[0].actual == view->predicateArguments[0].formal &&
            child.seeds[0].resolved == view->items[0].formal &&
            child.captures[0].actual == view->predicateArguments[1].formal &&
            child.captures[0].resolved == view->captures[0].actual &&
            child.environment.resolveCapture(child.seeds[0].formal) ==
                child.seeds[0].formal,
        "predicate to nested mapping collapsed axes, captures, or state");
  });
  cases.run("structural work is cumulative across nested subjects", [&] {
    auto first = parseSourceString<ModuleOp>(fixture("nested-total"), &context);
    auto second =
        parseSourceString<ModuleOp>(fixture("nested-total"), &context);
    require(bool(first) && bool(second) && succeeded(verify(*first)) &&
                succeeded(verify(*second)),
            "nested controls not admitted");
    finite::ComputationWork measured;
    measured.structural = 1000;
    require(bool(finite::analyzeComputation(computation(*first), measured)),
            "nested measurement unavailable");
    uint64_t cost = 1000 - measured.structural;
    require(cost > 1 && cost < 1000, "structural walk was not charged");
    finite::ComputationWork shared;
    shared.structural = cost;
    auto accepted = finite::analyzeComputation(computation(*first), shared);
    require(accepted && accepted->nested.size() == 1 && !shared.structural &&
                !finite::analyzeComputation(computation(*second), shared),
            "second subject replenished structural work");
    shared.structural = cost - 1;
    require(!finite::analyzeComputation(computation(*second), shared) &&
                !shared.structural,
            "partial nested structure escaped exhausted traversal");
  });
  cases.run("nested selected-index proofs share optional evidence work", [&] {
    const char *source = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
!M = !algebra.field_matrix<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%m:!M):
   %d = "data.domain_indices"(%m) {axis=0:i64} : (!M)->!data.domain<ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64>)->()
 }) {sym_name="rows",sym_visibility="private",function_type=(!M)->!data.domain<ui64>} : ()->()
 "data.domain"() ({ ^entry(%m:!M):
   %d = "data.domain_indices"(%m) {axis=1:i64} : (!M)->!data.domain<ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64>)->()
 }) {sym_name="columns",sym_visibility="private",function_type=(!M)->!data.domain<ui64>} : ()->()
 func.func private @step(%s:!F,%j:ui64,%m:!M,%row:ui64)->!F attributes {data.preconditions=[#data.index_bound<1,2,1>,#data.index_bound<3,2,0>]} {
   %v = "data.bounded_matrix_at"(%m,%row,%j) : (!M,ui64,ui64)->!F
   %out = algebra.field_add %s,%v : (!F,!F)->!F
   func.return %out : !F
 }
 func.func private @row(%i:ui64,%m:!M)->!F attributes {data.preconditions=[#data.index_bound<0,1,0>]} {
   %zero = "algebra.constant"() {value="0"} : ()->!F
   %out = "algebra.finite_fold"(%m,%zero,%i) {domain=@columns,step=@step} : (!M,!F,ui64)->!F
   func.return %out : !F
 }
 "protocol.func"() ({ ^entry(%m:!M):
   %out = "algebra.finite_collect"(%m) {domain=@rows,body=@row} : (!M)->!V
   "protocol.return"(%out) : (!V)->()
 }) {sym_name="main",function_type=(!M)->!V,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
    auto module = parseSourceString<ModuleOp>(source, &context);
    require(bool(module) && succeeded(verify(*module)),
            "selected-index source not admitted");
    auto c = computation(*module);
    finite::ComputationWork measured;
    measured.evidence = 1000;
    auto view = finite::analyzeComputation(c, measured);
    require(view && view->nested.size() == 1 &&
                view->nested[0].accesses.size() == 1 &&
                view->nested[0].accesses[0].kind ==
                    finite::AccessKind::MatrixRow,
            "nested selected-index evidence unavailable");
    uint64_t cost = 1000 - measured.evidence;
    require(cost && cost < 1000, "selected-index proof bypassed shared work");
    finite::ComputationWork shared;
    shared.evidence = cost;
    view = finite::analyzeComputation(c, shared);
    require(view && view->nested[0].accesses.size() == 1 && !shared.evidence,
            "first nested proof did not consume exact allowance");
    auto second = parseSourceString<ModuleOp>(source, &context);
    view = finite::analyzeComputation(computation(*second), shared);
    require(view && view->nested.size() == 1 &&
                view->nested[0].accesses.empty() && !shared.evidence,
            "nested selected-index proof replenished optional allowance");
  });
  cases.run("predicate arguments and payload remain distinct from body", [&] {
    auto module =
        parseSourceString<ModuleOp>(fixture("total-predicate"), &context);
    auto c = computation(*module);
    auto view = finite::analyzeComputation(c);
    require(
        view && view->predicateArguments.size() == 3 &&
            view->predicatePayload.size() == 1 && view->payload.size() == 2 &&
            view->predicateResults.size() == 1 &&
            view->predicateArguments[0].source == view->items[0].formal &&
            view->predicateArguments[1].source == view->captures[0].formal &&
            view->predicateArguments[2].source == view->captures[1].formal &&
            view->resultMappings.size() == 1 &&
            !view->resultMappings[0].initial,
        "predicate environment, ordering, or collect result mapping lost");
  });
  cases.run("terminal stops retain structure without successful yields", [&] {
    auto module =
        parseSourceString<ModuleOp>(fixture("predicate-stop"), &context);
    require(bool(module) && succeeded(verify(*module)), "stop fixture refused");
    auto c = computation(*module);
    auto view = finite::analyzeComputation(c);
    require(view && isa<local::StopOp>(view->terminator) &&
                isa<local::StopOp>(view->predicateTerminator) &&
                view->results.empty() && view->resultMappings.empty() &&
                view->predicateResults.empty() && view->seeds.size() == 1 &&
                view->admission.size() == 4 &&
                view->predicateArguments.size() == 6,
            "terminal stop erased admission/state or fabricated a successful "
            "yield");
  });
  return cases.result();
}
