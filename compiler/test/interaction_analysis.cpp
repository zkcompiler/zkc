#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/Interactions.h"
#include "zkc/Analysis/MathematicalFacts.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace {
namespace pir = protocol_ir;
constexpr StringLiteral source = R"mlir(
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%n:ui64):
   "protocol.return"() : ()->()
 }) {sym_name="leaf",function_type=(ui64)->(),roles=["P","V"],
     input_roles=[["P","V"]],output_roles=[]} : ()->()
 "protocol.func"() ({ ^entry(%n:ui64):
   "protocol.return"() : ()->()
 }) {sym_name="other",function_type=(ui64)->(),roles=["P","V"],
     input_roles=[["P","V"]],output_roles=[]} : ()->()
 "protocol.func"() ({ ^entry(%n:ui64):
   %zero = "data.index"() {value=0:ui64} : ()->ui64
   "protocol.repeat"(%n,%n) ({ ^outer(%i:ui64,%trips:ui64):
     "protocol.repeat"(%trips,%trips) ({ ^inner(%j:ui64,%capture:ui64):
       protocol.apply @leaf(%capture) {roles=["P","V"],site="nested_call"} : (ui64)->()
       "protocol.yield"() : ()->()
     }) {site="inner",carried=0:i64,maximum=1048576:i64,
         roles=["P","V"],carried_roles=[]} : (ui64,ui64)->()
     "protocol.yield"() : ()->()
   }) {site="outer",carried=0:i64,maximum=1048576:i64,
       roles=["P","V"],carried_roles=[]} : (ui64,ui64)->()
   protocol.apply @leaf(%n) {roles=["P","V"],site="second_call"} : (ui64)->()
   "protocol.return"() : ()->()
 }) {sym_name="subject",function_type=(ui64)->(),roles=["P","V"],
     input_roles=[["P","V"]],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
pir::MathematicalOp declaration(ModuleOp module, StringRef name) {
  auto protocol = cast<pir::ProtocolModuleOp>(module.getBody()->front());
  auto result = SymbolTable(protocol).lookup<pir::MathematicalOp>(name);
  require(bool(result), "missing fixture declaration");
  return result;
}
const InteractionAction &at(const InteractionDeclaration &view,
                            ArrayRef<unsigned> path, facts::Work &work) {
  auto *action = take(view.lookup(path, work));
  require(action != nullptr, "missing source path");
  require(action->getPath() == path, "lookup changed a lexical coordinate");
  return *action;
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto parse = [&] {
    auto module = parseSourceString<ModuleOp>(source, &context);
    require(bool(module) && succeeded(admitStage(*module)),
            "interaction fixture was not admitted");
    return module;
  };
  Cases cases;
  cases.run("nested lexical coordinates retain actual blocks and values", [&] {
    auto module = parse();
    auto subject = declaration(*module, "subject");
    InteractionAnalysis analysis(*module);
    uint64_t remaining = 1000;
    facts::Work work(remaining);
    auto *view = take(analysis.get(subject, work));
    require(view->getDeclaration() == subject &&
                view->getBody().getBlock() == &subject.getBody().front(),
            "selected declaration identity was lost");
    auto outer = cast<pir::RepeatOp>(at(*view, {1}, work).getOperation());
    auto inner = cast<pir::RepeatOp>(at(*view, {1, 0}, work).getOperation());
    const auto &call = at(*view, {1, 0, 0}, work);
    require(call.getDeclaration() == subject &&
                call.getBlock() == &inner.getBody().front() &&
                call.getInputs().front() ==
                    inner.getBody().front().getArgument(1),
            "borrowed declaration/block/SSA association was reconstructed");
    require(at(*view, {1, 1}, work).getBlock() == &outer.getBody().front(),
            "outer yield acquired its nested block's path");
    require(at(*view, {0}, work).getOutputs().front() ==
                subject.getBody().front().front().getResult(0),
            "actual result identity was lost");
    require(!take(view->lookup({}, work)) && !take(view->lookup({99}, work)) &&
                !take(view->lookup({0, 0}, work)),
            "absent paths became source actions");
  });
  cases.run("symbolic repeats and applications stay retained and ordered", [&] {
    auto module = parse();
    auto subject = declaration(*module, "subject");
    auto leaf = declaration(*module, "leaf");
    InteractionAnalysis analysis(*module);
    uint64_t remaining = 1000;
    facts::Work work(remaining);
    auto *view = take(analysis.get(subject, work));
    require(view->getActions().size() == 8 &&
                view->getBody().getActions().size() == 4,
            "repeat was unrolled or application was expanded");
    auto nested = at(*view, {1}, work).getRepeatBody();
    require(nested && view->getSequence(*nested).getActions().size() == 2,
            "owned repeat did not supply its exact sequence");
    const auto &first = at(*view, {1, 0, 0}, work);
    const auto &second = at(*view, {2}, work);
    require(first.getReferencedSymbol() == leaf &&
                second.getReferencedSymbol() == leaf &&
                first.getOperation() != second.getOperation() &&
                !first.getRepeatBody() && !second.getRepeatBody(),
            "two applications merged their source sites or expanded a callee");
    require(analysis.getOwner() == module->getOperation() &&
                analysis.getOwner() != first.getReferencedSymbol(),
            "referenced symbols became the containing owner");
    require(view->getActions()[1].getOperation() ==
                    at(*view, {1}, work).getOperation() &&
                view->getActions()[6].getOperation() == second.getOperation(),
            "source preorder changed");
  });
  cases.run("equal paths preserve distinct source declarations", [&] {
    auto module = parse();
    InteractionAnalysis analysis(*module);
    uint64_t remaining = 1000;
    facts::Work work(remaining);
    auto *left = take(analysis.get(declaration(*module, "leaf"), work));
    auto *right = take(analysis.get(declaration(*module, "other"), work));
    const auto &a = at(*left, {0}, work);
    const auto &b = at(*right, {0}, work);
    require(a.getPath() == b.getPath() &&
                a.getDeclaration() != b.getDeclaration() &&
                a.getOperation() != b.getOperation(),
            "lexical coordinates merged distinct declaration identities");
  });
  cases.run("clear expires borrowed views before source mutation", [&] {
    auto module = parse();
    auto subject = declaration(*module, "subject");
    InteractionAnalysis analysis(*module);
    uint64_t remaining = 1000;
    facts::Work work(remaining);
    auto *before = take(analysis.get(subject, work));
    require(take(analysis.get(subject, work)) == before,
            "unchanged snapshot did not reuse its structural view");
    Operation *removed = at(*before, {2}, work).getOperation();
    analysis.clear();
    // No pointer/reference into the expired view is read after clear().
    removed->erase();
    require(succeeded(admitStage(*module)), "changed source was not admitted");
    auto *after = take(analysis.get(subject, work));
    require(after->getActions().size() == 7 &&
                isa<pir::MathematicalReturnOp>(
                    at(*after, {2}, work).getOperation()),
            "reconstruction reused an erased operation or stale source path");
  });
  cases.run("foreign modules and callable owners are refused", [&] {
    auto module = parse();
    OwningOpRef<ModuleOp> clone(cast<ModuleOp>(module->clone()));
    InteractionAnalysis analysis(*module);
    uint64_t remaining = 1000;
    facts::Work work(remaining);
    refuses(analysis.get(declaration(*clone, "subject"), work),
            "interaction-analysis-owner");
    InteractionAnalysis local(declaration(*module, "subject"));
    refuses(local.get(declaration(*module, "subject"), work),
            "interaction-analysis-owner");
    refuses(analysis.get(nullptr, work), "interaction-analysis-owner");
    InteractionAnalysis candidate(*clone);
    (void)take(candidate.get(declaration(*clone, "subject"), work));
  });
  cases.run("unsupported subjects are distinct from capacity", [&] {
    auto module = parse();
    InteractionAnalysis analysis(*module);
    uint64_t remaining = 1000;
    facts::Work work(remaining);
    refuses(analysis.get(&module->getBody()->front(), work),
            "interaction-analysis-unsupported");
    require(!work.exhausted(), "unsupported subject exhausted analysis work");
  });
  cases.run(
      "capacity is sticky on warm extraction and source-path queries", [&] {
        auto module = parse();
        auto subject = declaration(*module, "subject");
        InteractionAnalysis analysis(*module);
        uint64_t remaining = 1000;
        facts::Work work(remaining);
        auto *view = take(analysis.get(subject, work));
        uint64_t empty = 0;
        facts::Work limited(empty);
        refuses(analysis.get(subject, limited),
                "interaction-analysis-capacity");
        empty = 1000;
        refuses(analysis.get(subject, limited),
                "interaction-analysis-capacity");
        refuses(view->lookup({1}, limited), "interaction-analysis-capacity");
        require(limited.exhausted() && empty == 1000,
                "a cached view replenished exhausted work");
        (void)take(analysis.get(subject, work));
      });
  cases.run(
      "depth and size limits refuse without caching partial structure", [&] {
        auto module = parse();
        auto subject = declaration(*module, "subject");
        for (auto limits : {InteractionAnalysis::Limits{1, 100000},
                            InteractionAnalysis::Limits{64, 2}}) {
          InteractionAnalysis analysis(*module, limits);
          uint64_t remaining = 1000;
          facts::Work work(remaining);
          refuses(analysis.get(subject, work), "interaction-analysis-capacity");
          require(work.exhausted(), "structural capacity was not sticky");
          facts::Work fresh(remaining);
          auto *leaf = take(analysis.get(declaration(*module, "leaf"), fresh));
          require(leaf->getActions().size() == 1,
                  "failed view poisoned a sibling");
          refuses(analysis.get(subject, fresh),
                  "interaction-analysis-capacity");
        }
      });
  cases.run("cold and warm queries pay equal cumulative extraction work", [&] {
    auto module = parse();
    auto subject = declaration(*module, "subject");
    InteractionAnalysis warm(*module);
    uint64_t coldRemaining = 1000, warmRemaining = 1000;
    facts::Work coldWork(coldRemaining), warmWork(warmRemaining);
    auto *coldView = take(warm.get(subject, coldWork));
    auto *warmView = take(warm.get(subject, warmWork));
    require(coldRemaining == warmRemaining && coldRemaining < 1000,
            "cache warmth changed the successful allowance");
    uint64_t cost = 1000 - coldRemaining;
    uint64_t coldPath = 1000, warmPath = 1000;
    facts::Work coldPathWork(coldPath), warmPathWork(warmPath);
    (void)at(*coldView, {1, 0, 0}, coldPathWork);
    (void)at(*warmView, {1, 0, 0}, warmPathWork);
    require(coldPath == warmPath && coldPath < 1000,
            "source-path queries hid work behind a warm view");
    for (uint64_t budget = 0; budget < cost; ++budget) {
      InteractionAnalysis cold(*module);
      uint64_t a = budget, b = budget;
      facts::Work left(a), right(b);
      refuses(cold.get(subject, left), "interaction-analysis-capacity");
      refuses(warm.get(subject, right), "interaction-analysis-capacity");
      require(a == b && left.exhausted() && right.exhausted(),
              "cold/warm capacity boundary changed");
    }
    uint64_t exact = cost * 2;
    facts::Work cumulative(exact);
    (void)take(warm.get(subject, cumulative));
    (void)take(warm.get(subject, cumulative));
    require(exact == 0 && !cumulative.exhausted(),
            "cache hits did not debit the same cumulative allowance");
    refuses(warm.get(subject, cumulative), "interaction-analysis-capacity");
  });
  cases.run("module analysis depends on both subject and symbol closure", [&] {
    auto module = parse();
    auto subject = declaration(*module, "subject");
    ModuleAnalysisManager storage(*module, nullptr);
    AnalysisManager manager = storage;
    uint64_t remaining = 1000;
    facts::Work work(remaining);
    auto *initial =
        take(manager.getAnalysis<InteractionAnalysis>().get(subject, work));
    auto *nestedCall = at(*initial, {1, 0, 0}, work).getOperation();
    auto *secondCall = at(*initial, {2}, work).getOperation();
    auto leaf = declaration(*module, "leaf");
    require(manager.getCachedAnalysis<SymbolClosureAnalysis>().has_value(),
            "analysis did not register its symbol closure dependency");
    AnalysisManager::PreservedAnalyses both;
    both.preserve<InteractionAnalysis>();
    both.preserve<SymbolClosureAnalysis>();
    manager.invalidate(both);
    require(manager.getCachedAnalysis<InteractionAnalysis>().has_value(),
            "preserved immutable structure was discarded");
    AnalysisManager::PreservedAnalyses subjectOnly;
    subjectOnly.preserve<InteractionAnalysis>();
    manager.invalidate(subjectOnly);
    require(!manager.getCachedAnalysis<InteractionAnalysis>(),
            "subject preservation concealed an invalidated symbol closure");
    // The old view has expired before mutating the inspected symbol and uses.
    leaf->setAttr(SymbolTable::getSymbolAttrName(),
                  StringAttr::get(&context, "renamed_leaf"));
    auto target = FlatSymbolRefAttr::get(&context, "renamed_leaf");
    nestedCall->setAttr("callee", target);
    secondCall->setAttr("callee", target);
    require(succeeded(admitStage(*module)), "renamed symbol was not admitted");
    auto *rebuilt =
        take(manager.getAnalysis<InteractionAnalysis>().get(subject, work));
    require(at(*rebuilt, {1, 0, 0}, work).getReferencedSymbol() == leaf &&
                at(*rebuilt, {2}, work).getReferencedSymbol() == leaf,
            "invalidated symbol inventory survived reconstruction");
    AnalysisManager::PreservedAnalyses closureOnly;
    closureOnly.preserve<SymbolClosureAnalysis>();
    manager.invalidate(closureOnly);
    require(!manager.getCachedAnalysis<InteractionAnalysis>(),
            "symbol preservation concealed an invalidated subject");
  });
  return cases.result();
}
