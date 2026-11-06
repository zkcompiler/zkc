#include "../lib/Compiler/NativeProofVerification.h"
#include "../lib/Compiler/NativeRequest.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace pir = protocol_ir;
namespace req = zkc::detail;
namespace {
pir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<pir::ProtocolModuleOp>(module.getBody()->front());
}
NativeProofPolicy policy() {
  NativeProofPolicy result;
  result.entry = "main";
  result.producer = "P";
  result.validator = "V";
  result.suite = "merlin3.bls12-381.fr64be/0";
  result.publicInputs = {0, 1, 2, 3};
  return result;
}
std::string sourceText(StringRef body) {
  return (Twine(R"mlir(module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%choice:i1,%other:i1,%x:ui64,%y:ui64):
)mlir") + body +
          R"mlir(
 "protocol.return"() : ()->()
 }) {sym_name="main",function_type=(i1,i1,ui64,ui64)->(),roles=["P","V"],input_roles=[["P","V"],["P","V"],["P","V"],["P","V"]],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir")
      .str();
}
std::string emptyBranch(StringRef selector = "%choice",
                        StringRef site = "choose") {
  return (Twine("\"protocol.branch\"(") + selector + R"mlir() ({
 "protocol.yield"() : ()->()
 }, { "protocol.yield"() : ()->()
 }) {site=")mlir" +
          site +
          R"mlir(",roles=["P","V"],output_roles=[],alternatives=["then","else"]} : (i1)->()
)mlir")
      .str();
}
std::string replace(std::string text, StringRef from, StringRef to) {
  auto at = text.find(from.str());
  require(at != std::string::npos, "missing fixture fragment");
  text.replace(at, from.size(), to.str());
  return text;
}
OwningOpRef<ModuleOp> projected(MLIRContext &context, StringRef text) {
  auto source =
      parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
  require(bool(source) && succeeded(admitStage(*source)),
          "source fixture admission failed");
  OwningOpRef<ModuleOp> result(cast<ModuleOp>((*source)->clone()));
  PassManager manager(&context);
  manager.addPass(protocol::createProjectProtocolPass(false));
  require(succeeded(manager.run(*result)) && succeeded(admitStage(*result)),
          "ordinary projection admission failed");
  require(succeeded(mathematical::verifyProjectionPreserved(*source, *result)),
          "ordinary projection correspondence failed");
  return result;
}
Operation *site(ModuleOp module, StringRef name, StringRef role) {
  Operation *result = nullptr;
  module.walk([&](Operation *op) {
    auto p = op->getParentOfType<pir::ParticipantOp>();
    auto s = op->getAttrOfType<StringAttr>("site");
    if (p && p.getRole() == role && s && s.getValue() == name)
      result = op;
  });
  require(result != nullptr, "missing participant site");
  return result;
}
SmallVector<req::NativeTranscriptEvent> requests(MLIRContext &context,
                                                 ArrayRef<StringRef> sites) {
  SmallVector<req::NativeTranscriptEvent> result;
  for (auto site : sites) {
    req::NativeTranscriptEvent event{};
    event.site = site.str();
    event.payload = IntegerType::get(&context, 64, IntegerType::Unsigned);
    event.reconstructed = true;
    result.push_back(std::move(event));
  }
  return result;
}
// This consumer reads actual inserted operations and exact rows. In particular,
// it never consults NativeRequestEmission::requests or generated call IDs.
bool read(const req::NativeRequestFrame &frame, Block &actual,
          req::NativeRequestValues ordinary, req::NativeRequestValues replica,
          uint64_t &allowance) {
  Operation *cursor = actual.empty() ? nullptr : &actual.front();
  for (Operation &source : *frame.producer) {
    if (!req::readNativeRequestSteps(frame, &source, cursor, ordinary, replica,
                                     allowance) ||
        !cursor || source.getName() != cursor->getName())
      return false;
    auto selected = frame.branches.find(&source);
    if (selected != frame.branches.end()) {
      const auto &branch = *selected->second;
      auto candidate = dyn_cast<pir::ParticipantBranchOp>(cursor);
      if (!req::readNativeRequestBranchInputs(branch, candidate, 0, 0, ordinary,
                                              replica))
        return false;
      for (unsigned i = 0; i < branch.arms.size(); ++i) {
        auto childOrdinary = ordinary, childReplica = replica;
        if (!req::bindNativeRequestBranchArm(branch, candidate, i, 0, 0,
                                             childOrdinary, childReplica) ||
            !read(*branch.arms[i], candidate->getRegion(i).front(),
                  std::move(childOrdinary), std::move(childReplica), allowance))
          return false;
      }
      if (!req::bindNativeRequestBranchOutputs(branch, candidate, 0, ordinary,
                                               replica))
        return false;
    } else if (auto found = frame.loops.find(&source);
               found != frame.loops.end()) {
      const auto &loop = *found->second;
      auto candidate = dyn_cast<pir::ProtocolLoopOp>(cursor);
      if (!candidate || !req::readNativeRequestLoopInputs(loop, candidate, 0,
                                                          ordinary, replica))
        return false;
      auto childOrdinary = ordinary, childReplica = replica;
      auto p = loop.producer;
      unsigned split = 1 + p.getCarried();
      for (auto [i, arg] : enumerate(loop.body->producer->getArguments()))
        childOrdinary[arg] = candidate.getBody().front().getArgument(
            i < split ? i : i + loop.carried.size());
      if (!req::bindNativeRequestLoop(loop, candidate, 0, childReplica) ||
          !read(*loop.body, candidate.getBody().front(), childOrdinary,
                childReplica, allowance))
        return false;
      for (auto [i, index] : enumerate(loop.carried))
        replica[pir::ProtocolLoopOp(loop.validator).getResult(index)] =
            candidate.getResult(p.getNumResults() + i);
      for (auto [a, b] : zip(source.getResults(), candidate.getResults()))
        ordinary[a] = b;
    } else if (isa<pir::ProtocolYieldOp>(source) && frame.branch) {
      if (!req::readNativeRequestBranchYield(*frame.branch, frame.arm,
                                             cursor->getOperands(), 0, ordinary,
                                             replica))
        return false;
    } else {
      unsigned extra = isa<pir::ProtocolYieldOp>(source) && frame.loop
                           ? frame.loop->yielded.size()
                           : 0;
      if (cursor->getNumOperands() != source.getNumOperands() + extra ||
          cursor->getNumResults() != source.getNumResults() ||
          cursor->getAttrDictionary() != source.getAttrDictionary())
        return false;
      for (auto [i, operand] : enumerate(source.getOperands()))
        if (ordinary.lookup(operand) != cursor->getOperand(i))
          return false;
      if (extra && !req::readNativeRequestYield(
                       *frame.loop, cursor->getOperands().take_back(extra),
                       ordinary, replica))
        return false;
      if (frame.requests.count(&source) &&
          !req::resolveNativeRequestValue(frame.requests.lookup(&source),
                                          ordinary, replica))
        return false;
      for (auto [a, b] : zip(source.getResults(), cursor->getResults()))
        ordinary[a] = b;
    }
    cursor = cursor->getNextNode();
  }
  return !cursor;
}
bool read(const req::NativeRequestPlan &plan, ModuleOp candidate) {
  auto p = SymbolTable(unit(candidate))
               .lookup<pir::ParticipantOp>(
                   pir::ParticipantOp(plan.producer).getSymName());
  req::NativeRequestValues ordinary;
  for (auto [a, b] : zip(plan.root->producer->getArguments(),
                         p.getBody().front().getArguments()))
    ordinary[a] = b;
  uint64_t allowance = 1000000;
  return read(*plan.root, p.getBody().front(), std::move(ordinary),
              req::NativeRequestValues{}, allowance);
}
OwningOpRef<ModuleOp> emit(const req::NativeRequestPlan &plan,
                           ModuleOp source) {
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(source->clone()));
  unsigned fresh = 0;
  take(req::emitNativeRequests(plan, unit(*candidate), [&] {
    return "replica_" + std::to_string(fresh++);
  }));
  require(succeeded(verify(*candidate)), "emitted MLIR does not form");
  require(read(plan, *candidate),
          "independent request reader refused emission");
  return candidate;
}
constexpr StringLiteral replicaBranch = R"mlir(
 %seed = "data.index_wrapping_add"(%x,%y) : (ui64,ui64)->ui64
 %joined = "protocol.branch"(%choice,%seed,%x) ({
 ^then(%thenSeed:ui64,%thenX:ui64):
  %request = "data.index_wrapping_add"(%thenSeed,%thenX) : (ui64,ui64)->ui64
  %received = protocol.exchange %request {site="request",sender="V",receiver="P"} : ui64
  "protocol.yield"(%request) : (ui64)->()
 }, {
 ^else(%elseSeed:ui64,%elseX:ui64):
  "protocol.yield"(%elseSeed) : (ui64)->()
 }) {site="choose",roles=["P","V"],output_roles=[["V"]],alternatives=["then","else"]} : (i1,ui64,ui64)->ui64
 %last = protocol.exchange %joined {site="last",sender="V",receiver="P"} : ui64
)mlir";
// Different role result rows: V's choice is result 1; P's is result 0.
constexpr StringLiteral joinedSelectors = R"mlir(
 %unused,%joined = "protocol.branch"(%choice,%other,%x) ({
 ^then(%thenOther:i1,%thenX:ui64):
  "protocol.yield"(%thenX,%thenOther) : (ui64,i1)->()
 }, {
 ^else(%elseOther:i1,%elseX:ui64):
  "protocol.yield"(%elseX,%elseOther) : (ui64,i1)->()
 }) {site="first",roles=["P","V"],output_roles=[["V"],["P","V"]],alternatives=["then","else"]} : (i1,i1,ui64)->(ui64,i1)
)mlir";
// Only V demands these total selections before transport. P must synthesize
// one complete invocation, including the dormant arm and both result slots.
std::string mathRequestText() {
  auto text = sourceText(R"mlir(
 %first,%second = "data.branch"(%choice,%other,%x,%y) ({
 ^then(%innerChoice:i1,%left:ui64,%right:ui64):
  %nested = "data.branch"(%innerChoice,%left,%right) ({
  ^innerThen(%nestedLeft:ui64,%nestedRight:ui64):
   %sum = func.call @request_add(%nestedLeft,%nestedRight) : (ui64,ui64)->ui64
   "data.yield"(%sum) : (ui64)->()
  }, { ^innerElse(%unusedLeft:ui64,%nestedFallback:ui64):
   "data.yield"(%nestedFallback) : (ui64)->()
  }) {alternatives=["then","else"]} : (i1,ui64,ui64)->ui64
  "data.yield"(%nested,%left) : (ui64,ui64)->()
 }, { ^else(%unusedChoice:i1,%fallbackLeft:ui64,%fallbackRight:ui64):
  "data.yield"(%fallbackRight,%fallbackLeft) : (ui64,ui64)->()
 }) {alternatives=["then","else"]} : (i1,i1,ui64,ui64)->(ui64,ui64)
 %received = protocol.exchange %first {site="request",sender="V",receiver="P"} : ui64
 %receivedAgain = protocol.exchange %second {site="last",sender="V",receiver="P"} : ui64
)mlir");
  return replace(text, " \"protocol.func\"()", R"mlir(
 func.func private @request_add(%a:ui64,%b:ui64)->ui64 {
  %sum = "data.index_wrapping_add"(%a,%b) : (ui64,ui64)->ui64
  return %sum : ui64
 }
 func.func private @request_left(%a:ui64,%b:ui64)->ui64 {
  return %a : ui64
 }
 "protocol.func"())mlir");
}
data::BranchOp mathReplica(ModuleOp module, StringRef role = "P") {
  auto p = site(module, "request", role)->getParentOfType<pir::ParticipantOp>();
  auto branches = p.getBody().front().getOps<data::BranchOp>();
  require(hasSingleElement(branches), "expected one complete Math replica");
  return *branches.begin();
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("public selector on event-free identity route", [&] {
    auto source = projected(context, sourceText(emptyBranch()));
    auto plan = take(req::planNativeRequests(unit(*source), policy(), {}));
    require(plan.root->branches.size() == 1 && plan.frames.size() == 3,
            "branch arms are absent from the plan");
    emit(plan, *source);
  });
  cases.run("event-free unrelated selector refuses", [&] {
    auto source = projected(context, sourceText(emptyBranch()));
    auto p = policy();
    p.publicInputs = {1, 2, 3};
    refuses(req::planNativeRequests(unit(*source), p, {}),
            "native-request-reconstruction");
  });
  cases.run("actual selector substitution refuses", [&] {
    auto source = projected(context, sourceText(emptyBranch()));
    auto *branch = site(*source, "choose", "V");
    auto participant = branch->getParentOfType<pir::ParticipantOp>();
    branch->setOperand(0, participant.getBody().front().getArgument(1));
    refuses(req::planNativeRequests(unit(*source), policy(), {}),
            "native-request-reconstruction");
  });
  cases.run("joins use each role's exact result positions", [&] {
    auto source =
        projected(context, sourceText(joinedSelectors.str() +
                                      emptyBranch("%joined", "second")));
    auto plan = take(req::planNativeRequests(unit(*source), policy(), {}));
    auto &branch = *plan.root->branches.begin()->second;
    require(branch.producer.getNumResults() != branch.validator.getNumResults(),
            "fixture did not retain distinct role result rows");
    require(branch.joins.size() == 1 && branch.joins.begin()->second,
            "exact all-arm join was not memoized");
    emit(plan, *source);
  });
  cases.run("one-arm relation cannot escape to a later selector", [&] {
    auto source =
        projected(context, sourceText(joinedSelectors.str() +
                                      emptyBranch("%joined", "second")));
    auto branch = cast<pir::ParticipantBranchOp>(site(*source, "first", "V"));
    auto &arm = branch->getRegion(1).front();
    OpBuilder builder(&context);
    builder.setInsertionPoint(&arm.back());
    OperationState state(branch.getLoc(), "arith.constant");
    state.addTypes(builder.getI1Type());
    state.addAttribute("value", builder.getBoolAttr(false));
    arm.back().setOperand(1, builder.create(state)->getResult(0));
    refuses(req::planNativeRequests(unit(*source), policy(), {}),
            "native-request-reconstruction");
  });
  cases.run("reverse requests capture replicas and yield branch outputs", [&] {
    auto source = projected(context, sourceText(replicaBranch));
    auto events = requests(context, {"request", "last"});
    auto plan = take(req::planNativeRequests(unit(*source), policy(), events));
    auto &branch = *plan.root->branches.begin()->second;
    require(!branch.captures.empty() && branch.outputs.size() == 1 &&
                branch.arms[0]->requests.size() == 1 &&
                branch.arms[1]->requests.empty(),
            "requests or replica state escaped their actual arm frontier");
    emit(plan, *source);
  });
  for (bool capture : {false, true})
    cases.run(
        capture ? "actual replica capture substitution refuses"
                : "actual replica yield substitution refuses",
        [&] {
          auto source = projected(context, sourceText(replicaBranch));
          auto events = requests(context, {"request", "last"});
          auto plan =
              take(req::planNativeRequests(unit(*source), policy(), events));
          auto candidate = emit(plan, *source);
          auto &branch = *plan.root->branches.begin()->second;
          auto actual =
              cast<pir::ParticipantBranchOp>(site(*candidate, "choose", "P"));
          if (capture) {
            auto p = actual->getParentOfType<pir::ParticipantOp>();
            actual->setOperand(branch.producer.getNumOperands(),
                               p.getBody().front().getArgument(2));
          } else {
            auto &arm = actual->getRegion(0).front();
            arm.back().setOperand(branch.producer.getNumResults(),
                                  arm.getArgument(arm.getNumArguments() - 1));
          }
          require(!read(plan, *candidate),
                  "mutated replica state was accepted");
        });
  for (bool capture : {false, true})
    cases.run(
        capture ? "missing replica capture refuses"
                : "missing replica yield refuses",
        [&] {
          auto source = projected(context, sourceText(replicaBranch));
          auto events = requests(context, {"request", "last"});
          auto plan =
              take(req::planNativeRequests(unit(*source), policy(), events));
          auto candidate = emit(plan, *source);
          auto &branch = *plan.root->branches.begin()->second;
          auto actual =
              cast<pir::ParticipantBranchOp>(site(*candidate, "choose", "P"));
          if (capture)
            actual->eraseOperand(branch.producer.getNumOperands());
          else
            actual->getRegion(0).front().back().eraseOperand(
                branch.producer.getNumResults());
          require(!read(plan, *candidate), "missing replica row was accepted");
        });
  cases.run("nonordinary reference cannot fall back to source SSA", [&] {
    auto source = projected(context, sourceText(replicaBranch));
    auto events = requests(context, {"request", "last"});
    auto plan = take(req::planNativeRequests(unit(*source), policy(), events));
    auto &branch = *plan.root->branches.begin()->second;
    require(!branch.captured.empty(), "missing replica capture fixture");
    branch.captured[0] = {plan.root->producer->getArgument(2), false};
    OwningOpRef<ModuleOp> candidate(cast<ModuleOp>((*source)->clone()));
    refuses(
        req::emitNativeRequests(plan, unit(*candidate), [] { return "fresh"; }),
        "native-request-emission");
  });
  cases.run("later publication cannot justify branch entry capture", [&] {
    auto text = replace(
        replicaBranch.str(),
        "%seed = \"data.index_wrapping_add\"(%x,%y) : (ui64,ui64)->ui64",
        "%seed = protocol.exchange %x "
        "{site=\"published\",sender=\"P\",receiver=\"V\"} : ui64");
    auto source = projected(context, sourceText(text));
    auto *published = site(*source, "published", "P");
    published->moveAfter(site(*source, "choose", "P"));
    auto events = requests(context, {"request", "last"});
    refuses(req::planNativeRequests(unit(*source), policy(), events),
            "native-request-reconstruction");
  });
  cases.run("sequential branches share bounded join summaries", [&] {
    std::string body;
    for (unsigned i = 0; i < 160; ++i) {
      auto name = std::to_string(i);
      auto input = i ? "%choice" + std::to_string(i - 1) : "%choice";
      body +=
          "%choice" + name + " = \"protocol.branch\"(" + input + "," + input +
          R"mlir() ({ ^then(%c:i1):
 "protocol.yield"(%c) : (i1)->()
 }, { ^else(%c:i1): "protocol.yield"(%c) : (i1)->()
 }) {site="branch_)mlir" +
          name +
          R"mlir(",roles=["P","V"],output_roles=[["P","V"]],alternatives=["then","else"]} : (i1,i1)->i1
)mlir";
    }
    body += emptyBranch("%choice159", "last");
    auto source = projected(context, sourceText(body));
    auto plan = take(req::planNativeRequests(unit(*source), policy(), {}));
    require(plan.root->branches.size() == 161,
            "sequential summary lost branches");
    for (auto &item : plan.root->branches)
      require(item.second->joins.size() <= 1,
              "join cache enumerated branch paths");
    emit(plan, *source);
  });
  cases.run("closed Math selection supplies whole selector agreement", [&] {
    auto body = R"mlir(
 %selected = "data.branch"(%choice,%other) ({ ^then(%thenOther:i1):
  "data.yield"(%thenOther) : (i1)->()
 }, { ^else(%elseOther:i1): "data.yield"(%elseOther) : (i1)->()
 }) {alternatives=["then","else"]} : (i1,i1)->i1
)mlir";
    auto source = projected(
        context, sourceText(std::string(body) + emptyBranch("%selected")));
    auto plan = take(req::planNativeRequests(unit(*source), policy(), {}));
    emit(plan, *source);
  });
  cases.run(
      "generated total Math request retains nested regions and results", [&] {
        auto source = projected(context, mathRequestText());
        auto events = requests(context, {"request", "last"});
        auto plan =
            take(req::planNativeRequests(unit(*source), policy(), events));
        require(plan.root->definitions.size() == 1,
                "two result demands duplicated the selected invocation");
        auto candidate = emit(plan, *source);
        auto selected = mathReplica(*candidate);
        require(selected.getNumResults() == 2 &&
                    selected->getRegion(0)
                            .front()
                            .getOps<data::BranchOp>()
                            .begin() != selected->getRegion(0)
                                            .front()
                                            .getOps<data::BranchOp>()
                                            .end(),
                "nested Math region or result disappeared");
      });
  for (StringRef mutation :
       {"selector", "capture", "yield", "symbol", "body", "nested selector",
        "nested capture", "dormant yield", "ambient capture", "extra operation",
        "payload shape"})
    cases.run(Twine("actual generated Math replica rejects ") + mutation, [&] {
      auto source = projected(context, mathRequestText());
      if (mutation == "symbol") {
        // Preparation inlines helpers. Exercise the admitted retained-call
        // profile independently, using the same total helper definition.
        auto selected = mathReplica(*source, "V");
        auto nested =
            cast<data::BranchOp>(selected->getRegion(0).front().front());
        Operation *sum = &nested->getRegion(0).front().front();
        OpBuilder builder(sum);
        OperationState state(sum->getLoc(), func::CallOp::getOperationName());
        state.addOperands(sum->getOperands());
        state.addTypes(sum->getResultTypes());
        state.addAttribute("callee",
                           FlatSymbolRefAttr::get(&context, "request_add"));
        Operation *call = builder.create(state);
        sum->getResult(0).replaceAllUsesWith(call->getResult(0));
        sum->erase();
        require(succeeded(admitStage(*source)),
                "retained total helper fixture did not form");
      }
      auto events = requests(context, {"request", "last"});
      auto plan =
          take(req::planNativeRequests(unit(*source), policy(), events));
      auto candidate = emit(plan, *source);
      auto selected = mathReplica(*candidate);
      auto &thenArm = selected->getRegion(0).front();
      auto nested = cast<data::BranchOp>(thenArm.front());
      auto &inner = nested->getRegion(0).front();
      Operation *computation = &inner.front();
      OpBuilder builder(&context);
      if (mutation == "selector")
        selected->setOperand(0, selected->getOperand(1));
      else if (mutation == "capture")
        selected->setOperand(2, selected->getOperand(3));
      else if (mutation == "yield")
        thenArm.back().setOperand(0, thenArm.getArgument(1));
      else if (mutation == "symbol")
        cast<func::CallOp>(computation).setCallee("request_left");
      else if (mutation == "body") {
        builder.setInsertionPoint(computation);
        OperationState state(computation->getLoc(),
                             data::IndexWrappingSubtractOp::getOperationName());
        state.addOperands(computation->getOperands());
        state.addTypes(computation->getResultTypes());
        auto *changed = builder.create(state);
        computation->getResult(0).replaceAllUsesWith(changed->getResult(0));
        computation->erase();
      } else if (mutation == "nested selector") {
        builder.setInsertionPoint(nested);
        OperationState state(nested.getLoc(), "arith.constant");
        state.addTypes(builder.getI1Type());
        state.addAttribute("value", builder.getBoolAttr(false));
        nested->setOperand(0, builder.create(state)->getResult(0));
      } else if (mutation == "nested capture")
        nested->setOperand(1, thenArm.getArgument(2));
      else if (mutation == "dormant yield") {
        auto &arm = nested->getRegion(1).front();
        arm.back().setOperand(0, arm.getArgument(0));
      } else if (mutation == "ambient capture")
        computation->setOperand(0, selected->getOperand(2));
      else if (mutation == "extra operation") {
        builder.setInsertionPoint(&inner.back());
        IRMapping mapping;
        builder.clone(*computation, mapping);
      } else
        inner.addArgument(builder.getI1Type(), selected.getLoc());
      require(!read(plan, *candidate),
              "mutated actual Math replica was accepted");
    });
  cases.run("same-typed private Math capture is not reconstructible", [&] {
    auto source = projected(context, mathRequestText());
    auto events = requests(context, {"request", "last"});
    auto p = policy();
    p.publicInputs = {0, 1, 3};
    refuses(req::planNativeRequests(unit(*source), p, events),
            "native-request-reconstruction");
  });
  cases.run("generated variant Math replica binds exact payload slots", [&] {
    auto text = R"mlir(
!Choice = !data.variant<#data.identity<["atom", "MathRequestChoice"]>, [#data.alternative<"none">, #data.alternative<"some", [ui64,ui64]>]>
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%choice:!Choice,%x:ui64):
 %selected = "data.branch"(%choice,%x) ({
 ^none(%fallback:ui64): "data.yield"(%fallback) : (ui64)->()
 }, { ^some(%firstPayload:ui64,%secondPayload:ui64,%capture:ui64):
  %sum = "data.index_wrapping_add"(%firstPayload,%capture) : (ui64,ui64)->ui64
  "data.yield"(%sum) : (ui64)->()
 }) {alternatives=["none","some"]} : (!Choice,ui64)->ui64
 %received = protocol.exchange %selected {site="request",sender="V",receiver="P"} : ui64
 "protocol.return"() : ()->()
 }) {sym_name="main",function_type=(!Choice,ui64)->(),roles=["P","V"],input_roles=[["P","V"],["P","V"]],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
    auto source = projected(context, text);
    auto events = requests(context, {"request"});
    auto plan = take(req::planNativeRequests(unit(*source), policy(), events));
    auto candidate = emit(plan, *source);
    auto selected = mathReplica(*candidate);
    auto &arm = selected->getRegion(1).front();
    require(arm.getNumArguments() == 3, "variant payload/capture shape lost");
    arm.front().setOperand(0, arm.getArgument(1));
    require(!read(plan, *candidate), "same-typed sibling payload was accepted");
  });
  cases.run(
      "Math region reader charges nested work and exact input arity", [&] {
        auto source = projected(context, mathRequestText());
        auto events = requests(context, {"request", "last"});
        auto plan =
            take(req::planNativeRequests(unit(*source), policy(), events));
        auto candidate = emit(plan, *source);
        auto selected = mathReplica(*candidate);
        auto p = selected->getParentOfType<pir::ParticipantOp>();
        req::NativeRequestValues ordinary, replica;
        for (auto [a, b] : zip(plan.root->producer->getArguments(),
                               p.getBody().front().getArguments()))
          ordinary[a] = b;
        auto *anchor = site(*source, "request", "P");
        Operation *cursor = selected;
        uint64_t allowance = 40;
        require(!req::readNativeRequestSteps(*plan.root, anchor, cursor,
                                             ordinary, replica, allowance),
                "nested region work escaped the reader allowance");
        require(allowance == 0, "exhausted nested allowance was not returned");
        auto &step = plan.root->before[anchor].front();
        cursor = selected;
        replica.clear();
        allowance = 1000000;
        require(req::readNativeRequestSteps(*plan.root, anchor, cursor,
                                            ordinary, replica, allowance) &&
                    replica.size() == 2 &&
                    replica.lookup(step.source->getResult(0)) ==
                        selected.getResult(0) &&
                    replica.lookup(step.source->getResult(1)) ==
                        selected.getResult(1),
                "result positions changed or arm-local values escaped");
        require(allowance < 1000000,
                "nested work did not debit caller allowance");
        step.inputs.pop_back();
        cursor = selected;
        replica.clear();
        require(!req::readNativeRequestSteps(*plan.root, anchor, cursor,
                                             ordinary, replica, allowance),
                "truncated planned inputs were silently zipped");
      });
  cases.run("caller state slots follow replica captures and outputs", [&] {
    auto source = projected(context, sourceText(emptyBranch()));
    auto plan = take(req::planNativeRequests(unit(*source), policy(), {}));
    auto candidate = emit(plan, *source);
    auto &branch = *plan.root->branches.begin()->second;
    auto old = cast<pir::ParticipantBranchOp>(site(*candidate, "choose", "P"));
    auto participant = old->getParentOfType<pir::ParticipantOp>();
    auto &root = participant.getBody().front();
    OpBuilder builder(old);
    OperationState state(old.getLoc(), old->getName());
    state.addOperands({old.getOperand(0), root.getArgument(1)});
    state.addTypes(builder.getI1Type());
    state.addAttributes(old->getAttrs());
    state.addRegion();
    state.addRegion();
    auto actual = cast<pir::ParticipantBranchOp>(builder.create(state));
    for (unsigned i = 0; i < 2; ++i) {
      actual->getRegion(i).takeBody(old->getRegion(i));
      auto &arm = actual->getRegion(i).front();
      auto argument = arm.addArgument(builder.getI1Type(), old.getLoc());
      arm.back().insertOperands(0, ValueRange{argument});
    }
    old.erase();
    req::NativeRequestValues ordinary, replica;
    for (auto [a, b] :
         zip(plan.root->producer->getArguments(), root.getArguments()))
      ordinary[a] = b;
    require(req::readNativeRequestBranchInputs(branch, actual, 1, 1, ordinary,
                                               replica),
            "state-tail offsets rejected");
    for (unsigned i = 0; i < 2; ++i) {
      auto child = ordinary;
      auto childReplica = replica;
      require(req::bindNativeRequestBranchArm(branch, actual, i, 1, 1, child,
                                              childReplica) &&
                  req::readNativeRequestBranchYield(
                      branch, i,
                      actual->getRegion(i).front().back().getOperands(), 1,
                      child, childReplica),
              "state-tail arm binding rejected");
    }
    // Extra-state meaning belongs to the caller. Changing a checked original
    // slot to a same-typed state capture must still fail at this boundary.
    actual->setOperand(0, actual->getOperand(1));
    require(!req::readNativeRequestBranchInputs(branch, actual, 1, 1, ordinary,
                                                replica),
            "same-typed state substituted for selector");
  });
  cases.run("variant payload and role-local capture rows agree", [&] {
    auto text = R"mlir(
!Choice = !data.variant<#data.identity<["atom", "RequestChoice"]>, [#data.alternative<"none">, #data.alternative<"some", [i1,i1]>]>
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%choice:!Choice,%fallback:i1,%x:ui64):
 %unused,%joined = "protocol.branch"(%choice,%x,%fallback) ({
 ^none(%noneX:ui64,%noneFallback:i1):
  "protocol.yield"(%noneX,%noneFallback) : (ui64,i1)->()
 }, {
 ^some(%first:i1,%second:i1,%someX:ui64,%someFallback:i1):
  "protocol.yield"(%someX,%first) : (ui64,i1)->()
 }) {site="choose",roles=["P","V"],output_roles=[["V"],["P","V"]],alternatives=["none","some"]} : (!Choice,ui64,i1)->(ui64,i1)
 "protocol.branch"(%joined) ({ "protocol.yield"() : ()->()
 }, { "protocol.yield"() : ()->()
 }) {site="next",roles=["P","V"],output_roles=[],alternatives=["then","else"]} : (i1)->()
 "protocol.return"() : ()->()
 }) {sym_name="main",function_type=(!Choice,i1,ui64)->(),roles=["P","V"],input_roles=[["P","V"],["P","V"],["V"]],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
    auto source = projected(context, text);
    auto plan = take(req::planNativeRequests(unit(*source), policy(), {}));
    auto &branch = *plan.root->branches.begin()->second;
    require(branch.arms[0]->producer->getNumArguments() !=
                branch.arms[0]->validator->getNumArguments(),
            "fixture did not retain differing capture rows");
    emit(plan, *source);
    auto v = cast<pir::ParticipantBranchOp>(site(*source, "choose", "V"));
    auto &some = v->getRegion(1).front();
    some.back().setOperand(1, some.getArgument(1));
    refuses(req::planNativeRequests(unit(*source), policy(), {}),
            "native-request-reconstruction");
  });
  cases.run("alternative labels must match exactly", [&] {
    auto source = projected(context, sourceText(emptyBranch()));
    auto *branch = site(*source, "choose", "V");
    OpBuilder builder(&context);
    branch->setAttr("alternatives", builder.getStrArrayAttr({"else", "then"}));
    refuses(req::planNativeRequests(unit(*source), policy(), {}),
            "native-request-reconstruction");
  });
  for (bool branchInside : {false, true})
    for (unsigned trips : {0, 1, 3})
      cases.run(
          Twine(branchInside ? "branch in loop, trips "
                             : "loop in arm, trips ") +
              Twine(trips),
          [&] {
            std::string request = R"mlir(
 %r = "data.index_wrapping_add"(%value,%i) : (ui64,ui64)->ui64
 %received = protocol.exchange %r {site="request",sender="V",receiver="P"} : ui64
)mlir";
            std::string body;
            if (branchInside) {
              body = "%n = \"data.index\"() {value=" + std::to_string(trips) +
                     R"mlir(:ui64} : ()->ui64
 "protocol.repeat"(%n,%choice,%x) ({
 ^body(%i:ui64,%c:i1,%value:ui64):
 "protocol.branch"(%c,%value,%i) ({
 ^then(%armValue:ui64,%armIndex:ui64):
)mlir" + replace(replace(request, "%value", "%armValue"), "%i", "%armIndex") +
                     R"mlir(
 "protocol.yield"() : ()->()
 }, { ^else(%elseValue:ui64,%elseIndex:ui64): "protocol.yield"() : ()->()
 }) {site="choose",roles=["P","V"],output_roles=[],alternatives=["then","else"]} : (i1,ui64,ui64)->()
 "protocol.yield"() : ()->()
 }) {site="rounds",carried=0:i64,maximum=4:i64,roles=["P","V"],carried_roles=[]} : (ui64,i1,ui64)->()
)mlir";
            } else {
              body = R"mlir("protocol.branch"(%choice,%x) ({
 ^then(%initial:ui64):
)mlir" + std::string("%n = \"data.index\"() {value=") +
                     std::to_string(trips) +
                     R"mlir(:ui64} : ()->ui64
 "protocol.repeat"(%n,%initial) ({
 ^body(%i:ui64,%value:ui64):
)mlir" + request + R"mlir(
 "protocol.yield"() : ()->()
 }) {site="rounds",carried=0:i64,maximum=4:i64,roles=["P","V"],carried_roles=[]} : (ui64,ui64)->()
 "protocol.yield"() : ()->()
 }, { ^else(%value:ui64): "protocol.yield"() : ()->()
 }) {site="choose",roles=["P","V"],output_roles=[],alternatives=["then","else"]} : (i1,ui64)->()
)mlir";
            }
            auto source = projected(context, sourceText(body));
            auto events = requests(context, {"request"});
            auto plan =
                take(req::planNativeRequests(unit(*source), policy(), events));
            emit(plan, *source);
            auto loop = cast<pir::ProtocolLoopOp>(site(*source, "rounds", "P"));
            auto *count = loop.getInputs()[0].getDefiningOp();
            OpBuilder builder(&context);
            count->setAttr("value", builder.getIntegerAttr(
                                        IntegerType::get(&context, 64,
                                                         IntegerType::Unsigned),
                                        (trips + 1) % 4));
            refuses(req::planNativeRequests(unit(*source), policy(), events),
                    "native-request-reconstruction");
          });
  cases.run("loop-carried selector retains named construction profile", [&] {
    auto source = projected(context, sourceText(R"mlir(
 %n = "data.index"() {value=0:ui64} : ()->ui64
 %out = "protocol.repeat"(%n,%choice) ({
 ^body(%i:ui64,%c:i1):
 "protocol.branch"(%c) ({ "protocol.yield"() : ()->()
 }, { "protocol.yield"() : ()->()
 }) {site="choose",roles=["P","V"],output_roles=[],alternatives=["then","else"]} : (i1)->()
 "protocol.yield"(%c) : (i1)->()
 }) {site="rounds",carried=1:i64,maximum=4:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,i1)->i1
)mlir"));
    refuses(req::planNativeRequests(unit(*source), policy(), {}),
            "native-request-selector-profile");
  });
  cases.run("late-demand branch sequence has bounded analysis depth", [&] {
    std::string body;
    for (unsigned i = 0; i < 80; ++i) {
      auto name = std::to_string(i);
      auto input = i ? "%c" + std::to_string(i - 1) : "%other";
      body +=
          "%c" + name + " = \"protocol.branch\"(%choice," + input +
          R"mlir() ({ ^then(%c:i1): "protocol.yield"(%c) : (i1)->()
 }, { ^else(%c:i1): "protocol.yield"(%c) : (i1)->()
 }) {site="late_)mlir" +
          name +
          R"mlir(",roles=["P","V"],output_roles=[["P","V"]],alternatives=["then","else"]} : (i1,i1)->i1
)mlir";
    }
    body += emptyBranch("%c79", "last");
    auto source = projected(context, sourceText(body));
    refuses(req::planNativeRequests(unit(*source), policy(), {}),
            "native-request-limit");
  });
  cases.run("adversarial sequential setup exhausts a named allowance", [&] {
    auto source = projected(context, sourceText(emptyBranch()));
    auto p = policy();
    // Exercise charged setup independently of native formation's own limits.
    // Repeating a public port cannot change its meaning or buy analysis work.
    p.publicInputs.assign(1000001, 0);
    refuses(req::planNativeRequests(unit(*source), p, {}),
            "native-request-limit");
  });
  for (unsigned depth : {63u, 64u})
    cases.run(Twine("request preflight excludes module wrappers at depth ") +
                  Twine(depth),
              [&] {
                std::string body;
                for (unsigned i = 0; i < depth; ++i) {
                  auto suffix = std::to_string(i);
                  body += "%n" + suffix +
                          " = \"data.index\"() {value=0:ui64} : ()->ui64\n";
                  body += "\"protocol.repeat\"(%n" + suffix + ") ({\n^loop" +
                          suffix + "(%i" + suffix + ":ui64):\n";
                }
                for (unsigned i = depth; i != 0; --i)
                  body += "\"protocol.yield\"() : ()->()\n}) {site=\"depth_" +
                          std::to_string(i - 1) +
                          "\",carried=0:i64,maximum=1:i64,roles=[\"P\",\"V\"],"
                          "carried_roles=[]} : (ui64)->()\n";
                auto source = projected(context, sourceText(body));
                auto plan =
                    take(req::planNativeRequests(unit(*source), policy(), {}));
                emit(plan, *source);
              });
  return cases.result();
}
