#include "../lib/Compiler/NativeCodec.h"
#include "../lib/Compiler/NativeRequest.h"
#include "../lib/Transforms/Computation/Support.h"
#include "../lib/Transforms/OracleAnchorStorage.h"
#include "../lib/Transforms/OracleCommonPlan.h"
#include "../lib/Transforms/OracleQueryBlocks.h"
#include "../lib/Transforms/OracleQueryCapacity.h"
#include "../lib/Transforms/OracleSchedule.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "support/ResourceSources.h"
#include "zkc/Analysis/CommonControl.h"
#include "zkc/Analysis/Interactions.h"
#include "zkc/Analysis/ProtocolConstants.h"
#include "zkc/Analysis/SuccessfulContinuations.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/SelectedControl.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace {
namespace pir = protocol_ir;
std::string fixture(StringRef name) {
  auto buffer = MemoryBuffer::getFile(std::string(ZKC_CONTROL_FIXTURES) + "/" +
                                      name.str() + ".mlir");
  require(bool(buffer), "cannot read native fixture");
  return (*buffer)->getBuffer().str();
}
std::string replaceText(std::string text, StringRef before, StringRef after) {
  auto position = text.find(before.str());
  require(position != std::string::npos, "missing fixture fragment: " + before);
  text.replace(position, before.size(), after.str());
  return text;
}
pir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<pir::ProtocolModuleOp>(module.getBody()->front());
}
pir::MathematicalOp program(ModuleOp module) {
  return SymbolTable(unit(module)).lookup<pir::MathematicalOp>("main");
}
OwningOpRef<ModuleOp> parse(MLIRContext &context, StringRef source) {
  auto result =
      parseSourceString<ModuleOp>(source, ParserConfig(&context, false));
  require(bool(result), "fixture syntax refused");
  return result;
}
OwningOpRef<ModuleOp> admitted(MLIRContext &context, StringRef source) {
  auto result = parse(context, source);
  require(succeeded(admitStage(*result)), "fixture admission refused");
  return result;
}
void rejects(MLIRContext &context, StringRef source, StringRef code) {
  bool matched = false;
  ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
    matched |= namesIdentifier(diagnostic.str(), code);
    return success();
  });
  auto module = parse(context, source);
  require(failed(admitStage(*module)) && matched, "missing refusal: " + code);
}
OwningOpRef<ModuleOp> projected(ModuleOp source, bool simplify = false) {
  OwningOpRef<ModuleOp> result(cast<ModuleOp>(source->clone()));
  PassManager manager(source.getContext());
  manager.addPass(protocol::createProjectProtocolPass(simplify));
  require(succeeded(manager.run(*result)), "projection refused");
  require(succeeded(mathematical::verifyProjectionPreserved(source, *result)),
          "projection correspondence refused");
  return result;
}
Operation *site(ModuleOp module, StringRef name, StringRef role) {
  Operation *found = nullptr;
  module.walk([&](Operation *op) {
    auto participant = op->getParentOfType<pir::ParticipantOp>();
    auto actual = op->getAttrOfType<StringAttr>("site");
    if (participant && participant.getRole() == role && actual &&
        actual.getValue() == name)
      found = op;
  });
  require(found != nullptr, "missing actual participant site");
  return found;
}
std::string emptyBranch(StringRef selector = "%choice") {
  return (Twine(R"mlir(module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%choice:i1):
  "protocol.branch"()mlir") +
          selector + R"mlir() ({
   "protocol.yield"() : ()->()
  }, {
   "protocol.yield"() : ()->()
  }) {site="choose",roles=["P","V"],output_roles=[],alternatives=["then","else"]} : (i1)->()
  "protocol.return"() : ()->()
 }) {sym_name="main",function_type=(i1)->(),roles=["P","V"],input_roles=[["P","V"]],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir")
      .str();
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  for (StringRef name : {"branch", "match", "math", "roots"})
    for (bool simplify : {false, true})
      cases.run(name + (simplify ? " simplified native projection"
                                 : " native projection"),
                [&] {
                  auto source = admitted(context, fixture(name));
                  auto target = projected(*source, simplify);
                  require(succeeded(admitStage(*target)),
                          "actual projected candidate refused");
                });
  for (StringRef name : {"branch", "match", "roots"})
    cases.run(
        name + " retains selected control through native Exec lowering", [&] {
          auto source = admitted(context, fixture(name));
          auto target = projected(*source);
          OwningOpRef<ModuleOp> before(cast<ModuleOp>((*target)->clone()));
          PassManager manager(&context);
          manager.addPass(protocol::createLowerMathPass());
          require(succeeded(manager.run(*target)) &&
                      succeeded(admitStage(*target)),
                  "selected Exec lowering refused");
          require(unit(*target).getProfile() == pir::Profile::Exec &&
                      succeeded(mathematical::verifyProjectionPreserved(
                          *before, *target)),
                  "selected Exec correspondence failed");
        });
  cases.run("selected Math retains independently checked computation scopes",
            [&] {
              auto source = admitted(context, fixture("math"));
              auto target = projected(*source);
              PassManager manager(&context);
              manager.addPass(protocol::createLowerMathPass());
              manager.addPass(computation::createRealizeComputationsPass());
              require(succeeded(manager.run(*target)) &&
                          succeeded(admitStage(*target)),
                      "selected Math scope adapter refused");
            });
  cases.run("three-role selected projection retains an inactive peer", [&] {
    auto text =
        replaceText(fixture("branch"), "roles=[\"P\",\"V\"],output_roles",
                    "roles=[\"P\",\"V\",\"W\"],output_roles");
    text = replaceText(
        text, "roles=[\"P\",\"V\"],input_roles=[[\"P\",\"V\"]",
        "roles=[\"P\",\"V\",\"W\"],input_roles=[[\"P\",\"V\",\"W\"]");
    auto source = admitted(context, text);
    auto target = projected(*source);
    auto inactive =
        cast<pir::ParticipantBranchOp>(site(*target, "choose", "W"));
    require(inactive.getNumOperands() == 1 && inactive.getNumResults() == 0,
            "inactive peer acquired another role's payload or completion");
  });
  cases.run("selected completion retains each participant's own continuation",
            [&] {
              auto text = replaceText(
                  fixture("branch"),
                  "protocol.guard %enabled {site=\"chosen_guard\",owner=\"V\"}",
                  "\"protocol.finish_if\"(%enabled,%received) "
                  "{site=\"chosen_finish\",owner=\"V\"} : (i1,ui64)->()");
              auto source = admitted(context, text);
              auto target = projected(*source);
              require(isa<pir::FinishIfOp>(site(*target, "chosen_finish", "V")),
                      "selected completion lost its owner");
              auto peer =
                  cast<pir::ParticipantBranchOp>(site(*target, "choose", "P"));
              unsigned completions = 0;
              peer.walk([&](pir::FinishIfOp) { ++completions; });
              require(completions == 0 && peer.getNumResults() == 0,
                      "one participant completed its peer");
              OwningOpRef<ModuleOp> before(cast<ModuleOp>((*target)->clone()));
              PassManager manager(&context);
              manager.addPass(protocol::createLowerMathPass());
              require(succeeded(manager.run(*target)) &&
                          succeeded(admitStage(*target)) &&
                          succeeded(mathematical::verifyProjectionPreserved(
                              *before, *target)),
                      "selected completion lost its native Exec continuation");
            });
  cases.run(
      "application expansion substitutes branch roles and keeps arm occurrence",
      [&] {
        auto child = replaceText(emptyBranch(), "sym_name=\"main\"",
                                 "sym_name=\"child\"");
        child = replaceText(child, "roles=[\"P\",\"V\"],output_roles",
                            "roles=[\"A\",\"B\"],output_roles");
        child = replaceText(child,
                            "roles=[\"P\",\"V\"],input_roles=[[\"P\",\"V\"]]",
                            "roles=[\"A\",\"B\"],input_roles=[[\"A\",\"B\"]]");
        auto main = R"mlir(
 "protocol.func"() ({ ^entry(%choice:i1):
   protocol.apply @child(%choice) {site="call",roles=["V","P"]} : (i1)->()
   "protocol.return"() : ()->()
 }) {sym_name="main",function_type=(i1)->(),roles=["P","V"],input_roles=[["P","V"]],output_roles=[]} : ()->()
)mlir";
        auto text = replaceText(
            child, "}) {profile=#protocol.profile<protocol>}",
            (Twine(main) + "}) {profile=#protocol.profile<protocol>}").str());
        auto source = admitted(context, text);
        auto prepared = mathematical::prepareProtocol(*source, false);
        require(bool(prepared), "selected application preparation refused");
        pir::BranchOp branch;
        program(*prepared).walk([&](pir::BranchOp actual) { branch = actual; });
        require(branch &&
                    cast<StringAttr>(branch.getRoles()[0]).getValue() == "V" &&
                    cast<StringAttr>(branch.getRoles()[1]).getValue() == "P" &&
                    branch.getSite() != "choose",
                "application roles or occurrence prefix were lost");
        uint64_t remaining = 10000;
        facts::Work work(remaining);
        auto requirements =
            take(deriveCommonControlRequirements(program(*source), work));
        require(requirements.size() == 1 &&
                    requirements[0].components[0].input == 0,
                "wrapper lost its callee's actual input obligation");
        auto untrusted =
            replaceText(text, "   protocol.apply @child(%choice)",
                        "   %received = protocol.exchange %choice "
                        "{site=\"receive\",sender=\"P\",receiver=\"V\"} : i1\n "
                        "  protocol.apply @child(%received)");
        rejects(context, untrusted, "common-control-provenance");
      });
  cases.run(
      "unrelated selected declarations preserve generic loop admission", [&] {
        auto source = replaceText(emptyBranch(), "sym_name=\"main\"",
                                  "sym_name=\"unused\"");
        StringRef main = R"mlir(
 "protocol.func"() ({
   %one = "data.index"() {value=1:ui64} : ()->ui64
   %received = protocol.exchange %one {site="receive",sender="P",receiver="V"} : ui64
   %count = "protocol.assemble_roles"(%one,%received) {roles=["P","V"]} : (ui64,ui64)->ui64
   "protocol.repeat"(%count) ({ ^body(%i:ui64):
     "protocol.yield"() : ()->()
   }) {site="rounds",carried=0:i64,maximum=2:i64,roles=["P","V"],carried_roles=[]} : (ui64)->()
   "protocol.return"() : ()->()
 }) {sym_name="main",function_type=()->(),roles=["P","V"],input_roles=[],output_roles=[]} : ()->()
)mlir";
        source = replaceText(
            source, "}) {profile=#protocol.profile<protocol>}",
            (Twine(main) + "}) {profile=#protocol.profile<protocol>}").str());
        auto module = admitted(context, source);
        // Named Entry inventory remains strict even though generic
        // formation does not discharge loop-count agreement.
        uint64_t remaining = 100000;
        facts::Work work(remaining);
        refuses(deriveCommonControlRequirements(program(*module), work),
                "common-control-provenance");
        auto invoked =
            replaceText(source, "   %one =",
                        "   %yes = arith.constant true\n"
                        "   protocol.apply @unused(%yes) "
                        "{site=\"call\",roles=[\"V\",\"P\"]} : (i1)->()\n"
                        "   %one =");
        rejects(context, invoked, "common-control-provenance");
        auto transitive = replaceText(invoked, "protocol.apply @unused",
                                      "protocol.apply @wrapper");
        transitive =
            replaceText(transitive, "}) {profile=#protocol.profile<protocol>}",
                        R"mlir(
 "protocol.func"() ({ ^entry(%choice:i1):
   protocol.apply @unused(%choice) {site="inner",roles=["V","P"]} : (i1)->()
   "protocol.return"() : ()->()
 }) {sym_name="wrapper",function_type=(i1)->(),roles=["P","V"],input_roles=[["P","V"]],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>})mlir");
        rejects(context, transitive, "common-control-provenance");
      });
  cases.run("all arm coordinates preserve actual SSA and work", [&] {
    auto source = admitted(context, fixture("branch"));
    InteractionAnalysis analysis(*source);
    uint64_t remaining = 10000;
    facts::Work work(remaining);
    auto view = take(analysis.get(program(*source), work));
    auto branch = take(view->lookup({0}, work));
    require(branch && branch->getRegions().size() == 2 &&
                !branch->getRepeatBody(),
            "selected edges collapsed to a repeat");
    for (unsigned arm = 0; arm < 2; ++arm) {
      const auto &edge = branch->getRegions()[arm];
      const auto &sequence = view->getSequence(edge.sequence);
      require(edge.kind == InteractionRegion::Kind::BranchArm &&
                  edge.ordinal == arm &&
                  edge.alternative.getValue() == (arm ? "else" : "then") &&
                  sequence.getArguments().size() == 3 &&
                  sequence.getYields().size() == 1,
              "arm interface lost exact identity");
      auto action = take(view->lookup({0, arm, 0}, work));
      require(action && action->getBlock() == sequence.getBlock(),
              "arm path selected another region");
    }
    require(!take(view->lookup({0, 2, 0}, work)),
            "unknown arm became an action");
    uint64_t cold = 10000;
    facts::Work first(cold);
    InteractionAnalysis other(*source);
    take(other.get(program(*source), first));
    auto cost = 10000 - cold;
    uint64_t warm = cost;
    facts::Work replay(warm);
    take(other.get(program(*source), replay));
    require(warm == 0, "cached selected extraction changed its debit");
    for (uint64_t allowance = 0; allowance < cost; ++allowance) {
      uint64_t budget = allowance;
      facts::Work limited(budget);
      refuses(other.get(program(*source), limited),
              "interaction-analysis-capacity");
    }
  });
  cases.run("raw availability exports an obligation instead of agreement", [&] {
    auto source = admitted(context, fixture("branch"));
    uint64_t remaining = 10000;
    facts::Work work(remaining);
    auto requirements =
        take(deriveCommonControlRequirements(program(*source), work));
    require(requirements.size() == 1 &&
                requirements[0].components.size() == 2 &&
                !requirements[0].tagOnly &&
                requirements[0].components[0].input == 0 &&
                requirements[0].components[1].input == 0 &&
                requirements[0].components[0].role.getValue() == "P" &&
                requirements[0].components[1].role.getValue() == "V",
            "entry component requirement differs");
    uint64_t zero = 0;
    facts::Work exhausted(zero);
    refuses(deriveCommonControlRequirements(program(*source), exhausted),
            "common-control-capacity");
  });
  cases.run("variant scheduling requires the tag without payload equality",
            [&] {
              auto source = admitted(context, fixture("match"));
              uint64_t remaining = 10000;
              facts::Work work(remaining);
              auto requirements =
                  take(deriveCommonControlRequirements(program(*source), work));
              require(requirements.size() == 1 && requirements[0].tagOnly &&
                          requirements[0].components[0].path.empty(),
                      "enum payload became a common-input requirement");
            });
  cases.run(
      "nested common payload control retains the exact component path", [&] {
        auto source = admitted(context, fixture("payload"));
        uint64_t remaining = 10000;
        facts::Work work(remaining);
        auto requirements =
            take(deriveCommonControlRequirements(program(*source), work));
        require(requirements.size() == 2 && requirements[0].tagOnly &&
                    !requirements[1].tagOnly &&
                    requirements[1].components[0].path ==
                        SmallVector<unsigned>({1, 0}) &&
                    requirements[1].components[1].path ==
                        SmallVector<unsigned>({1, 0}),
                "tag equality was used as payload equality or lost its path");
        auto target = projected(*source);
        require(succeeded(admitStage(*target)),
                "nested payload projection refused");
      });
  cases.run("static selectors require no entry agreement", [&] {
    auto text =
        replaceText(emptyBranch(), "  \"protocol.branch\"",
                    "  %static = arith.constant true\n  \"protocol.branch\"");
    text = replaceText(text, "\"protocol.branch\"(%choice)",
                       "\"protocol.branch\"(%static)");
    auto source = admitted(context, text);
    uint64_t remaining = 10000;
    facts::Work work(remaining);
    require(
        take(deriveCommonControlRequirements(program(*source), work)).empty(),
        "closed static value became an input obligation");
  });
  cases.run(
      "common dimensions export extent equality without content equality", [&] {
        auto text = replaceText(emptyBranch(), "^entry(%choice:i1)",
                                "^entry(%choice:i1,%bytes:!data.bytes)");
        text = replaceText(text, "function_type=(i1)->()",
                           "function_type=(i1,!data.bytes)->()");
        text = replaceText(text, "input_roles=[[\"P\",\"V\"]]",
                           "input_roles=[[\"P\",\"V\"],[\"P\",\"V\"]]");
        text = replaceText(
            text, "  \"protocol.branch\"",
            "  %size = \"data.dim\"(%bytes) {axis=0:i64} : "
            "(!data.bytes)->ui64\n"
            "  %zero = \"data.index\"() {value=0:ui64} : ()->ui64\n"
            "  %enabled = \"data.index_less\"(%zero,%size) : (ui64,ui64)->i1\n"
            "  \"protocol.branch\"");
        text = replaceText(text, "\"protocol.branch\"(%choice)",
                           "\"protocol.branch\"(%enabled)");
        auto source = admitted(context, text);
        uint64_t remaining = 10000;
        facts::Work work(remaining);
        auto requirements =
            take(deriveCommonControlRequirements(program(*source), work));
        require(requirements.size() == 1 &&
                    requirements[0].components[0].input == 1 &&
                    requirements[0].extentAxis == 0 && !requirements[0].tagOnly,
                "dimension scheduling demanded full collection content");
      });
  cases.run("a constructor tag is static despite an ordered payload", [&] {
    auto source = admitted(context, fixture("constructed"));
    uint64_t remaining = 10000;
    facts::Work work(remaining);
    require(
        take(deriveCommonControlRequirements(program(*source), work)).empty(),
        "static tag acquired a payload equality obligation");
    auto target = projected(*source);
    require(succeeded(admitStage(*target)),
            "constructed tag projection refused");
  });
  cases.run("a static enum tag does not certify ordered payload control", [&] {
    auto text =
        replaceText(fixture("constructed"), "     \"protocol.yield\"(%payload)",
                    R"mlir(     %zero = "data.index"() {value=0:ui64} : ()->ui64
     %enabled = "data.index_equal"(%payload,%zero) : (ui64,ui64)->i1
     "protocol.branch"(%enabled) ({
       "protocol.yield"() : ()->()
     }, {
       "protocol.yield"() : ()->()
     }) {site="payload_choice",roles=["P","V"],output_roles=[],alternatives=["then","else"]} : (i1)->()
     "protocol.yield"(%payload))mlir");
    rejects(context, text, "common-control-provenance");
  });
  cases.run("received role components do not establish common control", [&] {
    auto text =
        replaceText(emptyBranch(), "  \"protocol.branch\"",
                    "  %received = protocol.exchange %choice "
                    "{site=\"receive\",sender=\"P\",receiver=\"V\"} : i1\n "
                    " \"protocol.branch\"");
    text = replaceText(text, "\"protocol.branch\"(%choice)",
                       "\"protocol.branch\"(%received)");
    rejects(context, text, "common-control-provenance");
  });
  for (auto pair : std::initializer_list<std::pair<StringRef, StringRef>>{
           {"alternatives=[\"then\",\"else\"]",
            "alternatives=[\"then\",\"then\"]"},
           {"alternatives=[\"then\",\"else\"]",
            "alternatives=[\"else\",\"then\"]"},
           {"alternatives=[\"then\",\"else\"]", "alternatives=[\"then\"]"}}) {
    StringRef before = pair.first, after = pair.second;
    cases.run("reject malformed closed alternatives " + after, [&] {
      rejects(context, replaceText(fixture("branch"), before, after),
              "selected-control-shape");
    });
  }
  cases.run("dormant arm must yield every typed result", [&] {
    rejects(context,
            replaceText(fixture("branch"),
                        "\"protocol.yield\"(%seven) : (ui64)->()",
                        "\"protocol.yield\"() : ()->()"),
            "selected-control-shape");
  });
  cases.run("a statically dormant arm still checks its exact yield", [&] {
    auto text = replaceText(fixture("branch"), "   %result =",
                            "   %static = arith.constant true\n   %result =");
    text = replaceText(text, "\"protocol.branch\"(%choice,",
                       "\"protocol.branch\"(%static,");
    rejects(context,
            replaceText(text, "\"protocol.yield\"(%seven) : (ui64)->()",
                        "\"protocol.yield\"() : ()->()"),
            "selected-control-shape");
  });
  cases.run("match payload arguments are exact", [&] {
    rejects(context,
            replaceText(fixture("match"), "^some(%payload:ui64,%captured:ui64)",
                        "^some(%payload:ui64,%captured:ui64,%duplicate:ui64)"),
            "selected-control-shape");
  });
  cases.run("match cannot omit a declared payload argument", [&] {
    auto text =
        replaceText(fixture("match"), "^some(%payload:ui64,%captured:ui64)",
                    "^some(%captured:ui64)");
    text = replaceText(text, "\"protocol.yield\"(%payload)",
                       "\"protocol.yield\"(%captured)");
    rejects(context, text, "selected-control-shape");
  });
  cases.run("match payload and same-type capture remain distinct", [&] {
    auto source = admitted(context, fixture("match"));
    auto target = projected(*source);
    auto branch = cast<pir::ParticipantBranchOp>(site(*target, "choose", "V"));
    Block &arm = branch->getRegion(1).front();
    arm.back().setOperand(0, arm.getArgument(1));
    require(succeeded(admitStage(*target)),
            "payload mutation must remain formed");
    bool code = false;
    ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
      code |= namesIdentifier(diagnostic.str(), "mathematical-correspondence");
      return success();
    });
    require(failed(mathematical::verifyProjectionPreserved(*source, *target)) &&
                code,
            "a same-type capture replaced the selected payload");
  });
  cases.run("unknown native attributes supply no certificate", [&] {
    rejects(context,
            replaceText(fixture("branch"), "site=\"choose\",roles=",
                        "common=true,site=\"choose\",roles="),
            "mathematical-formation");
  });
  cases.run("a role-local roster cannot hide a peer action", [&] {
    auto text =
        replaceText(emptyBranch(), "roles=[\"P\",\"V\"],output_roles=[]",
                    "roles=[\"P\"],output_roles=[]");
    text = replaceText(text, "\"protocol.branch\"(%choice)",
                       "\"protocol.branch\"(%choice,%choice)");
    text =
        replaceText(text, "({\n   \"protocol.yield\"",
                    "({ ^then(%captured:i1):\n   %sent = protocol.exchange "
                    "%captured {site=\"hidden\",sender=\"P\",receiver=\"V\"} : "
                    "i1\n   \"protocol.yield\"");
    text = replaceText(text, "}, {\n   \"protocol.yield\"",
                       "}, { ^else(%captured:i1):\n   \"protocol.yield\"");
    text = replaceText(text, ": (i1)->()\n  \"protocol.return\"",
                       ": (i1,i1)->()\n  \"protocol.return\"");
    rejects(context, text, "mathematical-formation");
  });
  cases.run("Math arms refuse ordered Protocol actions", [&] {
    auto text = replaceText(fixture("math"), "\"data.branch\"(%choice,%x,%y)",
                            "\"data.branch\"(%choice,%x,%y,%choice)");
    text = replaceText(text, "^then(%left:ui64,%right:ui64)",
                       "^then(%left:ui64,%right:ui64,%enabled:i1)");
    text = replaceText(text, "^else(%left:ui64,%right:ui64)",
                       "^else(%left:ui64,%right:ui64,%enabled:i1)");
    text = replaceText(
        text, "alternatives=[\"then\",\"else\"]} : (i1,ui64,ui64)->ui64",
        "alternatives=[\"then\",\"else\"]} : (i1,ui64,ui64,i1)->ui64");
    text = replaceText(
        text, "     \"data.yield\"(%right)",
        "     protocol.guard %enabled {site=\"ordered\",owner=\"P\"}\n "
        "    \"data.yield\"(%right)");
    rejects(context, text, "expects parent op");
  });
  cases.run("a total helper propagates exact formal common requirements", [&] {
    auto text =
        replaceText(emptyBranch(), " \"protocol.func\"",
                    " func.func private @identity(%x:i1)->i1 { return %x : "
                    "i1 }\n \"protocol.func\"");
    text =
        replaceText(text, "  \"protocol.branch\"",
                    "  %forwarded = func.call @identity(%choice) : (i1)->i1\n  "
                    "\"protocol.branch\"");
    text = replaceText(text, "\"protocol.branch\"(%choice)",
                       "\"protocol.branch\"(%forwarded)");
    auto source = admitted(context, text);
    uint64_t remaining = 10000;
    facts::Work work(remaining);
    auto requirements =
        take(deriveCommonControlRequirements(program(*source), work));
    require(requirements.size() == 1 &&
                requirements[0].components[0].input == 0,
            "helper lost its actual input association");
  });
  cases.run("affine capture cannot occur twice in one yield", [&] {
    rejects(context,
            replaceText(fixture("roots"), "\"protocol.yield\"(%left,%right)",
                        "\"protocol.yield\"(%left,%left)"),
            "mathematical-formation");
  });
  cases.run("one alternative cannot swap exact recurrence roots", [&] {
    auto source = fixture("roots");
    auto last = source.rfind("\"protocol.yield\"(%left,%right)");
    require(last != std::string::npos, "missing dormant root yield");
    source.replace(last, StringRef("\"protocol.yield\"(%left,%right)").size(),
                   "\"protocol.yield\"(%right,%left)");
    rejects(context, source, "mathematical-formation");
  });
  cases.run(
      "zero trips retain initial roots while still checking recurrence", [&] {
        auto source =
            admitted(context, replaceText(fixture("roots"), "maximum=8:i64",
                                          "maximum=0:i64"));
        auto target = projected(*source);
        require(site(*target, "rounds", "P")->getNumOperands() == 4,
                "zero path manufactured a root");
      });
  cases.run(
      "participant selector mutation fails independent correspondence", [&] {
        auto source = admitted(context, fixture("branch"));
        auto target = projected(*source);
        auto branch =
            cast<pir::ParticipantBranchOp>(site(*target, "choose", "V"));
        // Both operands are genuine available Booleans of the same native type.
        branch->setOperand(0, branch->getOperand(branch.getNumOperands() - 1));
        require(succeeded(admitStage(*target)),
                "selector mutation must remain formed");
        bool code = false;
        ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
          code |=
              namesIdentifier(diagnostic.str(), "mathematical-correspondence");
          return success();
        });
        require(
            failed(mathematical::verifyProjectionPreserved(*source, *target)) &&
                code,
            "selector mutation was trusted");
      });
  cases.run(
      "moving actions to another arm fails retained occurrence checking", [&] {
        auto source = admitted(context, fixture("branch"));
        auto target = projected(*source);
        auto branch =
            cast<pir::ParticipantBranchOp>(site(*target, "choose", "V"));
        auto *guard = site(*target, "chosen_guard", "V");
        guard->setOperand(0,
                          branch->getRegion(1).front().getArguments().back());
        guard->moveBefore(&branch->getRegion(1).front().back());
        bool code = false;
        ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
          code |= namesIdentifier(diagnostic.str(), "mathematical-projection");
          return success();
        });
        require(failed(admitStage(*target)) && code,
                "arm movement was flattened");
      });
  cases.run("conditional oracle inventory preserves both arm paths", [&] {
    auto source = admitted(context, fixture("oracle"));
    auto capacity = take(protocol::analyzeOracleQueryCapacity(*source, "main"));
    require(capacity.constructors.size() == 2 && capacity.queries.size() == 1,
            "conditional inventory lost an arm");
    for (auto [op, size] : capacity.queries)
      require(size.leaves == 1 && size.nodes == 1,
              "alternative capacity was added as sequential demand");
    auto storage = take(protocol::planOracleAnchorStorage(
        *source, "main",
        [](const auto &) -> Expected<std::string> { return std::string{}; }));
    require(
        storage.constructors.size() == 2 &&
            storage.constructors[0].path == std::vector<unsigned>({0, 0, 1}) &&
            storage.constructors[1].path == std::vector<unsigned>({0, 1, 1}),
        "conditional constructor coordinates collapsed");
    for (const auto &constructor : storage.constructors) {
      require(constructor.repeatDepth == 0 && constructor.maximumInstances == 1,
              "a selected coordinate became a repeat coordinate");
      for (const auto &role : constructor.roles)
        for (const auto &field : role.fields)
          require(!StringRef(field.name).starts_with("iteration."),
                  "an arm manufactured an iteration payload");
    }
    auto observation =
        take(protocol::analyzeOracleObservations(*source, "main", "V"));
    require(!observation.queryBeforeDraw(),
            "alternatives invented a sequential oracle/draw path");
    refuses(protocol::oracleRequirements(*source, "main", {}),
            "oracle-realization-control-profile");
  });
  cases.run("oracle batching remains inside the actual selected arm", [&] {
    auto text =
        replaceText(fixture("observations"),
                    "     %random = \"protocol.query\"(%service) "
                    "{site=\"alternative_draw\",owner=\"V\",method=\"draw\"} : "
                    "(!S)->!algebra.field<\"bls12-381.fr\">",
                    "     %answer = \"protocol.oracle_query\"(%word,%index) "
                    "{site=\"else_read\",owner=\"V\"} : (!H,ui64)->ui64");
    auto source = admitted(context, text);
    auto capacity = take(protocol::analyzeOracleQueryCapacity(*source, "main"));
    DominanceInfo dominance(*source);
    SmallVector<pir::OracleQueryOp> queries;
    source->walk([&](pir::OracleQueryOp query) { queries.push_back(query); });
    require(queries.size() == 2, "missing actual arm queries");
    for (auto query : queries) {
      unsigned remaining = 10000;
      auto window = take(protocol::selectOracleQueryWindow(
          query, protocol::OracleAuthentication::AtomicBlocks, capacity,
          dominance, remaining));
      require(window.queries.size() == 1 && window.queries[0] == query &&
                  window.leaves == 1,
              "a query window crossed a selected arm boundary");
    }
  });
  cases.run(
      "selected oracle storage retains only actual enclosing repeats", [&] {
        auto source = admitted(context, fixture("nested_oracle"));
        auto storage = take(protocol::planOracleAnchorStorage(
            *source, "main", [](const auto &) -> Expected<std::string> {
              return std::string{};
            }));
        require(storage.constructors.size() == 2,
                "lost an alternative constructor");
        for (auto [arm, constructor] : enumerate(storage.constructors)) {
          require(constructor.repeatDepth == 1 &&
                      constructor.maximumInstances == 3 &&
                      constructor.path ==
                          std::vector<unsigned>({0, 0, unsigned(arm), 1}),
                  "repeat capacity or selected occurrence differs");
          for (const auto &role : constructor.roles) {
            unsigned iterations = 0;
            for (const auto &field : role.fields)
              iterations += StringRef(field.name).starts_with("iteration.");
            require(iterations == 1,
                    "an arm ordinal supplied an iteration payload");
          }
        }
      });
  for (bool insideRepeat : {false, true})
    for (bool fresh : {false, true})
      cases.run(
          Twine(fresh ? "fresh" : "passed") + " selected custody " +
              (insideRepeat ? "recurrence" : "standalone result"),
          [&] {
            resource_sources::Source source;
            source.binding("pass", "resource_unit.pass", {"Slot.A"});
            source.binding("consume", "resource_unit.consume", {"Slot.A"});
            source.binding("create", "resource_unit.create", {"Slot.A"});
            auto helper = source.function("step", source.unit, source.unit);
            exec::ScopedExecutionBuilder scoped(source.builder, helper);
            Value next;
            if (fresh) {
              source.invoke(scoped, "consume", helper.getArgument(1), {},
                            "consume");
              next =
                  source.invoke(scoped, "create", {}, source.unit, "create")[0];
            } else
              next = source.invoke(scoped, "pass", helper.getArgument(1),
                                   source.unit, "pass")[0];
            scoped.returned(next);
            auto *outer = source.protocol(
                "main", {source.index, source.boolean, source.unit},
                source.unit);
            Block *body = outer;
            Value selector = outer->getArgument(1),
                  input = outer->getArgument(2);
            pir::RepeatOp repeat;
            if (insideRepeat) {
              auto *op = source.operation(
                  "protocol.repeat", {outer->getArgument(0), input, selector},
                  source.unit,
                  {source.text("site", "rounds"),
                   source.builder.getNamedAttr(
                       "carried", source.builder.getI64IntegerAttr(1)),
                   source.builder.getNamedAttr(
                       "maximum", source.builder.getI64IntegerAttr(8)),
                   source.builder.getNamedAttr("roles", source.roles()),
                   source.builder.getNamedAttr("carried_roles",
                                               source.portRoles(1))},
                  true);
              repeat = cast<pir::RepeatOp>(op);
              body = new Block();
              repeat.getBody().push_back(body);
              body->addArgument(source.index, source.location);
              input = body->addArgument(source.unit, source.location);
              selector = body->addArgument(source.boolean, source.location);
            }
            source.builder.setInsertionPointToEnd(body);
            OperationState state(source.location,
                                 pir::BranchOp::getOperationName());
            state.addOperands({selector, input});
            state.addTypes(source.unit);
            state.addAttributes(
                {source.text("site", "choose"),
                 source.builder.getNamedAttr("roles", source.roles()),
                 source.builder.getNamedAttr("output_roles",
                                             source.portRoles(1)),
                 source.builder.getNamedAttr(
                     "alternatives",
                     source.builder.getStrArrayAttr({"then", "else"}))});
            state.addRegion();
            state.addRegion();
            auto selected = cast<pir::BranchOp>(source.builder.create(state));
            for (unsigned arm = 0; arm < 2; ++arm) {
              auto *region = new Block();
              selected->getRegion(arm).push_back(region);
              Value argument =
                  region->addArgument(source.unit, source.location);
              source.builder.setInsertionPointToEnd(region);
              Value result = argument;
              if (!arm)
                result =
                    source
                        .operation("protocol.local_call", argument, source.unit,
                                   {source.symbol("callee", "step"),
                                    source.text("site", "selected_step"),
                                    source.text("role", "P")})
                        ->getResult(0);
              source.operation("protocol.yield", result);
            }
            source.builder.setInsertionPointToEnd(body);
            if (insideRepeat)
              source.operation("protocol.yield", selected.getResult(0));
            source.builder.setInsertionPointToEnd(outer);
            source.operation("protocol.return", insideRepeat
                                                    ? repeat.getResult(0)
                                                    : selected.getResult(0));
            bool rootRefusal = false;
            ScopedDiagnosticHandler capture(
                &source.context, [&](Diagnostic &diagnostic) {
                  rootRefusal |= namesIdentifier(diagnostic.str(),
                                                 "mathematical-formation");
                  return success();
                });
            bool valid = succeeded(admitStage(*source.module));
            require(valid == !(fresh && insideRepeat) && (valid || rootRefusal),
                    "selected fresh root was inferred from its nominal type");
          });
  cases.run(
      "reached bounds intersect continuing arms and preserve nested paths",
      [&] {
        for (bool missing : {false, true}) {
          auto text = fixture("facts");
          if (missing)
            text = replaceText(
                text, "protocol.guard %less {site=\"else_bound\",owner=\"V\"}",
                "");
          auto source = admitted(context, text);
          auto declaration = program(*source);
          auto &body = declaration.getBody().front();
          Operation *after = nullptr, *inside = nullptr;
          declaration.walk([&](pir::GuardOp guard) {
            if (guard.getSite() == "after")
              after = guard;
            if (guard.getSite() == "then_after")
              inside = guard;
          });
          require(after && inside, "missing fact query sites");
          SuccessfulContinuationAnalysis facts(*source);
          uint64_t remaining = 100000;
          zkc::facts::Work work(remaining);
          using Status = SuccessfulContinuationAnalysis::Status;
          require(
              take(facts.bound(declaration, inside, "V", body.getArgument(1),
                               body.getArgument(2), work)) == Status::Proven,
              "selected arm lost its reached bound");
          require(take(facts.bound(declaration, after, "V", body.getArgument(1),
                                   body.getArgument(2), work)) ==
                      (missing ? Status::Unknown : Status::Proven),
                  "a branch fact escaped its continuing join");
        }
      });
  cases.run(
      "oracle observation alternatives do not create cross-arm paths", [&] {
        auto source = admitted(context, fixture("observations"));
        require(!take(protocol::analyzeOracleObservations(*source, "main", "V"))
                     .queryBeforeDraw(),
                "exclusive query and draw became sequential");
        auto text = replaceText(
            fixture("observations"), "   \"protocol.return\"",
            "   %later = \"protocol.query\"(%coins) "
            "{site=\"later\",owner=\"V\",method=\"draw\"} : "
            "(!S)->!algebra.field<\"bls12-381.fr\">\n   \"protocol.return\"");
        auto sequential = admitted(context, text);
        require(
            take(protocol::analyzeOracleObservations(*sequential, "main", "V"))
                .queryBeforeDraw(),
            "continuing query arm lost its later draw");
        for (StringRef owner : {"P", "V"}) {
          auto stopped =
              replaceText(text, "     \"protocol.yield\"() : ()->()",
                          (Twine("     %no = arith.constant false\n     "
                                 "protocol.guard %no {site=\"stop\",owner=\"") +
                           owner + "\"}\n     \"protocol.yield\"() : ()->()")
                              .str());
          auto candidate = admitted(context, stopped);
          require(
              take(protocol::analyzeOracleObservations(*candidate, "main", "V"))
                      .queryBeforeDraw() == (owner == "P"),
              "one participant's stop pruned its peer");
        }
      });
  cases.run(
      "security stages refuse unsupported selected transcript profiles", [&] {
        auto source = admitted(context, fixture("branch"));
        NativeProofPolicy policy;
        policy.entry = "main";
        policy.producer = "P";
        policy.validator = "V";
        policy.suite = "merlin3.bls12-381.fr64be/0";
        policy.services = {2};
        policy.draws = {{"alternative_draw", "challenge"}};
        refuses(constructNativeProof(*source, policy),
                "native-proof-control-profile");
        auto target = projected(*source);
        refuses(zkc::detail::planNativeRequests(unit(*target), policy, {}),
                "native-request-control-profile");
        protocol::ConstructionPlan plan{};
        refuses(
            zkc::detail::constructNativeCodec(*target, policy, plan, {}, {}),
            "native-codec-control-profile");
      });
  // Selected control outside the selected entry's static closure does not
  // gate the entry; selected control the entry reaches still refuses.
  {
    auto schnorr = [] {
      auto buffer =
          MemoryBuffer::getFile(std::string(ZKC_CONTROL_FIXTURES) +
                                "/../mathematical/schnorr-services.mlir");
      require(bool(buffer), "cannot read the Schnorr fixture");
      return (*buffer)->getBuffer().str();
    }();
    const std::string helper =
        R"mlir(func.func private @choose(%c: i1, %a: !algebra.field<"bls12-381.fr">, %b: !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr"> {
  %r = "data.branch"(%c, %a, %b) ({
  ^then(%x: !algebra.field<"bls12-381.fr">, %y: !algebra.field<"bls12-381.fr">):
    "data.yield"(%x) : (!algebra.field<"bls12-381.fr">) -> ()
  }, {
  ^else(%x: !algebra.field<"bls12-381.fr">, %y: !algebra.field<"bls12-381.fr">):
    "data.yield"(%y) : (!algebra.field<"bls12-381.fr">) -> ()
  }) {alternatives=["then","else"]} : (i1, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
  return %r : !algebra.field<"bls12-381.fr">
}
)mlir";
    // A dormant helper: no definition calls it.
    auto dormant =
        replaceText(schnorr, "relation.declare", helper + "relation.declare");
    // An uncalled protocol with a Protocol selection.
    auto branch = fixture("branch");
    auto begin = branch.find("\"protocol.func\"");
    auto end = branch.find("}) {profile");
    require(begin != std::string::npos && end != std::string::npos,
            "missing branch protocol");
    auto uncalled =
        replaceText(schnorr, "relation.declare",
                    replaceText(branch.substr(begin, end - begin),
                                "sym_name=\"main\"", "sym_name=\"unused\"") +
                        "relation.declare");
    // The entry reaches the helper's selection through a call.
    auto reached = replaceText(
        dormant,
        R"mlir(%z = algebra.field_add %k, %cx : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">)mlir",
        R"mlir(%t = arith.constant true
%z = func.call @choose(%t, %k, %cx) : (i1, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">)mlir");
    auto policy = take(parseNativeProofPolicy(
        R"(["zkc.native-proof-policy/0", "main", "Alice", "Bob", "0", "merlin3.bls12-381.fr64be/0", ["4"], ["0", "2"], [["draw_challenge", "challenge"]], "zkc.framed/0", "", []])"));
    for (const auto &[name, text] :
         {std::pair<StringRef, StringRef>{"a dormant selected helper", dormant},
          {"an uncalled selected protocol", uncalled}}) {
      StringRef subject = text;
      cases.run(Twine("an entry beside ") + name + " proves", [&] {
        auto source = admitted(context, subject);
        auto built = take(constructNativeProof(*source, policy));
        if (auto e = checkNativeProof(*source, *built.module, policy))
          throw std::runtime_error(toString(std::move(e)));
        // The projected unit retains the unrelated selection; the projected
        // stages start from the entry's participants and do not reach it.
        auto target = projected(*source);
        bool retained = false;
        target->walk([&](Operation *op) { retained |= isSelectedControl(op); });
        require(retained, "projection dropped the unrelated selection");
        auto requests =
            zkc::detail::planNativeRequests(unit(*target), policy, {});
        if (!requests)
          require(!namesIdentifier(toString(requests.takeError()),
                                   "native-request-control-profile"),
                  "native requests read an unrelated declaration");
        if (auto e = requireUnconditionalProtocolControl(
                {SymbolTable::lookupSymbolIn(unit(*target), "main")},
                "native-codec-control-profile"))
          throw std::runtime_error(toString(std::move(e)));
        take(protocol::oracleRequirements(*source, "main", {}));
      });
    }
    cases.run("an entry that calls a selected helper still refuses", [&] {
      auto source = admitted(context, reached);
      refuses(constructNativeProof(*source, policy),
              "native-proof-control-profile");
      // Oracle planning follows the call into the helper as well.
      refuses(protocol::oracleRequirements(*source, "main", {}),
              "oracle-realization-control-profile");
    });
  }
  return cases.result();
}
