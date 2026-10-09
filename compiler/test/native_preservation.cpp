#include "../lib/Compiler/NativeDeployment.h"
#include "../lib/Compiler/NativeProofVerification.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/NativeOrigin.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/Support/MemoryBuffer.h"
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace pir = protocol_ir;
namespace {
unsigned removeAbsorption(ModuleOp module, StringRef origin) {
  auto *context = module.getContext();
  std::string helper;
  local::OperationBindingOp binding;
  module.walk([&](local::FuncOp fn) {
    fn.walk([&](Operation *op) {
      auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
      if (parameters && parameters.size() == 1 &&
          cast<StringAttr>(parameters[0]).getValue() == origin) {
        helper = fn.getSymName().str();
        binding =
            SymbolTable::lookupNearestSymbolFrom<local::OperationBindingOp>(
                op, op->getAttrOfType<FlatSymbolRefAttr>("binding"));
      }
    });
  });
  require(!helper.empty() && bool(binding), "absorption helper missing");
  SmallVector<local::CallOp> calls;
  module.walk([&](local::CallOp call) {
    if (call.getCallee() == helper)
      calls.push_back(call);
  });
  for (auto call : calls) {
    call.getResults().back().replaceAllUsesWith(call.getInputs().front());
    call.erase();
  }
  auto root = *module.getOps<pir::ProtocolModuleOp>().begin();
  SymbolTable::lookupSymbolIn(root, helper)->erase();
  auto bindingName = binding.getSymName();
  bool used = false;
  module.walk([&](Operation *op) {
    auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    used |= ref && ref.getValue() == bindingName;
  });
  if (!used)
    binding.erase();
  auto projection = *root.getBody().front().getOps<pir::ProjectionOp>().begin();
  NamedAttrList interface(cast<DictionaryAttr>(projection.getInterfaces()[0]));
  NamedAttrList construction(
      cast<DictionaryAttr>(interface.get("construction")));
  auto filter = [&](auto &&self, ArrayAttr source) -> ArrayAttr {
    SmallVector<Attribute> actions;
    for (auto item : source) {
      auto action = cast<DictionaryAttr>(item);
      auto callee = action.getAs<FlatSymbolRefAttr>("callee");
      if (callee && callee.getValue() == helper)
        continue;
      NamedAttrList retained(action);
      if (auto body = action.getAs<ArrayAttr>("body"))
        retained.set("body", self(self, body));
      actions.push_back(retained.getDictionary(context));
    }
    return ArrayAttr::get(context, actions);
  };
  construction.set(
      "actions", filter(filter, cast<ArrayAttr>(construction.get("actions"))));
  interface.set("construction", construction.getDictionary(context));
  projection.setInterfacesAttr(
      ArrayAttr::get(context, {interface.getDictionary(context)}));
  return calls.size();
}

constexpr StringLiteral loopFixture = R"mlir(
!f = !algebra.field<"bls12-381.fr">
!rng = !protocol.service_ref<"random.bls12-381.fr/1">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%n:ui64,%x:!f,%coins:!rng):
  "protocol.repeat"(%n,%n,%x) ({ ^outer(%i:ui64,%N:ui64,%X:!f):
   "protocol.repeat"(%N,%X) ({ ^inner(%j:ui64,%Y:!f):
    %seen = protocol.exchange %Y {site="message",sender="P",receiver="V"} : !f
    "protocol.yield"() : ()->()
   }) {site="inner",carried=0:i64,maximum=4:i64,roles=["P","V"],carried_roles=[]} : (ui64,!f)->()
   "protocol.yield"() : ()->()
  }) {site="outer",carried=0:i64,maximum=4:i64,roles=["P","V"],carried_roles=[]} : (ui64,ui64,!f)->()
  %c = "protocol.query"(%coins) {site="draw",owner="V",method="draw"} : (!rng)->!f
  %challenge = protocol.exchange %c {site="challenge",sender="V",receiver="P"} : !f
  %ok = arith.constant true
  "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",function_type=(ui64,!f,!rng)->i1,roles=["P","V"],input_roles=[["P","V"],["P","V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
} // namespace
int main(int argc, char **argv) {
  require(argc == 2, "fixture path required");
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto source = parseSourceFile<ModuleOp>(argv[1], &context);
  require(bool(source), "fixture parse");
  auto policy = take(parseNativeProofPolicy(
      R"(["zkc.native-proof-policy/5", "main", "Alice", "Bob", "0", "merlin3.bls12-381.fr64be/1", "4", ["0", "2"], [["draw_challenge", "challenge"]]])"));
  auto built = take(constructNativeProof(*source, policy));
  auto projected = OwningOpRef<ModuleOp>(cast<ModuleOp>((*source)->clone()));
  PassManager passes(&context);
  passes.addPass(protocol::createProjectProtocolPass(false));
  require(succeeded(passes.run(*projected)), "projection");
  auto *sequence = (*built.descriptor.getAsArray())[3].getAsArray();
  SmallVector<zkc::detail::NativeTranscriptEvent> events;
  unsigned i = 0;
  source->walk([&](Operation *op) {
    auto query = dyn_cast<pir::QueryOp>(op);
    auto exchange = dyn_cast<pir::ExchangeOp>(op);
    if (!exchange && (!query || query.getOwner() != policy.validator))
      return;
    auto payload =
        query ? query.getResult(0).getType() : exchange.getInput().getType();
    auto origin = (*(*sequence)[i++].getAsArray())[1].getAsString()->str();
    events.push_back({op->getAttrOfType<StringAttr>("site").str(), origin,
                      payload, bool(query), 0});
  });
  Cases cases;
  cases.run("independent transcript wiring", [&] {
    if (auto e = zkc::detail::verifyNativeTranscript(*projected, *built.module,
                                                     policy, events))
      throw std::runtime_error(toString(std::move(e)));
  });
  auto mutation = [&](StringRef name,
                      llvm::function_ref<bool(ModuleOp)> change) {
    cases.run(name, [&] {
      auto altered =
          OwningOpRef<ModuleOp>(cast<ModuleOp>((*built.module)->clone()));
      require(change(*altered), "mutation not reached");
      require(succeeded(verify(*altered)), "mutant must remain formed");
      auto e = zkc::detail::verifyNativeTranscript(*projected, *altered, policy,
                                                   events);
      require(bool(e) && namesIdentifier(toString(std::move(e)),
                                         "native-transcript-correspondence"),
              "wrong transcript accepted");
    });
  };
  mutation("absorb local input instead of actual sent value",
           [&](ModuleOp module) {
             bool changed = false;
             module.walk([&](pir::ParticipantOp participant) {
               if (participant.getRole() != policy.producer)
                 return;
               auto &block = participant.getBody().front();
               for (auto call : block.getOps<local::CallOp>())
                 if (!changed && call.getNumOperands() == 2 &&
                     call.getInputs()[1].getType() ==
                         block.getArgument(0).getType()) {
                   call->setOperand(1, block.getArgument(0));
                   changed = true;
                 }
             });
             return changed;
           });
  mutation("helper absorbs a different valid occurrence", [&](ModuleOp module) {
    bool changed = false;
    auto origin = take(protocol::encodeNativeOriginTemplate(
        "main", {}, {"message", "main", "other", "other", "Alice", "Bob"}));
    module.walk([&](Operation *op) {
      auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding");
      if (!ref || changed)
        return;
      auto binding =
          SymbolTable::lookupNearestSymbolFrom<local::OperationBindingOp>(op,
                                                                          ref);
      if (binding &&
          binding.getContract() == "transcript.native.indexed.observe.data") {
        op->setAttr(
            "parameters",
            ArrayAttr::get(&context, {StringAttr::get(&context, origin)}));
        changed = true;
      }
    });
    return changed;
  });
  mutation("retained arithmetic operand changed", [&](ModuleOp module) {
    bool changed = false;
    module.walk([&](Operation *op) {
      if (!changed && op->getName().getStringRef() == "algebra.field_add") {
        op->setOperand(0, op->getOperand(1));
        changed = true;
      }
    });
    return changed;
  });
  cases.run(
      "missing absorption cannot be hidden by an incomplete event list", [&] {
        auto altered =
            OwningOpRef<ModuleOp>(cast<ModuleOp>((*built.module)->clone()));
        require(removeAbsorption(*altered, events.front().origin) == 2,
                "expected two absorptions");
        require(succeeded(verify(*altered)),
                "missing-absorption mutant must be formed");
        auto incomplete = events;
        incomplete.erase(incomplete.begin());
        auto e = zkc::detail::verifyNativeTranscript(*projected, *altered,
                                                     policy, incomplete);
        require(bool(e) && namesIdentifier(toString(std::move(e)),
                                           "native-transcript-correspondence"),
                "incomplete event list hid missing absorption");
      });
  cases.run("removed delivery must use the paired challenge", [&] {
    auto before = OwningOpRef<ModuleOp>(cast<ModuleOp>((*projected)->clone()));
    auto after =
        OwningOpRef<ModuleOp>(cast<ModuleOp>((*built.module)->clone()));
    auto alteredValue = [&](Operation *position, Value value) {
      OpBuilder builder(position);
      OperationState state(position->getLoc(), "algebra.field_add");
      state.addOperands({value, value});
      state.addTypes(value.getType());
      return builder.create(state)->getResult(0);
    };
    bool changedBefore = false, changedAfter = false;
    before->walk([&](pir::EmitOp send) {
      if (send.getSite() == "challenge") {
        send->setOperand(0, alteredValue(send, send.getInput()));
        changedBefore = true;
      }
    });
    after->walk([&](pir::ParticipantOp participant) {
      if (participant.getRole() != policy.validator)
        return;
      for (auto call : participant.getBody().front().getOps<local::CallOp>()) {
        auto fn = SymbolTable::lookupNearestSymbolFrom<local::FuncOp>(
            call, call.getCalleeAttr());
        bool delivery = false;
        fn.walk([&](Operation *op) {
          auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
          delivery |=
              parameters && parameters.size() == 1 &&
              cast<StringAttr>(parameters[0]).getValue() == events[2].origin;
        });
        if (delivery) {
          call->setOperand(1, alteredValue(call, call.getInputs()[1]));
          changedAfter = true;
        }
      }
    });
    require(changedBefore && changedAfter && succeeded(verify(*before)) &&
                succeeded(verify(*after)),
            "delivery mutant must be formed on both sides");
    auto e =
        zkc::detail::verifyNativeTranscript(*before, *after, policy, events);
    require(bool(e) && namesIdentifier(toString(std::move(e)),
                                       "native-transcript-correspondence"),
            "mismatched removed challenge delivery accepted");
  });
  cases.run("nested message-only loops cannot hide missing absorption", [&] {
    auto input = parseSourceString<ModuleOp>(loopFixture, &context);
    require(bool(input), "loop fixture parse");
    auto selected = take(parseNativeProofPolicy(
        R"(["zkc.native-proof-policy/5","main","P","V","0","merlin3.bls12-381.fr64be/1","2",["0","1"],[["draw","challenge"]]])"));
    auto construction = take(constructNativeProof(*input, selected));
    SmallVector<zkc::detail::NativeTranscriptEvent> facts;
    auto &sequence = *(*construction.descriptor.getAsArray())[3].getAsArray();
    unsigned index = 0;
    input->walk<WalkOrder::PreOrder>([&](Operation *op) {
      auto query = dyn_cast<pir::QueryOp>(op);
      auto exchange = dyn_cast<pir::ExchangeOp>(op);
      if (!exchange && !query)
        return;
      unsigned depth = 0;
      for (auto *parent = op->getParentOp(); parent;
           parent = parent->getParentOp())
        depth += isa<pir::RepeatOp>(parent);
      auto origin = (*sequence[index++].getAsArray())[1].getAsString()->str();
      facts.push_back(
          {op->getAttrOfType<StringAttr>("site").str(), origin,
           query ? query.getResult(0).getType() : exchange.getInput().getType(),
           bool(query), depth});
    });
    require(facts.size() == 3 && facts.front().depth == 2,
            "nested event coordinates");
    auto before = OwningOpRef<ModuleOp>(cast<ModuleOp>((*input)->clone()));
    PassManager project(&context);
    project.addPass(protocol::createProjectProtocolPass(false));
    require(succeeded(project.run(*before)), "loop projection");
    if (auto e = zkc::detail::verifyNativeTranscript(
            *before, *construction.module, selected, facts))
      throw std::runtime_error(toString(std::move(e)));
    auto altered =
        OwningOpRef<ModuleOp>(cast<ModuleOp>((*construction.module)->clone()));
    before->walk([&](pir::ParticipantOp original) {
      pir::ParticipantOp candidate;
      altered->walk([&](pir::ParticipantOp p) {
        if (p.getRole() == original.getRole())
          candidate = p;
      });
      require(bool(candidate), "loop participant");
      auto oldLoop =
          *original.getBody().front().getOps<pir::ProtocolLoopOp>().begin();
      auto newLoop =
          *candidate.getBody().front().getOps<pir::ProtocolLoopOp>().begin();
      require(newLoop.getNumResults() == 1, "only transcript state is carried");
      IRMapping mapping;
      mapping.map(original.getBody().front().getArguments(),
                  candidate.getBody().front().getArguments().drop_back());
      OpBuilder builder(newLoop);
      builder.clone(*oldLoop, mapping);
      newLoop.getResults().back().replaceAllUsesWith(newLoop.getInputs()[1]);
      newLoop.erase();
    });
    require(removeAbsorption(*altered, facts.front().origin) == 0,
            "loop replacement already removed absorptions");
    facts.erase(facts.begin());
    require(succeeded(verify(*altered)),
            "unthreaded nested loop mutant must be formed");
    auto e =
        zkc::detail::verifyNativeTranscript(*before, *altered, selected, facts);
    require(bool(e) && namesIdentifier(toString(std::move(e)),
                                       "native-transcript-correspondence"),
            "incomplete event list hid nested absorption");
  });
  auto buffer = MemoryBuffer::getFile(argv[1]);
  require(bool(buffer), "read fixture bytes");
  StringRef text = (*buffer)->getBuffer();
  NativeProofOptions options{printJson(encodeNativeProofPolicy(policy)), true,
                             true};
  auto compiled = take(compileNativeProof(text, argv[1], options, registry));
  auto physical = cast<ModuleOp>(compiled.compilation.module());
  cases.run("exact native deployment bytes", [&] {
    if (auto e = zkc::detail::verifyNativeDeployment(
            *source, physical, text, policy, options, built.descriptor,
            built.wireSites, compiled.deployment))
      throw std::runtime_error(toString(std::move(e)));
  });
  cases.run("deployment JSON whitespace preserves decoded correspondence", [&] {
    if (auto e = zkc::detail::verifyNativeDeployment(
            *source, physical, text, policy, options, built.descriptor,
            built.wireSites, " \n" + compiled.deployment + "\n"))
      throw std::runtime_error(toString(std::move(e)));
  });
  auto deploymentMutation =
      [&](StringRef name, llvm::function_ref<void(json::Array &)> change) {
        cases.run(name, [&] {
          auto value = take(json::parse(compiled.deployment));
          change(*value.getAsArray());
          auto e = zkc::detail::verifyNativeDeployment(
              *source, physical, text, policy, options, built.descriptor,
              built.wireSites, printJson(value));
          require(bool(e) &&
                      namesIdentifier(toString(std::move(e)),
                                      "native-deployment-correspondence"),
                  "wrong deployment accepted");
        });
      };
  deploymentMutation("unknown deployment tag",
                     [](auto &a) { a[0] = "invalid.native-proof"; });
  deploymentMutation("unknown descriptor tag", [](auto &a) {
    (*a[2].getAsArray())[0] = "invalid.native-proof-descriptor";
  });
  deploymentMutation("unknown policy tag", [](auto &a) {
    (*(*a[2].getAsArray())[1].getAsArray())[0] = "invalid.native-proof-policy";
  });
  deploymentMutation("source identity changed",
                     [](auto &a) { a[1] = "changed"; });
  deploymentMutation("participant port map changed", [](auto &a) {
    (*(*(*a[6].getAsArray())[0].getAsArray())[2].getAsArray())[0] =
        json::Array{"1", "bool"};
  });
  deploymentMutation("selected acceptance changed", [](auto &a) {
    (*(*a[6].getAsArray())[1].getAsArray())[5] = "1";
  });
  deploymentMutation("source wire site changed", [](auto &a) {
    (*(*a[8].getAsArray())[0].getAsArray())[1] = "other";
  });
  deploymentMutation("recorded options changed",
                     [](auto &a) { (*a[7].getAsArray())[0] = "false"; });
  deploymentMutation("selected policy changed", [](auto &a) {
    (*(*a[2].getAsArray())[1].getAsArray())[1] = "other";
  });
  return cases.result();
}
