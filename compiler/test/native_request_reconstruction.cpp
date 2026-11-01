#include "../lib/Compiler/NativeProofVerification.h"
#include "../lib/Compiler/NativeRequest.h"
#include "../lib/Transforms/OracleRealizationSelection.h"
#include "../lib/Transforms/RealizedProtocol.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/NativeOrigin.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/MemoryBuffer.h"
#include <algorithm>
#include <functional>

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace pir = protocol_ir;
namespace {
constexpr StringLiteral fixture = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!R = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%public:!F,%published:!F,%secret:!F,%verifier:!F,%coins:!R):
  %sent = protocol.exchange %published {sender="P",receiver="V",site="published"} : !F
  %c = "protocol.query"(%coins) {owner="V",method="draw",site="draw"} : (!R)->!F
  %challenge = protocol.exchange %c {sender="V",receiver="P",site="challenge"} : !F
  %request = "protocol.local_call"(%public,%sent) {callee=@request,role="V",site="compute_request"} : (!F,!F)->!F
  %received = protocol.exchange %request {sender="V",receiver="P",site="request"} : !F
  %answered = protocol.exchange %received {sender="P",receiver="V",site="answer"} : !F
  %last = "protocol.local_call"(%answered,%c) {callee=@request,role="V",site="compute_last"} : (!F,!F)->!F
  %replay = protocol.exchange %last {sender="V",receiver="P",site="replay"} : !F
  %ok = algebra.field_equal %answered,%request : (!F,!F)->i1
  "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",origin=["main",[]],function_type=(!F,!F,!F,!F,!R)->i1,
     roles=["P","V"],input_roles=[["P","V"],["P"],["P"],["V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
constexpr StringLiteral loopFixture = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!R = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%public:!F,%published:!F,%secret:!F,%verifier:!F,%coins:!R):
  %n = "data.index"() {value=2:ui64} : ()->ui64
  %done = "protocol.repeat"(%n,%public,%published,%coins,%public) ({
  ^body(%i:ui64,%current:!F,%value:!F,%random:!R,%known:!F):
   %sent = protocol.exchange %value {sender="P",receiver="V",site="published"} : !F
   %c = "protocol.query"(%random) {owner="V",method="draw",site="draw"} : (!R)->!F
   %challenge = protocol.exchange %c {sender="V",receiver="P",site="challenge"} : !F
   %request = "protocol.local_call"(%current,%sent) {callee=@request,role="V",site="compute_request"} : (!F,!F)->!F
   %received = protocol.exchange %request {sender="V",receiver="P",site="request"} : !F
   %answered = protocol.exchange %received {sender="P",receiver="V",site="answer"} : !F
   %next = "protocol.local_call"(%answered,%known) {callee=@request,role="V",site="compute_next"} : (!F,!F)->!F
   "protocol.yield"(%next) : (!F)->()
  }) {site="rounds",carried=1:i64,maximum=4:i64,roles=["P","V"],carried_roles=[["V"]]} : (ui64,!F,!F,!R,!F)->!F
  %replay = protocol.exchange %done {sender="V",receiver="P",site="replay"} : !F
  %ok = algebra.field_equal %done,%public : (!F,!F)->i1
  "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",origin=["main",[]],function_type=(!F,!F,!F,!F,!R)->i1,
     roles=["P","V"],input_roles=[["P","V"],["P"],["P"],["V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
constexpr StringLiteral lateLoopFixture = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!R = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%public:!F,%published:!F,%secret:!F,%verifier:!F,%coins:!R):
  %sent = protocol.exchange %published {sender="P",receiver="V",site="published"} : !F
  %seed = "protocol.local_call"(%public,%sent) {callee=@request,role="V",site="seed"} : (!F,!F)->!F
  %n = "data.index"() {value=2:ui64} : ()->ui64
  %done = "protocol.repeat"(%n,%seed,%public) ({
  ^body(%i:ui64,%current:!F,%known:!F):
   %next = "protocol.local_call"(%current,%known) {callee=@request,role="V",site="advance"} : (!F,!F)->!F
   "protocol.yield"(%next) : (!F)->()
  }) {site="rounds",carried=1:i64,maximum=4:i64,roles=["P","V"],carried_roles=[["V"]]} : (ui64,!F,!F)->!F
  %c = "protocol.query"(%coins) {owner="V",method="draw",site="draw"} : (!R)->!F
  %challenge = protocol.exchange %c {sender="V",receiver="P",site="challenge"} : !F
  %received = protocol.exchange %seed {sender="V",receiver="P",site="request"} : !F
  %replay = protocol.exchange %done {sender="V",receiver="P",site="replay"} : !F
  %ok = algebra.field_equal %done,%seed : (!F,!F)->i1
  "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",origin=["main",[]],function_type=(!F,!F,!F,!F,!R)->i1,
     roles=["P","V"],input_roles=[["P","V"],["P"],["P"],["V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
// No reconstructed exchanges: the two actual role counts must still relate.
constexpr StringLiteral challengeLoopFixture = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!R = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%public:!F,%coins:!R):
  %p = "data.index"() {value=1:ui64} : ()->ui64
  %v = "data.index"() {value=1:ui64} : ()->ui64
  %count = "protocol.assemble_roles"(%p,%v) {roles=["P","V"]} : (ui64,ui64)->ui64
  "protocol.repeat"(%count,%coins) ({
  ^body(%i:ui64,%random:!R):
   %c = "protocol.query"(%random) {owner="V",method="draw",site="draw"} : (!R)->!F
   %challenge = protocol.exchange %c {sender="V",receiver="P",site="challenge"} : !F
   "protocol.yield"() : ()->()
  }) {site="rounds",carried=0:i64,maximum=1:i64,roles=["P","V"],carried_roles=[]} : (ui64,!R)->()
  %ok = algebra.field_equal %public,%public : (!F,!F)->i1
  "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",origin=["main",[]],function_type=(!F,!R)->i1,
     roles=["P","V"],input_roles=[["P","V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
constexpr StringLiteral identityLoopFixture = R"mlir(
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry:
  %p = "data.index"() {value=1:ui64} : ()->ui64
  %v = "data.index"() {value=1:ui64} : ()->ui64
  %count = "protocol.assemble_roles"(%p,%v) {roles=["P","V"]} : (ui64,ui64)->ui64
  "protocol.repeat"(%count) ({
  ^body(%i:ui64):
   "protocol.yield"() : ()->()
  }) {site="rounds",carried=0:i64,maximum=1:i64,roles=["P","V"],carried_roles=[]} : (ui64)->()
  %ok = "data.index_equal"(%v,%v) : (ui64,ui64)->i1
  "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",origin=["main",[]],function_type=()->i1,
     roles=["P","V"],input_roles=[],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
void checked(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
NativeProofPolicy policy() {
  NativeProofPolicy result;
  result.entry = "main";
  result.producer = "P";
  result.validator = "V";
  result.suite = "merlin3.bls12-381.fr64be/0";
  result.services = {4};
  result.publicInputs = {0, 3};
  result.draws = {{"draw", "challenge"}};
  return result;
}
pir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<pir::ProtocolModuleOp>(module.getBody()->front());
}
pir::ParticipantOp participant(ModuleOp module, StringRef role) {
  for (auto p : unit(module).getBody().front().getOps<pir::ParticipantOp>())
    if (p.getRole() == role)
      return p;
  throw std::runtime_error("missing participant");
}
void installRequest(ModuleOp module) {
  OpBuilder b(module.getContext());
  auto owner = unit(module);
  b.setInsertionPointToStart(&owner.getBody().front());
  auto f = algebra::FieldType::get(module.getContext(), "bls12-381.fr");
  auto scope = runtime::ScopeType::get(module.getContext());
  auto outcome = exec::OutcomeType::get(module.getContext(), {f});
  auto binding = runtime::BindingOp::create(
      b, module.getLoc(), "add", "field.add",
      b.getArrayAttr({b.getStringAttr("bls12-381.fr")}), "");
  auto function =
      func::FuncOp::create(b, module.getLoc(), "request_step",
                           b.getFunctionType({scope, f, f}, {outcome}));
  function.setPrivate();
  function.setNoInline(true);
  function->setAttr("runtime.region", b.getUnitAttr());
  b.setInsertionPointToEnd(function.addEntryBlock());
  exec::ScopedExecutionBuilder control(b, function);
  auto sum = control.invoke(
      "exec.apply", {f}, control.scoped(function.getArguments().drop_front()),
      {b.getNamedAttr("binding", FlatSymbolRefAttr::get(binding)),
       b.getNamedAttr("parameters", b.getArrayAttr({})),
       b.getNamedAttr("site", b.getStringAttr("sum"))});
  control.complete(sum);
  b.setInsertionPointToStart(&owner.getBody().front());
  auto alternative = cast<func::FuncOp>(b.clone(*function));
  alternative.setSymName("request_else");
  alternative.walk([&](exec::ApplyOp call) { call.setSite("sum_else"); });
  auto wrapper = func::FuncOp::create(b, module.getLoc(), "request",
                                      function.getFunctionType());
  wrapper.setPrivate();
  wrapper.setNoInline(true);
  wrapper->setAttr("runtime.origin", b.getArrayAttr({b.getStringAttr("request"),
                                                     b.getArrayAttr({})}));
  b.setInsertionPointToEnd(wrapper.addEntryBlock());
  exec::ScopedExecutionBuilder nested(b, wrapper);
  Value branch =
      nested
          .invoke("exec.boolean", {b.getI1Type()}, {nested.getScope()},
                  {b.getNamedAttr("value", b.getBoolAttr(true)),
                   b.getNamedAttr("site", b.getStringAttr("branch"))})
          .front();
  auto values = nested.conditional(
      branch, wrapper.getArguments().drop_front(), {f}, "request_scope",
      [&](unsigned arm) { return arm ? alternative : function; });
  nested.returned(values);
}
void addUnusedRequestWork(ModuleOp module, bool unclassified) {
  auto owner = unit(module);
  auto function =
      cast<func::FuncOp>(SymbolTable::lookupSymbolIn(owner, "request_step"));
  OpBuilder b(module.getContext());
  b.setInsertionPointToStart(&owner.getBody().front());
  auto f = algebra::FieldType::get(module.getContext(), "bls12-381.fr");
  auto inverse = runtime::BindingOp::create(
      b, module.getLoc(), "unused_inverse", "field.inverse",
      b.getStrArrayAttr({"bls12-381.fr"}), "");
  auto requireBinding =
      runtime::BindingOp::create(b, module.getLoc(), "unused_require",
                                 "control.require", b.getArrayAttr({}), "");
  runtime::BindingOp extra;
  if (unclassified)
    extra = runtime::BindingOp::create(b, module.getLoc(),
                                       "unused_unclassified", "curve.generator",
                                       b.getStrArrayAttr({"bls12-381.g1"}), "");
  function.getBody().dropAllReferences();
  function.getBody().getBlocks().clear();
  b.setInsertionPointToEnd(function.addEntryBlock());
  exec::ScopedExecutionBuilder control(b, function);
  auto apply = [&](runtime::BindingOp binding, TypeRange results,
                   ValueRange inputs, StringRef site) {
    return control.invoke(
        "exec.apply", results, control.scoped(inputs),
        {b.getNamedAttr("binding", FlatSymbolRefAttr::get(binding)),
         b.getNamedAttr("parameters", b.getArrayAttr({})),
         b.getNamedAttr("site", b.getStringAttr(site))});
  };
  // The returned request ignores the inverse result and the zero-result guard.
  // Their normal-or-stop outcomes must remain part of the complete invocation.
  apply(inverse, {f}, {function.getArgument(1)}, "unused_inverse");
  Value accept =
      control
          .invoke("exec.boolean", {b.getI1Type()}, {control.getScope()},
                  {b.getNamedAttr("value", b.getBoolAttr(true)),
                   b.getNamedAttr("site", b.getStringAttr("unused_condition"))})
          .front();
  apply(requireBinding, {}, {accept}, "unused_require");
  if (unclassified) {
    auto g = algebra::GroupType::get(module.getContext(), "bls12-381.g1");
    apply(extra, {g}, {}, "unused_unclassified");
  }
  auto add =
      cast<runtime::BindingOp>(SymbolTable::lookupSymbolIn(owner, "add"));
  auto sum = apply(add, {f}, function.getArguments().drop_front(), "sum");
  control.complete(sum);
  auto stopped =
      cast<func::FuncOp>(SymbolTable::lookupSymbolIn(owner, "request_else"));
  stopped.getBody().dropAllReferences();
  stopped.getBody().getBlocks().clear();
  b.setInsertionPointToEnd(stopped.addEntryBlock());
  exec::ScopedExecutionBuilder alternative(b, stopped);
  alternative.reject("reject", "request_stopped");
}
SmallVector<zkc::detail::NativeTranscriptEvent>
events(const NativeProofConstruction &built, ModuleOp projected) {
  SmallVector<zkc::detail::NativeTranscriptEvent> result;
  StringMap<Operation *> sites;
  participant(projected, "V").walk([&](Operation *op) {
    if (auto site = op->getAttrOfType<StringAttr>("site"))
      sites[site.getValue()] = op;
  });
  for (const auto &value : *(*built.descriptor.getAsArray())[3].getAsArray()) {
    const auto &row = *value.getAsArray();
    auto origin =
        take(protocol::decodeNativeOriginTemplate(*row[1].getAsString()));
    std::string site =
        std::visit([](const auto &event) { return event.site; }, origin.event);
    auto *op = sites.lookup(site);
    require(bool(op), "descriptor event lost actual source occurrence");
    Type payload;
    if (auto send = dyn_cast<pir::EmitOp>(op))
      payload = send.getInput().getType();
    else if (auto receive = dyn_cast<pir::AwaitOp>(op))
      payload = receive.getOutput().getType();
    else if (auto query = dyn_cast<pir::ParticipantQueryOp>(op))
      payload = query.getResult(0).getType();
    require(bool(payload), "unexpected fixture event");
    zkc::detail::NativeTranscriptEvent event{
        site,    row[1].getAsString()->str(),
        payload, *row[0].getAsString() == "query",
        0,       std::nullopt};
    event.depth = count_if(origin.path, [](const auto &step) {
      return step.kind == protocol::NativeOriginStep::Kind::Repeat;
    });
    event.reconstructed = *row[0].getAsString() == "reconstructed-message";
    result.push_back(std::move(event));
  }
  return result;
}
// Directly invokes the actual-body reader. checkNativeProof's additional
// regeneration comparison cannot make these mutation controls pass.
void direct(Cases &cases, ModuleOp source, const NativeProofPolicy &p,
            const protocol::OracleRealizationPolicy &oracle = {}) {
  auto built = take(constructNativeProof(source, p, {}, oracle));
  auto projected = built.realization->project(false);
  require(bool(projected), "ordinary projection");
  auto facts = events(built, *projected);
  checked(zkc::detail::verifyNativeTranscript(*projected, *built.module, p,
                                              facts, nullptr, {},
                                              built.realization.get()));
  auto mutate = [&](StringRef name, llvm::function_ref<void(ModuleOp)> change,
                    StringRef expected = "") {
    cases.run(name, [&] {
      auto candidate =
          OwningOpRef<ModuleOp>(cast<ModuleOp>((*built.module)->clone()));
      change(*candidate);
      ScopedDiagnosticHandler diagnostics(
          candidate->getContext(), [](Diagnostic &) { return success(); });
      auto error = zkc::detail::verifyNativeTranscript(*projected, *candidate,
                                                       p, facts, nullptr, {},
                                                       built.realization.get());
      require(bool(error), "mutated actual candidate accepted");
      auto message = toString(std::move(error));
      require(expected.empty() || namesIdentifier(message, expected),
              "mutation failed outside expected correspondence reader: " +
                  message);
    });
  };
  auto replicaCall = [](ModuleOp candidate) {
    pir::LocalCallOp result;
    participant(candidate, "P").walk([&](pir::LocalCallOp call) {
      if (!result && call.getCallee() == "request" &&
          call.getSite().starts_with("_transcript_"))
        result = call;
    });
    require(bool(result), "missing actual replica call");
    return result;
  };
  bool ordinary = SymbolTable::lookupSymbolIn(unit(*built.module), "request");
  if (ordinary) {
    mutate(
        "wrong request operand",
        [&](ModuleOp m) {
          auto call = replicaCall(m);
          call->setOperand(0, call.getInputs()[1]);
        },
        "native-transcript-correspondence");
    mutate(
        "same-type unpublished private operand",
        [&](ModuleOp m) {
          auto call = replicaCall(m);
          if (call->getBlock() == &participant(m, "P").getBody().front())
            call->setOperand(
                1, participant(m, "P").getBody().front().getArgument(2));
          else
            call->setOperand(0, call.getInputs()[1]);
        },
        "native-transcript-correspondence");
    mutate("call body change", [](ModuleOp m) {
      auto function = cast<func::FuncOp>(
          SymbolTable::lookupSymbolIn(unit(m), "request_step"));
      function.walk([&](exec::ApplyOp op) {
        if (op.getBinding() == "add")
          op->setOperand(1, op->getOperand(2));
      });
    });
    mutate("call scope change", [](ModuleOp m) {
      auto function =
          cast<func::FuncOp>(SymbolTable::lookupSymbolIn(unit(m), "request"));
      function.walk(
          [&](runtime::EnterScopeOp op) { op.setSite("different_scope"); });
    });
    mutate("call normal outcome change", [](ModuleOp m) {
      auto function =
          cast<func::FuncOp>(SymbolTable::lookupSymbolIn(unit(m), "request"));
      bool changed = false;
      function.walk([&](exec::ReturnOp op) {
        op->setOperand(0, function.getArgument(1));
        changed = true;
      });
      require(changed, "actual returned outcome required");
    });
    mutate(
        "replica moved before actual publication frontier",
        [&](ModuleOp m) {
          auto call = replicaCall(m);
          pir::LocalCallOp first;
          for (auto prior : call->getBlock()->getOps<pir::LocalCallOp>())
            if (prior.getCallee().starts_with("_transcript_") &&
                prior->isBeforeInBlock(call) &&
                all_of(call.getInputs(), [&](Value input) {
                  auto *definition = input.getDefiningOp();
                  return !definition ||
                         definition->getBlock() != call->getBlock() ||
                         definition->isBeforeInBlock(prior);
                })) {
              first = prior;
              break;
            }
          require(bool(first), "actual earlier publication observation");
          call->moveBefore(first);
          // Keep the existing formation inventory truthful about the mutated
          // actual order. The independent source-frontier reader must refuse.
          auto record =
              *unit(m).getBody().front().getOps<pir::ProjectionOp>().begin();
          NamedAttrList interface(
              cast<DictionaryAttr>(record.getInterfaces()[0]));
          NamedAttrList construction(
              cast<DictionaryAttr>(interface.get("construction")));
          bool moved = false;
          auto reorder = [&](auto &&self, ArrayAttr actions) -> ArrayAttr {
            SmallVector<Attribute> rows;
            for (auto item : actions) {
              NamedAttrList row(cast<DictionaryAttr>(item));
              if (auto body = dyn_cast_or_null<ArrayAttr>(row.get("body")))
                row.set("body", self(self, body));
              rows.push_back(row.getDictionary(m.getContext()));
            }
            auto at = [&](StringRef site) {
              return find_if(rows, [&](Attribute row) {
                return cast<DictionaryAttr>(row)
                           .getAs<StringAttr>("site")
                           .getValue() == site;
              });
            };
            auto from = at(call.getSite()), to = at(first.getSite());
            if (from != rows.end() && to != rows.end()) {
              Attribute row = *from;
              rows.erase(from);
              rows.insert(at(first.getSite()), row);
              moved = true;
            }
            return ArrayAttr::get(m.getContext(), rows);
          };
          construction.set(
              "actions",
              reorder(reorder, cast<ArrayAttr>(construction.get("actions"))));
          require(moved, "actual inserted action inventory");
          interface.set("construction",
                        construction.getDictionary(m.getContext()));
          record.setInterfacesAttr(ArrayAttr::get(
              m.getContext(), {interface.getDictionary(m.getContext())}));
        },
        "native-transcript-correspondence");
    if (SymbolTable::lookupSymbolIn(unit(*built.module), "unused_require")) {
      mutate(
          "ignored zero-result guard still controls the invocation",
          [](ModuleOp m) {
            auto function = cast<func::FuncOp>(
                SymbolTable::lookupSymbolIn(unit(m), "request_step"));
            bool changed = false;
            function.walk([&](exec::BooleanOp op) {
              op->setAttr("value", BoolAttr::get(m.getContext(), false));
              changed = true;
            });
            require(changed, "actual ignored guard condition");
          },
          "native-transcript-correspondence");
      mutate(
          "stopped Local arm still controls the invocation",
          [](ModuleOp m) {
            auto function = cast<func::FuncOp>(
                SymbolTable::lookupSymbolIn(unit(m), "request_else"));
            bool changed = false;
            function.walk([&](exec::RejectOp op) {
              op->setAttr("reason", StringAttr::get(m.getContext(), "abort"));
              changed = true;
            });
            require(changed, "actual stopped arm");
          },
          "native-transcript-correspondence");
    }
  } else {
    llvm::StringSet<> initializers;
    participant(*projected, "V").walk([&](pir::LocalCallOp call) {
      if (call.getSite().contains("query_discovery_initialize"))
        initializers.insert(call.getCallee());
    });
    mutate(
        "different instance with the same reference type",
        [&](ModuleOp m) {
          SmallVector<pir::LocalCallOp> calls;
          participant(m, "P").walk([&](pir::LocalCallOp call) {
            if (initializers.contains(call.getCallee()))
              calls.push_back(call);
          });
          bool changed = false;
          for (auto first : calls)
            for (auto second : calls)
              if (!changed && first != second &&
                  first->getBlock() == second->getBlock() &&
                  first->isBeforeInBlock(second) &&
                  !first.getInputs().empty() && !second.getInputs().empty() &&
                  first.getInputs()[0].getType() ==
                      second.getInputs()[0].getType() &&
                  first.getInputs()[0] != second.getInputs()[0]) {
                second->setOperand(0, first.getInputs()[0]);
                changed = true;
              }
          require(changed, "two actual same-type instance references required");
        },
        "native-transcript-correspondence");
    mutate(
        "oracle store changed to earlier same-type store",
        [](ModuleOp m) {
          bool changed = false;
          m.walk([&](pir::LocalCallOp call) {
            if (changed || !call.getCallee().starts_with("_oracle_"))
              return;
            for (auto [i, input] : enumerate(call.getInputs())) {
              if (!isa<data::SequenceType>(input.getType()))
                continue;
              for (Operation &prior : *call->getBlock()) {
                if (&prior == call.getOperation())
                  break;
                for (Value value : prior.getResults())
                  if (!changed && value.getType() == input.getType() &&
                      value != input) {
                    call->setOperand(i, value);
                    changed = true;
                  }
              }
            }
          });
          require(changed, "actual oracle store versions required");
        },
        "native-transcript-correspondence");
    mutate("all authentication before answer replay", [](ModuleOp m) {
      pir::LocalCallOp auth, replay;
      participant(m, "V").walk([&](pir::LocalCallOp call) {
        if (!auth && call.getSite().contains("opening_authenticate"))
          auth = call;
        if (!replay && call.getSite().contains("query_replay"))
          replay = call;
      });
      require(auth && replay && auth->getBlock() == replay->getBlock(),
              "actual authentication and replay calls required");
      replay->moveBefore(auth);
    });
  }
  mutate("observation omission", [](ModuleOp m) {
    pir::LocalCallOp observation;
    participant(m, "P").walk([&](pir::LocalCallOp op) {
      if (!observation && op.getCallee().starts_with("_transcript_"))
        observation = op;
    });
    require(bool(observation), "missing observation");
    auto n = observation.getNumResults();
    require(n && observation.getInputs()[0].getType() ==
                     observation.getResult(n - 1).getType(),
            "observation state slot");
    observation.getResult(n - 1).replaceAllUsesWith(observation.getInputs()[0]);
    observation.erase();
  });
  mutate("observation order", [](ModuleOp m) {
    SmallVector<pir::LocalCallOp> calls;
    participant(m, "P").walk([&](pir::LocalCallOp op) {
      if (op.getCallee().starts_with("_transcript_"))
        calls.push_back(op);
    });
    require(calls.size() > 1, "two observations required");
    calls[1]->moveBefore(calls[0]);
  });
  mutate("final observation after final sample omitted", [](ModuleOp m) {
    pir::LocalCallOp observation;
    participant(m, "P").walk([&](pir::LocalCallOp op) {
      if (op.getCallee().starts_with("_transcript_"))
        observation = op;
    });
    require(bool(observation), "actual final observation required");
    auto n = observation.getNumResults();
    require(n && observation.getInputs()[0].getType() ==
                     observation.getResult(n - 1).getType(),
            "actual final observation state");
    observation.getResult(n - 1).replaceAllUsesWith(observation.getInputs()[0]);
    observation.erase();
  });
  pir::ProtocolLoopOp loop;
  participant(*built.module, "P").walk([&](pir::ProtocolLoopOp op) {
    if (!loop && op.getCarried() > 1)
      loop = op;
  });
  if (loop) {
    auto firstLoop = [](ModuleOp m) {
      pir::ProtocolLoopOp result;
      participant(m, "P").walk([&](pir::ProtocolLoopOp op) {
        if (!result && op.getCarried() > 1)
          result = op;
      });
      return result;
    };
    mutate("loop count including zero iterations", [&](ModuleOp m) {
      auto loop = firstLoop(m);
      OpBuilder b(loop);
      auto zero = data::IndexOp::create(
          b, loop.getLoc(), b.getIntegerType(64, false),
          b.getIntegerAttr(b.getIntegerType(64, false), 0));
      loop->setOperand(0, zero.getResult());
    });
    mutate("loop carry initializer", [&](ModuleOp m) {
      auto loop = firstLoop(m);
      auto &body = participant(m, "P").getBody().front();
      require(loop.getCarried() > 1, "replica and state carry");
      loop->setOperand(1, body.getArgument(1));
    });
    mutate("loop yielded replica", [&](ModuleOp m) {
      auto loop = firstLoop(m);
      auto &body = loop.getBody().front();
      auto yield = cast<pir::ProtocolYieldOp>(body.back());
      require(yield.getNumOperands() > 1, "replica yielded slot");
      yield->setOperand(0, body.getArgument(1));
    });
    if (ordinary)
      mutate("loop capture swap", [&](ModuleOp m) {
        auto loop = firstLoop(m);
        unsigned split = 1 + loop.getCarried();
        bool changed = false;
        for (unsigned i = split; i < loop.getNumOperands() && !changed; ++i)
          for (unsigned j = i + 1; j < loop.getNumOperands() && !changed; ++j)
            if (loop.getOperand(i).getType() == loop.getOperand(j).getType() &&
                loop.getOperand(i) != loop.getOperand(j)) {
              auto value = loop.getOperand(i);
              loop->setOperand(i, loop.getOperand(j));
              loop->setOperand(j, value);
              changed = true;
            }
        require(changed, "two distinct same-type captures required");
      });
  }
}
} // namespace
int main(int argc, char **argv) {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  cases.run(
      "loop obligations follow source order, not allocation addresses", [&] {
        NativeProofPolicy p;
        p.entry = "main";
        p.producer = "P";
        p.validator = "V";
        auto source =
            parseSourceString<ModuleOp>(identityLoopFixture, &context);
        require(bool(source), "ordered-loop source");
        auto function = *unit(*source)
                             .getBody()
                             .front()
                             .getOps<pir::MathematicalOp>()
                             .begin();
        auto loop = *function.getBody().front().getOps<pir::RepeatOp>().begin();
        OpBuilder builder(function.getBody().front().getTerminator());
        for (unsigned i = 0; i != 3; ++i) {
          auto copy = cast<pir::RepeatOp>(builder.clone(*loop));
          copy.setSite("extra_" + std::to_string(i));
        }
        auto built = take(constructNativeProof(*source, p));
        auto projected = built.realization->project(false);
        require(bool(projected), "ordered-loop projection");
        auto &body = participant(*projected, "P").getBody().front();
        SmallVector<Operation *> originals, order;
        for (auto item : body.getOps<pir::ProtocolLoopOp>())
          originals.push_back(item);
        require(originals.size() == 4, "four actual paired loops");
        for (auto *item : originals) {
          require(item->getNumResults() == 0, "fixture loops have no outputs");
          order.push_back(item->clone());
        }
        // Relocate the same operations without changing their lexical order,
        // sites, operands or bodies. Only allocation addresses are reversed.
        llvm::sort(order, [](Operation *a, Operation *b) {
          return std::less<Operation *>{}(b, a);
        });
        for (auto [original, copy] : zip(originals, order)) {
          copy->setAttrs(original->getAttrs());
          copy->setOperands(original->getOperands());
          copy->setLoc(original->getLoc());
          copy->getRegion(0).takeBody(original->getRegion(0));
          builder.setInsertionPoint(original);
          builder.insert(copy);
          original->erase();
        }
        require(succeeded(admitStage(*projected)),
                "relocated loops must retain their admitted source meaning");
        auto plan =
            take(zkc::detail::planNativeRequests(unit(*projected), p, {}));
        require(plan.root && plan.root->loops.size() == order.size(),
                "all source loop obligations must remain present");
        for (auto [expected, actual] : zip(order, plan.root->loops))
          require(actual.first == expected,
                  "allocation order changed obligation discovery");
      });
  for (unsigned count : {0, 1})
    cases.run(
        Twine("identity construction paired-loop counts ") + Twine(count), [&] {
          NativeProofPolicy p;
          p.entry = "main";
          p.producer = "P";
          p.validator = "V";
          auto source =
              parseSourceString<ModuleOp>(identityLoopFixture, &context);
          require(bool(source), "identity-loop source");
          if (!count)
            source->walk([&](data::IndexOp index) {
              index.setValueAttr(
                  IntegerAttr::get(index.getResult().getType(), 0));
            });
          auto selected = take(selectNativeProofDraws(*source, p));
          require(selected.draws.empty(), "identity has no selected draws");
          auto built = take(constructNativeProof(*source, p));
          checked(checkNativeProof(*source, *built.module, p));
          auto projected = built.realization->project(false);
          require(bool(projected), "identity-loop projection");
          checked(zkc::detail::verifyNativeTranscript(*projected, *built.module,
                                                      p, {}, nullptr, {},
                                                      built.realization.get()));
          if (!count)
            return;
          auto unequalSource = cast<ModuleOp>(source->clone());
          OwningOpRef<ModuleOp> changed(unequalSource);
          auto program = *unit(unequalSource)
                              .getBody()
                              .front()
                              .getOps<pir::MathematicalOp>()
                              .begin();
          auto index =
              *program.getBody().front().getOps<data::IndexOp>().begin();
          index.setValueAttr(IntegerAttr::get(index.getResult().getType(), 0));
          refuses(selectNativeProofDraws(unequalSource, p),
                  "native-request-reconstruction");
          refuses(constructNativeProof(unequalSource, p),
                  "native-request-reconstruction");
          // Identical actual candidates cannot bypass the missing source count
          // premise merely because this construction adds no transcript
          // helpers.
          for (auto module : {*projected, *built.module})
            participant(module, "P").walk([&](data::IndexOp value) {
              value.setValueAttr(
                  IntegerAttr::get(value.getResult().getType(), 0));
            });
          auto refusal = zkc::detail::verifyNativeTranscript(
              *projected, *built.module, p, {}, nullptr, {},
              built.realization.get());
          require(bool(refusal),
                  "identity reader accepted unequal actual counts");
          require(namesIdentifier(toString(std::move(refusal)),
                                  "native-request-reconstruction"),
                  "identity reader must check the original count premise");
        });
  // Preserve the installed scalar-index, block and gated construction paths.
  // These use the public source admission and supplied-candidate checker.
  for (unsigned degree : {4, 8})
    for (bool block : {false, true})
      for (int difficulty : {-1, 0, 6})
        cases.run(
            Twine("installed index construction degree ") + Twine(degree) +
                (block ? " block " : " scalar ") + Twine(difficulty),
            [&] {
              std::string field =
                  "koala-bear.ext" + std::to_string(degree) + "-binomial3";
              std::string text = R"mlir(
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%secret:ui64,%coins:!protocol.service_ref<"random.FIELD/0">):
  %sent = protocol.exchange %secret {sender="P",receiver="V",site="commitment"} : ui64
  %n = "data.index"() {value=16:ui64} : ()->ui64
  %q = "data.index"() {value=4:ui64} : ()->ui64
  %sample = "protocol.query"(%coins,%n,%q) {method="indices",owner="V",site="pick"} : (!protocol.service_ref<"random.FIELD/0">,ui64,ui64)->!data.indices
  %actual = protocol.exchange %sample {sender="V",receiver="P",site="delivery"} : !data.indices
  %echo = protocol.exchange %actual {sender="P",receiver="V",site="response"} : !data.indices
  %ok = arith.constant true
  "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",function_type=(ui64,!protocol.service_ref<"random.FIELD/0">)->i1,
     roles=["P","V"],input_roles=[["P"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
              for (size_t at = text.find("FIELD"); at != std::string::npos;
                   at = text.find("FIELD"))
                text.replace(at, StringRef("FIELD").size(), field);
              auto source = parseSourceString<ModuleOp>(text, &context);
              require(bool(source), "installed index source");
              if (!block) {
                source->walk([&](pir::QueryOp query) {
                  query->setOperands(query->getOperands().take_front(2));
                  query.setMethod("index");
                  query.getResult(0).setType(
                      IntegerType::get(&context, 64, IntegerType::Unsigned));
                });
                source->walk([&](pir::ExchangeOp exchange) {
                  exchange.getResult().setType(exchange.getInput().getType());
                });
              }
              auto p = policy();
              p.suite = "hash-chain.keccak256." + field + ".rejection31le/0";
              p.services = {1};
              p.publicInputs.clear();
              p.draws = {{"pick", "delivery"}};
              if (difficulty >= 0)
                p.gates = {{"pick", unsigned(difficulty)}};
              if (!block && difficulty >= 0) {
                // Installed gating applies to block requests; retain
                // the explicit scalar-index gate refusal as well.
                refuses(constructNativeProof(*source, p),
                        "native-proof-gate-selection");
                return;
              }
              auto built = take(constructNativeProof(*source, p));
              checked(checkNativeProof(*source, *built.module, p));
            });
  for (bool eventful : {false, true})
    for (bool nested : {false, true}) {
      auto text = challengeLoopFixture.str();
      if (nested) {
        auto at = text.find("  \"protocol.repeat\"(%count,%coins) ({");
        require(at != std::string::npos, "challenge outer-loop insertion");
        text.replace(
            at, StringRef("  \"protocol.repeat\"(%count,%coins) ({").size(),
            "  %one = \"data.index\"() {value=1:ui64} : ()->ui64\n"
            "  \"protocol.repeat\"(%one,%count,%coins) ({\n"
            "  ^outer(%j:ui64,%innerCount:ui64,%outerCoins:!R):\n"
            "  \"protocol.repeat\"(%innerCount,%outerCoins) ({");
        at = text.find("  %ok = algebra.field_equal");
        require(at != std::string::npos, "challenge outer-loop termination");
        text.insert(
            at, "  \"protocol.yield\"() : ()->()\n"
                "  }) {site=\"outer\",carried=0:i64,maximum=1:i64,"
                "roles=[\"P\",\"V\"],carried_roles=[]} : (ui64,ui64,!R)->()\n");
      }
      if (!eventful) {
        auto begin = text.find("   %c = ");
        auto end = text.find("   \"protocol.yield\"", begin);
        require(begin != std::string::npos && end != std::string::npos,
                "move selected events outside the communication-free loop");
        auto selected = text.substr(begin, end - begin);
        text.erase(begin, end - begin);
        auto random = selected.find("%random");
        require(random != std::string::npos, "selected source authority");
        selected.replace(random, StringRef("%random").size(), "%coins");
        text.insert(text.find("  %ok = "), selected);
      }
      std::string prefix = nested ? "nested " : "";
      prefix += eventful ? "challenge-only" : "communication-free";
      auto p = policy();
      p.publicInputs = {0};
      p.services = {1};
      auto unequal = text;
      auto at = unequal.find("%p = \"data.index\"() {value=1:ui64}");
      require(at != std::string::npos, "challenge producer count");
      unequal.replace(at,
                      StringRef("%p = \"data.index\"() {value=1:ui64}").size(),
                      "%p = \"data.index\"() {value=0:ui64}");
      cases.run(prefix + " 0/1 construction refuses", [&] {
        auto source = parseSourceString<ModuleOp>(unequal, &context);
        require(bool(source), "unequal challenge-loop source");
        refuses(constructNativeProof(*source, p),
                "native-request-reconstruction");
      });
      cases.run(prefix + " 0/1 selection refuses", [&] {
        auto source = parseSourceString<ModuleOp>(unequal, &context);
        require(bool(source), "unequal challenge-loop source");
        auto selection = p;
        selection.draws.clear();
        refuses(selectNativeProofDraws(*source, selection),
                "native-request-reconstruction");
      });
      for (unsigned count : {0, 1})
        cases.run(prefix + Twine(" equal counts ") + Twine(count), [&] {
          auto source = parseSourceString<ModuleOp>(text, &context);
          require(bool(source), "equal challenge-loop source");
          if (!count) {
            auto program = *unit(*source)
                                .getBody()
                                .front()
                                .getOps<pir::MathematicalOp>()
                                .begin();
            for (auto [i, index] :
                 enumerate(program.getBody().front().getOps<data::IndexOp>()))
              if (i < 2)
                index.setValueAttr(
                    IntegerAttr::get(index.getResult().getType(), 0));
          }
          auto selection = p;
          selection.draws.clear();
          auto selected = take(selectNativeProofDraws(*source, selection));
          require(selected.draws == p.draws,
                  "challenge-loop selected delivery");
          auto built = take(constructNativeProof(*source, p));
          auto projected = built.realization->project(false);
          require(bool(projected), "challenge-loop projection");
          auto facts = events(built, *projected);
          require(
              none_of(facts,
                      [](const auto &event) { return event.reconstructed; }),
              "challenge-only fixture has no requests");
          checked(zkc::detail::verifyNativeTranscript(*projected, *built.module,
                                                      p, facts, nullptr, {},
                                                      built.realization.get()));
          if (count) {
            // Keep both supplied bodies well formed and identical to their
            // own role's original computation; the missing premise is joint
            // counts.
            auto change = [&](ModuleOp module) {
              pir::ProtocolLoopOp loop;
              participant(module, "P").walk([&](pir::ProtocolLoopOp op) {
                if (op.getSite() == "rounds")
                  loop = op;
              });
              require(bool(loop), "actual challenge loop");
              Value value = loop.getInputs()[0];
              if (auto argument = dyn_cast<BlockArgument>(value)) {
                auto parent = cast<pir::ProtocolLoopOp>(loop->getParentOp());
                value = parent.getInputs()[argument.getArgNumber()];
              }
              auto index = value.getDefiningOp<data::IndexOp>();
              require(bool(index), "actual producer count source");
              index.setValueAttr(IntegerAttr::get(value.getType(), 0));
            };
            change(*projected);
            change(*built.module);
            auto refusal = zkc::detail::verifyNativeTranscript(
                *projected, *built.module, p, facts, nullptr, {},
                built.realization.get());
            require(bool(refusal),
                    "unequal supplied actual loop counts accepted");
            require(namesIdentifier(toString(std::move(refusal)),
                                    "native-request-reconstruction"),
                    "unequal actual counts must reach correspondence planning");
          }
        });
    }
  cases.run(
      "complete Local closure retains ignored partial work and stopped arm",
      [&] {
        auto source =
            parseSourceString<ModuleOp>(fixture, ParserConfig(&context, false));
        require(bool(source), "partial request source");
        installRequest(*source);
        addUnusedRequestWork(*source, false);
        direct(cases, *source, policy());
      });
  cases.run(
      "publication of f(private) does not justify private substitution", [&] {
        auto source =
            parseSourceString<ModuleOp>(fixture, ParserConfig(&context, false));
        require(bool(source), "private-function publication source");
        installRequest(*source);
        pir::ExchangeOp publication;
        source->walk([&](pir::ExchangeOp op) {
          if (op.getSite() == "published")
            publication = op;
        });
        require(bool(publication), "actual publication");
        OpBuilder b(publication);
        auto program = publication->getParentOfType<pir::MathematicalOp>();
        Value secret = program.getBody().front().getArgument(2);
        auto call = pir::LocalCallOp::create(
            b, publication.getLoc(), TypeRange{secret.getType()},
            ValueRange{secret, secret}, "request", "private_publication", "P");
        publication->setOperand(0, call.getResult(0));
        direct(cases, *source, policy());
      });
  cases.run(
      "ignored unclassified operation refuses despite unused result", [&] {
        auto source =
            parseSourceString<ModuleOp>(fixture, ParserConfig(&context, false));
        require(bool(source), "unclassified request source");
        installRequest(*source);
        addUnusedRequestWork(*source, true);
        refuses(constructNativeProof(*source, policy()),
                "native-request-reconstruction");
      });
  for (auto item : {std::pair<StringRef, StringRef>{"ordinary", fixture},
                    {"loop", loopFixture}})
    cases.run(item.first, [&] {
      auto source = parseSourceString<ModuleOp>(item.second,
                                                ParserConfig(&context, false));
      require(bool(source), "fixture parse");
      installRequest(*source);
      direct(cases, *source, policy());
    });
  cases.run("ordinary loop with zero actual iterations", [&] {
    auto source =
        parseSourceString<ModuleOp>(loopFixture, ParserConfig(&context, false));
    require(bool(source), "zero-iteration source parse");
    installRequest(*source);
    source->walk([&](data::IndexOp count) {
      if (count.getValue() == 2)
        count.setValueAttr(IntegerAttr::get(count.getResult().getType(), 0));
    });
    direct(cases, *source, policy());
  });
  cases.run("late carry moves one actual definition to the earlier frontier",
            [&] {
              auto source = parseSourceString<ModuleOp>(
                  lateLoopFixture, ParserConfig(&context, false));
              require(bool(source), "late carry source parse");
              installRequest(*source);
              auto built = take(constructNativeProof(*source, policy()));
              auto projected = built.realization->project(false);
              require(bool(projected), "late carry ordinary projection");
              auto facts = events(built, *projected);
              checked(zkc::detail::verifyNativeTranscript(
                  *projected, *built.module, policy(), facts, nullptr, {},
                  built.realization.get()));
              unsigned definitions = 0;
              auto producer = participant(*built.module, "P");
              pir::ProtocolLoopOp loop;
              producer.walk([&](pir::ProtocolLoopOp op) {
                if (!loop)
                  loop = op;
              });
              require(bool(loop), "actual late carry loop required");
              for (Operation &op : producer.getBody().front())
                if (auto call = dyn_cast<pir::LocalCallOp>(op);
                    call && call.getCallee() == "request") {
                  ++definitions;
                  require(call->isBeforeInBlock(loop),
                          "shared replica must precede its carry initializer");
                }
              require(definitions == 1,
                      "one actual replica of the shared initializer");
            });
  for (unsigned count : {0, 2})
    cases.run(
        Twine("earlier loop result at saved capture frontier ") + Twine(count),
        [&] {
          std::string text = lateLoopFixture.str();
          auto replace = [&](StringRef from, StringRef to) {
            auto at = text.find(from.str());
            require(at != std::string::npos, "successive loop fixture");
            text.replace(at, from.size(), to.str());
          };
          replace("  %c = \"protocol.query\"", R"mlir(
  %after = "protocol.repeat"(%n,%public,%done) ({
  ^later(%j:ui64,%currentLater:!F,%prior:!F):
   %nextLater = "protocol.local_call"(%currentLater,%prior) {callee=@request,role="V",site="advance_later"} : (!F,!F)->!F
   "protocol.yield"(%nextLater) : (!F)->()
  }) {site="later_rounds",carried=1:i64,maximum=4:i64,roles=["P","V"],carried_roles=[["V"]]} : (ui64,!F,!F)->!F
  %c = "protocol.query")mlir");
          replace("%received = protocol.exchange %seed",
                  "%received = protocol.exchange %done");
          replace("%replay = protocol.exchange %done",
                  "%replay = protocol.exchange %after");
          auto source =
              parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
          require(bool(source), "successive loop source parse");
          installRequest(*source);
          if (!count)
            source->walk([&](data::IndexOp index) {
              index.setValueAttr(
                  IntegerAttr::get(index.getResult().getType(), 0));
            });
          auto p = policy();
          auto built = take(constructNativeProof(*source, p));
          auto projected = built.realization->project(false);
          require(bool(projected), "successive loop projection");
          auto facts = events(built, *projected);
          checked(zkc::detail::verifyNativeTranscript(*projected, *built.module,
                                                      p, facts, nullptr, {},
                                                      built.realization.get()));
          auto candidate =
              OwningOpRef<ModuleOp>(cast<ModuleOp>((*built.module)->clone()));
          pir::ProtocolLoopOp earlier, later;
          auto producer = participant(*candidate, "P");
          producer.walk([&](pir::ProtocolLoopOp loop) {
            if (loop.getSite() == "rounds")
              earlier = loop;
            if (loop.getSite() == "later_rounds")
              later = loop;
          });
          require(earlier && later && earlier.getNumResults() == 1 &&
                      later.getInputs().back() == earlier.getResult(0),
                  "capture must use the exact earlier replica result");
          later->setOperand(later.getNumOperands() - 1,
                            producer.getBody().front().getArgument(0));
          require(succeeded(verify(*candidate)),
                  "same-type capture mutation must remain well formed");
          auto refusal = zkc::detail::verifyNativeTranscript(
              *projected, *candidate, p, facts, nullptr, {},
              built.realization.get());
          require(bool(refusal), "earlier loop result substitution accepted");
          require(namesIdentifier(toString(std::move(refusal)),
                                  "native-transcript-correspondence"),
                  "capture mutation must reach correspondence reader");
        });
  for (unsigned count : {0, 2})
    cases.run(
        Twine("late mutually dependent carries share one source call ") +
            Twine(count),
        [&] {
          std::string text = lateLoopFixture.str();
          auto replace = [&](StringRef from, StringRef to) {
            auto at = text.find(from.str());
            require(at != std::string::npos, "mutual carry fixture");
            text.replace(at, from.size(), to.str());
          };
          replace("%done =", "%done:2 =");
          replace("\"protocol.yield\"(%next) : (!F)->()",
                  "\"protocol.yield\"(%next,%next) : (!F,!F)->()");
          replace("carried=1:i64,maximum=4:i64,roles=[\"P\",\"V\"],"
                  "carried_roles=[[\"V\"]]} : (ui64,!F,!F)->!F",
                  "carried=2:i64,maximum=4:i64,roles=[\"P\",\"V\"],"
                  "carried_roles=[[\"V\"],[\"V\"]]} : (ui64,!F,!F)->(!F,!F)");
          replace("%replay = protocol.exchange %done",
                  "%replay = protocol.exchange %done#0");
          replace("%ok = algebra.field_equal %done,%seed",
                  "%ok = algebra.field_equal %done#0,%seed");
          auto source =
              parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
          require(bool(source), "mutual carry source parse");
          installRequest(*source);
          if (!count)
            source->walk([&](data::IndexOp index) {
              index.setValueAttr(
                  IntegerAttr::get(index.getResult().getType(), 0));
            });
          auto p = policy();
          auto built = take(constructNativeProof(*source, p));
          auto projected = built.realization->project(false);
          require(bool(projected), "mutual carry projection");
          auto facts = events(built, *projected);
          checked(zkc::detail::verifyNativeTranscript(*projected, *built.module,
                                                      p, facts, nullptr, {},
                                                      built.realization.get()));
          auto candidate =
              OwningOpRef<ModuleOp>(cast<ModuleOp>((*built.module)->clone()));
          pir::ProtocolLoopOp loop;
          participant(*candidate, "P").walk([&](pir::ProtocolLoopOp op) {
            if (op.getSite() == "rounds")
              loop = op;
          });
          require(loop && loop.getCarried() == 2,
                  "both replica invariant slots must be retained");
          unsigned calls = 0;
          Value next;
          loop.walk([&](pir::LocalCallOp call) {
            if (call.getCallee() == "request") {
              ++calls;
              next = call.getResult(0);
            }
          });
          auto yield =
              cast<pir::ProtocolYieldOp>(loop.getBody().front().back());
          require(calls == 1 && yield.getNumOperands() == 2 &&
                      yield.getOperand(0) == next &&
                      yield.getOperand(1) == next,
                  "one complete invocation must supply both back edges");
          yield->setOperand(1, loop.getBody().front().getArgument(2));
          require(succeeded(verify(*candidate)),
                  "same-type back-edge mutation must remain well formed");
          auto refusal = zkc::detail::verifyNativeTranscript(
              *projected, *candidate, p, facts, nullptr, {},
              built.realization.get());
          require(bool(refusal),
                  "mutual carry back-edge substitution accepted");
          require(namesIdentifier(toString(std::move(refusal)),
                                  "native-transcript-correspondence"),
                  "back-edge mutation must reach correspondence reader");
        });
  cases.run("uninstalled deterministic implementation refuses", [&] {
    auto source =
        parseSourceString<ModuleOp>(fixture, ParserConfig(&context, false));
    require(bool(source), "implementation source parse");
    installRequest(*source);
    source->walk([&](runtime::BindingOp binding) {
      binding.setImplementation("unknown.implementation/0");
    });
    ScopedDiagnosticHandler diagnostics(&context,
                                        [](Diagnostic &) { return success(); });
    refuses(constructNativeProof(*source, policy()), "native-proof-source");
  });
  for (bool captureCoordinate : {false, true})
    cases.run(
        captureCoordinate
            ? "nested transcript reuses exact source coordinate capture"
            : "nested loop count follows same-original public capture",
        [&] {
          std::string text = loopFixture.str();
          auto replace = [&](StringRef from, StringRef to) {
            auto at = text.find(from.str());
            require(at != std::string::npos, "nested fixture substitution");
            text.replace(at, from.size(), to.str());
          };
          replace("%coins:!R):", "%coins:!R,%trips:ui64):");
          replace(
              "%done = "
              "\"protocol.repeat\"(%n,%public,%published,%coins,%public) ({",
              "%completed = "
              "\"protocol.repeat\"(%n,%public,%published,%coins,%trips) "
              "({\n"
              "  "
              "^outer(%j:ui64,%outerSeed:!F,%outerValue:!F,%outerRandom:!R,%"
              "innerCount:ui64):\n"
              "  %done = "
              "\"protocol.repeat\"(%innerCount,%outerSeed,%outerValue,%"
              "outerRandom,%"
              "outerSeed) ({");
          replace(
              "  %replay = protocol.exchange %done",
              "  \"protocol.yield\"(%done) : (!F)->()\n"
              "  }) "
              "{site=\"outer\",carried=1:i64,maximum=4:i64,roles=[\"P\",\"V\"],"
              "carried_roles=[[\"V\"]]} : (ui64,!F,!F,!R,ui64)->!F\n"
              "  %replay = protocol.exchange %completed");
          replace("%ok = algebra.field_equal %done,%public",
                  "%ok = algebra.field_equal %completed,%public");
          replace("function_type=(!F,!F,!F,!F,!R)->i1",
                  "function_type=(!F,!F,!F,!F,!R,ui64)->i1");
          replace("input_roles=[[\"P\",\"V\"],[\"P\"],[\"P\"],[\"V\"],[\"V\"]]",
                  "input_roles=[[\"P\",\"V\"],[\"P\"],[\"P\"],[\"V\"],[\"V\"],["
                  "\"P\","
                  "\"V\"]]");
          if (captureCoordinate) {
            replace("outerSeed) ({", "outerSeed,%j) ({");
            replace("%known:!F):", "%known:!F,%coordinate:ui64):");
            replace("%sent = protocol.exchange %value",
                    "%sameCoordinate = "
                    "\"data.index_equal\"(%coordinate,%coordinate) : "
                    "(ui64,ui64)->i1\n"
                    "   protocol.guard %sameCoordinate "
                    "{owner=\"V\",site=\"coordinate_guard\"}\n"
                    "   %sent = protocol.exchange %value");
            replace("(ui64,!F,!F,!R,!F)->!F", "(ui64,!F,!F,!R,!F,ui64)->!F");
          }
          auto source =
              parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
          require(bool(source), "nested count source parse");
          installRequest(*source);
          auto p = policy();
          p.publicInputs.push_back(5);
          auto built = take(constructNativeProof(*source, p));
          auto projected = built.realization->project(false);
          require(bool(projected), "nested count ordinary projection");
          auto facts = events(built, *projected);
          checked(zkc::detail::verifyNativeTranscript(*projected, *built.module,
                                                      p, facts, nullptr, {},
                                                      built.realization.get()));
          if (captureCoordinate) {
            pir::ProtocolLoopOp original, actual;
            participant(*projected, "V").walk([&](pir::ProtocolLoopOp loop) {
              if (loop.getSite() == "rounds")
                original = loop;
            });
            participant(*built.module, "V").walk([&](pir::ProtocolLoopOp loop) {
              if (loop.getSite() == "rounds")
                actual = loop;
            });
            require(original && actual &&
                        actual.getNumOperands() ==
                            original.getNumOperands() + 1 &&
                        actual.getCarried() == original.getCarried() + 1,
                    "existing source coordinate capture must be reused; only "
                    "state is added");
            auto candidate =
                OwningOpRef<ModuleOp>(cast<ModuleOp>((*built.module)->clone()));
            pir::LocalCallOp transition;
            participant(*candidate, "V").walk([&](pir::LocalCallOp call) {
              if (!transition && call->getParentOfType<pir::ProtocolLoopOp>() &&
                  call.getSite().starts_with("_transcript_"))
                transition = call;
            });
            require(bool(transition) && transition.getNumOperands() >= 2,
                    "nested transition has two logical coordinates");
            auto &body = *transition->getBlock();
            transition->setOperand(transition.getNumOperands() - 2,
                                   body.getArgument(0));
            require(succeeded(verify(*candidate)),
                    "coordinate mutation must remain well formed");
            auto refusal = zkc::detail::verifyNativeTranscript(
                *projected, *candidate, p, facts, nullptr, {},
                built.realization.get());
            require(bool(refusal), "inner induction substituted for captured "
                                   "outer coordinate accepted");
            require(namesIdentifier(toString(std::move(refusal)),
                                    "native-transcript-correspondence"),
                    "coordinate mutation must reach correspondence reader");
          }
          auto mutant =
              OwningOpRef<ModuleOp>(cast<ModuleOp>((*built.module)->clone()));
          pir::ProtocolLoopOp inner;
          participant(*mutant, "P").walk([&](pir::ProtocolLoopOp op) {
            if (op.getSite() == "rounds")
              inner = op;
          });
          require(inner && isa<pir::ProtocolLoopOp>(inner->getParentOp()),
                  "actual nested count loop");
          inner->setOperand(0, inner->getBlock()->getArgument(0));
          auto refusal = zkc::detail::verifyNativeTranscript(
              *projected, *mutant, p, facts, nullptr, {},
              built.realization.get());
          require(
              bool(refusal),
              "outer iteration substituted for public inner count accepted");
          consumeError(std::move(refusal));
        });
  cases.run("verifier-only public operand refuses", [&] {
    auto source =
        parseSourceString<ModuleOp>(fixture, ParserConfig(&context, false));
    require(bool(source), "fixture parse");
    installRequest(*source);
    source->walk([&](pir::LocalCallOp call) {
      if (call.getSite() == "compute_request")
        call->setOperand(0, call->getParentOfType<pir::MathematicalOp>()
                                .getBody()
                                .front()
                                .getArgument(3));
    });
    refuses(constructNativeProof(*source, policy()),
            "native-request-reconstruction");
  });
  for (bool nested : {false, true})
    cases.run(
        nested ? "nested Common generated request counts"
               : "common generated requests",
        [&] {
          require(argc == 2, "Common fixture path argument required");
          auto source = parseSourceFile<ModuleOp>(argv[1], &context);
          require(bool(source), "Common fixture parse");
          auto program = *unit(*source)
                              .getBody()
                              .front()
                              .getOps<pir::MathematicalOp>()
                              .begin();
          auto &body = program.getBody().front();
          OpBuilder b(&context);
          auto loc = program.getLoc();
          auto rng =
              pir::ServiceReferenceType::get(&context, "random.bls12-381.fr/0");
          Value coins = body.addArgument(rng, loc);
          auto f = algebra::FieldType::get(&context, "bls12-381.fr");
          auto first = *body.getOps<pir::OracleQueryOp>().begin();
          b.setInsertionPoint(first);
          auto query = pir::QueryOp::create(b, loc, TypeRange{f}, coins,
                                            ValueRange{}, "draw", "V", "draw");
          pir::ExchangeOp::create(b, loc, query.getResult(0), "challenge", "V",
                                  "P");
          auto returned = cast<pir::MathematicalReturnOp>(body.back());
          b.setInsertionPoint(returned);
          auto ok = algebra::FieldEqualOp::create(b, loc, b.getI1Type(),
                                                  returned.getOperand(0),
                                                  returned.getOperand(0));
          returned->setOperands(ValueRange{ok.getResult()});
          SmallVector<Type> inputs(program.getFunctionType().getInputs());
          inputs.push_back(rng);
          program.setFunctionType(b.getFunctionType(inputs, {b.getI1Type()}));
          SmallVector<Attribute> owners(program.getInputRoles().begin(),
                                        program.getInputRoles().end());
          owners.push_back(b.getStrArrayAttr({"V"}));
          program.setInputRolesAttr(b.getArrayAttr(owners));
          program.setOutputRolesAttr(
              b.getArrayAttr({b.getStrArrayAttr({"V"})}));
          if (nested) {
            // Put actual logical construction/query work in an outer source
            // repeat. Common's separately checked request loops must then
            // reproduce captured receiver stores and prove their inner count
            // recurrence in that frame.
            Region replacement;
            auto *root = new Block;
            replacement.push_back(root);
            for (BlockArgument arg : body.getArguments())
              root->addArgument(arg.getType(), loc);
            b.setInsertionPointToEnd(root);
            auto index = b.getIntegerType(64, false);
            Value count = data::IndexOp::create(b, loc, index,
                                                b.getIntegerAttr(index, 2));
            OperationState state(loc, "protocol.repeat");
            SmallVector<Value> captures{count};
            append_range(captures, root->getArguments());
            state.addOperands(captures);
            state.addAttributes(
                {b.getNamedAttr("site", b.getStringAttr("outer")),
                 b.getNamedAttr("carried", b.getI64IntegerAttr(0)),
                 b.getNamedAttr("maximum", b.getI64IntegerAttr(2)),
                 b.getNamedAttr("roles", b.getStrArrayAttr({"P", "V"})),
                 b.getNamedAttr("carried_roles", b.getArrayAttr({}))});
            auto *region = state.addRegion();
            auto *inside = new Block;
            region->push_back(inside);
            inside->addArgument(index, loc);
            IRMapping mapping;
            for (BlockArgument arg : body.getArguments())
              mapping.map(arg, inside->addArgument(arg.getType(), loc));
            b.setInsertionPointToEnd(inside);
            for (Operation &op : body)
              if (!isa<pir::MathematicalReturnOp>(op))
                b.clone(op, mapping);
            pir::ProtocolYieldOp::create(b, loc, ValueRange{});
            b.setInsertionPointToEnd(root);
            b.create(state);
            pir::MathematicalReturnOp::create(b, loc,
                                              ValueRange{root->getArgument(3)});
            program.getBody().takeBody(replacement);
          }
          auto p = policy();
          p.publicInputs = {2, 3};
          protocol::OracleRealizationPolicy oracle;
          auto prepared = mathematical::prepareProtocol(*source, false);
          require(bool(prepared), "Common prepare");
          auto roots = take(
              protocol::resolveOracleRealizationSelection(*prepared, oracle));
          for (auto &root : roots)
            root.realization = {
                "rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0",
                protocol::OracleLeafGrouping::AntipodalPairs,
                protocol::OracleLeafOrder::Natural};
          oracle.roots = std::move(roots);
          direct(cases, *source, p, oracle);
        });
  return cases.result();
}
