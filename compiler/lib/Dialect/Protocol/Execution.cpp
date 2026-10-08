#include "zkc/Dialect/Protocol/Execution.h"
#include "../Verification.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Relation/IR/Assets.h"
#include "zkc/Dialect/detail/Builders.h"
#include "zkc/Program/Admission.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/DenseMap.h"

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
namespace {
class ExecutionModelReader {
  Operation *root;
  zkc::protocol_ir::ProfileAttr profile;
  bool localDefinitionsOnly = false;
  bool physical;
  std::string problem;
  unsigned next = 0;
  using Env = llvm::DenseMap<mlir::Value, std::string>;
  void fail(StringRef why) {
    if (problem.empty())
      problem = why.str();
  }
  bool attributes(Operation *op, ArrayRef<StringRef> allowed) {
    for (auto a : op->getAttrs())
      if (!is_contained(allowed, a.getName().getValue())) {
        fail("interactive-unknown-attribute");
        return false;
      }
    return true;
  }
  program::Names strings(ArrayAttr attrs,
                         StringRef code = "interactive-attribute") {
    if (!attrs) {
      fail(code);
      return {};
    }
    program::Names out;
    for (auto a : attrs) {
      auto s = dyn_cast<StringAttr>(a);
      if (!s) {
        fail(code);
        return {};
      }
      out.push_back(s.getValue().str());
    }
    return out;
  }
  protocol::Assignments pairs(ArrayAttr attrs, bool symbols = false) {
    if (!attrs) {
      fail("interactive-attribute");
      return {};
    }
    protocol::Assignments out;
    for (auto a : attrs) {
      auto p = dyn_cast<ArrayAttr>(a);
      if (!p || p.size() != 2 || !isa<StringAttr>(p[0]) ||
          (symbols ? !isa<FlatSymbolRefAttr>(p[1]) : !isa<StringAttr>(p[1]))) {
        fail("interactive-binding-attribute");
        return {};
      }
      out.emplace_back(cast<StringAttr>(p[0]).getValue().str(),
                       (symbols ? cast<FlatSymbolRefAttr>(p[1]).getValue()
                                : cast<StringAttr>(p[1]).getValue())
                           .str());
    }
    return out;
  }
  std::string fresh() { return "v" + std::to_string(next++); }
  std::string type(Type t) {
    auto value = encodeBoundType(t, physical);
    if (!value) {
      consumeError(value.takeError());
      fail("binding-type");
      return "invalid";
    }
    return value->spelling();
  }
  program::Names names(ValueRange values, const Env &env) {
    program::Names out;
    for (auto v : values) {
      auto p = env.find(v);
      if (p == env.end()) {
        fail("interactive-ssa");
        return {};
      }
      out.push_back(p->second);
    }
    return out;
  }
  std::string name(mlir::Value v, const Env &env) {
    auto p = env.find(v);
    if (p == env.end()) {
      fail("interactive-ssa");
      return "invalid";
    }
    return p->second;
  }
  program::Names results(Operation *op, Env &env) {
    program::Names out;
    for (auto v : op->getResults()) {
      std::string n = fresh();
      env[v] = n;
      out.push_back(n);
    }
    return out;
  }
  FunctionType signature(Operation *op) {
    auto a = op ? op->getAttrOfType<TypeAttr>("function_type") : TypeAttr();
    auto t = a ? dyn_cast<FunctionType>(a.getValue()) : FunctionType();
    if (!t)
      fail("interactive-callable-type");
    return t;
  }
  bool callTypes(Operation *op, StringRef callee) {
    Operation *definition = SymbolTable::lookupSymbolIn(root, callee);
    bool kind = isa_and_nonnull<zkc::local::FuncOp>(definition) ||
                (localDefinitionsOnly && isa<zkc::local::ApplyOp>(op) &&
                 profile.getValue() == zkc::protocol_ir::Profile::Protocol &&
                 isa_and_nonnull<zkc::local::RealizeOp>(definition));
    if (!kind) {
      fail("interactive-symbol-kind");
      return false;
    }
    FunctionType ft = signature(definition);
    return (ft && op->getOperandTypes() == ft.getInputs() &&
            op->getResultTypes() == ft.getResults()) ||
           (fail("interactive-call-type"), false);
  }
  program::Body body(Block &block, Env env, TypeRange outputs,
                     Operation *definition, bool local,
                     bool localRegion = false) {
    program::Body out;
    if (block.empty()) {
      fail("interactive-empty-body");
      return {};
    }
    for (auto &operation : block) {
      Operation *op = &operation;
      std::string site = attr(op, "site").str();
      if (isa<zkc::local::LocalYieldOp, zkc::local::LocalConditionOp>(op)) {
        auto *parent = op->getParentOp();
        unsigned offset = isa<zkc::local::LocalConditionOp>(op) ? 1 : 0;
        unsigned forwarded =
            isa<zkc::local::LocalForOp>(parent)
                ? block.getNumArguments() - 1 - (outputs.size() - offset)
                : 0;
        if (!localRegion || !attributes(op, {}) || op != &block.back() ||
            op->getNumOperands() != outputs.size() + forwarded ||
            op->getOperands().take_front(outputs.size()).getTypes() !=
                outputs) {
          fail("local-control-yield");
          return {};
        }
        for (unsigned i = 0; i < forwarded; ++i)
          if (op->getOperand(outputs.size() + i) !=
              block.getArgument(block.getNumArguments() - forwarded + i)) {
            fail("local-control-capture-forwarding");
            return {};
          }
        out.push_back(
            {"", program::Yield{names(
                     op->getOperands().take_front(outputs.size()), env)}});
      } else if (isa<zkc::local::ReturnOp,
                     zkc::protocol_ir::MathematicalReturnOp,
                     zkc::protocol_ir::FinishOp,
                     zkc::protocol_ir::ProtocolYieldOp>(op)) {
        if (localRegion || !attributes(op, {}) || op != &block.back() ||
            op->getOperandTypes() != outputs ||
            (local != isa<zkc::local::ReturnOp>(op))) {
          fail("interactive-return-type");
          return {};
        }
        program::Instruction instruction;
        if (isa<zkc::protocol_ir::ProtocolYieldOp>(op))
          instruction.value = program::Yield{names(op->getOperands(), env)};
        else
          instruction.value = program::Return{names(op->getOperands(), env)};
        out.push_back(std::move(instruction));
      } else if (auto completion = dyn_cast<zkc::protocol_ir::FinishIfOp>(op)) {
        if (local || !attributes(op, {"site", "owner"}) ||
            failed(completion.verify())) {
          fail("interactive-return-type");
          return {};
        }
        auto inputs = names(completion.getOperands(), env);
        if (inputs.empty())
          return {};
        program::Names values(inputs.begin() + 1, inputs.end());
        auto continuations = results(op, env);
        out.push_back(
            {site, program::ReturnIf{inputs.front(), std::move(values),
                                     std::move(continuations)}});
      } else if (isa<zkc::plan::ReleaseOp>(op)) {
        if (!physical || !local || !attributes(op, {})) {
          fail("interactive-release-context");
          return {};
        }
        out.push_back({"", program::Release{names(op->getOperands(), env)}});
      } else if (isa<zkc::local::StopOp>(op)) {
        if (!local || !attributes(op, {"site", "reason"}) ||
            op != &block.back()) {
          fail("interactive-halt");
          return {};
        }
        out.push_back({site, program::Stop{attr(op, "reason").str()}});
      } else if (auto call = dyn_cast<zkc::local::ApplyOp>(op)) {
        if (!localDefinitionsOnly || !local ||
            !attributes(op, {"site", "callee"}) ||
            !callTypes(op, call.getCallee())) {
          fail("algorithm-call-context");
          return {};
        }
        out.push_back({site, program::LocalApply{call.getCallee().str(),
                                                 names(op->getOperands(), env),
                                                 results(op, env)}});
      } else if (auto call = dyn_cast<zkc::local::CallOp>(op)) {
        if (local || !attributes(op, {"site", "callee"}) ||
            !callTypes(op, call.getCallee())) {
          fail("interactive-local-symbol");
          return {};
        }
        out.push_back({site, program::LocalCall{call.getCallee().str(),
                                                names(op->getOperands(), env),
                                                results(op, env)}});
      } else if (auto query =
                     dyn_cast<zkc::protocol_ir::ParticipantQueryOp>(op)) {
        StringRef field;
        auto participant =
            query->getParentOfType<zkc::protocol_ir::ParticipantOp>();
        if (participant)
          if (auto ports =
                  participant->getAttrOfType<ArrayAttr>("service_ports"))
            for (auto item : ports) {
              auto port = dyn_cast<ArrayAttr>(item);
              if (port && port.size() == 3 && port[0] == query.getPortAttr())
                if (auto contract = dyn_cast<StringAttr>(port[1]))
                  field = protocol::randomServiceField(contract.getValue());
            }
        auto logical = protocol::parseBoundType("field:" + field.str(), false);
        std::string expected;
        if (logical) {
          if (physical) {
            auto selected = protocol::defaultRepresentation(*logical);
            if (selected)
              expected = selected->spelling();
            else
              llvm::consumeError(selected.takeError());
          } else
            expected = logical->spelling();
        } else
          llvm::consumeError(logical.takeError());
        if (local || expected.empty() ||
            !attributes(op, {"site", "port", "method"}) ||
            op->getNumResults() != 1 ||
            type(op->getResult(0).getType()) != expected) {
          fail("service-query-context");
          return {};
        }
        out.push_back(
            {site, program::ServiceQuery{
                       query.getPort().str(), query.getMethod().str(),
                       names(query.getInputs(), env), results(op, env)}});
      } else if (isa<zkc::protocol_ir::EmitOp, zkc::protocol_ir::AwaitOp>(op)) {
        if (!attributes(op, {"site", "schema", "peer"})) {
          fail("interactive-stage");
          return {};
        }
        if (isa<zkc::protocol_ir::EmitOp>(op))
          out.push_back({site, program::Send{attr(op, "schema").str(),
                                             attr(op, "peer").str(),
                                             name(op->getOperand(0), env)}});
        else {
          std::string n = fresh();
          env[op->getResult(0)] = n;
          out.push_back(
              {site, program::Receive{attr(op, "schema").str(),
                                      attr(op, "peer").str(), n,
                                      type(op->getResult(0).getType())}});
        }
      } else if (isa<zkc::local::BoolConstantOp, zkc::plan::BoolConstantOp>(
                     op)) {
        if (!local || physical != isa<zkc::plan::BoolConstantOp>(op) ||
            !attributes(op, {"site", "value"})) {
          fail("native-boolean-context");
          return {};
        }
        auto value = op->getAttrOfType<BoolAttr>("value");
        if (!value || type(op->getResult(0).getType()) !=
                          (physical ? "bool@native.bool/1" : "bool")) {
          fail("native-boolean-type");
          return {};
        }
        auto output = results(op, env);
        out.push_back(
            {site, program::BooleanConstant{output[0], value.getValue()}});
      } else if (auto pack = dyn_cast<zkc::local::VariantInjectOp>(op)) {
        if (!local || !attributes(op, {"site", "alternative"}) ||
            failed(pack.verify())) {
          fail("variant-payload");
          return {};
        }
        auto payload = names(op->getOperands(), env);
        auto outputs = results(op, env);
        out.push_back(
            {site, program::VariantConstruct{type(pack.getOutput().getType()),
                                             pack.getAlternative().str(),
                                             std::move(payload), outputs[0]}});
      } else if (auto match = dyn_cast<zkc::local::LocalMatchOp>(op)) {
        if (!local || !attributes(op, {"site", "alternatives"}) ||
            failed(match.verifyRegions())) {
          fail("local-match-shape");
          return {};
        }
        program::Match result;
        result.input = name(op->getOperand(0), env);
        result.captures = names(op->getOperands().drop_front(), env);
        for (auto [i, region] : enumerate(match.getArms())) {
          auto &inner = region.front();
          Env nested;
          program::MatchArm arm;
          arm.alternative = cast<StringAttr>(match.getAlternatives()[i]).str();
          unsigned payload = inner.getNumArguments() - result.captures.size();
          for (auto arg : inner.getArguments().take_front(payload)) {
            auto n = fresh();
            nested[arg] = n;
            arm.payload.push_back(n);
          }
          for (auto [arg, capture] :
               zip(inner.getArguments().drop_front(payload), result.captures))
            nested[arg] = capture;
          arm.body = body(inner, std::move(nested), op->getResultTypes(),
                          definition, true, true);
          result.arms.push_back(std::move(arm));
        }
        result.outputs = results(op, env);
        out.push_back({site, std::move(result)});
      } else if (auto branch = dyn_cast<zkc::local::LocalIfOp>(op)) {
        if (!local || !attributes(op, {"site"}) ||
            failed(branch.verifyRegions())) {
          fail("local-control-shape");
          return {};
        }
        auto captures = names(op->getOperands().drop_front(), env);
        program::Body bodies[2];
        for (unsigned i = 0; i < 2; ++i) {
          auto &inner = op->getRegion(i).front();
          Env nested;
          for (auto [arg, capture] : zip(inner.getArguments(), captures))
            nested[arg] = capture;
          bodies[i] = body(inner, std::move(nested), op->getResultTypes(),
                           definition, true, true);
        }
        out.push_back({site, program::Conditional{
                                 name(op->getOperand(0), env),
                                 std::move(captures), std::move(bodies[0]),
                                 std::move(bodies[1]), results(op, env)}});
      } else if (auto loop = dyn_cast<zkc::local::LocalForOp>(op)) {
        if (!local || !attributes(op, {"site"}) ||
            failed(loop.verifyRegions())) {
          fail("local-control-shape");
          return {};
        }
        auto &inner = loop.getBody().front();
        Env nested;
        std::string induction = fresh();
        nested[inner.getArgument(0)] = induction;
        protocol::Assignments carried;
        program::Names captures;
        for (unsigned i = 2; i < op->getNumOperands(); ++i) {
          auto input = name(op->getOperand(i), env);
          if (i - 2 < op->getNumResults()) {
            auto n = fresh();
            nested[inner.getArgument(i - 1)] = n;
            carried.emplace_back(n, input);
          } else {
            nested[inner.getArgument(i - 1)] = input;
            captures.push_back(input);
          }
        }
        bool conditional = isa<zkc::local::LocalConditionOp>(inner.back());
        SmallVector<Type> yielded(op->getResultTypes());
        if (conditional)
          yielded.insert(yielded.begin(), inner.back().getOperand(0).getType());
        auto content =
            body(inner, std::move(nested), yielded, definition, true, true);
        out.push_back(
            {site,
             program::For{induction, name(op->getOperand(0), env),
                          name(op->getOperand(1), env), std::move(carried),
                          std::move(captures), std::move(content),
                          results(op, env), conditional}});
      } else if (auto loop = dyn_cast<zkc::protocol_ir::ProtocolLoopOp>(op)) {
        if (!attributes(op,
                        {"site", "carried", "count", "parameter", "maximum"}) ||
            !llvm::hasSingleElement(loop.getBody())) {
          fail("interactive-loop-body");
          return {};
        }
        auto count = loop.getCarried();
        constexpr unsigned offset = 1;
        if (!loop.getMaximum() || op->getNumOperands() == 0) {
          fail("interactive-loop-count");
          return {};
        }
        Block &inner = loop.getBody().front();
        if (loop.getCarriedAttr().getInt() < 0 ||
            static_cast<size_t>(count) != op->getNumResults() ||
            op->getNumOperands() < static_cast<size_t>(count) + offset ||
            inner.getArgumentTypes() != op->getOperandTypes() ||
            op->getResultTypes() !=
                op->getOperands().slice(offset, count).getTypes()) {
          fail("interactive-loop-type");
          return {};
        }
        Env innerEnv;
        protocol::Assignments initial;
        program::Names captures;
        std::string induction;
        if (offset) {
          induction = fresh();
          innerEnv[inner.getArgument(0)] = induction;
        }
        for (size_t i = offset; i < op->getNumOperands(); ++i) {
          std::string input = name(op->getOperand(i), env);
          if (i < static_cast<size_t>(count) + offset) {
            std::string n = fresh();
            innerEnv[inner.getArgument(i)] = n;
            initial.emplace_back(n, input);
          } else {
            innerEnv[inner.getArgument(i)] = input;
            captures.push_back(input);
          }
        }
        program::LoopCount n{name(op->getOperand(0), env), *loop.getMaximum(),
                             induction};
        auto content = body(inner, std::move(innerEnv), op->getResultTypes(),
                            definition, false);
        out.push_back(
            {site, program::Loop{std::move(n), std::move(initial),
                                 std::move(captures), std::move(content),
                                 results(op, env)}});
      } else {
        if (!local ||
            !attributes(op, physical
                                ? ArrayRef<StringRef>{"site", "binding",
                                                      "kernel", "parameters"}
                                : ArrayRef<StringRef>{"site", "binding",
                                                      "parameters"}) ||
            failed(verifyBoundOperation(op, physical))) {
          fail("binding-operation");
          return {};
        }
        auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
        out.push_back(
            {site, program::Operation{
                       reference.getValue().str(),
                       strings(op->getAttrOfType<ArrayAttr>("parameters")),
                       names(op->getOperands(), env), results(op, env)}});
      }
      if (!problem.empty())
        return {};
    }
    return out;
  }
  using Definition = std::variant<program::Function, program::Participant>;
  Definition definition(Operation *op, bool local) {
    if (!attributes(
            op, local
                    ? ArrayRef<StringRef>{"sym_name", "function_type",
                                          "sym_visibility", "logical_origin"}
                    : ArrayRef<StringRef>{"sym_name", "function_type",
                                          "instance", "role", "service_ports"}))
      return {};
    FunctionType ft = signature(op);
    if (!ft || op->getNumRegions() != 1) {
      fail("interactive-definition");
      return {};
    }
    if (local && op->hasAttr("sym_visibility")) {
      fail("interactive-local-visibility");
      return {};
    }
    if (!llvm::hasSingleElement(op->getRegion(0))) {
      fail("interactive-definition-body");
      return {};
    }
    Env env;
    program::Function function;
    program::Participant projected;
    if (op->getRegion(0).front().getArgumentTypes() != ft.getInputs()) {
      fail("interactive-block-arguments");
      return {};
    }
    for (size_t i = 0; i < ft.getNumInputs(); ++i) {
      std::string n = fresh();
      env[op->getRegion(0).front().getArgument(i)] = n;
      (local ? function.arguments : projected.arguments)
          .push_back({n, type(ft.getInput(i))});
    }
    for (auto t : ft.getResults())
      (local ? function.results : projected.results).push_back(type(t));
    auto content = body(op->getRegion(0).front(), std::move(env),
                        ft.getResults(), op, local);
    if (local) {
      function.name = attr(op, "sym_name").str();
      function.body = std::move(content);
      {
        auto origin = op->getAttrOfType<ArrayAttr>("logical_origin");
        if (!origin || origin.size() != 2 || !isa<StringAttr>(origin[0]) ||
            !isa<ArrayAttr>(origin[1])) {
          fail("binding-logical-origin");
          return {};
        }
        function.origin =
            program::LogicalOrigin{cast<StringAttr>(origin[0]).getValue().str(),
                                   pairs(cast<ArrayAttr>(origin[1]))};
      }
      return function;
    }
    {
      if (auto ports = op->getAttrOfType<ArrayAttr>("service_ports")) {
        for (auto attribute : ports) {
          auto row = dyn_cast<ArrayAttr>(attribute);
          if (!row || row.size() != 3 || !isa<StringAttr>(row[0]) ||
              !isa<StringAttr>(row[1]) || !isa<IntegerAttr>(row[2]) ||
              !cast<IntegerAttr>(row[2]).getType().isSignlessInteger(64) ||
              cast<IntegerAttr>(row[2]).getInt() < 0) {
            fail("service-port-interface");
            return {};
          }
          projected.services.push_back(
              {cast<StringAttr>(row[0]).str(), cast<StringAttr>(row[1]).str(),
               uint64_t(cast<IntegerAttr>(row[2]).getInt())});
        }
      } else if (op->hasAttr("service_ports")) {
        fail("service-port-interface");
        return {};
      }
      projected.name = attr(op, "sym_name").str();
      projected.instance = attr(op, "instance").str();
      projected.role = attr(op, "role").str();
      projected.body = std::move(content);
      return projected;
    }
  }

public:
  explicit ExecutionModelReader(Operation *root)
      : root(root),
        profile(root->getAttrOfType<zkc::protocol_ir::ProfileAttr>("profile")),
        physical(profile &&
                 profile.getValue() == zkc::protocol_ir::Profile::Physical) {}
  Expected<program::LocalDefinitions> localDefinitions() {
    // Reconstruct local callables and realization signatures directly from
    // mathematical IR for the shared local-control admission checks.
    localDefinitionsOnly = true;
    physical = false;
    program::LocalDefinitions module;
    SmallVector<LocalRealization> realizations;
    for (auto &op : root->getRegion(0).front()) {
      if (isa<zkc::local::OperationBindingOp>(op)) {
        if (!attributes(
                &op, {"sym_name", "contract", "arguments", "implementation"}))
          return error(problem);
        auto binding = readBinding(&op);
        if (!binding)
          return binding.takeError();
        module.bindings.push_back(std::move(*binding));
      } else if (auto realization = dyn_cast<zkc::local::RealizeOp>(op)) {
        if (profile.getValue() != zkc::protocol_ir::Profile::Protocol ||
            !attributes(&op, {"sym_name", "helper", "function_type"}))
          return error("local-realization-context");
        LocalRealization value;
        value.name = realization.getSymName().str();
        for (bool input : {true, false})
          for (auto type : input ? realization.getFunctionType().getInputs()
                                 : realization.getFunctionType().getResults()) {
            auto bound = encodeBoundType(type, false);
            if (!bound) {
              consumeError(bound.takeError());
              return error("local-realization-signature");
            }
            (input ? value.inputs : value.outputs).push_back(bound->spelling());
          }
        realizations.push_back(std::move(value));
      } else if (isa<zkc::local::FuncOp>(op)) {
        auto value = definition(&op, true);
        if (!problem.empty())
          return error(problem);
        module.functions.push_back(
            std::get<program::Function>(std::move(value)));
      }
    }
    if (auto e = admitNativeLocalDefinitions(module, realizations))
      return std::move(e);
    return module;
  }
  Expected<program::Participants> run() {
    if (!isa<zkc::protocol_ir::ProtocolModuleOp>(root) ||
        !attributes(root, {"profile"}) || !profile ||
        !zkc::protocol_ir::isExecutableProfile(profile.getValue()) ||
        !llvm::hasSingleElement(root->getRegion(0)))
      return error("interactive-module");
    program::Participants participants;
    participants.stage = physical ? program::Participants::Stage::Physical
                                  : program::Participants::Stage::Logical;
    for (auto &op : root->getRegion(0).front()) {
      if (isa<zkc::protocol_ir::ProjectionOp, zkc::relation::DeclareOp>(op))
        continue;
      if (isa<zkc::local::OperationBindingOp>(op)) {
        if (!attributes(
                &op, {"sym_name", "contract", "arguments", "implementation"}))
          return error("binding-attribute");
        auto binding = readBinding(&op);
        if (!binding)
          return binding.takeError();
        participants.bindings.push_back(std::move(*binding));
      } else if (isa<zkc::local::FuncOp>(op)) {
        auto value = definition(&op, true);
        if (!problem.empty())
          return error(problem);
        participants.functions.push_back(
            std::get<program::Function>(std::move(value)));
      } else if (isa<zkc::protocol_ir::ParticipantOp>(op)) {
        auto value = definition(&op, false);
        if (!problem.empty())
          return error(problem);
        participants.participants.push_back(
            std::get<program::Participant>(std::move(value)));
      } else if (auto entry = dyn_cast<zkc::protocol_ir::ProtocolEntryOp>(op)) {
        if (!attributes(&op, {"sym_name", "targets"}))
          return error("interactive-entry-attribute");
        program::ParticipantEntry value;
        value.name = entry.getSymName().str();
        value.participants = pairs(entry.getTargets(), true);
        participants.entries.push_back(std::move(value));
      } else
        return error("interactive-top-operation");
    }
    if (!problem.empty())
      return error(problem);
    if (auto e = admit(participants))
      return e;
    return participants;
  }
};
} // namespace
Expected<program::Participants> readExecutionModel(Operation *root) {
  // Check each operation's local invariants before accessing typed operands,
  // results, regions or properties. Full recursive verification would call this
  // reader again through zkc::protocol_ir::ProtocolModuleOp::verifyRegions.
  if (!root || root->walk<WalkOrder::PreOrder>([](Operation *op) {
                     return failed(op->getName().verifyInvariants(op))
                                ? WalkResult::interrupt()
                                : WalkResult::advance();
                   })
                   .wasInterrupted())
    return error("interactive-malformed-ir");
  if (auto module = dyn_cast<ModuleOp>(root)) {
    if (!llvm::hasSingleElement(*module.getBody()))
      return error("interactive-module-count");
    root = &module.getBody()->front();
  }
  return ExecutionModelReader(root).run();
}
LogicalResult verifyLocalDefinitions(Operation *root) {
  auto value = ExecutionModelReader(root).localDefinitions();
  if (!value)
    return diagnostics::emit(root->emitOpError(), value.takeError());
  return success();
}
LogicalResult verifyModule(Operation *root) {
  // Region verification already checked all nested operation invariants.
  auto v = ExecutionModelReader(root).run();
  if (!v)
    return diagnostics::emit(root->emitOpError(), v.takeError());
  return success();
}
} // namespace zkc::protocol
