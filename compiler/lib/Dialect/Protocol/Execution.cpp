#include "zkc/Dialect/Protocol/Execution.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Exec/ExecutionModel.h"
#include "zkc/Dialect/Exec/IR/ExecTypes.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/detail/Builders.h"
#include "zkc/Program/Admission.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringSet.h"

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
namespace {
class ExecutionModelReader {
  Operation *root;
  zkc::protocol_ir::ProfileAttr profile;
  bool physical;
  std::string problem;
  unsigned next = 0;
  llvm::StringSet<> reserved;

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
  std::string fresh() {
    std::string name;
    do {
      name = "v" + std::to_string(next++);
    } while (reserved.contains(name));
    return name;
  }
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
    auto function = dyn_cast_or_null<func::FuncOp>(definition);
    auto type = function ? function.getFunctionType() : FunctionType();
    auto outcome = type && type.getNumResults() == 1
                       ? dyn_cast<exec::OutcomeType>(type.getResult(0))
                       : exec::OutcomeType();
    return (function && isScopedExecutionFunction(function) && outcome &&
            op->getOperandTypes() == type.getInputs().drop_front() &&
            op->getResultTypes() == outcome.getPayload()) ||
           (fail("interactive-call-type"), false);
  }
  program::Body body(Block &block, Env env, TypeRange outputs) {
    program::Body out;
    if (block.empty()) {
      fail("interactive-empty-body");
      return {};
    }
    for (auto &operation : block) {
      Operation *op = &operation;
      std::string site = attr(op, "site").str();
      if (isa<zkc::protocol_ir::MathematicalReturnOp,
              zkc::protocol_ir::FinishOp, zkc::protocol_ir::ProtocolYieldOp>(
              op)) {
        if (!attributes(op, {}) || op != &block.back() ||
            op->getOperandTypes() != outputs) {
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
        if (!attributes(op, {"site", "owner"}) || failed(completion.verify())) {
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
      } else if (auto call = dyn_cast<protocol_ir::LocalCallOp>(op)) {
        auto participant = op->getParentOfType<protocol_ir::ParticipantOp>();
        if (!participant || call.getRoleAttr() != participant.getRoleAttr() ||
            !attributes(op, {"site", "callee", "role"}) ||
            !callTypes(op, call.getCallee())) {
          fail("interactive-local-symbol");
          return {};
        }
        out.push_back({site, program::LocalCall{call.getCallee().str(),
                                                names(op->getOperands(), env),
                                                results(op, env)}});
      } else if (auto query =
                     dyn_cast<zkc::protocol_ir::ParticipantQueryOp>(op)) {
        std::optional<protocol::ServiceMethod> method;
        auto participant =
            query->getParentOfType<zkc::protocol_ir::ParticipantOp>();
        if (participant)
          if (auto ports =
                  participant->getAttrOfType<ArrayAttr>("service_ports"))
            for (auto item : ports) {
              auto port = dyn_cast<ArrayAttr>(item);
              if (port && port.size() == 3 && port[0] == query.getPortAttr())
                if (auto contract = dyn_cast<StringAttr>(port[1]))
                  method = protocol::serviceMethod(contract.getValue(),
                                                   query.getMethod());
            }
        auto expected = [&](const BoundType &logical) -> std::string {
          if (!physical)
            return logical.spelling();
          auto selected = protocol::defaultRepresentation(logical);
          if (!selected) {
            llvm::consumeError(selected.takeError());
            return {};
          }
          return selected->spelling();
        };
        if (!method || !attributes(op, {"site", "port", "method"}) ||
            op->getNumResults() != 1 ||
            query.getInputs().size() != method->inputs.size() ||
            expected(method->output).empty() ||
            type(op->getResult(0).getType()) != expected(method->output) ||
            any_of(zip(query.getInputs(), method->inputs), [&](auto pair) {
              auto spelling = expected(std::get<1>(pair));
              return spelling.empty() ||
                     type(std::get<0>(pair).getType()) != spelling;
            })) {
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
        protocol::Assignments captures;
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
            // Each formal has its own storage binding even when several
            // Copy captures reference the same parent value.
            std::string local = fresh();
            innerEnv[inner.getArgument(i)] = local;
            captures.emplace_back(std::move(local), std::move(input));
          }
        }
        program::LoopCount n{name(op->getOperand(0), env), *loop.getMaximum(),
                             induction};
        auto content = body(inner, std::move(innerEnv), op->getResultTypes());
        out.push_back(
            {site, program::Loop{std::move(n), std::move(initial),
                                 std::move(captures), std::move(content),
                                 results(op, env)}});
      } else {
        fail("binding-operation");
        return {};
      }
      if (!problem.empty())
        return {};
    }
    return out;
  }
  program::Participant participant(Operation *op) {
    if (!attributes(op, {"sym_name", "function_type", "instance", "role",
                         "service_ports"}))
      return {};
    FunctionType ft = signature(op);
    if (!ft || op->getNumRegions() != 1) {
      fail("interactive-definition");
      return {};
    }
    if (!llvm::hasSingleElement(op->getRegion(0))) {
      fail("interactive-definition-body");
      return {};
    }
    Env env;
    // Artifact-local value names have no authority over service identities.
    // Reserve the latter before choosing names for actual SSA data arguments.
    if (auto ports = op->getAttrOfType<ArrayAttr>("service_ports")) {
      if (ports.size() > 1024) {
        fail("interactive-port-limit");
        return {};
      }
      for (auto item : ports)
        if (auto row = dyn_cast<ArrayAttr>(item); row && !row.empty())
          if (auto name = dyn_cast<StringAttr>(row[0]))
            reserved.insert(name.getValue());
    }
    program::Participant projected;
    if (op->getRegion(0).front().getArgumentTypes() != ft.getInputs()) {
      fail("interactive-block-arguments");
      return {};
    }
    for (size_t i = 0; i < ft.getNumInputs(); ++i) {
      std::string n = fresh();
      env[op->getRegion(0).front().getArgument(i)] = n;
      projected.arguments.push_back({n, type(ft.getInput(i))});
    }
    for (auto t : ft.getResults())
      projected.results.push_back(type(t));
    auto content =
        body(op->getRegion(0).front(), std::move(env), ft.getResults());
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
  Expected<program::Participants> run() {
    if (!isa<zkc::protocol_ir::ProtocolModuleOp>(root) ||
        !attributes(root, {"profile", "source_declarations"}) || !profile ||
        !zkc::protocol_ir::isExecutableProfile(profile.getValue()) ||
        !llvm::hasSingleElement(root->getRegion(0)))
      return error("interactive-module");
    if (root->hasAttr("source_declarations") &&
        !root->getAttrOfType<ArrayAttr>("source_declarations"))
      return error("component-declaration");
    program::Participants participants;
    participants.stage = physical ? program::Participants::Stage::Physical
                                  : program::Participants::Stage::Logical;
    auto definitions = readExecutionDefinitions(root, physical);
    if (!definitions)
      return definitions.takeError();
    participants.functions = std::move(definitions->functions);
    for (auto &op : root->getRegion(0).front()) {
      if (isa<func::FuncOp, data::DomainOp>(op)) {
        // Publication accepts only the fully realized executable profile.
        if (isa<data::DomainOp>(op))
          return error("execution-unresolved-domain");
        continue;
      }
      if (isa<mlir::ModuleOp>(op)) {
        // Computation units belong to pre-publication native admission.
        return error("computation-profile");
      }
      if (isa<zkc::protocol_ir::ProjectionOp, zkc::relation::DeclareOp>(op))
        continue;
      if (isa<zkc::runtime::BindingOp>(op)) {
        if (!attributes(&op,
                        {"sym_name", "contract", "arguments", "implementation",
                         "function_type", "arg_attrs", "res_attrs"}))
          return error("binding-attribute");
        auto binding = readBinding(&op);
        if (!binding)
          return binding.takeError();
        participants.bindings.push_back(std::move(*binding));
      } else if (isa<zkc::protocol_ir::ParticipantOp>(op)) {
        auto value = participant(&op);
        if (!problem.empty())
          return error(problem);
        participants.participants.push_back(std::move(value));
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
} // namespace zkc::protocol
