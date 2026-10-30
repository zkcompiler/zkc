#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/ExecutionModel.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Program/Admission.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringSet.h"
using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
namespace {
// Compare decoded fields with the actual physical SSA. In particular this does
// not export, import, or rerun ExecutionModelReader to obtain an expected
// model.
class ArtifactCorrespondence {
  struct Environment {
    llvm::DenseMap<Value, std::string> values;
    llvm::StringSet<> names;
    bool bind(Value value, StringRef name, bool capture = false) {
      if (name.empty() || (!names.insert(name).second && !capture))
        return false;
      values[value] = name.str();
      return true;
    }
    bool inputs(ValueRange operands, ArrayRef<std::string> names) const {
      if (operands.size() != names.size())
        return false;
      for (auto [operand, name] : zip(operands, names)) {
        auto found = values.find(operand);
        if (found == values.end() || found->second != name)
          return false;
      }
      return true;
    }
    bool outputs(ValueRange results, ArrayRef<std::string> names) {
      if (results.size() != names.size())
        return false;
      for (auto [result, name] : zip(results, names))
        if (!bind(result, name))
          return false;
      return true;
    }
  };
  unsigned remaining = 1000000;
  std::string checkpoint;
  bool charge() { return remaining && (--remaining, true); }
  static StringRef text(Operation *op, StringRef name) {
    if (auto value = op->getAttrOfType<StringAttr>(name))
      return value.getValue();
    return {};
  }
  static StringRef symbol(Operation *op, StringRef name) {
    if (auto value = op->getAttrOfType<FlatSymbolRefAttr>(name))
      return value.getValue();
    return {};
  }
  static bool strings(ArrayAttr actual, ArrayRef<std::string> expected) {
    if (!actual || actual.size() != expected.size())
      return false;
    for (auto [a, b] : zip(actual, expected))
      if (cast<StringAttr>(a).getValue() != b)
        return false;
    return true;
  }
  static bool pairs(ArrayAttr actual, const protocol::Assignments &expected,
                    bool reference = false) {
    if (!actual || actual.size() != expected.size())
      return false;
    for (auto [row, value] : zip(actual, expected)) {
      auto pair = dyn_cast<ArrayAttr>(row);
      if (!pair || pair.size() != 2 ||
          cast<StringAttr>(pair[0]).getValue() != value.first)
        return false;
      StringRef second = reference ? cast<FlatSymbolRefAttr>(pair[1]).getValue()
                                   : cast<StringAttr>(pair[1]).getValue();
      if (second != value.second)
        return false;
    }
    return true;
  }
  static bool type(Type actual, StringRef spelling) {
    auto encoded = encodeBoundType(actual, true);
    if (!encoded) {
      consumeError(encoded.takeError());
      return false;
    }
    return encoded->spelling() == spelling;
  }
  bool signature(Block &body, FunctionType signature,
                 const std::vector<program::Parameter> &arguments,
                 const program::Names &results, Environment &environment) {
    if (signature.getNumInputs() != arguments.size() ||
        signature.getNumResults() != results.size() ||
        body.getNumArguments() != arguments.size())
      return false;
    for (auto [argument, port] : zip(body.getArguments(), arguments))
      if (!charge() || !type(argument.getType(), port.type) ||
          !environment.bind(argument, port.name))
        return false;
    for (auto [actual, spelling] : zip(signature.getResults(), results))
      if (!charge() || !type(actual, spelling))
        return false;
    return true;
  }
  bool captures(ValueRange arguments, ArrayRef<std::string> names,
                Environment &environment) {
    if (arguments.size() != names.size())
      return false;
    for (auto [argument, name] : zip(arguments, names))
      if (!charge() || !environment.bind(argument, name, true))
        return false;
    return true;
  }
  bool body(Block &block, const program::Body &instructions,
            Environment environment, unsigned depth = 0) {
    if (depth > 64 || block.getOperations().size() != instructions.size())
      return false;
    for (auto pair : zip(block, instructions)) {
      Operation &op = std::get<0>(pair);
      const auto &record = std::get<1>(pair);
      checkpoint = op.getName().getStringRef().str() + " at " + record.site;
      if (!charge() || text(&op, "site") != record.site)
        return false;
      auto inputs = [&](ArrayRef<std::string> names) {
        return environment.inputs(op.getOperands(), names);
      };
      auto outputs = [&](ArrayRef<std::string> names) {
        return environment.outputs(op.getResults(), names);
      };
      if (auto r = record.get<program::LocalCall>()) {
        if (!isa<protocol_ir::LocalCallOp>(op) ||
            symbol(&op, "callee") != r->callee || !inputs(r->inputs) ||
            !outputs(r->outputs))
          return false;
      } else if (auto r = record.get<program::Send>()) {
        if (!isa<protocol_ir::EmitOp>(op) || text(&op, "schema") != r->schema ||
            text(&op, "peer") != r->peer || !inputs({r->input}))
          return false;
      } else if (auto r = record.get<program::Receive>()) {
        if (!isa<protocol_ir::AwaitOp>(op) ||
            text(&op, "schema") != r->schema || text(&op, "peer") != r->peer ||
            !type(op.getResult(0).getType(), r->type) || !outputs({r->output}))
          return false;
      } else if (auto r = record.get<program::ServiceQuery>()) {
        if (!isa<protocol_ir::ParticipantQueryOp>(op) ||
            text(&op, "port") != r->port || text(&op, "method") != r->method ||
            !inputs(r->inputs) || !outputs(r->outputs))
          return false;
      } else if (auto r = record.get<program::Return>()) {
        if (!isa<protocol_ir::FinishOp>(op) || !inputs(r->values))
          return false;
      } else if (auto r = record.get<program::Yield>()) {
        if (!isa<protocol_ir::ProtocolYieldOp>(op) || !inputs(r->values))
          return false;
      } else if (auto r = record.get<program::ReturnIf>()) {
        if (!isa<protocol_ir::FinishIfOp>(op) ||
            !environment.inputs(op.getOperands().take_front(),
                                {r->condition}) ||
            !environment.inputs(op.getOperands().drop_front(), r->values) ||
            !outputs(r->continuations))
          return false;
      } else if (auto r = record.get<program::Loop>()) {
        auto loop = dyn_cast<protocol_ir::ProtocolLoopOp>(op);
        if (!loop || r->carried.size() != op.getNumResults())
          return false;
        constexpr unsigned offset = 1;
        if (!loop.getMaximum() || r->count.maximum != *loop.getMaximum() ||
            !environment.inputs(op.getOperands().take_front(),
                                {r->count.value}))
          return false;
        auto &region = loop.getBody().front();
        if (region.getNumArguments() !=
            offset + r->carried.size() + r->captures.size())
          return false;
        Environment inner;
        if (offset && !inner.bind(region.getArgument(0), r->count.induction))
          return false;
        for (auto [i, carried] : enumerate(r->carried))
          if (!environment.inputs(op.getOperands().slice(offset + i, 1),
                                  {carried.second}) ||
              !inner.bind(region.getArgument(offset + i), carried.first))
            return false;
        unsigned start = offset + r->carried.size();
        if (!environment.inputs(op.getOperands().drop_front(start),
                                r->captures) ||
            !captures(region.getArguments().drop_front(start), r->captures,
                      inner) ||
            !body(region, r->body, std::move(inner), depth + 1) ||
            !outputs(r->outputs))
          return false;
      } else
        return false;
    }
    return true;
  }

public:
  bool check(protocol_ir::ProtocolModuleOp module,
             const program::Participants &program) {
    if (module.getProfile() != protocol_ir::Profile::Physical ||
        program.stage != program::Participants::Stage::Physical)
      return false;
    unsigned binding = 0, function = 0, participant = 0, entry = 0;
    for (auto &op : module.getBody().front()) {
      checkpoint = op.getName().getStringRef().str() + " @" +
                   text(&op, "sym_name").str();
      if (!charge())
        return false;
      if (auto b = dyn_cast<runtime::BindingOp>(op)) {
        if (binding == program.bindings.size())
          return false;
        const auto &expected = program.bindings[binding++];
        if (!bindingMatches(b, expected, true))
          return false;
      } else if (auto fn = dyn_cast<func::FuncOp>(op)) {
        // The independent scoped execution comparator below checks every
        // actual body, binding, origin, and closed-region reference. This
        // traversal owns participant transport and declaration ordering.
        if (!fn->hasAttr("runtime.region")) {
          if (function == program.functions.size() ||
              fn.getSymName() != program.functions[function++].name)
            return false;
        }
      } else if (auto p = dyn_cast<protocol_ir::ParticipantOp>(op)) {
        if (participant == program.participants.size())
          return false;
        const auto &expected = program.participants[participant++];
        if (p.getSymName() != expected.name ||
            p.getInstance() != expected.instance ||
            p.getRole() != expected.role)
          return false;
        auto ports = p->getAttrOfType<ArrayAttr>("service_ports");
        if ((ports ? ports.size() : 0) != expected.services.size())
          return false;
        if (ports)
          for (auto [item, service] : zip(ports, expected.services)) {
            auto row = cast<ArrayAttr>(item);
            if (cast<StringAttr>(row[0]).getValue() != service.name ||
                cast<StringAttr>(row[1]).getValue() != service.contract ||
                uint64_t(cast<IntegerAttr>(row[2]).getInt()) !=
                    service.inputIndex)
              return false;
          }
        Environment environment;
        auto &block = p.getBody().front();
        if (!signature(block, p.getFunctionType(), expected.arguments,
                       expected.results, environment) ||
            !body(block, expected.body, std::move(environment)))
          return false;
      } else if (auto e = dyn_cast<protocol_ir::ProtocolEntryOp>(op)) {
        if (entry == program.entries.size())
          return false;
        const auto &expected = program.entries[entry++];
        if (e.getSymName() != expected.name ||
            !pairs(e.getTargets(), expected.participants, true))
          return false;
      } else if (!isa<protocol_ir::ProjectionOp, relation::DeclareOp>(op))
        return false;
    }
    return binding == program.bindings.size() &&
           function == program.functions.size() &&
           participant == program.participants.size() &&
           entry == program.entries.size();
  }
  StringRef detail() const { return checkpoint; }
  bool exhausted() const { return !remaining; }
};
} // namespace
Expected<program::Participants> verifyProgramArtifact(Operation *subject,
                                                      StringRef bytes) {
  if (!subject || failed(zkc::admitStage(subject)))
    return error("artifact-correspondence-subject");
  if (auto wrapper = dyn_cast<ModuleOp>(subject)) {
    if (!hasSingleElement(*wrapper.getBody()))
      return error("artifact-correspondence-subject");
    subject = &wrapper.getBody()->front();
  }
  auto module = dyn_cast<protocol_ir::ProtocolModuleOp>(subject);
  if (!module)
    return error("artifact-correspondence-subject");
  auto decoded = program::parse(bytes);
  if (!decoded)
    return decoded.takeError();
  auto *program = &*decoded;
  if (auto e = admit(*program))
    return e;
  if (auto e = verifyExecutionDefinitions(
          module, {program->bindings, program->functions}, true))
    return e;
  ArtifactCorrespondence checker;
  if (!checker.check(module, *program))
    return error(checker.exhausted() ? "artifact-correspondence-limit"
                                     : "artifact-correspondence",
                 checker.detail());
  return std::move(*decoded);
}
} // namespace zkc::protocol
