#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"
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
            Environment environment, unsigned depth = 0,
            std::optional<unsigned> yieldWidth = {}) {
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
      if (auto r = record.get<program::Operation>()) {
        auto kernel = dyn_cast<plan::ExecuteKernelOp>(op);
        if (!kernel || symbol(&op, "binding") != r->callee ||
            !strings(op.getAttrOfType<ArrayAttr>("parameters"),
                     r->attributes) ||
            !inputs(r->inputs) || !outputs(r->outputs))
          return false;
        auto declaration =
            SymbolTable::lookupNearestSymbolFrom<local::OperationBindingOp>(
                &op, kernel.getBindingAttr());
        if (!declaration ||
            kernel.getKernel() != declaration.getImplementation())
          return false;
      } else if (auto r = record.get<program::LocalCall>()) {
        if (!isa<local::CallOp>(op) || symbol(&op, "callee") != r->callee ||
            !inputs(r->inputs) || !outputs(r->outputs))
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
      } else if (auto r = record.get<program::BooleanConstant>()) {
        auto literal = dyn_cast<plan::BoolConstantOp>(op);
        if (!literal || literal.getValue() != r->value || !outputs({r->output}))
          return false;
      } else if (auto r = record.get<program::Return>()) {
        if (!isa<local::ReturnOp, protocol_ir::FinishOp>(op) ||
            !inputs(r->values))
          return false;
      } else if (auto r = record.get<program::Yield>()) {
        if (!isa<local::LocalYieldOp, local::LocalConditionOp,
                 protocol_ir::ProtocolYieldOp>(op))
          return false;
        // Local for captures are immutable explicit forwarding operands in
        // MLIR, implicit in the artifact. Formation checks exact forwarding.
        unsigned width = yieldWidth.value_or(op.getNumOperands());
        if (width > op.getNumOperands() ||
            !environment.inputs(op.getOperands().take_front(width), r->values))
          return false;
      } else if (auto r = record.get<program::Release>()) {
        if (!isa<plan::ReleaseOp>(op) || !inputs(r->values))
          return false;
      } else if (auto r = record.get<program::Stop>()) {
        if (!isa<local::StopOp>(op) || text(&op, "reason") != r->reason)
          return false;
      } else if (auto r = record.get<program::ReturnIf>()) {
        if (!isa<protocol_ir::FinishIfOp>(op) ||
            !environment.inputs(op.getOperands().take_front(),
                                {r->condition}) ||
            !environment.inputs(op.getOperands().drop_front(), r->values) ||
            !outputs(r->continuations))
          return false;
      } else if (auto r = record.get<program::VariantConstruct>()) {
        if (!isa<local::VariantInjectOp>(op) ||
            text(&op, "alternative") != r->alternative ||
            !type(op.getResult(0).getType(), r->type) || !inputs(r->payload) ||
            !outputs({r->output}))
          return false;
      } else if (auto r = record.get<program::Conditional>()) {
        if (!isa<local::LocalIfOp>(op) ||
            !environment.inputs(op.getOperands().take_front(),
                                {r->condition}) ||
            !environment.inputs(op.getOperands().drop_front(), r->captures))
          return false;
        const program::Body *arms[] = {&r->thenBody, &r->elseBody};
        for (unsigned i = 0; i < 2; ++i) {
          Environment inner;
          auto &region = op.getRegion(i).front();
          if (!captures(region.getArguments(), r->captures, inner) ||
              !body(region, *arms[i], std::move(inner), depth + 1))
            return false;
        }
        if (!outputs(r->outputs))
          return false;
      } else if (auto r = record.get<program::Match>()) {
        auto match = dyn_cast<local::LocalMatchOp>(op);
        if (!match || r->arms.size() != op.getNumRegions() ||
            !environment.inputs(op.getOperands().take_front(), {r->input}) ||
            !environment.inputs(op.getOperands().drop_front(), r->captures))
          return false;
        for (auto [i, arm] : enumerate(r->arms)) {
          if (cast<StringAttr>(match.getAlternatives()[i]).getValue() !=
              arm.alternative)
            return false;
          auto &region = op.getRegion(i).front();
          if (region.getNumArguments() !=
              arm.payload.size() + r->captures.size())
            return false;
          Environment inner;
          if (!inner.outputs(
                  region.getArguments().take_front(arm.payload.size()),
                  arm.payload) ||
              !captures(region.getArguments().drop_front(arm.payload.size()),
                        r->captures, inner) ||
              !body(region, arm.body, std::move(inner), depth + 1))
            return false;
        }
        if (!outputs(r->outputs))
          return false;
      } else if (auto r = record.get<program::For>()) {
        if (!isa<local::LocalForOp>(op) ||
            r->carried.size() != op.getNumResults() ||
            !environment.inputs(op.getOperands().take_front(2),
                                {r->lower, r->upper}))
          return false;
        auto &region = op.getRegion(0).front();
        bool conditional = isa<local::LocalConditionOp>(region.back());
        if (r->conditional != conditional ||
            region.getNumArguments() !=
                1 + r->carried.size() + r->captures.size())
          return false;
        Environment inner;
        if (!inner.bind(region.getArgument(0), r->induction))
          return false;
        for (auto [i, carried] : enumerate(r->carried))
          if (!environment.inputs(op.getOperands().slice(2 + i, 1),
                                  {carried.second}) ||
              !inner.bind(region.getArgument(1 + i), carried.first))
            return false;
        unsigned start = 2 + r->carried.size();
        if (!environment.inputs(op.getOperands().drop_front(start),
                                r->captures) ||
            !captures(region.getArguments().drop_front(start - 1), r->captures,
                      inner) ||
            !body(region, r->body, std::move(inner), depth + 1,
                  op.getNumResults() + unsigned(conditional)) ||
            !outputs(r->outputs))
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
      if (auto b = dyn_cast<local::OperationBindingOp>(op)) {
        if (binding == program.bindings.size())
          return false;
        const auto &expected = program.bindings[binding++];
        if (b.getSymName() != expected.name ||
            b.getContract() != expected.application.contract ||
            b.getImplementation() != expected.application.implementation ||
            !strings(b.getArguments(), expected.application.arguments))
          return false;
      } else if (auto fn = dyn_cast<local::FuncOp>(op)) {
        if (function == program.functions.size())
          return false;
        const auto &expected = program.functions[function++];
        if (fn.getSymName() != expected.name || !fn.getBody().hasOneBlock() ||
            !expected.origin)
          return false;
        auto origin = fn->getAttrOfType<ArrayAttr>("logical_origin");
        if (!origin || origin.size() != 2 ||
            cast<StringAttr>(origin[0]).getValue() !=
                expected.origin->definition ||
            !pairs(cast<ArrayAttr>(origin[1]), expected.origin->arguments))
          return false;
        Environment environment;
        auto &block = fn.getBody().front();
        if (!signature(block, fn.getFunctionType(), expected.arguments,
                       expected.results, environment) ||
            !body(block, expected.body, std::move(environment)))
          return false;
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
  if (!subject || failed(verify(subject)))
    return error("artifact-correspondence-subject");
  if (auto wrapper = dyn_cast<ModuleOp>(subject)) {
    if (!hasSingleElement(*wrapper.getBody()))
      return error("artifact-correspondence-subject");
    subject = &wrapper.getBody()->front();
  }
  auto module = dyn_cast<protocol_ir::ProtocolModuleOp>(subject);
  if (!module)
    return error("artifact-correspondence-subject");
  auto json = parseJson(bytes);
  if (!json)
    return json.takeError();
  auto decoded = program::decode(*json);
  if (!decoded)
    return decoded.takeError();
  auto *program = &*decoded;
  if (auto e = admit(*program))
    return e;
  ArtifactCorrespondence checker;
  if (!checker.check(module, *program))
    return error(checker.exhausted() ? "artifact-correspondence-limit"
                                     : "artifact-correspondence",
                 checker.detail());
  return std::move(*decoded);
}
} // namespace zkc::protocol
