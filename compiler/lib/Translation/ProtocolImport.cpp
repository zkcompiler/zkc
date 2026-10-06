#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/detail/Builders.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Source/Codec.h"
#include "zkc/Source/Relations.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Protocol.h"
#include "zkc/Translation/Relations.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/ErrorHandling.h"
#include <type_traits>

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
namespace {
// Admission establishes source semantics. Check the complete set of native
// carriers before constructing any IR, including payloads whose types only
// become block arguments when a variant is matched.
class ImportPreflight {
  MLIRContext &context;
  bool physical;
  const source::Node **failureLocation;
  llvm::StringSet<> checkedTypes;

  Error fail(Error e, const source::Node &node) {
    if (failureLocation)
      *failureLocation = &node;
    return e;
  }
  Error type(const BoundType &bound, const source::Node &node) {
    if (!checkedTypes.insert(bound.spelling()).second)
      return Error::success();
    if (!decodeBoundType(&context, bound))
      return fail(error("binding-type"), node);
    for (const auto &argument : bound.arguments)
      if (argument.kind == TypeArgument::Kind::Type)
        if (auto e = type(*argument.type, node))
          return e;
    if (bound.kind == "variant") {
      auto descriptor = decodeVariant("variant:" + bound.identity);
      if (!descriptor)
        return fail(error("binding-type"), node);
      for (const auto &arm : descriptor->alternatives)
        for (const auto &leaf : arm.payload) {
          auto parsed = parseBoundType(leaf, false);
          if (!parsed)
            return fail(parsed.takeError(), node);
          if (!bound.representation.empty())
            parsed = defaultRepresentation(*parsed);
          if (!parsed)
            return fail(parsed.takeError(), node);
          if (auto e = type(*parsed, node))
            return e;
        }
    }
    return Error::success();
  }
  Error type(StringRef spelling, const source::Node &node) {
    auto parsed = parseBoundType(spelling, physical);
    if (!parsed)
      return fail(parsed.takeError(), node);
    return type(*parsed, node);
  }
  Error body(const source::Body &instructions) {
    Error result = Error::success();
    source::walk(instructions, [&](const source::Instruction &instruction) {
      if (result)
        return;
      if (const auto *receive = instruction.get<source::Receive>())
        result = type(receive->type, instruction);
      else if (const auto *pack = instruction.get<source::VariantConstruct>())
        result = type(pack->type, instruction);
    });
    return result;
  }
  template <typename Definition> Error definition(const Definition &value) {
    for (const auto &argument : value.arguments)
      if (auto e = type(argument.type, value))
        return e;
    for (const auto &result : value.results) {
      if constexpr (std::is_same_v<Definition, source::Protocol>) {
        if (auto e = type(result.type, value))
          return e;
      } else if (auto e = type(result, value))
        return e;
    }
    if constexpr (std::is_same_v<Definition, source::Participant>)
      return body(value.body);
    else
      return value.body ? body(*value.body) : Error::success();
  }

public:
  ImportPreflight(MLIRContext &context, bool physical,
                  const source::Node **failureLocation)
      : context(context), physical(physical), failureLocation(failureLocation) {
  }

  template <typename Root> Error run(const Root &root) {
    for (const auto &binding : root.bindings) {
      auto name = physical ? zkc::plan::ExecuteKernelOp::getOperationName()
                           : boundOperationName(binding.application.contract);
      if (name.empty() || !context.isOperationRegistered(name))
        return fail(error("binding-operation"), binding);
      auto selected = resolveBinding(binding.application, physical);
      if (!selected)
        return fail(selected.takeError(), binding);
      for (const auto &input : selected->inputs)
        if (auto e = type(input, binding))
          return e;
      for (const auto &output : selected->outputs)
        if (auto e = type(output, binding))
          return e;
    }
    for (const auto &function : root.functions)
      if (auto e = definition(function))
        return e;
    if constexpr (std::is_same_v<Root, source::Module>) {
      for (const auto &protocol : root.protocols)
        if (auto e = definition(protocol))
          return e;
    } else {
      for (const auto &participant : root.participants)
        if (auto e = definition(participant))
          return e;
    }
    return Error::success();
  }
};

class Importer {
  OpBuilder b;
  bool target, physical;
  std::map<std::string, FunctionType> signatures;
  std::map<std::string, source::OperationBinding> bindings;
  llvm::function_ref<Location(const source::Node &)> locations;
  Location location;
  using Env = std::map<std::string, mlir::Value>;

  void locate(const source::Node &node) {
    location = locations ? locations(node) : b.getUnknownLoc();
  }
  Type type(StringRef spelling) {
    auto parsed = parseBoundType(spelling, physical);
    assert(parsed && "admitted bound type");
    return decodeBoundType(b.getContext(), *parsed);
  }
  ArrayAttr strings(const source::Names &values) {
    SmallVector<Attribute> out;
    for (const auto &value : values)
      out.push_back(text(b, value));
    return b.getArrayAttr(out);
  }
  ArrayAttr pairs(const source::Assignments &values, bool symbols = false) {
    SmallVector<Attribute> out;
    for (const auto &[key, value] : values) {
      Attribute second =
          symbols ? Attribute(FlatSymbolRefAttr::get(b.getContext(), value))
                  : Attribute(text(b, value));
      out.push_back(b.getArrayAttr({text(b, key), second}));
    }
    return b.getArrayAttr(out);
  }
  ArrayAttr parameterBindings(const source::ParameterBindings &values) {
    SmallVector<Attribute> out;
    for (const auto &[key, value] : values) {
      Attribute selected;
      if (const auto *constant = std::get_if<std::string>(&value))
        selected = text(b, *constant);
      else {
        const auto &ingress = std::get<source::FamilyIngress>(value);
        SmallVector<Attribute> selectors;
        for (const auto &s : ingress.selectors)
          selectors.push_back(b.getArrayAttr(
              {text(b, s.role),
               FlatSymbolRefAttr::get(b.getContext(), s.function),
               strings(s.arguments)}));
        selected = b.getArrayAttr({text(b, "ingress"), text(b, ingress.bound),
                                   b.getArrayAttr(selectors)});
      }
      out.push_back(b.getArrayAttr({text(b, key), selected}));
    }
    return b.getArrayAttr(out);
  }
  ArrayAttr dependencies(const std::vector<source::Dependency> &values) {
    SmallVector<Attribute> out;
    for (const auto &dep : values)
      out.push_back(
          b.getArrayAttr({text(b, dep.name),
                          FlatSymbolRefAttr::get(b.getContext(), dep.protocol),
                          pairs(dep.agreements)}));
    return b.getArrayAttr(out);
  }
  SmallVector<mlir::Value> operands(const source::Names &values,
                                    const Env &env) {
    SmallVector<mlir::Value> out;
    for (const auto &value : values)
      out.push_back(env.at(value));
    return out;
  }
  void bind(const source::Names &names, ValueRange values, Env &env) {
    for (auto [name, value] : zip(names, values))
      env.emplace(name, value);
  }
  void body(const source::Body &instructions, Env env,
            const source::Protocol *definition, bool local,
            ValueRange forwarded = {}, bool localRegion = false) {
    for (const auto &instruction : instructions) {
      locate(instruction);
      const auto *ret = instruction.get<source::Return>();
      const auto *yield = instruction.get<source::Yield>();
      if (ret || yield) {
        auto values = operands(ret ? ret->values : yield->values, env);
        if (yield && localRegion)
          llvm::append_range(values, forwarded);
        if (yield && localRegion)
          zkc::local::LocalYieldOp::create(b, location, values);
        else if (local)
          zkc::local::ReturnOp::create(b, location, values);
        else if (ret && !target)
          zkc::protocol_ir::MathematicalReturnOp::create(b, location, values);
        else if (ret)
          zkc::protocol_ir::FinishOp::create(b, location, values);
        else
          zkc::protocol_ir::ProtocolYieldOp::create(b, location, values);
        continue;
      }
      if (const auto *release = instruction.get<source::Release>()) {
        zkc::plan::ReleaseOp::create(b, location,
                                     operands(release->values, env));
        continue;
      }
      if (const auto *completion = instruction.get<source::ReturnIf>()) {
        SmallVector<mlir::Value> inputs{env.at(completion->condition)};
        append_range(inputs, operands(completion->values, env));
        auto *parent = b.getInsertionBlock()->getParentOp();
        auto participant = dyn_cast<zkc::protocol_ir::ParticipantOp>(parent);
        if (!participant)
          participant =
              parent->getParentOfType<zkc::protocol_ir::ParticipantOp>();
        SmallVector<Type> types;
        for (Value value : ArrayRef(inputs).drop_front()) {
          auto bound =
              zkc::protocol::encodeBoundType(value.getType(), physical);
          assert(bound && "admitted return type");
          if (!zkc::protocol::duplicable(bound->spelling()))
            types.push_back(value.getType());
        }
        auto op = zkc::protocol_ir::FinishIfOp::create(
            b, location, types, inputs.front(), ArrayRef(inputs).drop_front(),
            instruction.site, participant.getRole());
        bind(completion->continuations, op.getResults(), env);
      } else if (instruction.get<source::Incomplete>()) {
        zkc::protocol_ir::IncompleteOp::create(b, location, instruction.site);
      } else if (const auto *stop = instruction.get<source::Stop>()) {
        if (local || target)
          zkc::local::StopOp::create(b, location, instruction.site,
                                     stop->reason);
        else
          zkc::protocol_ir::HaltOp::create(b, location, instruction.site,
                                           stop->reason, text(b, stop->role));
      } else if (const auto *op = instruction.get<source::Operation>()) {
        SmallVector<Type> outputs;
        const auto &binding = bindings.at(op->callee);
        auto selected = resolveBinding(binding.application, physical);
        assert(selected && "admitted operation binding");
        for (const auto &t : selected->outputs)
          outputs.push_back(decodeBoundType(b.getContext(), t));
        auto parameters = strings(op->attributes);
        auto bindingRef = FlatSymbolRefAttr::get(b.getContext(), binding.name);
        Operation *created;
        if (physical)
          created = zkc::plan::ExecuteKernelOp::create(
              b, location, outputs, operands(op->inputs, env), instruction.site,
              binding.application.implementation, parameters, bindingRef);
        else
          created =
              operation(b, boundOperationName(binding.application.contract),
                        operands(op->inputs, env), outputs,
                        {named(b, "site", instruction.site),
                         named(b, "parameters", parameters),
                         named(b, "binding", bindingRef)},
                        0, location);
        bind(op->outputs, created->getResults(), env);
      } else if (const auto *literal =
                     instruction.get<source::BooleanConstant>()) {
        auto outputType = type(physical ? "bool@native.bool/1" : "bool");
        auto *op = operation(
            b, physical ? "plan.bool_constant" : "local.bool_constant", {},
            TypeRange{outputType},
            {named(b, "site", instruction.site),
             named(b, "value", b.getBoolAttr(literal->value))},
            0, location);
        bind({literal->output}, op->getResults(), env);
      } else if (const auto *call = instruction.get<source::AlgorithmCall>()) {
        auto op = zkc::local::ApplyOp::create(
            b, location, signatures.at(call->callee).getResults(),
            operands(call->inputs, env), call->callee, instruction.site);
        bind(call->outputs, op->getResults(), env);
      } else if (const auto *query = instruction.get<source::ServiceQuery>()) {
        auto reply = type(physical ? "field:bls12-381.fr@arkworks.fr/1"
                                   : "field:bls12-381.fr");
        auto op = zkc::protocol_ir::ParticipantQueryOp::create(
            b, location, TypeRange{reply}, operands(query->inputs, env),
            query->port, query->method, instruction.site);
        bind(query->outputs, op.getOutputs(), env);
      } else if (const auto *call = instruction.get<source::LocalCall>()) {
        Operation *op;
        if (target)
          op = zkc::local::CallOp::create(
              b, location, signatures.at(call->callee).getResults(),
              operands(call->inputs, env), call->callee, instruction.site);
        else
          op = zkc::protocol_ir::LocalCallOp::create(
              b, location, signatures.at(call->callee).getResults(),
              operands(call->inputs, env), call->callee, instruction.site,
              text(b, call->role));
        bind(call->outputs, op->getResults(), env);
      } else if (const auto *call = instruction.get<source::ProtocolCall>()) {
        std::string signature = call->callee;
        if (!target) {
          assert(definition && "common protocol call owner");
          for (const auto &dep : definition->dependencies)
            if (dep.name == call->callee)
              signature = dep.protocol;
        }
        Operation *op;
        if (target)
          op = zkc::protocol_ir::ParticipantCallOp::create(
              b, location, signatures.at(signature).getResults(),
              operands(call->inputs, env), instruction.site, call->callee);
        else
          op = zkc::protocol_ir::ProtocolCallOp::create(
              b, location, signatures.at(signature).getResults(),
              operands(call->inputs, env), instruction.site, call->callee);
        bind(call->outputs, op->getResults(), env);
      } else if (const auto *message = instruction.get<source::Message>()) {
        auto input = env.at(message->input);
        auto op = zkc::protocol_ir::MessageOp::create(
            b, location, input.getType(), input, instruction.site,
            message->schema, message->sender, message->receiver);
        env.emplace(message->output, op->getResult(0));
      } else if (const auto *send = instruction.get<source::Send>()) {
        zkc::protocol_ir::EmitOp::create(b, location, env.at(send->input),
                                         instruction.site, send->schema,
                                         send->peer);
      } else if (const auto *receive = instruction.get<source::Receive>()) {
        auto op = zkc::protocol_ir::AwaitOp::create(
            b, location, type(receive->type), instruction.site, receive->schema,
            receive->peer);
        env.emplace(receive->output, op->getResult(0));
      } else if (const auto *pack =
                     instruction.get<source::VariantConstruct>()) {
        auto op = zkc::local::VariantInjectOp::create(
            b, location, type(pack->type), operands(pack->payload, env),
            instruction.site, pack->alternative);
        env.emplace(pack->output, op->getResult(0));
      } else if (const auto *match = instruction.get<source::Match>()) {
        SmallVector<mlir::Value> inputs{env.at(match->input)};
        llvm::append_range(inputs, operands(match->captures, env));
        auto bound = encodeBoundType(inputs[0].getType(), physical);
        assert(bound && "admitted match input");
        auto descriptor = decodeVariant("variant:" + bound->identity);
        assert(descriptor && "admitted descriptor");
        SmallVector<std::unique_ptr<Region>> regions;
        SmallVector<Type> outputs;
        source::Names alternatives;
        for (auto [i, arm] : enumerate(match->arms)) {
          alternatives.push_back(arm.alternative);
          auto region = std::make_unique<Region>();
          auto *block = new Block();
          region->push_back(block);
          Env inner;
          for (auto [name, leaf] :
               zip(arm.payload, descriptor->alternatives[i].payload)) {
            auto parsed = parseBoundType(leaf, false);
            assert(parsed && "admitted payload");
            if (physical)
              parsed = defaultRepresentation(*parsed);
            assert(parsed && "admitted physical payload");
            inner.emplace(
                name, block->addArgument(
                          decodeBoundType(b.getContext(), *parsed), location));
          }
          for (auto [capture, input] :
               zip(match->captures, ArrayRef(inputs).drop_front()))
            inner.emplace(capture,
                          block->addArgument(input.getType(), location));
          {
            OpBuilder::InsertionGuard guard(b);
            b.setInsertionPointToEnd(block);
            body(arm.body, std::move(inner), definition, true, {}, true);
          }
          if (isa<zkc::local::LocalYieldOp>(block->back()))
            outputs.assign(block->back().getOperandTypes().begin(),
                           block->back().getOperandTypes().end());
          regions.push_back(std::move(region));
        }
        locate(instruction);
        auto op = zkc::local::LocalMatchOp::create(
            b, location, outputs, inputs, instruction.site,
            strings(alternatives), regions.size());
        for (auto [i, region] : enumerate(regions))
          op->getRegion(i).takeBody(*region);
        bind(match->outputs, op->getResults(), env);
      } else if (const auto *branch = instruction.get<source::Conditional>()) {
        SmallVector<mlir::Value> inputs{env.at(branch->condition)};
        llvm::append_range(inputs, operands(branch->captures, env));
        // Build isolated regions before creating the parent, so result types
        // come from the admitted branch yield rather than guessed metadata.
        Region regions[2];
        const source::Body *bodies[] = {&branch->thenBody, &branch->elseBody};
        for (unsigned i = 0; i < 2; ++i) {
          auto *block = new Block();
          regions[i].push_back(block);
          Env inner;
          for (auto [capture, input] :
               zip(branch->captures, ArrayRef(inputs).drop_front()))
            inner.emplace(capture,
                          block->addArgument(input.getType(), location));
          OpBuilder::InsertionGuard guard(b);
          b.setInsertionPointToEnd(block);
          body(*bodies[i], std::move(inner), definition, true, {}, true);
        }
        locate(instruction);
        TypeRange outputs;
        for (auto &region : regions)
          if (isa<zkc::local::LocalYieldOp>(region.front().back()))
            outputs = region.front().back().getOperandTypes();
        auto op = zkc::local::LocalIfOp::create(b, location, outputs, inputs,
                                                instruction.site);
        for (unsigned i = 0; i < 2; ++i)
          op->getRegion(i).takeBody(regions[i]);
        bind(branch->outputs, op->getResults(), env);
      } else if (const auto *loop = instruction.get<source::For>()) {
        SmallVector<mlir::Value> inputs{env.at(loop->lower),
                                        env.at(loop->upper)};
        SmallVector<Type> outputs;
        for (const auto &[name, initial] : loop->carried) {
          inputs.push_back(env.at(initial));
          outputs.push_back(env.at(initial).getType());
        }
        llvm::append_range(inputs, operands(loop->captures, env));
        auto op = zkc::local::LocalForOp::create(b, location, outputs, inputs,
                                                 instruction.site);
        auto *block = new Block();
        op->getRegion(0).push_back(block);
        Env inner;
        inner.emplace(loop->induction,
                      block->addArgument(inputs[0].getType(), location));
        for (auto [i, pair] : enumerate(loop->carried))
          inner.emplace(pair.first,
                        block->addArgument(inputs[i + 2].getType(), location));
        SmallVector<mlir::Value> forwarded;
        for (auto [i, capture] : enumerate(loop->captures)) {
          auto arg = block->addArgument(
              inputs[i + 2 + outputs.size()].getType(), location);
          inner.emplace(capture, arg);
          forwarded.push_back(arg);
        }
        {
          OpBuilder::InsertionGuard guard(b);
          b.setInsertionPointToEnd(block);
          body(loop->body, std::move(inner), definition, true, forwarded, true);
          if (loop->conditional &&
              isa<zkc::local::LocalYieldOp>(block->back())) {
            auto *end = &block->back();
            b.setInsertionPoint(end);
            zkc::local::LocalConditionOp::create(
                b, location, end->getOperand(0),
                end->getOperands().drop_front());
            end->erase();
          }
        }
        bind(loop->outputs, op->getResults(), env);
      } else if (const auto *loop = instruction.get<source::Loop>()) {
        SmallVector<mlir::Value> inputs;
        source::Names names;
        bool dynamic = loop->count.kind == source::LoopCount::Kind::Value;
        if (dynamic) {
          inputs.push_back(env.at(loop->count.value));
          names.push_back(loop->count.induction);
        }
        for (const auto &[binding, initial] : loop->carried) {
          names.push_back(binding);
          inputs.push_back(env.at(initial));
        }
        SmallVector<Type> outputs;
        for (auto value : llvm::drop_begin(inputs, dynamic ? 1 : 0))
          outputs.push_back(value.getType());
        for (const auto &capture : loop->captures) {
          names.push_back(capture);
          inputs.push_back(env.at(capture));
        }
        auto op = zkc::protocol_ir::ProtocolLoopOp::create(
            b, location, outputs, inputs, instruction.site, outputs.size(),
            dynamic ? "" : loop->count.value,
            loop->count.kind == source::LoopCount::Kind::Parameter,
            dynamic ? b.getI64IntegerAttr(loop->count.maximum) : IntegerAttr());
        auto *block = new Block();
        op->getRegion(0).push_back(block);
        Env inner;
        for (auto [name, input] : zip(names, inputs))
          inner.emplace(name, block->addArgument(input.getType(), location));
        {
          OpBuilder::InsertionGuard guard(b);
          b.setInsertionPointToEnd(block);
          body(loop->body, std::move(inner), definition, false);
        }
        bind(loop->outputs, op->getResults(), env);
      } else
        llvm_unreachable("admission checked every source instruction variant");
    }
  }
  template <typename Definition> void signature(const Definition &definition) {
    SmallVector<Type> inputs, outputs;
    for (const auto &arg : definition.arguments)
      inputs.push_back(type(arg.type));
    for (const auto &result : definition.results) {
      if constexpr (std::is_same_v<Definition, source::Protocol>)
        outputs.push_back(type(result.type));
      else
        outputs.push_back(type(result));
    }
    signatures.emplace(definition.name, b.getFunctionType(inputs, outputs));
  }
  template <typename Definition>
  void definitionBody(const Definition &definition, Operation *op,
                      const source::Body &content, bool local) {
    auto *block = new Block();
    op->getRegion(0).push_back(block);
    Env env;
    auto ft = signatures.at(definition.name);
    for (auto [arg, type] : zip(definition.arguments, ft.getInputs()))
      env.emplace(arg.name, block->addArgument(type, location));
    OpBuilder::InsertionGuard guard(b);
    b.setInsertionPointToEnd(block);
    const source::Protocol *protocol = nullptr;
    if constexpr (std::is_same_v<Definition, source::Protocol>)
      protocol = &definition;
    body(content, std::move(env), protocol, local);
  }
  void definition(const source::Function &f) {
    locate(f);
    auto op =
        zkc::local::FuncOp::create(b, location, f.name, signatures.at(f.name));
    if (f.origin)
      op->setAttr("logical_origin",
                  b.getArrayAttr({text(b, f.origin->definition),
                                  pairs(f.origin->arguments)}));
    if (!f.body)
      op.setPrivate();
    else
      definitionBody(f, op, *f.body, true);
  }
  void definition(const source::Protocol &p) {
    locate(p);
    SmallVector<Attribute> inputRoles, outputRoles, argumentNames;
    for (const auto &arg : p.arguments)
      argumentNames.push_back(text(b, arg.name));
    for (const auto &arg : p.arguments)
      inputRoles.push_back(text(b, arg.role));
    for (const auto &result : p.results)
      outputRoles.push_back(text(b, result.role));
    auto op = zkc::protocol_ir::ExecFuncOp::create(
        b, location, p.name, signatures.at(p.name), b.getArrayAttr(inputRoles),
        b.getArrayAttr(outputRoles), strings(p.roles), strings(p.parameters),
        dependencies(p.dependencies), !p.body, b.getArrayAttr(argumentNames));
    if (p.body)
      definitionBody(p, op, *p.body, false);
  }
  void definition(const source::Participant &p) {
    locate(p);
    SmallVector<Attribute> argumentNames;
    for (const auto &arg : p.arguments)
      argumentNames.push_back(text(b, arg.name));
    auto op = zkc::protocol_ir::ParticipantOp::create(
        b, location, p.name, signatures.at(p.name), p.instance, p.role,
        parameterBindings(p.parameters), b.getArrayAttr(argumentNames));
    if (!p.services.empty()) {
      SmallVector<Attribute> ports;
      for (const auto &port : p.services)
        ports.push_back(
            b.getArrayAttr({text(b, port.name), text(b, port.contract),
                            b.getI64IntegerAttr(port.inputIndex)}));
      op->setAttr("service_ports", b.getArrayAttr(ports));
    }
    definitionBody(p, op, p.body, false);
  }
  template <typename Root> OwningOpRef<ModuleOp> start(const Root &m) {
    locate(m);
    auto module = ModuleOp::create(location);
    b.setInsertionPointToEnd(module.getBody());
    using namespace zkc::protocol_ir;
    auto profile = target ? physical ? Profile::Physical : Profile::Exec
                          : Profile::ProtocolExec;
    ExecutionContractAttr contract;
    if constexpr (std::is_same_v<Root, source::Participants>)
      contract = ExecutionContractAttr::get(
          b.getContext(), source::isProgram(m.contract)
                              ? ExecutionContract::Program
                              : ExecutionContract::LegacyParticipantsV1);
    auto root = ProtocolModuleOp::create(
        b, location, ProfileAttr::get(b.getContext(), profile), contract);
    auto *top = new Block();
    root->getRegion(0).push_back(top);
    b.setInsertionPointToEnd(top);
    for (const auto &binding : m.bindings) {
      locate(binding);
      zkc::local::OperationBindingOp::create(
          b, location, binding.name, binding.application.contract,
          strings(binding.application.arguments),
          binding.application.implementation);
      bindings.emplace(binding.name, binding);
    }
    for (const auto &f : m.functions)
      signature(f);
    return module;
  }
  void entry(StringRef name, ArrayAttr targets, const source::Node &node) {
    locate(node);
    zkc::protocol_ir::ProtocolEntryOp::create(b, location, name, targets);
  }

public:
  Importer(MLIRContext &ctx, bool target, bool physical,
           llvm::function_ref<Location(const source::Node &)> locations)
      : b(&ctx), target(target), physical(physical), locations(locations),
        location(b.getUnknownLoc()) {}
  OwningOpRef<ModuleOp> run(const source::Module &m) {
    auto module = start(m);
    if (!m.relations.empty() || !m.relationViews.empty()) {
      SmallVector<Attribute> views;
      for (const auto &v : m.relationViews)
        views.push_back(
            b.getArrayAttr({text(b, v.name),
                            FlatSymbolRefAttr::get(b.getContext(), v.relation),
                            text(b, v.kind), text(b, v.staging),
                            b.getI64IntegerAttr(v.height)}));
      b.getInsertionBlock()->getParentOp()->setAttr("relation_views",
                                                    b.getArrayAttr(views));
      for (const auto &r : m.relations) {
        auto imported = std::visit(
            [&](const auto &p) {
              using T = std::decay_t<decltype(*p)>;
              if constexpr (std::is_same_v<T, relation::R1CS>)
                return relation::importR1CS(*p, r.name, *b.getContext());
              else
                return relation::importAIR(*p, r.name, *b.getContext());
            },
            r.value);
        if (!imported)
          report_fatal_error(Twine("admitted relation import: ") +
                             toString(imported.takeError()));
        b.clone(imported->get().getBody()->front());
      }
    }
    for (const auto &p : m.protocols)
      signature(p);
    auto owners = relation::associations(m);
    if (!owners)
      report_fatal_error(Twine("admitted relation associations: ") +
                         toString(owners.takeError()));
    for (const auto &f : m.functions) {
      definition(f);
      if (auto found = owners->find(f.name); found != owners->end()) {
        auto *op = &b.getInsertionBlock()->back();
        op->setAttr("relation", FlatSymbolRefAttr::get(b.getContext(),
                                                       found->second.first));
        op->setAttr("relation_view", text(b, found->second.second));
      }
    }
    for (const auto &p : m.protocols)
      definition(p);
    for (const auto &instance : m.instances) {
      locate(instance);
      zkc::protocol_ir::InstanceOp::create(
          b, location, instance.name, instance.protocol,
          parameterBindings(instance.parameters),
          pairs(instance.dependencies, true), pairs(instance.roles));
    }
    for (const auto &e : m.entries)
      entry(
          e.name,
          b.getArrayAttr({FlatSymbolRefAttr::get(b.getContext(), e.instance)}),
          e);
    return module;
  }
  OwningOpRef<ModuleOp> run(const source::Participants &m) {
    auto module = start(m);
    for (const auto &p : m.participants)
      signature(p);
    for (const auto &f : m.functions)
      definition(f);
    for (const auto &p : m.participants)
      definition(p);
    for (const auto &e : m.entries)
      entry(e.name, pairs(e.participants, true), e);
    return module;
  }
};
template <typename Root>
Expected<OwningOpRef<ModuleOp>>
import(const Root &root, MLIRContext &ctx,
       llvm::function_ref<Location(const source::Node &)> locations,
       const source::Node **failureLocation) {
  if (auto e = admit(root, false, failureLocation))
    return e;
  if (!hasProtocolDialects(ctx))
    return make_error<DialectRegistrationError>(
        InvocationPrecondition::LoadedProtocolDialects,
        "protocol import requires loaded zkc dialects");
  bool physical = false;
  if constexpr (std::is_same_v<Root, source::Participants>)
    physical = root.stage == source::Participants::Stage::Physical;
  if (auto e = ImportPreflight(ctx, physical, failureLocation).run(root))
    return e;
  auto module = Importer(ctx, std::is_same_v<Root, source::Participants>,
                         physical, locations)
                    .run(root);
  if (failed(verify(*module)))
    return error("interactive-mlir-verification");
  return module;
}
} // namespace
Expected<OwningOpRef<ModuleOp>>
importModule(const source::Module &root, MLIRContext &ctx,
             llvm::function_ref<Location(const source::Node &)> locations,
             const source::Node **failureLocation) {
  return import(root, ctx, locations, failureLocation);
}
Expected<OwningOpRef<ModuleOp>>
importModule(const source::Participants &root, MLIRContext &ctx,
             llvm::function_ref<Location(const source::Node &)> locations,
             const source::Node **failureLocation) {
  return import(root, ctx, locations, failureLocation);
}
Expected<OwningOpRef<ModuleOp>>
importModule(const source::Content &root, MLIRContext &ctx,
             llvm::function_ref<Location(const source::Node &)> locations,
             const source::Node **failureLocation) {
  if (failureLocation)
    *failureLocation = nullptr;
  if (const auto *module = std::get_if<source::Module>(&root))
    return importModule(*module, ctx, locations, failureLocation);
  if (const auto *participants = std::get_if<source::Participants>(&root))
    return importModule(*participants, ctx, locations, failureLocation);
  return error("interactive-format");
}
} // namespace zkc::protocol
