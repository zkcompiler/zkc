#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Kernels.h"
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
#include "llvm/Support/ErrorHandling.h"
#include <type_traits>

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
namespace {
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
          LocalYieldOp::create(b, location, values);
        else if (local)
          func::ReturnOp::create(b, location, values);
        else if (ret)
          FinishOp::create(b, location, values);
        else
          ProtocolYieldOp::create(b, location, values);
        continue;
      }
      if (const auto *release = instruction.get<source::Release>()) {
        ReleaseOp::create(b, location, operands(release->values, env));
        continue;
      }
      if (instruction.get<source::Incomplete>()) {
        IncompleteOp::create(b, location, instruction.site);
      } else if (const auto *stop = instruction.get<source::Stop>()) {
        HaltOp::create(b, location, instruction.site, stop->reason,
                       !target && !local ? text(b, stop->role) : StringAttr());
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
          created = ExecuteKernelOp::create(
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
      } else if (const auto *call = instruction.get<source::AlgorithmCall>()) {
        auto op = func::CallOp::create(
            b, location, signatures.at(call->callee).getResults(),
            FlatSymbolRefAttr::get(b.getContext(), call->callee),
            operands(call->inputs, env), ArrayAttr(), ArrayAttr(), UnitAttr());
        op->setAttr("site", text(b, instruction.site));
        bind(call->outputs, op->getResults(), env);
      } else if (const auto *call = instruction.get<source::LocalCall>()) {
        auto op = LocalCallOp::create(
            b, location, signatures.at(call->callee).getResults(),
            operands(call->inputs, env), call->callee, instruction.site,
            !target ? text(b, call->role) : StringAttr());
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
          op = ParticipantCallOp::create(
              b, location, signatures.at(signature).getResults(),
              operands(call->inputs, env), instruction.site, call->callee);
        else
          op = ProtocolCallOp::create(
              b, location, signatures.at(signature).getResults(),
              operands(call->inputs, env), instruction.site, call->callee);
        bind(call->outputs, op->getResults(), env);
      } else if (const auto *message = instruction.get<source::Message>()) {
        auto input = env.at(message->input);
        auto op = MessageOp::create(b, location, input.getType(), input,
                                    instruction.site, message->schema,
                                    message->sender, message->receiver);
        env.emplace(message->output, op->getResult(0));
      } else if (const auto *send = instruction.get<source::Send>()) {
        EmitOp::create(b, location, env.at(send->input), instruction.site,
                       send->schema, send->peer);
      } else if (const auto *receive = instruction.get<source::Receive>()) {
        auto op =
            AwaitOp::create(b, location, type(receive->type), instruction.site,
                            receive->schema, receive->peer);
        env.emplace(receive->output, op->getResult(0));
      } else if (const auto *pack =
                     instruction.get<source::VariantConstruct>()) {
        auto op = VariantInjectOp::create(b, location, type(pack->type),
                                          operands(pack->payload, env),
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
          if (isa<LocalYieldOp>(block->back()))
            outputs.assign(block->back().getOperandTypes().begin(),
                           block->back().getOperandTypes().end());
          regions.push_back(std::move(region));
        }
        locate(instruction);
        auto op =
            LocalMatchOp::create(b, location, outputs, inputs, instruction.site,
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
          if (isa<LocalYieldOp>(region.front().back()))
            outputs = region.front().back().getOperandTypes();
        auto op =
            LocalIfOp::create(b, location, outputs, inputs, instruction.site);
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
        auto op =
            LocalForOp::create(b, location, outputs, inputs, instruction.site);
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
        }
        bind(loop->outputs, op->getResults(), env);
      } else if (const auto *loop = instruction.get<source::Loop>()) {
        SmallVector<mlir::Value> inputs;
        source::Names names;
        for (const auto &[binding, initial] : loop->carried) {
          names.push_back(binding);
          inputs.push_back(env.at(initial));
        }
        SmallVector<Type> outputs;
        for (auto value : inputs)
          outputs.push_back(value.getType());
        for (const auto &capture : loop->captures) {
          names.push_back(capture);
          inputs.push_back(env.at(capture));
        }
        auto op = ProtocolLoopOp::create(
            b, location, outputs, inputs, instruction.site, outputs.size(),
            loop->count.value,
            loop->count.kind == source::LoopCount::Kind::Parameter);
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
    auto op = func::FuncOp::create(b, location, f.name, signatures.at(f.name));
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
    auto op = ProtocolOp::create(
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
    auto op = ParticipantOp::create(
        b, location, p.name, signatures.at(p.name), p.instance, p.role,
        parameterBindings(p.parameters), b.getArrayAttr(argumentNames));
    definitionBody(p, op, p.body, false);
  }
  template <typename Root> OwningOpRef<ModuleOp> start(const Root &m) {
    locate(m);
    auto module = ModuleOp::create(location);
    b.setInsertionPointToEnd(module.getBody());
    auto root = ProtocolModuleOp::create(
        b, location, target ? physical ? "physical" : "logical" : "common");
    auto *top = new Block();
    root->getRegion(0).push_back(top);
    b.setInsertionPointToEnd(top);
    for (const auto &binding : m.bindings) {
      locate(binding);
      OperationBindingOp::create(b, location, binding.name,
                                 binding.application.contract,
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
    ProtocolEntryOp::create(b, location, name, targets);
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
      InstanceOp::create(b, location, instance.name, instance.protocol,
                         parameterBindings(instance.parameters),
                         pairs(instance.dependencies, true),
                         pairs(instance.roles));
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
