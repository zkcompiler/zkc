#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Builders.h"
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
  Operation *operation(OpBuilder &builder, StringRef name,
                       ValueRange inputs = {}, TypeRange outputs = {},
                       ArrayRef<NamedAttribute> attrs = {},
                       unsigned regions = 0) {
    return protocol::operation(builder, name, inputs, outputs, attrs, regions,
                               location);
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
        operation(b,
                  yield && localRegion ? "pir.local_yield"
                  : local              ? "func.return"
                  : ret                ? "pir.finish"
                                       : "pir.yield",
                  values);
        continue;
      }
      if (const auto *release = instruction.get<source::Release>()) {
        operation(b, "plan.release", operands(release->values, env));
        continue;
      }
      SmallVector<NamedAttribute> attrs{named(b, "site", instruction.site)};
      if (instruction.get<source::Incomplete>()) {
        operation(b, "pir.incomplete", {}, {}, attrs);
      } else if (const auto *stop = instruction.get<source::Stop>()) {
        attrs.push_back(named(b, "reason", stop->reason));
        if (!target && !local)
          attrs.push_back(named(b, "role", stop->role));
        operation(b, "pir.halt", {}, {}, attrs);
      } else if (const auto *op = instruction.get<source::Operation>()) {
        SmallVector<Type> outputs;
        const auto &binding = bindings.at(op->callee);
        auto selected = resolveBinding(binding.application, physical);
        assert(selected && "admitted operation binding");
        for (const auto &t : selected->outputs)
          outputs.push_back(decodeBoundType(b.getContext(), t));
        attrs.push_back(named(b, "parameters", strings(op->attributes)));
        attrs.push_back(
            named(b, "binding",
                  FlatSymbolRefAttr::get(b.getContext(), binding.name)));
        if (physical)
          attrs.push_back(
              named(b, "kernel", binding.application.implementation));
        auto *created = operation(
            b,
            physical ? ExecuteKernelOp::getOperationName()
                     : boundOperationName(binding.application.contract),
            operands(op->inputs, env), outputs, attrs);
        bind(op->outputs, created->getResults(), env);
      } else if (const auto *call = instruction.get<source::AlgorithmCall>()) {
        attrs.push_back(named(
            b, "callee", FlatSymbolRefAttr::get(b.getContext(), call->callee)));
        auto *op = operation(b, "func.call", operands(call->inputs, env),
                             signatures.at(call->callee).getResults(), attrs);
        bind(call->outputs, op->getResults(), env);
      } else if (const auto *call = instruction.get<source::LocalCall>()) {
        attrs.push_back(named(
            b, "callee", FlatSymbolRefAttr::get(b.getContext(), call->callee)));
        if (!target)
          attrs.push_back(named(b, "role", call->role));
        auto *op = operation(b, "pir.local_call", operands(call->inputs, env),
                             signatures.at(call->callee).getResults(), attrs);
        bind(call->outputs, op->getResults(), env);
      } else if (const auto *call = instruction.get<source::ProtocolCall>()) {
        std::string signature = call->callee;
        if (!target) {
          assert(definition && "common protocol call owner");
          for (const auto &dep : definition->dependencies)
            if (dep.name == call->callee)
              signature = dep.protocol;
          attrs.push_back(named(b, "dependency", call->callee));
        } else
          attrs.push_back(
              named(b, "callee",
                    FlatSymbolRefAttr::get(b.getContext(), call->callee)));
        auto *op =
            operation(b, target ? "pir.participant_call" : "pir.protocol_call",
                      operands(call->inputs, env),
                      signatures.at(signature).getResults(), attrs);
        bind(call->outputs, op->getResults(), env);
      } else if (const auto *message = instruction.get<source::Message>()) {
        attrs.push_back(named(b, "schema", message->schema));
        attrs.push_back(named(b, "sender", message->sender));
        attrs.push_back(named(b, "receiver", message->receiver));
        auto input = env.at(message->input);
        auto *op = operation(b, "pir.message", input, input.getType(), attrs);
        env.emplace(message->output, op->getResult(0));
      } else if (const auto *send = instruction.get<source::Send>()) {
        attrs.push_back(named(b, "schema", send->schema));
        attrs.push_back(named(b, "peer", send->peer));
        operation(b, "pir.emit", env.at(send->input), {}, attrs);
      } else if (const auto *receive = instruction.get<source::Receive>()) {
        attrs.push_back(named(b, "schema", receive->schema));
        attrs.push_back(named(b, "peer", receive->peer));
        auto *op = operation(b, "pir.await", {}, type(receive->type), attrs);
        env.emplace(receive->output, op->getResult(0));
      } else if (const auto *pack =
                     instruction.get<source::VariantConstruct>()) {
        attrs.push_back(named(b, "alternative", pack->alternative));
        auto *op =
            operation(b, "pir.variant_inject", operands(pack->payload, env),
                      type(pack->type), attrs);
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
        attrs.push_back(named(b, "alternatives", strings(alternatives)));
        auto *op = operation(b, "pir.local_match", inputs, outputs, attrs,
                             regions.size());
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
        auto *op = operation(b, "pir.local_if", inputs, outputs, attrs, 2);
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
        auto *op = operation(b, "pir.local_for", inputs, outputs, attrs, 1);
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
        attrs.push_back(
            named(b, "carried", b.getI64IntegerAttr(outputs.size())));
        attrs.push_back(named(b, "count", loop->count.value));
        attrs.push_back(
            named(b, "parameter",
                  b.getBoolAttr(loop->count.kind ==
                                source::LoopCount::Kind::Parameter)));
        auto *op = operation(b, "pir.loop", inputs, outputs, attrs, 1);
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
    auto *op = operation(
        b, "pir.protocol", {}, {},
        {named(b, "sym_name", p.name),
         named(b, "function_type", TypeAttr::get(signatures.at(p.name))),
         named(b, "roles", strings(p.roles)),
         named(b, "parameters", strings(p.parameters)),
         named(b, "dependencies", dependencies(p.dependencies)),
         named(b, "input_roles", b.getArrayAttr(inputRoles)),
         named(b, "argument_names", b.getArrayAttr(argumentNames)),
         named(b, "output_roles", b.getArrayAttr(outputRoles)),
         named(b, "external", b.getBoolAttr(!p.body))},
        1);
    if (p.body)
      definitionBody(p, op, *p.body, false);
  }
  void definition(const source::Participant &p) {
    locate(p);
    SmallVector<Attribute> argumentNames;
    for (const auto &arg : p.arguments)
      argumentNames.push_back(text(b, arg.name));
    auto *op = operation(
        b, "pir.participant", {}, {},
        {named(b, "sym_name", p.name),
         named(b, "function_type", TypeAttr::get(signatures.at(p.name))),
         named(b, "instance", p.instance), named(b, "role", p.role),
         named(b, "parameters", parameterBindings(p.parameters)),
         named(b, "argument_names", b.getArrayAttr(argumentNames))},
        1);
    definitionBody(p, op, p.body, false);
  }
  template <typename Root> OwningOpRef<ModuleOp> start(const Root &m) {
    locate(m);
    auto module = ModuleOp::create(location);
    b.setInsertionPointToEnd(module.getBody());
    SmallVector<NamedAttribute> attrs{named(
        b, "stage", target ? physical ? "physical" : "logical" : "common")};
    auto *root = operation(b, "pir.module", {}, {}, attrs, 1);
    auto *top = new Block();
    root->getRegion(0).push_back(top);
    b.setInsertionPointToEnd(top);
    for (const auto &binding : m.bindings) {
      locate(binding);
      operation(
          b, "pir.operation_binding", {}, {},
          {named(b, "sym_name", binding.name),
           named(b, "contract", binding.application.contract),
           named(b, "arguments", strings(binding.application.arguments)),
           named(b, "implementation", binding.application.implementation)});
      bindings.emplace(binding.name, binding);
    }
    for (const auto &f : m.functions)
      signature(f);
    return module;
  }
  void entry(StringRef name, ArrayAttr targets, const source::Node &node) {
    locate(node);
    operation(b, "pir.entry", {}, {},
              {named(b, "sym_name", name), named(b, "targets", targets)});
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
      operation(
          b, "pir.instance", {}, {},
          {named(b, "sym_name", instance.name),
           named(b, "protocol",
                 FlatSymbolRefAttr::get(b.getContext(), instance.protocol)),
           named(b, "parameters", parameterBindings(instance.parameters)),
           named(b, "dependencies", pairs(instance.dependencies, true)),
           named(b, "roles", pairs(instance.roles))});
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
