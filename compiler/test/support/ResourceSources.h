#ifndef ZKC_TEST_RESOURCE_SOURCES_H
#define ZKC_TEST_RESOURCE_SOURCES_H
// Directly authored scoped sources for compiler/root and runtime integration
// tests. The builder supplies CFG mechanics; the tests supply all programs.
#include "NativeCases.h"
#include "VariantFixture.h"
#include "mlir/AsmParser/AsmParser.h"
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"

namespace zkc::test::resource_sources {
using namespace mlir;

using Values = SmallVector<Value>;
using Types = SmallVector<Type>;
class Source {
public:
  MLIRContext context;
  Location location;
  OwningOpRef<ModuleOp> module;
  OpBuilder builder;
  protocol_ir::ProtocolModuleOp owner;
  Type scope, index, boolean, rng, unit, transcript, field, tag;
  unsigned regionNumber = 0;

  Source()
      : context(MLIRContext::Threading::DISABLED),
        location(UnknownLoc::get(&context)), module(ModuleOp::create(location)),
        builder(&context) {
    DialectRegistry registry;
    registerDialects(registry);
    context.appendDialectRegistry(registry);
    context.loadAllAvailableDialects();
    builder.setInsertionPointToEnd(module->getBody());
    owner = protocol_ir::ProtocolModuleOp::create(
        builder, location, protocol_ir::Profile::Protocol, mlir::ArrayAttr{});
    owner.getBody().emplaceBlock();
    scope = runtime::ScopeType::get(&context);
    index = builder.getIntegerType(64, false);
    boolean = builder.getI1Type();
    rng = parseType("!runtime.capability<rng, \"bls12-381.fr\">", &context);
    unit =
        parseType("!runtime.capability<resource_unit, \"Slot.A\">", &context);
    transcript = parseType(
        "!runtime.capability<transcript, \"merlin3.bls12-381.fr64be/0\">",
        &context);
    field = parseType("!algebra.field<\"bls12-381.fr\">", &context);
    tag = data::importVariantType(&context,
                                  {"Choice", {{"left", {}}, {"right", {}}}});
  }
  NamedAttribute text(StringRef name, StringRef value) {
    return builder.getNamedAttr(name, builder.getStringAttr(value));
  }
  NamedAttribute symbol(StringRef name, StringRef value) {
    return builder.getNamedAttr(name, FlatSymbolRefAttr::get(&context, value));
  }
  Operation *operation(StringRef name, ValueRange inputs = {},
                       TypeRange outputs = {},
                       ArrayRef<NamedAttribute> attrs = {},
                       bool region = false) {
    OperationState state(location, name);
    state.addOperands(inputs);
    state.addTypes(outputs);
    state.addAttributes(attrs);
    if (region)
      state.addRegion();
    return builder.create(state);
  }
  func::FuncOp function(StringRef name, TypeRange inputs, TypeRange outputs,
                        bool region = false) {
    builder.setInsertionPointToEnd(&owner.getBody().front());
    Types arguments{scope};
    llvm::append_range(arguments, inputs);
    auto function = func::FuncOp::create(
        builder, location, name,
        builder.getFunctionType(
            arguments,
            exec::OutcomeType::get(&context, llvm::to_vector(outputs))));
    function->setAttr("no_inline", builder.getUnitAttr());
    if (region) {
      function.setPrivate();
      function->setAttr("runtime.region", builder.getUnitAttr());
    } else
      function->setAttr("runtime.origin",
                        builder.getArrayAttr({builder.getStringAttr(name),
                                              builder.getArrayAttr({})}));
    builder.setInsertionPointToEnd(function.addEntryBlock());
    return function;
  }
  func::FuncOp region(TypeRange inputs, TypeRange outputs) {
    return function("body_" + std::to_string(regionNumber++), inputs, outputs,
                    true);
  }
  void binding(StringRef name, StringRef contract,
               ArrayRef<StringRef> arguments) {
    OpBuilder::InsertionGuard restore(builder);
    builder.setInsertionPointToEnd(&owner.getBody().front());
    protocol::BindingApplication application{contract.str(), {}, {}};
    for (StringRef argument : arguments)
      application.arguments.push_back(argument.str());
    auto native =
        protocol::decodeBindingArguments(builder.getContext(), application);
    assert(native && "resource fixture static arguments must be admitted");
    runtime::BindingOp::create(builder, location, name, contract, *native, "");
  }
  Values invoke(exec::ScopedExecutionBuilder &control, StringRef name,
                ValueRange inputs, TypeRange outputs, StringRef site,
                ArrayRef<StringRef> parameters = {}) {
    auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
        control.getFunction(), FlatSymbolRefAttr::get(&context, name));
    require(bool(binding), "fixture binding is missing");
    SmallVector<std::string> expected;
    for (auto parameter : parameters)
      expected.push_back(parameter.str());
    auto native = take(protocol::decodeInvocationParameters(
        binding.getContract(), binding.getArgumentsAttr(), expected));
    return control.invoke("exec.apply", outputs, control.scoped(inputs),
                          {symbol("binding", name), text("site", site),
                           builder.getNamedAttr("parameters", native)});
  }
  Values call(exec::ScopedExecutionBuilder &control, StringRef callee,
              ValueRange inputs, TypeRange outputs, StringRef site) {
    return control.invoke(
        "func.call", outputs, control.scoped(inputs),
        {symbol("callee", callee), text("runtime.site", site)});
  }
  ArrayAttr roles(ArrayRef<StringRef> values = {"P"}) {
    return builder.getStrArrayAttr(values);
  }
  ArrayAttr portRoles(unsigned count, ArrayRef<StringRef> names = {"P"}) {
    return builder.getArrayAttr(SmallVector<Attribute>(count, roles(names)));
  }
  Block *protocol(StringRef name, TypeRange inputs, TypeRange outputs,
                  ArrayRef<StringRef> participants = {"P"},
                  ArrayAttr inputRoles = {}, ArrayAttr outputRoles = {}) {
    builder.setInsertionPointToEnd(&owner.getBody().front());
    auto *op = operation(
        "protocol.func", {}, {},
        {text("sym_name", name),
         builder.getNamedAttr("origin",
                              builder.getArrayAttr({builder.getStringAttr(name),
                                                    builder.getArrayAttr({})})),
         builder.getNamedAttr(
             "function_type",
             TypeAttr::get(builder.getFunctionType(inputs, outputs))),
         builder.getNamedAttr("roles", roles(participants)),
         builder.getNamedAttr(
             "input_roles", inputRoles ? inputRoles : portRoles(inputs.size())),
         builder.getNamedAttr("output_roles", outputRoles
                                                  ? outputRoles
                                                  : portRoles(outputs.size()))},
        true);
    auto *block = new Block;
    op->getRegion(0).push_back(block);
    for (Type type : inputs)
      block->addArgument(type, location);
    builder.setInsertionPointToEnd(block);
    return block;
  }
  Values local(StringRef callee, ValueRange inputs, TypeRange outputs,
               StringRef site = "step", StringRef role = "P") {
    return llvm::to_vector(
        ValueRange(operation("protocol.local_call", inputs, outputs,
                             {symbol("callee", callee), text("role", role),
                              text("site", site)})
                       ->getResults()));
  }
  Values repeat(Value count, ValueRange carried, ValueRange captures,
                StringRef site, unsigned maximum,
                llvm::function_ref<Values(Block *)> body,
                ArrayRef<StringRef> participants = {"P"},
                StringRef carriedRole = "P") {
    Values inputs{count};
    llvm::append_range(inputs, carried);
    llvm::append_range(inputs, captures);
    auto *op = operation(
        "protocol.repeat", inputs, carried.getTypes(),
        {text("site", site),
         builder.getNamedAttr("carried",
                              builder.getI64IntegerAttr(carried.size())),
         builder.getNamedAttr("maximum", builder.getI64IntegerAttr(maximum)),
         builder.getNamedAttr("roles", roles(participants)),
         builder.getNamedAttr("carried_roles",
                              portRoles(carried.size(), {carriedRole}))},
        true);
    {
      OpBuilder::InsertionGuard restore(builder);
      auto *entry = new Block;
      op->getRegion(0).push_back(entry);
      entry->addArgument(index, location);
      for (Value value : ArrayRef(inputs).drop_front())
        entry->addArgument(value.getType(), location);
      builder.setInsertionPointToEnd(entry);
      operation("protocol.yield", body(entry));
    }
    return llvm::to_vector(ValueRange(op->getResults()));
  }
  void wrap(StringRef callee, Type state, bool outside) {
    auto *entry =
        protocol("main", {index, state, boolean, index, index}, state);
    auto args = entry->getArguments();
    auto result =
        outside
            ? local(callee, args.drop_front(), state)
            : repeat(args[0], args[1], args.drop_front(2), "rounds", 8,
                     [&](Block *round) {
                       return local(callee, round->getArguments().drop_front(),
                                    state);
                     });
    operation("protocol.return", result);
  }
};
inline void simple(Source &s, StringRef name, bool outside) {
  bool fresh = name.starts_with("fresh") || name.starts_with("unknown") ||
               name == "stop-call" || name == "continuing-call";
  auto state = fresh ? s.unit : s.rng;
  if (fresh)
    s.binding("create", "resource_unit.create", {"Slot.A"});
  if (name == "apply" || name == "missing" || name == "calls80" ||
      name == "endpoint-call") {
    auto identity = s.function("identity", state, state);
    exec::ScopedExecutionBuilder control(s.builder, identity);
    control.returned(identity.getArgument(1));
  }
  if (name == "stop-call") {
    auto never = s.function("never", {}, {});
    exec::ScopedExecutionBuilder control(s.builder, never);
    control.reject("abort", "abort");
  }
  auto fn = s.function("step", {state, s.boolean, s.index, s.index}, state);
  exec::ScopedExecutionBuilder control(s.builder, fn);
  Value result = fn.getArgument(1);
  if (name == "apply" || name == "missing" || name == "calls80" ||
      name == "cycle") {
    for (unsigned i = 0; i != (name == "calls80" ? 80u : 1u); ++i)
      result = name == "cycle"
                   ? s.call(control, "step", fn.getArguments().drop_front(),
                            state, "again")[0]
                   : s.call(control, name == "missing" ? "missing" : "identity",
                            result, state, "call" + std::to_string(i))[0];
  } else if (name == "endpoint-call") {
    result = s.local("identity", result, state, "endpoint")[0];
  } else if (name == "terminal-then-return") {
    control.conditional(fn.getArgument(2), {}, {}, "both", [&](unsigned arm) {
      auto body = s.region({}, {});
      exec::ScopedExecutionBuilder inner(s.builder, body);
      inner.reject("abort", arm == 0 ? "left" : "right");
      return body;
    });
  } else if (name == "draw80" || name == "draw-reuse") {
    s.binding("draw", "random.draw", {"bls12-381.fr"});
    for (unsigned i = 0; i != 80; ++i)
      result = s.invoke(control, "draw", result, {s.field, state},
                        "draw" + std::to_string(i))[1];
    if (name == "draw-reuse")
      result = fn.getArgument(1);
  } else if (name == "fresh") {
    result = s.invoke(control, "create", {}, state, "new")[0];
  } else if (name == "if" || name == "if-stop" || name == "if-terminal" ||
             name == "fresh-branch" || name == "fresh-stop-branch" ||
             name == "stop-call" || name == "continuing-call") {
    result = control.conditional(
        fn.getArgument(2), result, state, "choice", [&](unsigned arm) {
          auto body = s.region(state, state);
          exec::ScopedExecutionBuilder inner(s.builder, body);
          bool stops =
              name == "if-terminal" ||
              (arm == 0 && (name == "if-stop" || name == "fresh-stop-branch"));
          if (stops)
            inner.reject("abort", arm == 0 ? "abort" : "abort_other");
          else {
            Value value = body.getArgument(1);
            if ((arm == 1 && name.starts_with("fresh")) ||
                (arm == 0 &&
                 (name == "stop-call" || name == "continuing-call"))) {
              if (name == "stop-call")
                s.call(inner, "never", {}, {}, "never");
              value = s.invoke(inner, "create", {}, state, "new")[0];
            }
            inner.complete(value);
          }
          return body;
        })[0];
  } else if (name == "for" || name == "for-stop") {
    result = control.loop(fn.getArgument(3), fn.getArgument(4), result, {},
                          state, false, "loop", [&](unsigned) {
                            auto body = s.region({s.index, state}, state);
                            exec::ScopedExecutionBuilder inner(s.builder, body);
                            if (name == "for-stop")
                              inner.reject("abort", "abort");
                            else
                              inner.complete(body.getArgument(2));
                            return body;
                          })[0];
  } else if (name == "match" || name == "match-stop") {
    auto tag = control.conditional(
        fn.getArgument(2), {}, s.tag, "tag", [&](unsigned arm) {
          auto body = s.region({}, s.tag);
          exec::ScopedExecutionBuilder inner(s.builder, body);
          auto value =
              inner.invoke("exec.variant", s.tag, inner.scoped({}),
                           {s.text("alternative", arm == 0 ? "left" : "right"),
                            s.text("site", arm == 0 ? "left" : "right")});
          inner.complete(value);
          return body;
        })[0];
    result = control.match(
        tag, result, state, {"left", "right"}, "match", [&](unsigned arm) {
          auto body = s.region(state, state);
          exec::ScopedExecutionBuilder inner(s.builder, body);
          if (name == "match-stop" && arm == 0)
            inner.reject("abort", "abort");
          else
            inner.complete(body.getArgument(1));
          return body;
        })[0];
  } else if (name == "unknown-slot" || name == "unknown-wrong") {
    auto fresh = s.invoke(control, "create", {}, state, "new")[0];
    auto results = control.loop(
        fn.getArgument(3), fn.getArgument(4), {result, fresh}, {},
        {state, state}, false, "loop", [&](unsigned) {
          auto body = s.region({s.index, state, state}, {state, state});
          exec::ScopedExecutionBuilder inner(s.builder, body);
          auto replacement = s.invoke(inner, "create", {}, state, "replace")[0];
          inner.complete({body.getArgument(2), replacement});
          return body;
        });
    result = results[name == "unknown-wrong" ? 1 : 0];
  } else if (name == "box") {
    auto description =
        protocol::encodeVariant({"Box", {{"box", {"rng:bls12-381.fr"}}}});
    require(bool(description), "box descriptor refused");
    auto type = zkc::test::variantType(&s.context, *description);
    auto box = control.invoke(
        "exec.variant", type, control.scoped(result),
        {s.text("alternative", "box"), s.text("site", "box")})[0];
    result = control.match(box, {}, state, {"box"}, "match", [&](unsigned) {
      auto body = s.region(state, state);
      exec::ScopedExecutionBuilder inner(s.builder, body);
      inner.complete(body.getArgument(1));
      return body;
    })[0];
  } else
    throw std::runtime_error("unknown resource source: " + name.str());
  control.returned(result);
  s.wrap("step", state, outside);
}
inline void pair(Source &s, StringRef name, bool outside) {
  require(name == "swap" || name == "formal" || name == "formal-swap" ||
              name == "callee-repeat" || name == "callee-repeat-reverse" ||
              name == "callee-repeat-good" ||
              name == "callee-repeat-good-reverse",
          "unknown paired resource source");
  bool formal = name.starts_with("formal");
  bool swap = name == "swap" || name == "formal-swap" ||
              name == "callee-repeat" || name == "callee-repeat-reverse";
  if (formal) {
    auto identity = s.function("identity", s.rng, s.rng);
    exec::ScopedExecutionBuilder inner(s.builder, identity);
    inner.returned(identity.getArgument(1));
  }
  auto fn =
      s.function("swap", {s.rng, s.rng, s.index, s.index}, {s.rng, s.rng});
  exec::ScopedExecutionBuilder control(s.builder, fn);
  Values result;
  if (formal) {
    result.push_back(
        s.call(control, "identity", fn.getArgument(1), s.rng, "left")[0]);
    result.push_back(
        s.call(control, "identity", fn.getArgument(2), s.rng, "right")[0]);
    if (swap)
      std::swap(result[0], result[1]);
  } else
    result = control.loop(
        fn.getArgument(3), fn.getArgument(4), fn.getArguments().slice(1, 2), {},
        {s.rng, s.rng}, false, "inner", [&](unsigned) {
          auto body = s.region({s.index, s.rng, s.rng}, {s.rng, s.rng});
          exec::ScopedExecutionBuilder inner(s.builder, body);
          inner.complete(
              {body.getArgument(swap ? 3 : 2), body.getArgument(swap ? 2 : 3)});
          return body;
        });
  control.returned(result);
  auto emit = [&](StringRef symbol, bool apply) {
    auto *entry = s.protocol(symbol, {s.index, s.rng, s.rng, s.index, s.index},
                             {s.rng, s.rng});
    auto invoke = [&](Block *block) {
      if (apply)
        return llvm::to_vector(ValueRange(
            s.operation("protocol.apply", block->getArguments(), {s.rng, s.rng},
                        {s.symbol("callee", "child"), s.text("site", "child"),
                         s.builder.getNamedAttr("roles", s.roles())})
                ->getResults()));
      return s.local("swap", block->getArguments().drop_front(), {s.rng, s.rng},
                     "swap");
    };
    auto result =
        outside
            ? invoke(entry)
            : s.repeat(entry->getArgument(0), entry->getArguments().slice(1, 2),
                       entry->getArguments().drop_front(3),
                       symbol == "main" ? "outer" : "child_rounds", 8, invoke);
    s.operation("protocol.return", result);
  };
  bool child = name.starts_with("callee-repeat");
  if (child && !name.ends_with("reverse"))
    emit("child", false);
  emit("main", child);
  if (child && name.ends_with("reverse"))
    emit("child", false);
}
inline void calls(Source &s, StringRef name, bool outside) {
  if (name == "dag") {
    for (unsigned i = 0; i != 20; ++i) {
      auto function = s.function("f" + std::to_string(i), s.rng, s.rng);
      exec::ScopedExecutionBuilder control(s.builder, function);
      Value value = function.getArgument(1);
      if (i) {
        value =
            s.call(control, "f" + std::to_string(i - 1), value, s.rng, "a")[0];
        value =
            s.call(control, "f" + std::to_string(i - 1), value, s.rng, "b")[0];
      }
      control.returned(value);
    }
    auto function =
        s.function("step", {s.rng, s.boolean, s.index, s.index}, s.rng);
    exec::ScopedExecutionBuilder control(s.builder, function);
    auto result = s.call(control, "f19", function.getArgument(1), s.rng, "dag");
    control.returned(result);
    s.wrap("step", s.rng, outside);
  } else {
    auto fn = s.function("identity", s.rng, s.rng);
    exec::ScopedExecutionBuilder control(s.builder, fn);
    control.returned(fn.getArgument(1));
    auto *entry = s.protocol(
        "main", {s.index, s.rng, s.boolean, s.index, s.index}, s.rng);
    auto chain = [&](Block *block) {
      Value value = block->getArgument(1);
      for (unsigned i = 0; i != 80; ++i)
        value =
            s.local("identity", value, s.rng, "call" + std::to_string(i))[0];
      return Values{value};
    };
    auto result =
        outside
            ? chain(entry)
            : s.repeat(entry->getArgument(0), entry->getArgument(1),
                       entry->getArguments().drop_front(2), "rounds", 8, chain);
    s.operation("protocol.return", result);
  }
}
inline void roles(Source &s, StringRef name) {
  require(name == "role-stop" || name == "role-identity" ||
              name == "role-apply-stop" || name == "role-apply-identity" ||
              name == "role-apply-stop-reverse" ||
              name == "role-apply-identity-reverse",
          "unknown participant resource source");
  bool identity = name.contains("identity"), apply = name.contains("apply");
  s.binding("create", "resource_unit.create", {"Slot.A"});
  auto never = s.function("never", {}, {});
  exec::ScopedExecutionBuilder stopped(s.builder, never);
  stopped.reject("abort", "halt");
  auto halt = s.function("halt", {}, s.unit);
  exec::ScopedExecutionBuilder halting(s.builder, halt);
  s.call(halting, "never", {}, {}, "never");
  auto fresh = s.invoke(halting, "create", {}, s.unit, "new");
  halting.returned(fresh);
  auto swap = s.function("swap", {s.rng, s.rng}, {s.rng, s.rng});
  exec::ScopedExecutionBuilder swapping(s.builder, swap);
  swapping.returned(
      {swap.getArgument(identity ? 1 : 2), swap.getArgument(identity ? 2 : 1)});
  auto body = [&](ValueRange inputs) {
    s.local("halt", {}, s.unit, "stop_A", "A");
    return s.local("swap", inputs, {s.rng, s.rng}, "swap_B", "B");
  };
  auto child = [&] {
    auto *entry =
        s.protocol("child", {s.rng, s.rng}, {s.rng, s.rng}, {"A", "B"},
                   s.portRoles(2, {"B"}), s.portRoles(2, {"B"}));
    s.operation("protocol.return", body(entry->getArguments()));
  };
  if (apply && !name.ends_with("reverse"))
    child();
  auto inputs = s.builder.getArrayAttr(
      {s.roles({"A", "B"}), s.roles({"B"}), s.roles({"B"})});
  auto *entry = s.protocol("main", {s.index, s.rng, s.rng}, {s.rng, s.rng},
                           {"A", "B"}, inputs, s.portRoles(2, {"B"}));
  auto result = s.repeat(
      entry->getArgument(0), entry->getArguments().drop_front(), {}, "rounds",
      8,
      [&](Block *round) {
        auto args = round->getArguments().drop_front();
        if (!apply)
          return body(args);
        return llvm::to_vector(ValueRange(
            s.operation("protocol.apply", args, {s.rng, s.rng},
                        {s.symbol("callee", "child"), s.text("site", "child"),
                         s.builder.getNamedAttr("roles", s.roles({"A", "B"}))})
                ->getResults()));
      },
      {"A", "B"}, "B");
  s.operation("protocol.return", result);
  if (apply && name.ends_with("reverse"))
    child();
}
inline void conditionalCompletion(Source &s) {
  auto function = s.function("first", {s.index, s.index, s.field, s.field},
                             {s.field, s.field});
  exec::ScopedExecutionBuilder control(s.builder, function);
  auto result = control.loop(
      function.getArgument(1), function.getArgument(2),
      function.getArguments().drop_front(3), {}, {s.field, s.field}, true,
      "loop", [&](unsigned) {
        auto body = s.region({s.index, s.field, s.field},
                             {s.boolean, s.field, s.field});
        exec::ScopedExecutionBuilder inner(s.builder, body);
        auto done = inner.invoke(
            "exec.boolean", s.boolean, inner.scoped({}),
            {s.text("site", "finish"),
             s.builder.getNamedAttr("value", s.builder.getBoolAttr(false))});
        inner.complete({done[0], body.getArgument(3), body.getArgument(2)});
        return body;
      });
  control.returned(result);
  auto *entry = s.protocol("main", {s.index, s.index, s.field, s.field},
                           {s.field, s.field});
  s.operation("protocol.return", s.local("first", entry->getArguments(),
                                         {s.field, s.field}, "first"));
}
inline void execution(Source &s, StringRef mode) {
  s.binding("coordinates", "indices.empty", {});
  s.binding("random", "random.draw", {"bls12-381.fr"});
  s.binding("observe", "transcript.native.indexed.observe.data",
            {"merlin3.bls12-381.fr64be/0", "bool"});
  s.binding("challenge", "transcript.native.indexed.challenge",
            {"merlin3.bls12-381.fr64be/0"});
  constexpr StringLiteral observation =
      "010500000000000000001c000000000000007a6b632e6e61746976652d6f726967696e2d"
      "74656d706c6174652f300004000000000000006d61696e01000000000000000001000000"
      "00000000000106000000000000000007000000000000006d657373616765000700000000"
      "0000004f726967696e730007000000000000006d6573736167650007000000000000006d"
      "6573736167650001000000000000005000010000000000000056";
  constexpr StringLiteral challenge =
      "010500000000000000001c000000000000007a6b632e6e61746976652d6f726967696e2d"
      "74656d706c6174652f300004000000000000006d61696e01000000000000000001000000"
      "000000000001070000000000000000050000000000000071756572790005000000000000"
      "00526f756e6400040000000000000064726177000700000000000000696e7075745f3000"
      "150000000000000072616e646f6d2e626c7331322d3338312e66722f3000040000000000"
      "00006472617700010000000000000050";
  auto draw = s.function("draw", {s.rng, s.transcript, s.boolean},
                         {s.rng, s.transcript});
  exec::ScopedExecutionBuilder drawing(s.builder, draw);
  auto sample = s.invoke(drawing, "random", draw.getArgument(1),
                         {s.field, s.rng}, "random");
  auto coordinates =
      s.invoke(drawing, "coordinates", {},
               parseType("!algebra.indices", &s.context), "coordinates");
  auto observed =
      s.invoke(drawing, "observe",
               {draw.getArgument(2), draw.getArgument(3), coordinates[0]},
               s.transcript, "observe", {observation});
  auto queried = s.invoke(drawing, "challenge", {observed[0], coordinates[0]},
                          {s.field, s.transcript}, "challenge", {challenge});
  drawing.returned({sample[1], queried[1]});

  auto step =
      s.function("step", {s.rng, s.transcript, s.boolean, s.index, s.index},
                 {s.rng, s.transcript});
  exec::ScopedExecutionBuilder control(s.builder, step);
  auto tag = control.conditional(
      step.getArgument(3), {}, s.tag, "tag", [&](unsigned arm) {
        auto body = s.region({}, s.tag);
        exec::ScopedExecutionBuilder inner(s.builder, body);
        auto value =
            inner.invoke("exec.variant", s.tag, inner.scoped({}),
                         {s.text("alternative", arm == 0 ? "left" : "right"),
                          s.text("site", arm == 0 ? "left" : "right")});
        inner.complete(value);
        return body;
      })[0];
  Values matchInputs{step.getArgument(1), step.getArgument(2)};
  if (mode == "private-history")
    matchInputs.push_back(step.getArgument(3));
  auto same = control.match(
      tag, matchInputs, {s.rng, s.transcript}, {"left", "right"}, "match",
      [&](unsigned arm) {
        auto body =
            s.region(ValueRange(matchInputs).getTypes(), {s.rng, s.transcript});
        exec::ScopedExecutionBuilder inner(s.builder, body);
        Values result{body.getArgument(1), body.getArgument(2)};
        if (mode == "private-history" && arm == 0)
          result = s.call(inner, "draw", body.getArguments().drop_front(),
                          {s.rng, s.transcript}, "hidden");
        inner.complete(result);
        return body;
      });
  auto next = control.conditional(
      step.getArgument(3),
      {same[0], same[1], step.getArgument(3), step.getArgument(4),
       step.getArgument(5)},
      {s.rng, s.transcript}, "choice", [&](unsigned arm) {
        auto body = s.region({s.rng, s.transcript, s.boolean, s.index, s.index},
                             {s.rng, s.transcript});
        exec::ScopedExecutionBuilder inner(s.builder, body);
        if (arm == 1 && mode == "stop") {
          inner.reject("abort", "abort");
          return body;
        }
        Values result;
        if (arm == 0)
          result = inner.loop(
              body.getArgument(4), body.getArgument(5),
              body.getArguments().slice(1, 2), body.getArgument(3),
              {s.rng, s.transcript}, false, "loop", [&](unsigned) {
                auto iteration =
                    s.region({s.index, s.rng, s.transcript, s.boolean},
                             {s.rng, s.transcript});
                exec::ScopedExecutionBuilder loop(s.builder, iteration);
                auto drawn =
                    s.call(loop, "draw", iteration.getArguments().drop_front(2),
                           {s.rng, s.transcript}, "draw");
                if (mode == "nested_stop")
                  loop.reject("abort", "after_draw");
                else
                  loop.complete(drawn);
                return iteration;
              });
        else
          result = s.call(inner, "draw", body.getArguments().slice(1, 3),
                          {s.rng, s.transcript}, "once");
        inner.complete(result);
        return body;
      });
  control.returned(next);

  auto *child =
      s.protocol("child", {s.rng, s.transcript, s.boolean, s.index, s.index},
                 {s.rng, s.transcript});
  auto one = s.operation("data.index", {}, s.index,
                         {s.builder.getNamedAttr(
                             "value", s.builder.getIntegerAttr(s.index, 1))})
                 ->getResult(0);
  auto result = s.repeat(
      one, child->getArguments().take_front(2),
      child->getArguments().drop_front(2), "inner", 1, [&](Block *round) {
        return s.local("step", round->getArguments().drop_front(),
                       {s.rng, s.transcript});
      });
  s.operation("protocol.return", result);
  auto *entry = s.protocol(
      "main", {s.index, s.rng, s.transcript, s.boolean, s.index, s.index},
      {s.rng, s.transcript});
  auto done = s.repeat(
      entry->getArgument(0), entry->getArguments().slice(1, 2),
      entry->getArguments().drop_front(3), "outer", 8, [&](Block *round) {
        return llvm::to_vector(ValueRange(
            s.operation("protocol.apply", round->getArguments().drop_front(),
                        {s.rng, s.transcript},
                        {s.symbol("callee", "child"), s.text("site", "child"),
                         s.builder.getNamedAttr("roles", s.roles())})
                ->getResults()));
      });
  s.operation("protocol.return", done);
}
} // namespace zkc::test::resource_sources
#endif
