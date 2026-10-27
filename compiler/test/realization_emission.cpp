#include "../lib/Transforms/CollectionRealization.h"
#include "../lib/Transforms/RealizationEmission.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::mathematical;
using namespace zkc::test;

namespace {
OwningOpRef<ModuleOp> module(MLIRContext &context) {
  auto result = parseSourceString<ModuleOp>(R"mlir(
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%n: ui64):
   "protocol.return"(%n) : (ui64) -> ()
 }) {sym_name="main",function_type=(ui64)->ui64,roles=["P"],
     input_roles=[["P"]],output_roles=[["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
)mlir",
                                            &context);
  require(bool(result), "emission fixture did not parse");
  return result;
}

std::string spelling(Operation *op) {
  std::string result;
  llvm::raw_string_ostream stream(result);
  op->print(stream);
  return result;
}

func::FuncOp function(OpBuilder &builder, protocol_ir::ProtocolModuleOp unit,
                      StringRef name, TypeRange inputs, Type output) {
  builder.setInsertionPointToEnd(&unit.getBody().front());
  SmallVector<Type> arguments{runtime::ScopeType::get(builder.getContext())};
  llvm::append_range(arguments, inputs);
  auto result = func::FuncOp::create(
      builder, unit.getLoc(), name,
      builder.getFunctionType(
          arguments, {exec::OutcomeType::get(builder.getContext(), {output})}));
  result.setNoInline(true);
  result->setAttr("runtime.origin",
                  builder.getArrayAttr(
                      {builder.getStringAttr(name), builder.getArrayAttr({})}));
  builder.setInsertionPointToEnd(result.addEntryBlock());
  return result;
}
struct Emitted {
  Operation *operation;
  Value value;
};
Emitted emit(RealizationEmitter &emitter, exec::ScopedExecutionBuilder &control,
             OpBuilder &builder, StringRef site,
             const protocol::BindingApplication &application, ValueRange inputs,
             Type output, ArrayRef<std::string> parameters = {}) {
  auto reference = emitter.binding(builder, control.getLocation(), application);
  SmallVector<Attribute> encoded;
  for (const auto &parameter : parameters)
    encoded.push_back(builder.getStringAttr(parameter));
  auto *block = builder.getInsertionBlock();
  auto values = control.invoke(
      "exec.apply", {output}, control.scoped(inputs),
      {builder.getNamedAttr("binding", reference),
       builder.getNamedAttr("site", builder.getStringAttr(site)),
       builder.getNamedAttr("parameters", builder.getArrayAttr(encoded))});
  auto *operation = block->getTerminator()->getPrevNode();
  require(operation && isa<exec::ApplyOp>(operation) &&
              succeeded(verify(operation)),
          "scoped invocation failed resolved signature validation");
  return {operation, values.front()};
}

void checkPorts(const protocol::BindingApplication &application,
                TypeRange inputs, Type output) {
  auto resolved = take(protocol::resolveBinding(application, false));
  require(resolved.inputs.size() == inputs.size() &&
              resolved.outputs.size() == 1,
          "collection contract arity changed");
  for (auto [actual, expected] : llvm::zip(inputs, resolved.inputs))
    require(take(protocol::encodeBoundType(actual, false)) == expected,
            "collection contract input changed");
  require(take(protocol::encodeBoundType(output, false)) == resolved.outputs[0],
          "collection contract output changed");
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  auto field = algebra::FieldType::get(&context, "bls12-381.fr");
  auto vector = algebra::FieldVectorType::get(&context, field.getDomain());
  auto group = algebra::GroupType::get(&context, "bls12-381.g1");
  auto index = IntegerType::get(&context, 64, IntegerType::Unsigned);
  cases.run("byte collection observations do not grant finite recipes", [&] {
    require(!collectionRealization(data::BytesType::get(&context)),
            "byte observations acquired finite execution admission");
  });
  struct Family {
    Type type, element;
    const char *length, *get, *empty, *append;
    unsigned rank;
    std::optional<uint64_t> extent;
  };
  for (const auto &family :
       {Family{vector,
               field,
               "vector.length",
               "vector.get",
               "vector.empty",
               "vector.append",
               1,
               {}},
        Family{algebra::GroupVectorType::get(&context, group.getDomain()),
               group,
               "curve.length",
               "curve.get",
               "curve.empty",
               "curve.append",
               1,
               {}},
        Family{algebra::IndicesType::get(&context),
               index,
               "indices.length",
               "indices.at",
               "indices.empty",
               "indices.append",
               1,
               {}},
        Family{data::SequenceType::get(&context, vector),
               vector,
               "sequence.length",
               "sequence.at",
               "sequence.empty",
               "sequence.append",
               1,
               {}},
        Family{algebra::FieldMatrixType::get(&context, field.getDomain()),
               field,
               "matrix.dimension",
               "matrix.get",
               nullptr,
               nullptr,
               2,
               {}},
        Family{algebra::FieldArrayType::get(&context, field.getDomain(), 4),
               field, nullptr, "field_array.get", "vector.empty",
               "vector.append", 1, 4},
        Family{algebra::FieldArrayType::get(&context, field.getDomain(), 0),
               field, nullptr, "field_array.get", "vector.empty",
               "vector.append", 1, 0}}) {
    cases.run(
        "collection realization: " +
            take(protocol::encodeBoundType(family.type, false)).spelling(),
        [&] {
          auto recipe = collectionRealization(family.type);
          require(bool(recipe), "admitted collection has no recipe");
          require(recipe->element == family.element &&
                      recipe->rank == family.rank &&
                      recipe->staticExtent == family.extent,
                  "collection observation changed");
          auto storage = family.extent ? Type(vector) : family.type;
          require(recipe->storage == storage,
                  "collection storage family changed");
          auto candidate = module(context);
          auto unit = cast<protocol_ir::ProtocolModuleOp>(
              candidate->getBody()->front());
          OpBuilder builder(&context);
          RealizationEmitter emitter(unit, "_collection_binding_");
          auto helper = function(
              builder, unit, "collection",
              {family.type, family.element, index, index, storage}, index);
          auto args = helper.getArguments().drop_front();
          exec::ScopedExecutionBuilder control(builder, helper);
          unsigned site = 0;
          auto emit = [&](const std::optional<protocol::BindingApplication>
                              &application,
                          StringRef contract, ValueRange inputs, Type output,
                          llvm::ArrayRef<std::string> parameters = {}) {
            require(application && application->contract == contract &&
                        application->implementation.empty(),
                    "unexpected collection realization contract");
            checkPorts(*application, inputs.getTypes(), output);
            return ::emit(emitter, control, builder,
                          "collection_" + std::to_string(site++), *application,
                          inputs, output, parameters)
                .value;
          };
          if (family.extent) {
            require(!recipe->length, "array length must stay intrinsic");
            emit(protocol::BindingApplication{"index.constant", {}, ""},
                 "index.constant", {}, index, {std::to_string(*family.extent)});
          } else {
            for (unsigned axis = 0; axis < family.rank; ++axis)
              emit(recipe->length, family.length, args[0], index,
                   family.rank == 2
                       ? llvm::ArrayRef<std::string>{std::to_string(axis)}
                       : llvm::ArrayRef<std::string>{});
          }
          SmallVector<Value> lookup{args[0], args[2]};
          if (family.rank == 2)
            lookup.push_back(args[3]);
          emit(recipe->get, family.get, lookup, family.element);
          if (family.empty) {
            auto empty = emit(recipe->empty, family.empty, {}, storage);
            auto appended =
                emit(recipe->append, family.append, {empty, args[1]}, storage);
            if (family.extent)
              emit(recipe->wrap, "field_array.from_vector", appended,
                   family.type);
            else
              require(!recipe->wrap,
                      "dynamic collection gained a wrapping operation");
          } else {
            require(!recipe->empty && !recipe->append && !recipe->wrap,
                    "matrix gained a collection construction recipe");
          }
          control.returned(args[2]);
          require(succeeded(verify(*candidate)),
                  "collection emission failed candidate admission");
        });
  }
  cases.run("observation alone does not grant a realization", [&] {
    require(!collectionRealization(field) &&
                !collectionRealization(
                    algebra::FixedVectorType::get(&context, field, 4)),
            "unadmitted collection gained a realization");
  });
  for (StringRef prefix : {"_finite_binding_", "_map_binding_"}) {
    cases.run(prefix + "collisions, deduplication and source pins", [&] {
      auto original = module(context);
      auto sourceUnit =
          cast<protocol_ir::ProtocolModuleOp>(original->getBody()->front());
      OpBuilder builder(&context);
      builder.setInsertionPointToStart(&sourceUnit.getBody().front());
      auto pinned = runtime::BindingOp::create(
          builder, sourceUnit.getLoc(), prefix.str() + "0", "field.add",
          builder.getArrayAttr({builder.getStringAttr(field.getDomain())}),
          "arkworks/field.add", mlir::ArrayAttr{});
      auto authored = function(builder, sourceUnit, prefix.str() + "1",
                               {field, field}, field);
      exec::ScopedExecutionBuilder authoredBody(builder, authored);
      authoredBody.returned(authored.getArgument(1));
      auto before = spelling(*original);
      auto pinnedBefore = spelling(pinned);
      OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(original->clone()));
      auto unit =
          cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
      RealizationEmitter emitter(unit, prefix);
      // Other producer work may add symbols after emitter construction.
      builder.setInsertionPointToStart(&unit.getBody().front());
      runtime::BindingOp::create(builder, unit.getLoc(), prefix.str() + "2",
                                 "index.constant", builder.getArrayAttr({}), "",
                                 mlir::ArrayAttr{});
      auto helper = cast<func::FuncOp>(
          SymbolTable::lookupSymbolIn(unit, prefix.str() + "1"));
      helper.front().back().erase();
      helper.front().back().erase();
      builder.setInsertionPointToEnd(&helper.front());
      exec::ScopedExecutionBuilder control(builder, helper);
      protocol::BindingApplication application{
          "field.add", {field.getDomain().str()}, ""};
      auto emit = [&](StringRef site) {
        auto value = ::emit(emitter, control, builder, site, application,
                            helper.getArguments().drop_front(), field);
        auto *op = value.operation;
        require(op->getParentOp() == helper &&
                    op->getAttrOfType<StringAttr>("site").getValue() == site,
                "emitter lost function or occurrence identity");
        return take(protocol::operationBinding(op));
      };
      auto first = emit("authored_finite_0");
      auto second = emit("map_1");
      require(first.name == prefix.str() + "3" && first.name == second.name &&
                  first.application.implementation.empty(),
              "binding collision or generated deduplication changed");
      application.implementation = "arkworks/field.add";
      auto constrained = emit("explicit_2");
      require(constrained.name != first.name &&
                  constrained.name != pinned.getSymName() &&
                  constrained.application.implementation ==
                      application.implementation &&
                  emit("explicit_3").name == constrained.name,
              "exact generated pin was lost or merged with source binding");
      require(spelling(*original) == before &&
                  spelling(SymbolTable::lookupSymbolIn(
                      unit, prefix.str() + "0")) == pinnedBefore,
              "producer mutated the source or its retained named pin");
      control.returned(helper.getArgument(1));
      require(succeeded(verify(*candidate)),
              "binding emission failed candidate admission");
    });
  }
  cases.run(
      "static arguments distinguish bindings; parameters stay per use", [&] {
        auto candidate = module(context);
        auto unit =
            cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
        OpBuilder builder(&context);
        RealizationEmitter emitter(unit, "_constant_binding_");
        auto helper = function(builder, unit, "constants", {}, field);
        exec::ScopedExecutionBuilder control(builder, helper);
        auto other = algebra::FieldType::get(&context, "bn254.fr");
        auto emit = [&](algebra::FieldType type, StringRef parameter,
                        StringRef site) {
          return ::emit(emitter, control, builder, site,
                        {"field.constant", {type.getDomain().str()}, ""}, {},
                        type, {parameter.str()});
        };
        auto one = emit(field, "1", "one");
        auto two = emit(field, "2", "two");
        auto differentField = emit(other, "1", "other_field");
        auto first = take(protocol::operationBinding(one.operation));
        require(
            first.name ==
                    take(protocol::operationBinding(two.operation)).name &&
                first.name !=
                    take(protocol::operationBinding(differentField.operation))
                        .name &&
                one.operation->getAttr("parameters") !=
                    two.operation->getAttr("parameters"),
            "deduplication changed a static domain or occurrence parameters");
        control.returned(one.value);
        require(succeeded(verify(*candidate)),
                "constant candidate failed admission");
      });
  return cases.result();
}
