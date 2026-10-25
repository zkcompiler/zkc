#include "../lib/Transforms/CollectionRealization.h"
#include "../lib/Transforms/RealizationEmission.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Bindings.h"
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

local::FuncOp function(OpBuilder &builder, protocol_ir::ProtocolModuleOp unit,
                       StringRef name, TypeRange inputs, Type output) {
  builder.setInsertionPointToEnd(&unit.getBody().front());
  auto result =
      local::FuncOp::create(builder, unit.getLoc(), name,
                            builder.getFunctionType(inputs, TypeRange{output}));
  result->setAttr("logical_origin",
                  builder.getArrayAttr(
                      {builder.getStringAttr(name), builder.getArrayAttr({})}));
  auto *entry = result.addEntryBlock();
  builder.setInsertionPointToEnd(entry);
  return result;
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
          auto args = helper.getArguments();
          unsigned site = 0;
          auto emit = [&](const std::optional<protocol::BindingApplication>
                              &application,
                          StringRef contract, ValueRange inputs, Type output,
                          llvm::ArrayRef<std::string> parameters = {}) {
            require(application && application->contract == contract &&
                        application->implementation.empty(),
                    "unexpected collection realization contract");
            checkPorts(*application, inputs.getTypes(), output);
            auto *op = emitter.emit(builder, helper.getLoc(),
                                    "collection_" + std::to_string(site++),
                                    *application, inputs, TypeRange{output},
                                    parameters);
            require(succeeded(protocol::verifyBoundOperation(op, false)),
                    "emitted operation failed resolved contract check");
            return op->getResult(0);
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
          local::ReturnOp::create(builder, helper.getLoc(), args[2]);
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
      local::ReturnOp::create(builder, authored.getLoc(),
                              authored.getArgument(0));
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
      auto helper = cast<local::FuncOp>(
          SymbolTable::lookupSymbolIn(unit, prefix.str() + "1"));
      builder.setInsertionPoint(helper.getBody().front().getTerminator());
      protocol::BindingApplication application{
          "field.add", {field.getDomain().str()}, ""};
      auto emit = [&](StringRef site) {
        auto *op = emitter.emit(builder, helper.getLoc(), site, application,
                                helper.getArguments(), TypeRange{field});
        require(op->getBlock() == &helper.getBody().front() &&
                    op->getAttrOfType<StringAttr>("site").getValue() == site &&
                    succeeded(protocol::verifyBoundOperation(op, false)),
                "emitter lost insertion point, site or resolved signature");
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
        auto other = algebra::FieldType::get(&context, "bn254.fr");
        auto emit = [&](algebra::FieldType type, StringRef parameter,
                        StringRef site) {
          auto *op =
              emitter.emit(builder, helper.getLoc(), site,
                           {"field.constant", {type.getDomain().str()}, ""}, {},
                           TypeRange{type}, {parameter.str()});
          require(
              succeeded(protocol::verifyBoundOperation(op, false)),
              "constant failed declaration signature or parameter validation");
          return op;
        };
        auto *one = emit(field, "1", "one");
        auto *two = emit(field, "2", "two");
        auto *differentField = emit(other, "1", "other_field");
        auto first = take(protocol::operationBinding(one));
        require(
            first.name == take(protocol::operationBinding(two)).name &&
                first.name !=
                    take(protocol::operationBinding(differentField)).name &&
                one->getAttr("parameters") != two->getAttr("parameters"),
            "deduplication changed a static domain or occurrence parameters");
        local::ReturnOp::create(builder, helper.getLoc(), one->getResult(0));
        require(succeeded(verify(*candidate)),
                "constant candidate failed admission");
      });
  return cases.result();
}
