#include "mlir/AsmParser/AsmParser.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Interfaces/Collection.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::test;

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  auto field = algebra::FieldType::get(&context, "bls12-381.fr");
  auto group = algebra::GroupType::get(&context, "bls12-381.g1");
  auto index = IntegerType::get(&context, 64, IntegerType::Unsigned);
  auto vector = data::FieldVectorType::get(&context, field.getDomain());
  auto array = data::FieldArrayType::get(&context, field.getDomain(), 4);
  auto fixed = data::FixedVectorType::get(&context, field, 4);
  auto sequence = data::SequenceType::get(&context, vector);
  auto bytes = data::BytesType::get(&context);
  struct Expected {
    Type type;
    CollectionKind kind;
    Type element;
    unsigned rank;
    std::optional<uint64_t> extent;
  };
  for (const auto &expected :
       {Expected{vector, CollectionKind::FieldVector, field, 1, {}},
        Expected{data::GroupVectorType::get(&context, group.getDomain()),
                 CollectionKind::GroupVector,
                 group,
                 1,
                 {}},
        Expected{data::IndicesType::get(&context),
                 CollectionKind::Indices,
                 index,
                 1,
                 {}},
        Expected{data::FieldMatrixType::get(&context, field.getDomain()),
                 CollectionKind::FieldMatrix,
                 field,
                 2,
                 {}},
        Expected{array, CollectionKind::FieldArray, field, 1, 4},
        Expected{fixed, CollectionKind::FixedVector, field, 1, 4},
        Expected{sequence, CollectionKind::Sequence, vector, 1, {}},
        Expected{bytes,
                 CollectionKind::Bytes,
                 IntegerType::get(&context, 8, IntegerType::Unsigned),
                 1,
                 {}},
        Expected{data::FieldArrayType::get(&context, field.getDomain(), 0),
                 CollectionKind::FieldArray, field, 1, 0},
        Expected{data::FixedVectorType::get(&context, field, 0),
                 CollectionKind::FixedVector, field, 1, 0}}) {
    cases.run("collection observation: " +
                  take(encodeBoundType(expected.type, false)).spelling(),
              [&] {
                auto collection =
                    dyn_cast<CollectionTypeInterface>(expected.type);
                require(bool(collection), "collection interface missing");
                require(expected.type.getDialect().getNamespace() == "data",
                        "logical collections have more than one owner");
                require(collection.getCollectionKind() == expected.kind &&
                            collection.getElementType() == expected.element &&
                            collection.getRank() == expected.rank,
                        "nominal collection structure changed");
                for (unsigned axis = 0; axis < expected.rank; ++axis)
                  require(collection.getStaticExtent(axis) == expected.extent,
                          "unknown, zero, or exact extent changed");
                require(!collection.getStaticExtent(expected.rank),
                        "out-of-range axis acquired an extent");
              });
  }
  for (StringRef spelling :
       {"field_vector<\"bls12-381.fr\">", "group_vector<\"bls12-381.g1\">",
        "indices", "field_matrix<\"bls12-381.fr\">",
        "field_array<\"bls12-381.fr\", 4>",
        "fixed_vector<!algebra.field<\"bls12-381.fr\">, 4>"})
    cases.run("removed collection owner refuses: " + spelling.str(), [&] {
      ScopedDiagnosticHandler quiet(&context,
                                    [](Diagnostic &) { return success(); });
      require(!parseType(("!algebra." + spelling).str(), &context),
              "a removed Algebra collection spelling remains accepted");
      require(bool(parseType(("!data." + spelling).str(), &context)),
              "the Data collection spelling is unavailable");
    });
  for (StringRef name :
       {"array_from_elements", "array_at", "finite_fold", "finite_collect"})
    cases.run("structural operation has one owner: " + name.str(), [&] {
      require(
          !OperationName(("algebra." + name).str(), &context).isRegistered(),
          "a removed Algebra operation remains registered");
      require(OperationName(("data." + name).str(), &context).isRegistered(),
              "the structural Data operation is unavailable");
    });
  cases.run("structural observation preserves admission boundaries", [&] {
    require(finite::elementType(vector) == field &&
                finite::elementType(array) == field &&
                finite::elementType(sequence) == vector,
            "existing finite collection admission changed");
    require(!finite::elementType(fixed),
            "collection interface granted FixedVector finite admission");
    require(!finite::elementType(bytes),
            "collection interface granted Bytes finite admission");
    require(!isa<CollectionTypeInterface>(field),
            "scalar acquired collection structure");
    auto tensor = RankedTensorType::get({4}, field);
    require(!isa<CollectionTypeInterface>(tensor),
            "builtin tensor acquired nominal collection structure");
    auto bound = encodeBoundType(tensor, false);
    require(!bound, "builtin tensor shape still determines logical identity");
    llvm::consumeError(bound.takeError());
    auto byteTensor = RankedTensorType::get(
        {ShapedType::kDynamic},
        IntegerType::get(&context, 8, IntegerType::Unsigned));
    auto encodedBytes = encodeBoundType(byteTensor, false);
    require(!encodedBytes && !isa<CollectionTypeInterface>(byteTensor),
            "builtin byte tensor acquired a nominal Bytes identity");
    llvm::consumeError(encodedBytes.takeError());
    require(!(take(encodeBoundType(array, false)) ==
              take(encodeBoundType(fixed, false))),
            "equal-sized aggregate families collapsed");
  });
  cases.run("extent evidence preserves vector type and representation", [&] {
    auto module = parseSourceString<ModuleOp>(R"mlir(
!V = !data.field_vector<"bls12-381.fr">
!A = !data.field_array<"bls12-381.fr", 4>
module { "protocol.module"() ({
 func.func private @identity(%xs: !V, %fixed: !A) -> !V { func.return %xs : !V }
 "protocol.func"() ({ ^entry(%xs: !V):
   "protocol.return"(%xs) : (!V) -> ()
 }) {sym_name="main",function_type=(!V)->!V,roles=["P"],
     input_roles=[["P"]],output_roles=[["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
)mlir",
                                              &context);
    require(bool(module), "nominal collection fixture refused");
    func::FuncOp helper;
    module->walk([&](func::FuncOp op) { helper = op; });
    require(bool(helper), "fixture helper missing");
    auto xs = helper.getArgument(0), ys = helper.getArgument(1);
    auto logical = take(encodeBoundType(xs.getType(), false));
    auto physical = take(defaultRepresentation(logical));
    auto physicalType = decodeBoundType(&context, physical);
    require(bool(physicalType), "physical collection carrier missing");
    require(!finite::provesEqualExtent(xs, 0, ys, 0),
            "matching element types invented an extent");
    helper->setAttr("data.preconditions",
                    ArrayAttr::get(&context, {data::EqualExtentAttr::get(
                                                 &context, 0, 0, 1, 0)}));
    require(succeeded(finite::verifyPreconditions(helper)),
            "shared extent premise was refused");
    require(finite::provesEqualExtent(xs, 0, ys, 0),
            "shared extent premise was ignored");
    require(xs.getType() == vector && xs.getType() != ys.getType() &&
                !cast<CollectionTypeInterface>(xs.getType()).getStaticExtent(0),
            "value evidence rewrote a nominal type");
    require(take(encodeBoundType(xs.getType(), false)) == logical &&
                take(defaultRepresentation(
                    take(encodeBoundType(xs.getType(), false)))) == physical &&
                take(encodeBoundType(physicalType, true)) == physical &&
                decodeBoundType(&context, logical) == vector &&
                cast<runtime::RepresentedType>(physicalType).getLogical() ==
                    vector,
            "value evidence changed logical or physical encoding");
  });
  return cases.result();
}
