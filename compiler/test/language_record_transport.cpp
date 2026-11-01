#include "support/NativeCases.h"
#include "zkc/Language/Builtins.h"
#include "zkc/Language/Layout.h"
#include "zkc/Language/Names.h"
#include "llvm/ADT/STLExtras.h"
#include <limits>
using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
using Schema = std::shared_ptr<Layout>;
Schema scalar() {
  auto result = std::make_shared<Layout>();
  result->type.kind = Type::Kind::Index;
  result->leaves = {"index"};
  return result;
}
Schema product(StringRef name, ArrayRef<Schema> fields, unsigned custody = 0) {
  auto result = std::make_shared<Layout>();
  result->type.kind = Type::Kind::LogicalRecord;
  result->type.domain = name.str();
  result->custody = custody != 0;
  result->custodyCount = custody;
  for (unsigned i = 0; i < custody; ++i)
    result->leaves.push_back("resource_unit:test");
  for (auto field : fields) {
    result->fields.push_back({std::to_string(result->fields.size()),
                              field,
                              unsigned(result->leaves.size()),
                              {}});
    llvm::append_range(result->leaves, field->leaves);
  }
  return result;
}
ValuePlacement placed(const Schema &schema, std::vector<unsigned> roles,
                      std::vector<ValuePlacement> fields) {
  return ProductPlacement{typeIdentity(schema->type), std::move(roles),
                          std::move(fields)};
}
Expected<ProtocolPortLayout> observe(Schema schema, ValuePlacement placement,
                                     Limits limits = {}) {
  auto remaining = limits.work;
  return observeProtocolPort(schema, placement, remaining, limits);
}
void component(const ProtocolPortComponent &value, ArrayRef<unsigned> path,
               unsigned local, unsigned role, ProtocolComponentFacet facet,
               unsigned native) {
  require(ArrayRef(value.fieldPath) == path && value.localLeaf == local &&
              value.role == role && value.facet == facet &&
              value.nativeIndex == native,
          "typed component coordinate differs");
}
Type natural(uint64_t value) {
  Type result(Type::Kind::Natural);
  result.dimension = Natural::constant(value);
  return result;
}
Schema oracle() {
  Type rowType(Type::Kind::Field, "bls12-381.fr");
  auto kind = take(builtinType("oracle.table", {rowType, natural(4)}));
  auto type = take(builtinType("oracle", {kind}));
  auto data = scalar();
  data->type = take(builtinType("vector", {rowType}));
  data->leaves = {take(builtinLayout(data->type)).spelling()};
  auto result = std::make_shared<Layout>();
  result->type = type;
  result->oracleData = data;
  auto row = take(zkc::protocol::parseBoundType("field:bls12-381.fr", false));
  auto args = std::vector<zkc::protocol::TypeArgument>{
      zkc::protocol::TypeArgument::typeArgument(row),
      zkc::protocol::TypeArgument::naturalArgument(4)};
  auto signature = take(zkc::protocol::oracleKindSignature("table", args));
  result->leaves = {OracleLayout{{"table", args, signature}, {}}};
  return result;
}
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run("ordinary structural schemas retain field-specific placement", [] {
    auto tuple = product("", {scalar(), scalar()});
    tuple->type = Type(Type::Kind::Tuple);
    tuple->type.arguments = {Type(Type::Kind::Index), Type(Type::Kind::Index)};
    auto placement =
        placed(tuple, {0, 1}, {DataPlacement{{1}}, DataPlacement{{0}}});
    auto result = take(observe(tuple, placement));
    require(result.size() == 2 && result.components.size() == 2,
            "ordinary structural placement lost its leaves");
    component(result.components[0], {0}, 0, 1, ProtocolComponentFacet::Data, 0);
    component(result.components[1], {1}, 0, 0, ProtocolComponentFacet::Data, 1);
    auto local = take(observe(tuple, DataPlacement{{0}}));
    require(local.size() == 2 && local.components[0].role == 0 &&
                local.components[1].role == 0,
            "field placement changed ordinary static schema identity");
    std::get<ProductPlacement>(placement.value).arguments = {1, 0};
    refuses(observe(tuple, placement), "source.placement");
  });
  cases.run("zero array templates are validated without native storage", [] {
    auto array = std::make_shared<Layout>();
    array->type = Type(Type::Kind::Array);
    array->type.arguments = {Type(Type::Kind::Index)};
    array->type.dimension = Natural::constant(0);
    array->element = scalar();
    auto placement = placed(array, {1}, {DataPlacement{{1}}});
    auto result = take(observe(array, placement));
    require(result.size() == 0 && result.components.empty(),
            "zero array template acquired native storage");
    std::get<ProductPlacement>(placement.value).fields[0] =
        ProductPlacement{typeIdentity(array->element->type), {1}, {}};
    refuses(observe(array, placement), "source.placement");
    array->element.reset();
    refuses(observe(array, DataPlacement{{1}}), "source.layout");
  });
  cases.run("ordinary-only fields keep independent components and shared slots",
            [] {
              auto schema = product("Pair", {scalar(), scalar()});
              auto result = take(observe(
                  schema, placed(schema, {2, 0, 1},
                                 {DataPlacement{{0, 2}}, DataPlacement{{1}}})));
              require(result.size() == 2 && result.components.size() == 3,
                      "component count was confused with physical arity");
              component(result.components[0], {0}, 0, 0,
                        ProtocolComponentFacet::Data, 0);
              component(result.components[1], {0}, 0, 2,
                        ProtocolComponentFacet::Data, 0);
              component(result.components[2], {1}, 0, 1,
                        ProtocolComponentFacet::Data, 1);
            });
  cases.run("nested role maps and zero-field children retain exact paths", [] {
    auto empty = product("Empty", {});
    auto child = product("Child", {scalar(), empty});
    auto schema = product("Outer", {scalar(), child});
    auto childPlacement =
        placed(child, {2, 0}, {DataPlacement{{2}}, placed(empty, {0}, {})});
    auto result =
        take(observe(schema, placed(schema, {0, 1, 2},
                                    {DataPlacement{{1}}, childPlacement})));
    require(result.body->fields[1].layout->fields.size() == 2 &&
                result.size() == 2 && result.components.size() == 2,
            "empty nested field was erased");
    component(result.components[1], {1, 0}, 0, 2, ProtocolComponentFacet::Data,
              1);
  });
  cases.run("two holders and multi-receiver handles have no root family", [] {
    auto schema = product("Sources", {oracle(), oracle(), scalar()});
    auto result = take(
        observe(schema, placed(schema, {0, 1, 2, 3},
                               {OraclePlacement{0, {2, 3}},
                                OraclePlacement{1, {2}}, DataPlacement{{3}}})));
    require(result.size() == 5 && result.components.size() == 6,
            "handle expansion lost a participant");
    component(result.components[0], {0}, 0, 0,
              ProtocolComponentFacet::OracleData, 0);
    component(result.components[2], {0}, 0, 3,
              ProtocolComponentFacet::OracleAnchor, 1);
    component(result.components[3], {1}, 0, 1,
              ProtocolComponentFacet::OracleData, 2);
    component(result.components[4], {1}, 0, 2,
              ProtocolComponentFacet::OracleAnchor, 3);
    require(take(result.select({0}, true)).offset == 1 &&
                take(result.select({1}, true)).offset == 3,
            "oracle projection ignored per-field ABI expansion");
  });
  cases.run(
      "holder position does not reorder component roles or ABI slots", [] {
        for (unsigned holder : {0u, 1u, 2u}) {
          std::vector<unsigned> receivers;
          for (unsigned role = 0; role != 3; ++role)
            if (role != holder)
              receivers.push_back(role);
          auto result =
              take(observe(oracle(), OraclePlacement{holder, receivers}));
          require(result.size() == 2 && result.components.size() == 3,
                  "holder placement changed physical or component arity");
          for (unsigned role = 0; role != 3; ++role)
            component(result.components[role], {}, 0, role,
                      role == holder ? ProtocolComponentFacet::OracleData
                                     : ProtocolComponentFacet::OracleAnchor,
                      role == holder ? 0 : 1);
        }
      });
  cases.run("empty nested custody expands in telescope order", [] {
    auto empty = product("Restricted", {}, 2);
    auto outer = product("OuterRestricted", {empty, scalar()}, 3);
    auto result = take(observe(
        outer, placed(outer, {2, 0, 1},
                      {placed(empty, {1, 2}, {}), DataPlacement{{0}}})));
    require(result.size() == 6 && result.components.size() == 6 &&
                result.body->fields[0].offset == 3,
            "custody was erased or omitted from offsets");
    component(result.components[0], {}, 0, 2, ProtocolComponentFacet::Custody,
              0);
    component(result.components[3], {0}, 0, 1, ProtocolComponentFacet::Custody,
              3);
    component(result.components[4], {0}, 1, 2, ProtocolComponentFacet::Custody,
              4);
    require(*result.leaves[3].leaf.data() == *result.leaves[4].leaf.data(),
            "participant indices entered static native unit identity");
  });
  cases.run("zero arrays retain nominal element schemas without storage", [] {
    auto captured = take(capture({{"m", R"(
module m;
struct Empty<T:Type>{pub zero:(),hidden:()}
protocol Run roles(P)(x:[Empty<index>;0]@P)->(out:[Empty<index>;0]@P){
  return(out=x);
}
)",
                                   "zero-array.zkc"}}));
    auto checked = take(analyze(captured).checkedProject());
    const auto &decls = checked.declarations();
    auto run = llvm::find_if(
        decls, [](const auto &decl) { return decl.name == "Run"; });
    require(run != decls.end(), "missing zero-array protocol");
    Layouts layouts(checked);
    auto layout = take(layouts.get(run->inputs[0].type));
    require(layout->element && layout->leaves.empty() &&
                layout->fields.empty() && layout->element->fields.size() == 2 &&
                !layout->element->fields[1].isPublic &&
                layout->element->type.arguments ==
                    std::vector<Type>{Type(Type::Kind::Index)},
            "zero storage erased the instantiated element schema");
    auto other = run->inputs[0].type;
    other.arguments[0].arguments[0] = Type(Type::Kind::Boolean);
    auto alternate = take(layouts.get(other));
    uint64_t work = 100000;
    LayoutIdentities identities(work);
    require(take(identities.get(*layout)) != take(identities.get(*alternate)),
            "phantom zero-array elements share schema identity");
  });
  cases.run("explicit restriction and constructor authority stay separate", [] {
    auto captured = take(capture(
        {{"m", "module m;#[affine] struct Permit{}", "restriction.zkc"}}));
    auto checked = take(analyze(captured).checkedProject());
    Layouts layouts(checked);
    auto layout = take(layouts.get(Type(Type::Kind::Record, "m::Permit")));
    require(layout->restriction == Resource::Affine && !layout->sealed &&
                !layout->constructible && layout->custodyCount == 1 &&
                !layout->permissions.copy && layout->permissions.drop,
            "restriction, authority, and physical custody were conflated");
  });
  cases.run(
      "root-wide placement cannot replace product or handle placement", [] {
        auto schema = product("Pair", {scalar(), scalar()});
        refuses(observe(schema, DataPlacement{{0, 1}}), "source.placement");
        refuses(observe(oracle(), DataPlacement{{0, 1}}), "source.layout");
        refuses(observe(scalar(), OraclePlacement{0, {1}}), "source.placement");
      });
  cases.run("nominal or field coverage drift refuses", [] {
    auto schema = product("Pair", {scalar(), scalar()});
    refuses(observe(schema,
                    ProductPlacement{"Other",
                                     {0, 1},
                                     {DataPlacement{{0}}, DataPlacement{{1}}}}),
            "source.placement");
    refuses(observe(schema, placed(schema, {0, 1}, {DataPlacement{{0}}})),
            "source.placement");
  });
  cases.run("field formulas reject swapped components and changed holders", [] {
    auto schema = product("Sources", {oracle(), oracle(), scalar()});
    schema->roleParameters = {"A", "B", "V"};
    schema->fields[0].placement = OraclePlacement{0, {2}};
    schema->fields[1].placement = OraclePlacement{1, {2}};
    schema->fields[2].placement = DataPlacement{{2}};
    auto expected = placed(
        schema, {1, 0, 2},
        {OraclePlacement{1, {2}}, OraclePlacement{0, {2}}, DataPlacement{{2}}});
    take(observe(schema, expected));
    auto swapped = expected;
    auto &fields = std::get<ProductPlacement>(swapped.value).fields;
    std::swap(fields[0], fields[1]);
    refuses(observe(schema, swapped), "source.placement");
    swapped = expected;
    auto &changed = std::get<ProductPlacement>(swapped.value).fields;
    std::get<OraclePlacement>(changed[0].value).holder = 0;
    refuses(observe(schema, swapped), "source.placement");
  });
  cases.run("row bounds cannot attach to ordinary fields", [] {
    auto schema = product("Data", {scalar()});
    schema->fields[0].maximumRows = 3;
    refuses(observe(schema, placed(schema, {0}, {DataPlacement{{0}}})),
            "source.layout");
  });
  cases.run("one ordinary custody unit cannot represent multiple owners", [] {
    auto schema = std::make_shared<Layout>();
    schema->type = Type(Type::Kind::Record, "Permit");
    schema->custody = true;
    schema->custodyCount = 1;
    schema->leaves = {"resource_unit:permit"};
    refuses(observe(schema, DataPlacement{{0, 1}}), "source.placement");
  });
  cases.run("missing custody fragment refuses", [] {
    auto empty = product("Restricted", {}, 1);
    refuses(observe(empty, placed(empty, {0, 1}, {})), "source.layout");
  });
  cases.run("mixed nested fragment family refuses", [] {
    auto child = product("Restricted", {}, 2);
    auto outer = product("Outer", {child});
    refuses(observe(outer, placed(outer, {0, 1}, {placed(child, {1, 2}, {})})),
            "source.roles");
  });
  cases.run("missing receiver refuses", [] {
    refuses(observe(oracle(), OraclePlacement{0, {}}), "source.roles");
  });
  cases.run("invalid physical product coverage refuses", [] {
    auto schema = product("Pair", {scalar(), scalar()});
    schema->fields[1].offset = 0;
    refuses(observe(schema, placed(schema, {0, 1},
                                   {DataPlacement{{0}}, DataPlacement{{1}}})),
            "source.layout");
  });
  cases.run("component expansion obeys work and leaf limits", [] {
    auto schema = product("Pair", {scalar(), scalar()});
    Limits limits;
    limits.aggregateLeaves = 1;
    refuses(observe(schema,
                    placed(schema, {0, 1},
                           {DataPlacement{{0}}, DataPlacement{{1}}}),
                    limits),
            "source.limit");
    limits = {};
    limits.work = 1;
    refuses(observe(schema,
                    placed(schema, {0, 1},
                           {DataPlacement{{0}}, DataPlacement{{1}}}),
                    limits),
            "source.limit");
  });
  return cases.result();
}
