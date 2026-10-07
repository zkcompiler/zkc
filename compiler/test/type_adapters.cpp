#include "mlir/AsmParser/AsmParser.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/TypeAdapters.h"
#include "llvm/ADT/StringSet.h"

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::test;

namespace {
// A loaded namespace alone must not make native type construction fatal.
class EmptyAlgebraDialect : public Dialect {
public:
  explicit EmptyAlgebraDialect(MLIRContext *context)
      : Dialect(getDialectNamespace(), context,
                TypeID::get<EmptyAlgebraDialect>()) {}
  static StringRef getDialectNamespace() { return "algebra"; }
};

void roundTrip(MLIRContext &context, const BoundType &bound, bool physical) {
  auto native = decodeBoundType(&context, bound);
  require(bool(native), "decoding refused an admitted type");
  auto encoded = take(encodeBoundType(native, physical));
  require(encoded == bound, "logical identity or representation changed");
  require(decodeBoundType(&context, encoded) == native,
          "native type identity changed");
}
} // namespace

int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();

  cases.run("unique immutable constructor installation", [&] {
    llvm::StringSet<> constructors;
    for (auto table : type_adapters::installedAdapters())
      for (const auto &adapter : table) {
        require(constructors.insert(adapter.constructor).second,
                "duplicate constructor adapter");
        require(adapter.decode && adapter.encode, "missing callback");
        require(type_adapters::findAdapter(adapter.constructor) == &adapter,
                "constructor lookup changed ownership");
      }
    require(!constructors.empty(), "empty adapter installation");
    require(!type_adapters::findAdapter("uninstalled"),
            "unknown constructor acquired an adapter");
  });

  // Walk logical admission independently of physical availability, and test
  // each case separately so a failure does not hide other domains.
  for (const auto &instance : installedDomains().allLogicalTypes()) {
    BoundType bound{instance.kind, instance.domain, {}};
    cases.run("logical roundtrip: " + bound.spelling(), [&] {
      roundTrip(context, take(parseBoundType(bound.spelling(), false)), false);
    });
    if (installedDomains().defaultRepresentation(instance.kind,
                                                 instance.domain))
      cases.run("physical roundtrip: " + bound.spelling(), [&] {
        roundTrip(context, take(defaultRepresentation(bound)), true);
      });
  }
  cases.run("nondefault physical layout", [&] {
    roundTrip(
        context,
        take(parseBoundType("table:bls12-381.fr@arkworks.mle-msb/1", true)),
        true);
  });
  for (StringRef spelling : {"fixed_vector<field:koala-bear,4>",
                             "fixed_vector<field:bls12-381.fr,4>",
                             "fixed_vector<rng:bls12-381.fr,0>",
                             "fixed_vector<fixed_vector<bool,2>,3>"})
    cases.run("structural logical roundtrip: " + spelling, [&] {
      roundTrip(context, take(parseBoundType(spelling, false)), false);
    });
  cases.run(
      "structural carrier retains length and physical representation", [&] {
        auto logical =
            take(parseBoundType("fixed_vector<field:koala-bear,4>", false));
        require(decodeBoundType(&context, logical) ==
                    zkc::algebra::FixedVectorType::get(
                        &context,
                        zkc::algebra::FieldType::get(&context, "koala-bear"),
                        4),
                "structural native type lost its element or length");
        roundTrip(context, take(defaultRepresentation(logical)), true);
        // Invalid native construction is tested with getChecked below. Calling
        // get here asserts before the adapter can inspect an oversized vector.
        logical.arguments[1] = TypeArgument::naturalArgument(1048577);
        require(!decodeBoundType(&context, logical),
                "malformed aggregate bypassed admission");
      });

  const std::string field = "bls12-381.fr";
  const std::string group = "bls12-381.g1";
  const std::string pcs = "multilinear.kzg.bls12-381/1";
  const std::string oracle = "rows.merkle-keccak256.koala-bear/1";
  const std::string transcript = "merlin3.bls12-381.fr64be/1";
  auto dynamicVector = [](Type element) -> Type {
    return RankedTensorType::get({ShapedType::kDynamic}, element);
  };
  // These expectations are independent of adapter dispatch and freeze the
  // native carriers, including the two commitment dialects.
  std::vector<std::pair<std::string, Type>> nativeCases{
      {"bool", IntegerType::get(&context, 1)},
      {"index", IntegerType::get(&context, 64, IntegerType::Unsigned)},
      {"indices",
       dynamicVector(IntegerType::get(&context, 64, IntegerType::Unsigned))},
      {"field:" + field, zkc::algebra::FieldType::get(&context, field)},
      {"matrix:" + field,
       RankedTensorType::get({ShapedType::kDynamic, ShapedType::kDynamic},
                             zkc::algebra::FieldType::get(&context, field))},
      {"vector:" + field,
       dynamicVector(zkc::algebra::FieldType::get(&context, field))},
      {"group:" + group, zkc::algebra::GroupType::get(&context, group)},
      {"groups:" + group,
       dynamicVector(zkc::algebra::GroupType::get(&context, group))},
      {"polynomial:" + field, zkc::poly::UnivariateType::get(&context, field)},
      {"table:" + field, zkc::poly::MultilinearType::get(&context, field)},
      {"point:" + field, zkc::poly::PointType::get(&context, field)},
      {"round:" + field, zkc::poly::QuadraticType::get(&context, field)},
      {"rng:" + field,
       zkc::local::CapabilityType::get(&context, "rng:" + field)},
      {"nonce:" + field,
       zkc::local::CapabilityType::get(&context, "nonce:" + field)},
      {"transcript:" + transcript,
       zkc::local::CapabilityType::get(&context, "transcript:" + transcript)},
      {"resource_unit:Guard",
       zkc::local::CapabilityType::get(&context, "resource_unit:Guard")},
  };
  for (StringRef kind :
       {"commitment", "proof", "opening_state", "prover_key", "verifier_key"})
    nativeCases.emplace_back(kind.str() + ":" + pcs,
                             zkc::pcs::ObjectType::get(&context, pcs, kind));
  for (StringRef kind : {"commitment", "proof", "opening_state", "commitments",
                         "opening_states"})
    nativeCases.emplace_back(
        kind.str() + ":" + oracle,
        zkc::oracle::OracleObjectType::get(&context, oracle, kind));
  cases.run("variant native carrier and physical wrapper", [&] {
    auto descriptor = encodeVariant(
        {"Result", {{"Value", {"bool"}}, {"Guard", {"resource_unit:Guard"}}}});
    require(bool(descriptor), "variant fixture refused");
    auto bound = take(parseBoundType(*descriptor, false));
    require(decodeBoundType(&context, bound) ==
                zkc::local::VariantType::get(&context, *descriptor),
            "variant native carrier changed");
    roundTrip(context, bound, false);
    roundTrip(context, take(defaultRepresentation(bound)), true);
    nativeCases.emplace_back(
        *descriptor, zkc::local::VariantType::get(&context, *descriptor));
  });
  cases.run("resource unit physical wrapper", [&] {
    roundTrip(context,
              take(parseBoundType("resource_unit:Guard@logical.resource_unit/1",
                                  true)),
              true);
  });
  for (const auto &nativeCase : nativeCases) {
    const auto &spelling = nativeCase.first;
    auto native = nativeCase.second;
    cases.run("native carrier: " + spelling, [&] {
      auto bound = take(parseBoundType(spelling, false));
      require(decodeBoundType(&context, bound) == native,
              "native carrier changed");
      require(take(encodeBoundType(native, false)) == bound,
              "native encoder changed identity");
    });
    if (spelling == "bool" || spelling == "index" || spelling == "indices")
      continue;
    for (bool registered : {false, true})
      cases.run(
          Twine(registered ? "registered but unloaded: " : "unregistered: ") +
              spelling,
          [&] {
            MLIRContext fresh;
            if (registered)
              fresh.appendDialectRegistry(registry);
            auto before = fresh.getLoadedDialects().size();
            require(
                !decodeBoundType(&fresh, take(parseBoundType(spelling, false))),
                "unloaded dialect accepted");
            require(fresh.getLoadedDialects().size() == before,
                    "translation initialized a dialect");
          });
  }
  cases.run("builtin carriers need no zkc dialect", [&] {
    MLIRContext fresh;
    for (StringRef kind : {"bool", "index", "indices"})
      roundTrip(fresh, take(parseBoundType(kind, false)), false);
  });
  cases.run("loaded namespace without registered type", [&] {
    MLIRContext fresh;
    fresh.loadDialect<EmptyAlgebraDialect>();
    require(!decodeBoundType(&fresh, {"field", field, {}}),
            "namespace without native type accepted");
  });
  cases.run("unloaded physical wrapper", [&] {
    MLIRContext fresh;
    fresh.loadDialect<zkc::algebra::AlgebraDialect>();
    auto bound = take(defaultRepresentation({"field", field, {}}));
    require(!decodeBoundType(&fresh, bound), "unloaded plan dialect accepted");
    require(!fresh.getLoadedDialect("plan"), "plan dialect was initialized");
  });
  cases.run("loaded PCS cannot replace an unloaded oracle dialect", [&] {
    MLIRContext fresh;
    fresh.loadDialect<zkc::pcs::PCSDialect>();
    require(!decodeBoundType(&fresh, {"proof", oracle, {}}),
            "oracle scheme fell back to PCS");
  });
  cases.run("loaded oracle cannot replace an unloaded PCS dialect", [&] {
    MLIRContext fresh;
    fresh.loadDialect<zkc::oracle::OracleDialect>();
    require(!decodeBoundType(&fresh, {"proof", pcs, {}}),
            "PCS scheme fell back to oracle");
  });

  for (const auto &identity : {pcs, oracle, field, std::string("uninstalled")})
    cases.run("unknown constructor: " + identity, [&] {
      require(!decodeBoundType(&context, {"uninstalled", identity, {}}),
              "unknown constructor became an object");
      refuses(encodeBoundType(
                  zkc::pcs::ObjectType::get(&context, identity, "uninstalled"),
                  false),
              "binding-type");
      refuses(encodeBoundType(zkc::oracle::OracleObjectType::get(
                                  &context, identity, "uninstalled"),
                              false),
              "binding-type");
    });
  for (const auto &identity : {field, std::string("uninstalled")})
    cases.run("unknown commitment carrier: " + identity, [&] {
      require(!decodeBoundType(&context, {"commitment", identity, {}}),
              "inapplicable scheme became a PCS object");
    });

  std::vector<std::pair<std::string, Type>> invalidCarriers{
      {"PCS object with oracle scheme",
       zkc::pcs::ObjectType::get(&context, oracle, "proof")},
      {"oracle object with PCS scheme",
       zkc::oracle::OracleObjectType::get(&context, pcs, "proof")},
      {"PCS collection",
       zkc::pcs::ObjectType::get(&context, pcs, "commitments")},
      {"oracle key",
       zkc::oracle::OracleObjectType::get(&context, oracle, "prover_key")},
      {"field as PCS object",
       zkc::pcs::ObjectType::get(&context, field, "field")},
      {"field as capability",
       zkc::local::CapabilityType::get(&context, "field:" + field)},
      {"variant prefix", zkc::local::VariantType::get(&context, "invalid:")},
      {"signless index", IntegerType::get(&context, 64)},
      {"signed index", IntegerType::get(&context, 64, IntegerType::Signed)},
      {"unsigned boolean",
       IntegerType::get(&context, 1, IntegerType::Unsigned)},
      {"MLIR index", IndexType::get(&context)},
      {"boolean tensor", dynamicVector(IntegerType::get(&context, 1))},
  };
  for (const auto &invalid : invalidCarriers)
    cases.run("wrong carrier: " + invalid.first, [&] {
      refuses(encodeBoundType(invalid.second, false), "binding-type");
    });

  for (Type element :
       {Type(IntegerType::get(&context, 64, IntegerType::Unsigned)),
        Type(zkc::algebra::FieldType::get(&context, field)),
        Type(zkc::algebra::GroupType::get(&context, group))}) {
    for (const auto &shape : std::vector<SmallVector<int64_t>>{
             {}, {0}, {2}, {ShapedType::kDynamic, ShapedType::kDynamic}})
      cases.run("noncanonical tensor rank or dimension", [&] {
        if ((shape == SmallVector<int64_t>{0} ||
             shape == SmallVector<int64_t>{2}) &&
            isa<zkc::algebra::FieldType>(element)) {
          auto encoded =
              encodeBoundType(RankedTensorType::get(shape, element), false);
          require(bool(encoded) && encoded->kind == "field_array",
                  "static field array");
          return;
        }
        if (shape == SmallVector<int64_t>{ShapedType::kDynamic,
                                          ShapedType::kDynamic} &&
            isa<zkc::algebra::FieldType>(element)) {
          auto encoded =
              encodeBoundType(RankedTensorType::get(shape, element), false);
          require(bool(encoded) && encoded->kind == "matrix", "dynamic matrix");
          return;
        }
        refuses(encodeBoundType(RankedTensorType::get(shape, element), false),
                "binding-type");
      });
    cases.run("encoded tensor", [&] {
      refuses(encodeBoundType(
                  RankedTensorType::get({ShapedType::kDynamic}, element,
                                        StringAttr::get(&context, "layout")),
                  false),
              "binding-type");
    });
    cases.run("unranked tensor", [&] {
      refuses(encodeBoundType(UnrankedTensorType::get(element), false),
              "binding-type");
    });
  }
  auto logical = zkc::algebra::FieldType::get(&context, field);
  auto physical = zkc::plan::DataType::get(&context, logical, "arkworks.fr/1");
  cases.run("fixed-vector native type verifier", [&] {
    ScopedDiagnosticHandler diagnostics(&context,
                                        [](Diagnostic &) { return success(); });
    auto location = UnknownLoc::get(&context);
    auto emit = [&] { return emitError(location); };
    require(succeeded(zkc::algebra::FixedVectorType::verify(emit, logical, 4)),
            "valid logical fixed-vector native type rejected");
    require(failed(zkc::algebra::FixedVectorType::verify(emit, physical, 4)),
            "fixed-vector element acquired a physical representation");
    require(failed(zkc::algebra::FixedVectorType::verify(
                emit, Float32Type::get(&context), 4)),
            "unadmitted floating-point element accepted");
    require(
        failed(zkc::algebra::FixedVectorType::verify(emit, logical, 1048577)),
        "unbounded natural index accepted");
  });
  cases.run("physical carrier at logical stage", [&] {
    refuses(encodeBoundType(physical, false),
            "binding-physical-type-at-logical-stage");
  });
  cases.run("logical carrier at physical stage", [&] {
    refuses(encodeBoundType(logical, true),
            "binding-logical-type-at-physical-stage");
  });
  cases.run("nested physical wrapper", [&] {
    refuses(encodeBoundType(
                zkc::plan::DataType::get(&context, physical, "arkworks.fr/1"),
                true),
            "binding-type");
  });
  cases.run("wrapped noncanonical tensor", [&] {
    auto tensor = RankedTensorType::get({2}, logical);
    refuses(encodeBoundType(zkc::plan::DataType::get(&context, tensor,
                                                     "arkworks.fr-vector/1"),
                            true),
            "binding-representation");
  });
  for (StringRef representation : {"", "uninstalled", "arkworks.g1/1"})
    cases.run(Twine("wrong physical representation: ") + representation, [&] {
      refuses(encodeBoundType(
                  zkc::plan::DataType::get(&context, logical, representation),
                  true),
              "binding-representation");
    });
  cases.run("wrapped wrong commitment carrier", [&] {
    auto object = zkc::pcs::ObjectType::get(&context, oracle, "proof");
    auto representation = take(defaultRepresentation({"proof", oracle, {}}));
    refuses(
        encodeBoundType(zkc::plan::DataType::get(&context, object,
                                                 representation.representation),
                        true),
        "binding-type");
  });
  cases.run("checked native construction and assembly preserve formation", [&] {
    ScopedDiagnosticHandler diagnostics(&context,
                                        [](Diagnostic &) { return success(); });
    auto emit = [&] { return emitError(UnknownLoc::get(&context)); };
    auto field =
        zkc::algebra::FieldType::getChecked(emit, &context, StringRef("f7"));
    require(bool(field), "native field formation rejected f7");
    require(parseType("!algebra.field<\"f7\">", &context) == field,
            "native field parser changed f7 formation");
    auto element = zkc::algebra::FieldType::get(&context, "koala-bear");
    auto vector = zkc::algebra::FixedVectorType::getChecked(
        emit, &context, Type(element), uint64_t(4));
    require(bool(vector), "checked fixed-vector construction failed");
    require(
        parseType("!algebra.fixed_vector<!algebra.field<\"koala-bear\">, 4>",
                  &context) == vector,
        "fixed-vector parser changed native identity");
    require(!zkc::algebra::FixedVectorType::getChecked(
                emit, &context, Type(field), uint64_t(4)),
            "fixed-vector admitted an unadmitted nested field");
    require(!parseType("!algebra.fixed_vector<!algebra.field<\"f7\">, 4>",
                       &context),
            "fixed-vector parser bypassed nested admission");
    require(!zkc::algebra::FixedVectorType::getChecked(
                emit, &context, Type(element), uint64_t(1048577)),
            "checked fixed-vector accepted an excessive natural");
  });
  cases.run("explicit unavailable native binding decisions", [&] {
    require(!type_adapters::findAdapter("scalar"),
            "scalar acquired an adapter");
    require(!type_adapters::findAdapter("capability"),
            "capability acquired an adapter");
    require(!decodeBoundType(&context, {"scalar", {}, {}}),
            "unavailable scalar decoded");
    require(!decodeBoundType(&context, {"capability", {}, {}}),
            "unavailable capability decoded");
  });
  cases.run("admission still rejects a core-only field", [&] {
    refuses(
        encodeBoundType(zkc::algebra::FieldType::get(&context, "f7"), false),
        "binding-type-identity");
  });
  cases.run("null carrier and context", [&] {
    refuses(encodeBoundType({}, false), "binding-type");
    require(!decodeBoundType(nullptr, {"bool", {}, {}}),
            "null context accepted");
  });
  return cases.result();
}
