#include "mlir/AsmParser/AsmParser.h"
#include "mlir/IR/AttrTypeSubElements.h"
#include "support/NativeCases.h"
#include "support/VariantFixture.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/Layout.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/TypeAdapters.h"
#include "zkc/Dialect/TypeFormation.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/raw_ostream.h"
#include <future>

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

class EmptyDataDialect : public Dialect {
public:
  explicit EmptyDataDialect(MLIRContext *context)
      : Dialect(getDialectNamespace(), context,
                TypeID::get<EmptyDataDialect>()) {}
  static StringRef getDialectNamespace() { return "data"; }
};

void roundTrip(MLIRContext &context, const BoundType &bound, bool physical) {
  auto native = decodeBoundType(&context, bound);
  require(bool(native), "decoding refused an admitted type");
  auto encoded = take(encodeBoundType(native, physical));
  require(encoded == bound, "logical identity or representation changed");
  require(take(encodeBoundType(native, physical)) == bound,
          "repeated translation changed identity");
  refuses(encodeBoundType(native, !physical),
          physical ? "binding-physical-type-at-logical-stage"
                   : "binding-logical-type-at-physical-stage");
  require(decodeBoundType(&context, encoded) == native,
          "native type identity changed");
  std::string printed;
  llvm::raw_string_ostream stream(printed);
  native.print(stream);
  require(mlir::parseType(printed, &context) == native,
          "textual native type roundtrip changed identity");
}
} // namespace

int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();

  cases.run("resource carriers store kind and identity separately", [&] {
    SmallVector<std::string> codes;
    ScopedDiagnosticHandler diagnostics(&context, [&](Diagnostic &diagnostic) {
      for (const auto &refusal : zkc::diagnostics::refusals(diagnostic))
        codes.push_back(refusal.code);
      return success();
    });
    auto emit = [&] { return emitError(UnknownLoc::get(&context)); };
    using K = runtime::CapabilityKind;
    for (auto [kind, identity] :
         {std::pair{K::Random, StringRef("uninstalled")},
          std::pair{K::Nonce, StringRef("bls12-381.g1")},
          std::pair{K::Transcript, StringRef("bls12-381.fr")},
          std::pair{K::ResourceUnit, StringRef("bad:slot")},
          std::pair{static_cast<K>(255), StringRef("ticket")}}) {
      codes.clear();
      require(
          !runtime::CapabilityType::getChecked(emit, &context, kind, identity),
          "invalid resource identity acquired a native carrier");
      require(llvm::is_contained(codes, "capability-type"),
              "resource formation refusal lost its diagnostic identity");
    }
    require(
        !mlir::parseType("!runtime.capability<\"rng:bls12-381.fr\">", &context),
        "retired combined resource spelling remained a compatibility route");
    auto rng =
        runtime::CapabilityType::get(&context, K::Random, "bls12-381.fr");
    auto nonce =
        runtime::CapabilityType::get(&context, K::Nonce, "bls12-381.fr");
    require(rng != nonce && rng.getIdentity() == nonce.getIdentity(),
            "equal domain identities erased the resource kind");
  });

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
      auto native = decodeBoundType(&context, bound);
      auto emit = [&] { return emitError(UnknownLoc::get(&context)); };
      auto view = cast<CatalogTypeInterface>(native).getCatalogApplication();
      require(view && constructLogicalType(emit, &context, *view) == native,
              "native constructor changed the installed logical instance");
      require(succeeded(verifyLogicalType(emit, native)),
              "admitted byte type has no native logical formation");
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
        take(parseBoundType("table:bls12-381.fr@arkworks.mle-msb/0", true)),
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
  const std::string pcs = "multilinear.kzg.bls12-381/0";
  const std::string oracle = "rows.merkle-keccak256.koala-bear/0";
  const std::string transcript = "merlin3.bls12-381.fr64be/0";
  auto builtinTensor = [](Type element) -> Type {
    return RankedTensorType::get({ShapedType::kDynamic}, element);
  };
  // These expectations are independent of adapter dispatch and freeze the
  // native carriers and their semantic owners.
  std::vector<std::pair<std::string, Type>> nativeCases{
      {"bool", IntegerType::get(&context, 1)},
      {"index", IntegerType::get(&context, 64, IntegerType::Unsigned)},
      {"bytes", zkc::data::BytesType::get(&context)},
      {"shake128_state", zkc::crypto::Shake128StateType::get(&context)},
      {"quotient_matrix", zkc::runtime::QuotientMatrixType::get(&context)},
      {"indices", zkc::algebra::IndicesType::get(&context)},
      {"field:" + field, zkc::algebra::FieldType::get(&context, field)},
      {"matrix:" + field, zkc::algebra::FieldMatrixType::get(&context, field)},
      {"vector:" + field, zkc::algebra::FieldVectorType::get(&context, field)},
      {"group:" + group, zkc::algebra::GroupType::get(&context, group)},
      {"groups:" + group, zkc::algebra::GroupVectorType::get(&context, group)},
      {"field_array<" + field + ",0>",
       zkc::algebra::FieldArrayType::get(&context, field, 0)},
      {"field_array<" + field + ",4>",
       zkc::algebra::FieldArrayType::get(&context, field, 4)},
      {"polynomial:" + field, zkc::poly::UnivariateType::get(&context, field)},
      {"table:" + field, zkc::poly::MultilinearType::get(&context, field)},
      {"point:" + field, zkc::poly::PointType::get(&context, field)},
      {"round:" + field, zkc::poly::QuadraticType::get(&context, field)},
      {"rng:" + field,
       zkc::runtime::CapabilityType::get(
           &context, zkc::runtime::CapabilityKind::Random, field)},
      {"nonce:" + field,
       zkc::runtime::CapabilityType::get(
           &context, zkc::runtime::CapabilityKind::Nonce, field)},
      {"transcript:" + transcript,
       zkc::runtime::CapabilityType::get(
           &context, zkc::runtime::CapabilityKind::Transcript, transcript)},
      {"resource_unit:Guard",
       zkc::runtime::CapabilityType::get(
           &context, zkc::runtime::CapabilityKind::ResourceUnit, "Guard")},
  };
  for (StringRef kind :
       {"commitment", "proof", "opening_state", "prover_key", "verifier_key"})
    nativeCases.emplace_back(
        kind.str() + ":" + pcs,
        zkc::commitment::PolynomialObjectType::get(&context, pcs, kind));
  for (StringRef kind : {"commitment", "proof", "opening_state", "commitments",
                         "opening_states"})
    nativeCases.emplace_back(
        kind.str() + ":" + oracle,
        zkc::commitment::VectorObjectType::get(&context, oracle, kind));
  cases.run("variant native carrier and physical wrapper", [&] {
    auto descriptor = encodeVariant(
        {"Result", {{"Value", {"bool"}}, {"Guard", {"resource_unit:Guard"}}}});
    require(bool(descriptor), "variant fixture refused");
    auto bound = take(parseBoundType(*descriptor, false));
    require(decodeBoundType(&context, bound) ==
                zkc::test::variantType(&context, *descriptor),
            "variant native carrier changed");
    roundTrip(context, bound, false);
    roundTrip(context, take(defaultRepresentation(bound)), true);
    nativeCases.emplace_back(*descriptor,
                             zkc::test::variantType(&context, *descriptor));
  });
  cases.run("resource unit physical wrapper", [&] {
    roundTrip(context,
              take(parseBoundType("resource_unit:Guard@logical.resource_unit/0",
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
      std::string printed;
      llvm::raw_string_ostream(printed) << native;
      require(parseType(printed, &context) == native,
              "native parser/printer changed identity");
      if (isa<zkc::algebra::FieldVectorType, zkc::algebra::GroupVectorType,
              zkc::algebra::IndicesType, zkc::algebra::FieldMatrixType,
              zkc::algebra::FieldArrayType, zkc::data::BytesType,
              zkc::crypto::Shake128StateType, zkc::runtime::QuotientMatrixType>(
              native))
        roundTrip(context, take(defaultRepresentation(bound)), true);
    });
    if (spelling == "bool" || spelling == "index")
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
  cases.run("cached and standalone translation preserve exact carriers", [&] {
    // Loading the owners directly omits registry extensions. Both paths must
    // admit precisely the same closed logical and physical identities.
    MLIRContext standalone;
    standalone
        .loadDialect<algebra::AlgebraDialect, data::DataDialect,
                     crypto::CryptoDialect, poly::PolynomialDialect,
                     runtime::RuntimeDialect, commitment::CommitmentDialect>();
    for (const auto &[spelling, native] : nativeCases) {
      auto bound = take(parseBoundType(spelling, false));
      auto other = decodeBoundType(&standalone, bound);
      require(bool(other), "standalone carrier missing");
      require(take(encodeBoundType(native, false)) ==
                  take(encodeBoundType(other, false)),
              "context extension changed logical translation");
      auto physical = defaultRepresentation(bound);
      if (!physical) {
        consumeError(physical.takeError());
        continue;
      }
      roundTrip(standalone, *physical, true);
      roundTrip(context, *physical, true);
    }
  });
  cases.run("parallel repeated translation retains context and stage", [&] {
    std::vector<std::future<void>> workers;
    for (unsigned i = 0; i < 4; ++i)
      workers.push_back(std::async(std::launch::async, [&] {
        for (unsigned round = 0; round < 4; ++round)
          for (const auto &[spelling, native] : nativeCases) {
            require(take(encodeBoundType(native, false)).spelling() == spelling,
                    "parallel translation changed identity");
            refuses(encodeBoundType(native, true),
                    "binding-logical-type-at-physical-stage");
          }
      }));
    for (auto &worker : workers)
      worker.get();
  });
  cases.run("builtin carriers need no zkc dialect", [&] {
    MLIRContext fresh;
    for (StringRef kind : {"bool", "index"})
      roundTrip(fresh, take(parseBoundType(kind, false)), false);
  });
  cases.run("loaded namespace without registered type", [&] {
    MLIRContext fresh;
    fresh.loadDialect<EmptyAlgebraDialect>();
    require(!decodeBoundType(&fresh, {"field", field, {}}),
            "namespace without native type accepted");
  });
  cases.run("loaded Data namespace without registered variant", [&] {
    MLIRContext fresh;
    fresh.loadDialect<EmptyDataDialect>();
    auto spelling = protocol::encodeVariant({"Choice", {{"empty", {}}}});
    require(bool(spelling), "invalid boundary fixture");
    require(!decodeBoundType(&fresh, take(parseBoundType(*spelling, false))),
            "namespace without registered aggregate accepted");
  });
  cases.run("unloaded physical wrapper", [&] {
    MLIRContext fresh;
    fresh.loadDialect<zkc::algebra::AlgebraDialect>();
    auto bound = take(defaultRepresentation({"field", field, {}}));
    require(!decodeBoundType(&fresh, bound),
            "unloaded runtime dialect accepted");
    require(!fresh.getLoadedDialect("runtime"),
            "runtime dialect was initialized");
  });
  for (StringRef spelling : {"!local.capability<\"resource_unit:Guard\">",
                             "!local.variant<\"invalid\">", "!local.opaque",
                             "!plan.data<i1, \"logical.bool/0\">"})
    cases.run("retired value owner: " + spelling, [&] {
      ScopedDiagnosticHandler silence(&context,
                                      [](Diagnostic &) { return success(); });
      require(!parseType(spelling, &context),
              "retired type spelling retained a compatibility parser");
    });
  cases.run(
      "shared commitment owner preserves polynomial and vector carriers", [&] {
        MLIRContext fresh;
        fresh.loadDialect<zkc::commitment::CommitmentDialect>();
        auto polynomial = decodeBoundType(&fresh, {"proof", pcs, {}});
        auto vector = decodeBoundType(&fresh, {"proof", oracle, {}});
        require(polynomial &&
                    isa<zkc::commitment::PolynomialObjectType>(polynomial),
                "polynomial scheme lost its carrier");
        require(vector && isa<zkc::commitment::VectorObjectType>(vector),
                "vector scheme lost its carrier");
        require(polynomial != vector,
                "distinct authentication guarantees collapsed");
      });

  for (const auto &identity : {pcs, oracle, field, std::string("uninstalled")})
    cases.run("unknown constructor: " + identity, [&] {
      require(!decodeBoundType(&context, {"uninstalled", identity, {}}),
              "unknown constructor became an object");
      refuses(encodeBoundType(zkc::commitment::PolynomialObjectType::get(
                                  &context, identity, "uninstalled"),
                              false),
              "binding-type");
      refuses(encodeBoundType(zkc::commitment::VectorObjectType::get(
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
       zkc::commitment::PolynomialObjectType::get(&context, oracle, "proof")},
      {"oracle object with PCS scheme",
       zkc::commitment::VectorObjectType::get(&context, pcs, "proof")},
      {"PCS collection", zkc::commitment::PolynomialObjectType::get(
                             &context, pcs, "commitments")},
      {"oracle key",
       zkc::commitment::VectorObjectType::get(&context, oracle, "prover_key")},
      {"field as PCS object",
       zkc::commitment::PolynomialObjectType::get(&context, field, "field")},
      {"signless index", IntegerType::get(&context, 64)},
      {"signed index", IntegerType::get(&context, 64, IntegerType::Signed)},
      {"unsigned boolean",
       IntegerType::get(&context, 1, IntegerType::Unsigned)},
      {"MLIR index", IndexType::get(&context)},
      {"boolean tensor", builtinTensor(IntegerType::get(&context, 1))},
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
             {},
             {0},
             {2},
             {ShapedType::kDynamic},
             {ShapedType::kDynamic, ShapedType::kDynamic}})
      cases.run("builtin tensor has no logical collection alias", [&] {
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
  auto physical = zkc::runtime::RepresentedType::get(&context, logical,
                                                     "arkworks.fr/0", {});
  cases.run("field-array domain and length identity", [&] {
    auto empty = zkc::algebra::FieldArrayType::get(&context, field, 0);
    auto array = zkc::algebra::FieldArrayType::get(&context, field, 4);
    require(empty.getLength() == 0 && array.getLength() == 4 &&
                array.getDomain() == field && array.getElementType() == logical,
            "field-array domain, element or length changed");
    require(Type(array) !=
                    zkc::algebra::FieldVectorType::get(&context, field) &&
                Type(array) !=
                    zkc::algebra::FixedVectorType::get(&context, logical, 4) &&
                Type(array) != zkc::data::SequenceType::get(&context, logical),
            "distinct collection families acquired the same native type");
    ScopedDiagnosticHandler diagnostics(&context,
                                        [](Diagnostic &) { return success(); });
    auto emit = [&] { return emitError(UnknownLoc::get(&context)); };
    require(succeeded(zkc::algebra::FieldArrayType::verify(emit, field, 0)) &&
                succeeded(
                    zkc::algebra::FieldArrayType::verify(emit, field, 1048576)),
            "admitted field-array length boundary refused");
    require(failed(zkc::algebra::FieldArrayType::verify(emit, field, 1048577)),
            "field-array length limit ignored");
  });
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
    refuses(encodeBoundType(zkc::runtime::RepresentedType::get(
                                &context, physical, "arkworks.fr/0", {}),
                            true),
            "binding-type");
  });
  cases.run("wrapped noncanonical tensor", [&] {
    auto tensor = RankedTensorType::get({2}, logical);
    refuses(encodeBoundType(zkc::runtime::RepresentedType::get(
                                &context, tensor, "arkworks.fr-vector/0", {}),
                            true),
            "binding-type");
  });
  for (StringRef representation : {"", "uninstalled", "arkworks.g1/0"})
    cases.run(Twine("wrong physical representation: ") + representation, [&] {
      refuses(encodeBoundType(zkc::runtime::RepresentedType::get(
                                  &context, logical, representation, {}),
                              true),
              "binding-representation");
    });
  cases.run("wrapped wrong commitment carrier", [&] {
    auto object =
        zkc::commitment::PolynomialObjectType::get(&context, oracle, "proof");
    auto representation = take(defaultRepresentation({"proof", oracle, {}}));
    refuses(encodeBoundType(
                zkc::runtime::RepresentedType::get(
                    &context, object, representation.representation, {}),
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
  cases.run(
      "structural variants preserve complete identity and traversal", [&] {
        auto field = algebra::FieldType::get(&context, "bls12-381.fr");
        auto other = algebra::FieldType::get(&context, "koala-bear");
        auto name = data::importVariantIdentity(
            &context, json::Array{"Claim", "phantom-A"});
        auto different = data::importVariantIdentity(
            &context, json::Array{"Claim", "phantom-B"});
        auto arm = data::AlternativeAttr::get(
            &context, StringAttr::get(&context, "present"),
            ArrayRef<Type>{field});
        auto empty = data::AlternativeAttr::get(
            &context, StringAttr::get(&context, "empty"), {});
        auto value = data::VariantType::get(&context, name, {arm, empty});
        require(value !=
                    data::VariantType::get(&context, different, {arm, empty}),
                "phantom identity was erased");
        require(value != data::VariantType::get(&context, name, {empty, arm}),
                "alternative order was erased");
        bool visited = false;
        value.walk([&](Type type) { visited |= type == field; });
        require(visited, "generic MLIR walking cannot see variant payloads");
        AttrTypeReplacer replacer;
        replacer.addReplacement(
            [&](algebra::FieldType type) -> std::optional<Type> {
              return type == field ? std::optional<Type>(other) : std::nullopt;
            });
        auto replaced = cast<data::VariantType>(replacer.replace(Type(value)));
        require(replaced.getIdentity() == name &&
                    replaced.getAlternatives()[0].getPayload()[0] == other &&
                    replaced.getAlternatives()[1].getPayload().empty(),
                "generic replacement changed identity, order or empty payload");
        std::string text;
        raw_string_ostream out(text);
        Type(value).print(out);
        require(parseType(text, &context) == value,
                "structured variant did not roundtrip");
      });
  cases.run("malformed structured variants and retired assembly refuse", [&] {
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    auto emit = [&]() { return mlir::emitError(UnknownLoc::get(&context)); };
    require(!data::importVariantIdentity(&context, ""),
            "empty nominal identity atom admitted");
    auto name = data::importVariantIdentity(&context, "Claim");
    auto arm = data::AlternativeAttr::get(
        &context, StringAttr::get(&context, "present"), {});
    require(
        !data::VariantType::getChecked(
            emit, &context, name, ArrayRef<data::AlternativeAttr>{arm, arm}),
        "duplicate alternatives admitted");
    require(!data::VariantType::getChecked(emit, &context, name,
                                           ArrayRef<data::AlternativeAttr>{}),
            "empty alternatives admitted");
    require(!data::AlternativeAttr::getChecked(
                emit, &context, StringAttr::get(&context, "bad label"),
                ArrayRef<Type>{}),
            "invalid alternative label admitted");
    require(!parseType("!data.variant<\"variant:00\">", &context),
            "retired descriptor assembly still admitted");
    auto value = data::VariantType::get(&context, name, {arm});
    bool refused = false;
    for (unsigned i = 0; i != 8; ++i) {
      SmallVector<Type> payload(64, value);
      auto repeated = data::AlternativeAttr::get(
          &context, StringAttr::get(&context, "repeated"), payload);
      value = data::VariantType::getChecked(
          emit, &context, name, ArrayRef<data::AlternativeAttr>{repeated});
      if (!value) {
        refused = true;
        break;
      }
    }
    require(refused, "shared type DAG bypassed expanded-work bound");
  });
  cases.run(
      "logical layouts expose fields, alternatives and native leaves", [&] {
        auto scalar = [&]() -> llvm::json::Value {
          return llvm::json::Object{
              {"kind", "boolean"},
              {"identity", std::string(64, 'a')},
              {"type", "bool"},
              {"custody", false},
              {"constructible", true},
              {"permissions", llvm::json::Array{"Copy", "Drop"}},
              {"fields", llvm::json::Array{}},
              {"alternatives", llvm::json::Array{}},
              {"leaves", llvm::json::Array{"bool"}}};
        };
        auto record = scalar();
        auto &object = *record.getAsObject();
        object["kind"] = "record";
        object["identity"] = std::string(64, 'b');
        object["type"] = "Claim";
        object["fields"] = llvm::json::Array{llvm::json::Object{
            {"name", "accepted"}, {"offset", 0}, {"schema", scalar()}}};
        MLIRContext fresh;
        require(!data::importLayout(&fresh, record),
                "layout boundary initialized an unregistered dialect");
        auto layout = data::importLayout(&context, record);
        require(bool(layout), "formed logical layout refused");
        auto native = data::valueType(layout);
        require(isa<data::ValueType>(native) &&
                    data::valueType(layout.getFields().front().getLayout())
                        .isInteger(1),
                "logical field carrier differs");
        unsigned fields = 0, booleans = 0;
        native.walk(
            [&](Attribute attr) { fields += isa<data::LayoutFieldAttr>(attr); },
            [&](Type type) { booleans += type.isInteger(1); });
        require(fields == 1 && booleans > 0,
                "generic traversal missed layout children");
        std::string assembly;
        llvm::raw_string_ostream stream(assembly);
        native.print(stream);
        require(parseType(assembly, &context) == native,
                "logical layout did not roundtrip");
        object["fields"].getAsArray()->front().getAsObject()->operator[](
            "name") = "other";
        require(data::valueType(data::importLayout(&context, record)) != native,
                "field name was erased from logical layout identity");
        ScopedDiagnosticHandler silence(&context,
                                        [](Diagnostic &) { return success(); });
        object["fields"].getAsArray()->front().getAsObject()->operator[](
            "offset") = 1;
        require(!data::importLayout(&context, record),
                "noncontiguous field offset admitted");
        object["fields"].getAsArray()->front().getAsObject()->operator[](
            "offset") = 0;
        object["extra"] = true;
        require(!data::importLayout(&context, record),
                "unknown schema member admitted");
        object.erase("extra");
        object["permissions"] = llvm::json::Array{"Copy"};
        require(!data::importLayout(&context, record),
                "Copy without Drop admitted");
        require(!parseType("!data.value<\"{}\">", &context),
                "retired JSON schema parser retained");
        auto unit = scalar();
        auto &unitObject = *unit.getAsObject();
        unitObject["kind"] = "unit";
        unitObject["type"] = "()";
        unitObject["leaves"] = llvm::json::Array{};
        auto empty = data::valueType(data::importLayout(&context, unit));
        require(bool(empty), "empty logical product refused");
        assembly.clear();
        empty.print(stream);
        require(parseType(assembly, &context) == empty,
                "empty logical product did not roundtrip");
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
