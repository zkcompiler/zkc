#include "support/NativeCases.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Interfaces/CatalogType.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Builder builder(&context);
  Cases cases;
  cases.run(
      "consumer selection preserves kinded roots and refuses nonmembers", [&] {
        using namespace zkc::protocol;
        const auto *profile = consumerProfile("structured-source-primitives");
        require(profile && profile->operations.size() == 16 &&
                    profile->implementation ==
                        ConsumerImplementation::Unselected,
                "structured primitive selection changed");
        const auto *index =
            consumerProfileOperation(profile->name, "index.add");
        const auto *embed =
            consumerProfileOperation(profile->name, "field.embed");
        require(index && index->staticParameters.empty(),
                "index gained a static argument");
        require(embed && embed->staticParameters ==
                             std::vector<StaticParameter>{
                                 {StaticKind::Domain, "Field"}},
                "associated field projection became a caller argument");
        require(!consumerProfile("missing") &&
                    !consumerProfileOperation("missing", "index.add") &&
                    !consumerProfileOperation(profile->name, "field.add") &&
                    !consumerProfileOperation(profile->name, "numerical.map"),
                "declaration presence acquired consumer membership");
        const auto *constant = parameterContract("index.constant");
        const auto *embedding = parameterContract("field.embed");
        require(constant && embedding &&
                    constant->validator == ParameterValidator::Natural &&
                    embedding->validator == ParameterValidator::None,
                "selected validator lost correspondence");
      });
  auto location = builder.getUnknownLoc();
  auto emit = [&] { return emitError(location); };
  SmallVector<std::string> codes;
  ScopedDiagnosticHandler diagnostics(&context, [&](Diagnostic &diagnostic) {
    for (auto &refusal : diagnostics::refusals(diagnostic))
      codes.push_back(refusal.code);
    return success();
  });
  auto field = algebra::FieldType::get(&context, "koala-bear");
  auto nat = [&](uint64_t n) {
    return IntegerAttr::get(
        IntegerType::get(&context, 64, IntegerType::Unsigned), n);
  };
  auto application = [&](Type type) {
    auto interface = dyn_cast<CatalogTypeInterface>(type);
    require(bool(interface), "missing native catalog interface");
    auto result = interface.getCatalogApplication();
    require(bool(result), "missing unique catalog observation");
    return *result;
  };
  auto refuse = [&](const CatalogTypeApplication &app) {
    codes.clear();
    require(failed(verifyLogicalTypeApplication(emit, &context, app)),
            "malformed typed application accepted");
    require(llvm::is_contained(codes, "logical-type-formation"),
            "formation refusal lost its diagnostic identity");
  };
  cases.run(
      "local formation needs no unrelated dialect or registry extension", [&] {
        MLIRContext minimal;
        minimal.loadDialect<algebra::AlgebraDialect, data::DataDialect>();
        auto scalar = algebra::FieldType::get(&minimal, "koala-bear");
        auto sequence = data::SequenceType::getChecked(
            UnknownLoc::get(&minimal), &minimal, Type(scalar));
        require(bool(sequence) && isa<CatalogTypeInterface>(scalar),
                "intrinsic verifier depends on optional registry extensions");
        require(!minimal.getLoadedDialect<runtime::RuntimeDialect>(),
                "type observation loaded an unrelated dialect");
      });
  cases.run("native catalog arguments retain kinds and identity", [&] {
    auto scalar = application(field);
    require(scalar.constructor == "field" && scalar.arguments.size() == 1 &&
                cast<StringAttr>(scalar.arguments[0]).getValue() ==
                    "koala-bear",
            "nominal domain identity changed");
    auto fixed = algebra::FixedVectorType::get(&context, field, 4);
    auto view = application(fixed);
    require(view.constructor == "fixed_vector" && view.arguments.size() == 2 &&
                cast<TypeAttr>(view.arguments[0]).getValue() == field &&
                view.arguments[1] == nat(4),
            "typed static arguments changed");
    require(succeeded(verifyLogicalType(emit, fixed)), "formed type refused");
  });
  cases.run(
      "typed constructors preserve structure and reject unavailable owners",
      [&] {
        auto app = CatalogTypeApplication{"fixed_vector",
                                          {TypeAttr::get(field), nat(4)}};
        require(constructLogicalType(emit, &context, app) ==
                    algebra::FixedVectorType::get(&context, field, 4),
                "native construction changed the typed application");
        codes.clear();
        require(!constructLogicalType(emit, &context, {"fixed_vector", {}}) &&
                    llvm::is_contained(codes, "logical-type-formation"),
                "constructor bypassed argument formation");
        MLIRContext minimal(registry);
        auto diagnostic = [&] { return emitError(UnknownLoc::get(&minimal)); };
        ScopedDiagnosticHandler handler(&minimal, [&](Diagnostic &diagnostic) {
          for (const auto &refusal : diagnostics::refusals(diagnostic))
            codes.push_back(refusal.code);
          return success();
        });
        codes.clear();
        require(!constructLogicalType(
                    diagnostic, &minimal,
                    {"field", {StringAttr::get(&minimal, "koala-bear")}}) &&
                    llvm::is_contained(codes, "logical-type-construction"),
                "unloaded native owner acquired a type");
        require(!minimal.getLoadedDialect<algebra::AlgebraDialect>(),
                "constructor loaded an unrequested dialect");
      });
  cases.run("shared builtin carrier does not grant logical identity", [&] {
    require(application(builder.getI1Type()).constructor == "bool",
            "Boolean identity");
    require(application(nat(0).getType()).constructor == "index",
            "Index identity");
    for (Type type : {builder.getI64Type(), builder.getI32Type()}) {
      require(!cast<CatalogTypeInterface>(type).getCatalogApplication(),
              "nonlogical integer acquired a catalog identity");
      require(failed(verifyLogicalType(emit, type)),
              "nonlogical integer admitted");
    }
    require(!isa<CatalogTypeInterface>(RankedTensorType::get({4}, field)),
            "tensor shape invented a nominal type");
  });
  cases.run("typed arguments reject sort kind arity and bound mutations", [&] {
    refuse({"missing", {}});
    codes.clear();
    require(failed(verifyLogicalTypeApplication(emit, nullptr, {"bool", {}})) &&
                llvm::is_contained(codes, "logical-type-formation"),
            "missing context has no stable refusal");
    refuse({"field", {builder.getStringAttr("bls12-381.g1")}});
    refuse({"field", {TypeAttr::get(field)}});
    refuse({"fixed_vector", {TypeAttr::get(field)}});
    refuse(
        {"fixed_vector", {builder.getStringAttr("field:koala-bear"), nat(4)}});
    refuse(
        {"fixed_vector", {TypeAttr::get(field), builder.getI64IntegerAttr(4)}});
    refuse({"fixed_vector", {TypeAttr::get(field), nat(1048577)}});
    refuse({"fixed_vector", {TypeAttr::get(field), nat(UINT64_MAX)}});
    refuse({"sequence", {TypeAttr::get(builder.getI64Type())}});
    refuse({"resource_unit", {builder.getStringAttr("bad:slot")}});
    MLIRContext other;
    refuse({"sequence", {TypeAttr::get(IntegerType::get(&other, 1))}});
  });
  auto identity = data::IdentityAttr::get(
      &context, builder.getArrayAttr({builder.getStringAttr("atom"),
                                      builder.getStringAttr("Claim")}));
  auto variant = [&](ArrayRef<Type> payload) {
    return data::VariantType::get(
        &context, identity,
        {data::AlternativeAttr::get(&context, builder.getStringAttr("claim"),
                                    payload)});
  };
  cases.run("all variant payloads contribute permissions", [&] {
    auto rng = runtime::CapabilityType::get(
        &context, zkc::runtime::CapabilityKind::Random, "bls12-381.fr");
    auto resource = data::VariantType::get(
        &context, identity,
        {data::AlternativeAttr::get(&context, builder.getStringAttr("none"),
                                    {}),
         data::AlternativeAttr::get(&context, builder.getStringAttr("some"),
                                    {field, rng})});
    LogicalTypePermissions permissions;
    require(succeeded(verifyLogicalType(emit, resource, &permissions)) &&
                !permissions.copy && !permissions.drop,
            "variant hid an affine child");
    refuse({"sequence", {TypeAttr::get(resource)}});
    auto unit = runtime::CapabilityType::get(
        &context, zkc::runtime::CapabilityKind::ResourceUnit, "ticket");
    require(succeeded(verifyLogicalType(emit, unit, &permissions)) &&
                !permissions.copy && permissions.drop,
            "slot permission confused with an installed field domain");
  });
  cases.run(
      "structural formation and byte publication have separate bounds", [&] {
        Type type = field;
        for (unsigned i = 0; i < 12; ++i)
          type = data::SequenceType::get(&context, type);
        require(succeeded(verifyLogicalType(emit, type)),
                "byte parser depth leaked into native structural formation");
        auto bytes = protocol::encodeBoundType(type, false);
        require(!bytes, "structural formation weakened byte admission");
        llvm::consumeError(bytes.takeError());
      });
  cases.run("physical carriers do not become logical through their payload",
            [&] {
              auto physical = runtime::RepresentedType::get(
                  &context, field, "plonky3.koala-bear/0", ArrayRef<Type>{});
              require(failed(verifyLogicalType(emit, physical)),
                      "represented type became logical");
              refuse({"sequence", {TypeAttr::get(physical)}});
            });
  cases.run("variant formation refuses foreign-context children", [&] {
    MLIRContext foreign;
    Type leaf = IntegerType::get(&foreign, 1);
    auto arm = data::AlternativeAttr::get(
        &context, builder.getStringAttr("claim"), {leaf});
    require(!data::VariantType::getChecked(
                emit, &context, identity, ArrayRef<data::AlternativeAttr>{arm}),
            "variant retained a foreign-context payload");
  });
  cases.run("expanded structure counts shared native children", [&] {
    Type child = field;
    for (unsigned i = 0; i < 3; ++i) {
      SmallVector<Type> payload(32, child);
      child = variant(payload);
    }
    SmallVector<Type> repeated(32, child);
    // Refuse before interning the next parent; every expanded occurrence
    // counts.
    auto arm = data::AlternativeAttr::get(
        &context, builder.getStringAttr("claim"), repeated);
    codes.clear();
    require(failed(data::VariantType::verify(emit, identity, {arm})),
            "uniquing bypassed expanded work limits");
  });
  cases.run("logical signature formation shares limits and permissions", [&] {
    LogicalTypePermissions permissions;
    require(succeeded(verifyLogicalTypes(emit, {}, &permissions)) &&
                permissions.copy && permissions.drop,
            "empty logical signature changed permissions");
    auto rng = runtime::CapabilityType::get(
        &context, runtime::CapabilityKind::Random, "bls12-381.fr");
    require(succeeded(verifyLogicalTypes(emit, {rng, field}, &permissions)) &&
                !permissions.copy && !permissions.drop,
            "later copyable input reset aggregate permissions");
    auto wide = variant(SmallVector<Type>(512, field));
    require(succeeded(verifyLogicalTypes(emit, {wide, wide})),
            "bounded repeated signature refused");
    SmallVector<Type> inputs(600, wide);
    codes.clear();
    require(failed(verifyLogicalTypes(emit, inputs)) &&
                llvm::is_contained(codes, "logical-type-formation"),
            "signature reset its expanded budget per input");
    require(succeeded(data::DomainType::verify(emit, {wide, wide})) &&
                failed(data::DomainType::verify(emit, inputs)),
            "finite domain reset its expanded budget per item");
    MLIRContext foreign;
    require(failed(verifyLogicalTypes(
                emit, {builder.getI1Type(), IntegerType::get(&foreign, 1)})),
            "signature admitted types from different contexts");
  });
  return cases.result();
}
