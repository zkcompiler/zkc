#include "mlir/AsmParser/AsmParser.h"
#include "mlir/IR/Verifier.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/TypeRepresentations.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/TypeFormation.h"
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
  SmallVector<std::string> codes;
  ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
    for (const auto &refusal : diagnostics::refusals(diagnostic))
      codes.push_back(refusal.code);
    return success();
  });
  auto emit = [&] { return emitError(builder.getUnknownLoc()); };
  auto represented = [&](Type logical, StringRef name,
                         ArrayRef<Type> children = {}) {
    auto type = runtime::RepresentedType::getChecked(emit, &context, logical,
                                                     name, children);
    require(bool(type) && succeeded(verifyValueType(emit, type)),
            "formed native representation refused");
    return type;
  };
  auto refuse = [&](Type logical, StringRef name,
                    ArrayRef<Type> children = {}) {
    codes.clear();
    require(!runtime::RepresentedType::getChecked(emit, &context, logical, name,
                                                  children),
            "malformed representation acquired a native type");
    require(llvm::is_contained(codes, "represented-type-formation"),
            "represented formation lost its refusal identity");
  };
  for (const auto &row : protocol::installedDomains().allRepresentations())
    cases.run("atomic representation " + row.identity, [&] {
      SmallVector<Attribute> arguments;
      if (!row.domain.empty())
        arguments.push_back(builder.getStringAttr(row.domain));
      auto logical =
          constructLogicalType(emit, &context, {row.kind, arguments});
      require(bool(logical), "declared atom has no native owner");
      auto physical = represented(logical, row.identity);
      auto bound = take(protocol::encodeBoundType(physical, true));
      require(bound.kind == row.kind && bound.identity == row.domain &&
                  bound.representation == row.identity,
              "native formation differs from byte admission");
      refuse(logical, "missing/representation");
      refuse(logical, row.identity, {physical});
    });
  for (const auto &row : protocol::appliedTypeRepresentations())
    for (uint64_t n : {0u, 1u, 1048576u})
      cases.run(
          "dense representation " + row.representation + " " + llvm::Twine(n),
          [&] {
            SmallVector<Attribute> arguments;
            for (const auto &pattern : row.arguments) {
              const auto &value = pattern.argument;
              if (value.kind == protocol::TypeArgument::Kind::Domain)
                arguments.push_back(builder.getStringAttr(value.domain));
              else if (value.kind == protocol::TypeArgument::Kind::Type) {
                auto type = protocol::decodeBoundType(&context, *value.type);
                require(bool(type), "fixture type unavailable");
                arguments.push_back(TypeAttr::get(type));
              } else
                arguments.push_back(IntegerAttr::get(
                    IntegerType::get(&context, 64, IntegerType::Unsigned), n));
            }
            auto logical = constructLogicalType(emit, &context,
                                                {row.constructor, arguments});
            auto child = protocol::decodeBoundType(&context, row.childType);
            require(logical && child, "dense fixture type unavailable");
            auto physical = represented(logical, row.representation, {child});
            auto bound = take(protocol::encodeBoundType(physical, true));
            require(bound.physicalChildren &&
                        bound.physicalChildren->size() == 1 &&
                        bound.physicalChildren->front() == row.childType,
                    "dense child layout differs at byte publication");
            refuse(logical, row.representation);
            refuse(logical, row.representation, {logicalValueType(child)});
            refuse(logical, row.representation, {child, child});
            refuse(logical, "", {child});
          });
  auto bls = algebra::FieldType::get(&context, "bls12-381.fr");
  auto koala = algebra::FieldType::get(&context, "koala-bear");
  auto ark = represented(bls, "arkworks.fr/0");
  auto blst = represented(bls, "blst/fr");
  auto bear = represented(koala, "plonky3.koala-bear/0");
  cases.run("dense identity includes the exact child representation", [&] {
    auto array = data::FieldArrayType::get(&context, "bls12-381.fr", 4);
    represented(array, "arkworks.field-array/0", {ark});
    represented(array, "blst/field-array", {blst});
    refuse(array, "arkworks.field-array/0", {blst});
    refuse(array, "blst/field-array", {ark});
    refuse(array, "arkworks.field-array/0", {bear});
  });
  auto identity = data::IdentityAttr::get(
      &context, builder.getArrayAttr({builder.getStringAttr("atom"),
                                      builder.getStringAttr("Claim")}));
  auto variant = [&](ArrayRef<Type> payload) {
    return data::VariantType::get(
        &context, identity,
        {data::AlternativeAttr::get(&context, builder.getStringAttr("none"),
                                    {}),
         data::AlternativeAttr::get(&context, builder.getStringAttr("claim"),
                                    payload)});
  };
  cases.run("variant order and inactive payloads retain complete layouts", [&] {
    auto logical = variant({bls, koala});
    represented(logical, "logical.variant/0", {ark, bear});
    represented(logical, "logical.variant/0", {blst, bear});
    refuse(logical, "logical.variant/0", {bear, ark});
    refuse(logical, "logical.variant/0", {ark});
    auto forged = runtime::RepresentedType::get(&context, koala, "blst/fr",
                                                ArrayRef<Type>{});
    refuse(logical, "logical.variant/0", {ark, forged});
    refuse(logical, "logical.sequence/0", {ark, bear});
    refuse(variant({}), "logical.variant/0", {ark});
  });
  cases.run("native structure is independent from wire depth admission", [&] {
    Type logical = koala, physical = bear;
    for (unsigned i = 0; i < 12; ++i) {
      logical = data::SequenceType::get(&context, logical);
      physical = represented(logical, "logical.sequence/0", {physical});
    }
    auto bytes = protocol::encodeBoundType(physical, true);
    require(!bytes, "native formation weakened independent byte limits");
    llvm::consumeError(bytes.takeError());
    require(bool(data::DomainType::getChecked(emit, &context,
                                              ArrayRef<Type>{logical})),
            "finite-domain formation imposed a wire encoding limit");
  });
  cases.run("checked carriers refuse wrong logical stages and contexts", [&] {
    refuse(ark, "arkworks.fr/0");
    refuse(builder.getI64Type(), "native.index/0");
    refuse(bls, "");
    MLIRContext other(registry);
    other.loadAllAvailableDialects();
    auto foreignField = algebra::FieldType::get(&other, "bls12-381.fr");
    auto foreign = runtime::RepresentedType::get(
        &other, foreignField, "arkworks.fr/0", ArrayRef<Type>{});
    refuse(data::SequenceType::get(&context, bls), "logical.sequence/0",
           {foreign});
    auto malformed = runtime::RepresentedType::get(
        &context, foreignField, "arkworks.fr/0", ArrayRef<Type>{});
    require(failed(verifyValueType(emit, malformed)),
            "foreign logical child admitted");
  });
  cases.run(
      "operation formation rechecks forged values and uniform stage", [&] {
        auto forged = runtime::RepresentedType::get(&context, koala, "blst/fr",
                                                    ArrayRef<Type>{});
        for (SmallVector<Type> types :
             {SmallVector<Type>{forged}, SmallVector<Type>{koala, bear}}) {
          Block block;
          auto scope = block.addArgument(runtime::ScopeType::get(&context),
                                         builder.getUnknownLoc());
          for (auto type : types)
            block.addArgument(type, builder.getUnknownLoc());
          OpBuilder b(&context);
          b.setInsertionPointToStart(&block);
          auto outcome = exec::OutcomeType::get(&context, types);
          auto returned = exec::CompleteOp::create(
              b, builder.getUnknownLoc(), outcome, scope,
              block.getArguments().drop_front());
          codes.clear();
          require(failed(verify(returned)) &&
                      llvm::is_contained(codes, "execution-formation"),
                  "forged or mixed-stage completion admitted");
        }
      });
  cases.run("unused callable declarations recheck represented ports", [&] {
    OwningOpRef<ModuleOp> module(ModuleOp::create(builder.getUnknownLoc()));
    OpBuilder b(module->getBody(), module->getBody()->end());
    auto binding = runtime::BindingOp::create(
        b, module->getLoc(), "literal", "field.constant",
        b.getArrayAttr({b.getStringAttr("koala-bear")}), "");
    auto forged = runtime::RepresentedType::get(&context, koala, "blst/fr",
                                                ArrayRef<Type>{});
    binding.setFunctionType(
        executableBindingSignature(b.getFunctionType({}, {forged})));
    codes.clear();
    require(failed(verify(*module)) &&
                llvm::is_contained(codes, "represented-type-formation"),
            "unused binding accepted a forged represented port");
    binding.setFunctionType(
        executableBindingSignature(b.getFunctionType({}, {bear})));
    binding.setImplementation("plonky3/field.constant");
    require(succeeded(verify(*module)),
            "installed physical binding failed native admission");
  });
  cases.run("expanded represented alternatives consume structural work", [&] {
    Type logical = koala, physical = bear;
    for (unsigned i = 0; i < 2; ++i) {
      SmallVector<Type> payload(32, logical), children(32, physical);
      logical = variant(payload);
      physical = represented(logical, "logical.variant/0", children);
    }
    SmallVector<Type> payload(512, logical), children(512, physical);
    refuse(variant(payload), "logical.variant/0", children);
  });
  cases.run("text parser uses the same checked formation", [&] {
    require(
        !parseType(
            "!runtime.represented<!algebra.field<\"koala-bear\">, \"blst/fr\">",
            &context),
        "text parser accepted a mismatched nominal representation");
  });
  return cases.result();
}
