#include "../lib/Target/Evm/Arithmetic.h"
#include "../lib/Target/Evm/Authentication.h"
#include "mlir/AsmParser/AsmParser.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Instances.h"
#include "zkc/Dialect/Algebra/IR/AlgebraAttrs.h"
#include "zkc/Dialect/Commitment/IR/CommitmentTypes.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Evm/Evm.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialTypes.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#include "zkc/Target/Evm/Curve.h"
#include "zkc/Target/Evm/Layout.h"
#include "zkc/Target/Evm/Wire.h"

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace {
// Deliberately bypass builders for malformed concrete ODS verifier fixtures.
Operation *physicalFixture(OpBuilder &builder, Location loc, TypeRange results,
                           StringRef mnemonic, ValueRange operands,
                           ArrayRef<NamedAttribute> attributes = {}) {
  OperationState state(loc, ("evm." + mnemonic).str());
  state.addOperands(operands);
  state.addTypes(results);
  state.addAttributes(attributes);
  return builder.create(state);
}
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  registry.insert<evm::EvmDialect>();
  MLIRContext context(registry, MLIRContext::Threading::DISABLED);
  context.loadAllAvailableDialects();
  OpBuilder builder(&context);
  auto loc = builder.getUnknownLoc();
  ScopedDiagnosticHandler suppress(&context,
                                   [](Diagnostic &) { return success(); });
  evm::NativeLayouts layouts(context);
  auto field = [&](StringRef domain) {
    return algebra::FieldType::get(&context, domain);
  };
  auto variant = [&](ArrayRef<data::AlternativeAttr> alternatives) {
    auto identity = data::IdentityAttr::get(
        &context,
        builder.getArrayAttr({builder.getStringAttr("atom"),
                              builder.getStringAttr("LayoutRecord")}));
    return data::VariantType::get(&context, identity, alternatives);
  };
  auto alternative = [&](StringRef label, ArrayRef<Type> payload) {
    return data::AlternativeAttr::get(&context, builder.getStringAttr(label),
                                      payload);
  };
  auto base = field("koala-bear");
  auto extension = field("koala-bear.ext4-binomial3");
  auto i64 = builder.getI64Type();
  auto i256 = builder.getIntegerType(256);
  auto index = IntegerType::get(&context, 64, IntegerType::Unsigned);
  cases.run(
      "exact installed prime facts and immutable descriptor addresses", [&] {
        const auto *first = take(layouts.field(base));
        require(first->degree == 1 &&
                    first->modulus == APInt(256, 2130706433) &&
                    first->base == base,
                "inexact base field facts");
        for (StringRef name :
             {"bls12-381.fr", "bn254.fr", "ristretto255.scalar", "baby-bear",
              "goldilocks"}) {
          auto *value = take(layouts.field(field(name)));
          auto *installed = protocol::installedDomains().domain(name);
          APInt expected;
          require(
              installed &&
                  !StringRef(installed->modulus).getAsInteger(10, expected) &&
                  expected.zextOrTrunc(256) == value->modulus,
              "prime modulus differed from installation");
          require(take(layouts.get(field(name)))->lanes == ArrayRef<Type>{i256},
                  "prime lane was not i256");
        }
        require(first == take(layouts.field(base)),
                "cache invalidated descriptor address");
      });
  // Every residue field: a prime field, or a binomial extension of one.
  for (const auto &form : protocol::installation::fieldForms())
    if (form.arithmetic)
      cases.run("ascending-binomial facts: " + form.field, [&] {
        auto extension = protocol::instances::binomialExtension(form.field);
        unsigned degree = extension ? extension->degree : 1;
        auto baseField = field(extension ? extension->base : form.field);
        std::string nonresidue = extension ? extension->nonresidue : "0";
        const auto *value = take(layouts.field(field(form.field)));
        require(value->degree == degree && value->base == baseField &&
                    value->coefficientBytes() == uint64_t(degree) * 32,
                "extension basis facts were lost");
        require(value->beta == APInt(256, nonresidue, 10),
                "wrong binomial reduction");
      });
  for (StringRef name :
       {"gf2-64.pentanomial-4-3-1", "gf2-64.pentanomial-4-3-1.ext3-trinomial1"})
    cases.run("characteristic two is not a residue prime: " + name, [&] {
      refuses(layouts.field(field(name)), "evm.field");
      refuses(layouts.get(field(name)), "evm.field");
    });
  cases.run("coefficient stride differs from complete lane-cell stride", [&] {
    auto vector = data::FieldVectorType::get(&context, extension.getDomain());
    auto sequence = data::SequenceType::get(&context, extension);
    auto nested = data::SequenceType::get(&context, vector);
    require(take(layouts.get(vector))->collection->strideBytes == 128 &&
                take(layouts.get(sequence))->collection->strideBytes == 32 &&
                take(layouts.get(nested))->collection->strideBytes == 64,
            "extension/vector/sequence storage units conflated");
    require(take(layouts.get(extension))->lanes == ArrayRef<Type>{i64},
            "extension was expanded into coefficients");
    require(take(layouts.get(data::BytesType::get(&context)))
                    ->collection->strideBytes == 1,
            "bytes were not packed");
  });
  cases.run("fixed collections retain complete empty-element layout", [&] {
    auto array = data::FieldArrayType::get(&context, extension.getDomain(), 0);
    auto fixed = data::FixedVectorType::get(
        &context, data::SequenceType::get(&context, extension), 0);
    require(take(layouts.get(array))->collection->strideBytes == 128 &&
                take(layouts.get(fixed))->collection->strideBytes == 64,
            "fixed collection stride ignored empty child");
    auto group = algebra::GroupType::get(&context, "bls12-381.g1");
    require(take(layouts.get(data::FixedVectorType::get(&context, group, 0)))
                        ->collection->strideBytes == 32 &&
                take(layouts.get(data::SequenceType::get(&context, group)))
                        ->collection->strideBytes == 32,
            "group containers lost immutable pointer cells");
  });
  cases.run("inactive alternatives are fully admitted", [&] {
    auto group = algebra::GroupType::get(&context, "bls12-381.g1");
    auto value =
        variant({alternative("empty", {}), alternative("inactive", {group})});
    take(layouts.get(value));
    auto unsupported = algebra::GroupType::get(&context, "bls12-381.g2");
    auto bad = variant(
        {alternative("empty", {}), alternative("inactive", {unsupported})});
    refuses(layouts.get(bad), "evm.group");
    auto resource = runtime::ScopeType::get(&context);
    auto affine = variant(
        {alternative("empty", {}), alternative("inactive", {resource})});
    refuses(layouts.get(affine), "evm.layout");
  });
  cases.run("variant payload and signature use logical value slices", [&] {
    auto vector = data::FieldVectorType::get(&context, extension.getDomain());
    auto value = variant({alternative("empty", {}),
                          alternative("value", {extension, vector, index})});
    require(take(layouts.get(value))->lanes.size() == 1,
            "variant did not use a box");
    require(take(layouts.payload(value, 0)).lanes.empty(),
            "empty alternative acquired payload cells");
    auto payload = take(layouts.payload(value, 1));
    require(payload.lanes.size() == 4 && payload.values.size() == 3 &&
                payload.values[1].first == 1 && payload.values[1].count == 2,
            "payload flattening lost complete value boundaries");
    refuses(layouts.payload(value, 2), "evm.layout");
  });
  cases.run("nominal custody slots erase without erasing adjacent data", [&] {
    auto a = runtime::CapabilityType::get(
        &context, runtime::CapabilityKind::ResourceUnit, "Slot.A");
    auto b = runtime::CapabilityType::get(
        &context, runtime::CapabilityKind::ResourceUnit, "Slot.B");
    auto vector = data::FieldVectorType::get(&context, base.getDomain());
    auto signature = take(layouts.signature({a, base, b, vector, a}));
    require(
        a != b && signature.values.size() == 5 &&
            signature.lanes == ArrayRef<Type>{i256, i64, i64} &&
            signature.values[0].first == 0 && signature.values[0].count == 0 &&
            signature.values[1].first == 0 && signature.values[1].count == 1 &&
            signature.values[2].first == 1 && signature.values[2].count == 0 &&
            signature.values[3].first == 1 && signature.values[3].count == 2 &&
            signature.values[4].first == 3 && signature.values[4].count == 0,
        "zero-storage custody shifted or erased data lanes");
    require(take(layouts.signature({a, b})).lanes.empty(),
            "empty custody-only signature acquired storage");
    refuses(layouts.get(a), "evm.layout");
    auto wire = evm::verifyWireType(layouts, a);
    require(bool(wire), "unit acquired a wire codec");
    consumeError(std::move(wire));
    auto transcript = runtime::CapabilityType::get(
        &context, runtime::CapabilityKind::Transcript,
        "hash-chain.keccak256.bls12-381.fr64be/0");
    refuses(layouts.signature({transcript}), "evm.layout");
    MLIRContext foreign(registry);
    foreign.loadAllAvailableDialects();
    auto other = runtime::CapabilityType::get(
        &foreign, runtime::CapabilityKind::ResourceUnit, "Slot.A");
    refuses(layouts.signature({other}), "evm.layout");
  });
  cases.run("local representation does not grant a wire codec", [&] {
    auto fixed = data::FixedVectorType::get(&context, base, 0);
    take(layouts.get(fixed));
    auto error = evm::verifyWireType(layouts, fixed);
    require(bool(error), "local fixed vector acquired wire permission");
    consumeError(std::move(error));
    auto scalar = data::FieldArrayType::get(&context, "koala-bear", 0);
    take(layouts.get(scalar));
    error = evm::verifyWireType(layouts, scalar);
    require(bool(error), "unsupported concrete array codec was admitted");
    consumeError(std::move(error));
  });
  cases.run("root and path envelopes preserve exact nominal kinds", [&] {
    StringRef scheme = "rows.merkle-keccak256.koala-bear.ext4-binomial3/0";
    auto root =
        commitment::VectorObjectType::get(&context, scheme, "commitment");
    auto path = commitment::VectorObjectType::get(&context, scheme, "proof");
    auto *r = take(layouts.get(root));
    auto *p = take(layouts.get(path));
    require(r->kind == evm::ValueLayout::Kind::Root &&
                p->kind == evm::ValueLayout::Kind::Path &&
                r->lanes.size() == 2 && p->lanes.size() == 2 &&
                !r->collection && !p->collection,
            "envelopes lost nominal identity");
    refuses(layouts.get(commitment::VectorObjectType::get(&context, scheme,
                                                          "opening_state")),
            "evm.layout");
  });
  auto operation = [&](StringRef code, Type type, TypeRange inputs,
                       TypeRange outputs, ArrayRef<NamedAttribute> extra = {}) {
    OwningOpRef<ModuleOp> module(ModuleOp::create(loc));
    builder.setInsertionPointToEnd(module->getBody());
    SmallVector<Value> arguments;
    for (Type lane : inputs)
      arguments.push_back(arith::ConstantOp::create(
          builder, loc, lane, builder.getIntegerAttr(lane, 0)));
    SmallVector<NamedAttribute> attributes(extra.begin(), extra.end());
    if (type)
      attributes.push_back(
          builder.getNamedAttr("value_type", TypeAttr::get(type)));
    auto result =
        physicalFixture(builder, loc, outputs, code, arguments, attributes);
    return std::make_pair(std::move(module), result);
  };
  cases.run("G1 adapter pins Scalar, codec and padded affine layout", [&] {
    auto group = algebra::GroupType::get(&context, "bls12-381.g1");
    auto facts = take(evm::realizeGroup(group));
    auto *value = take(layouts.get(group));
    require(value == take(layouts.get(group)) &&
                value->kind == evm::ValueLayout::Kind::Group &&
                value->lanes == ArrayRef<Type>{i64} && !value->collection &&
                facts.scalar == field("bls12-381.fr") && facts.frameTag == 9 &&
                facts.baseModulus.getActiveBits() == 381 &&
                facts.scalarModulus.getActiveBits() == 255 &&
                evm::GroupLayout::affineBytes == 128,
            "curve facts were inferred from scalar width or lost");
    for (StringRef name : {"bls12-381.g2", "bn254.g1"})
      refuses(layouts.get(algebra::GroupType::get(&context, name)),
              "evm.group");
    require(!parseType(R"(!algebra.field<"bls12-381.fq">)", &context),
            "uninstalled base field bypassed checked type admission");
    for (auto fork : {EvmFork::Prague, EvmFork::Osaka}) {
      auto error = evm::verifyGroupFork(fork);
      require(!error, "supported group fork refused");
    }
    auto error = evm::verifyGroupFork(EvmFork::Cancun);
    require(bool(error) && toString(std::move(error)).find("evm.group-fork") !=
                               std::string::npos,
            "Cancun acquired EIP-2537 support");
  });
  for (StringRef code : {"group.add", "group.scale", "group.equal"}) {
    cases.run("typed ordered curve signature " + code, [&] {
      auto group = algebra::GroupType::get(&context, "bls12-381.g1");
      Type second = code == "group.scale" ? Type(i256) : Type(i64);
      Type result =
          code == "group.equal" ? Type(builder.getI1Type()) : Type(i64);
      auto correct = operation(code, group, {i64, second}, {result});
      require(succeeded(verify(correct.second)) &&
                  !isMemoryEffectFree(correct.second),
              "group operation lost signature or ordered effects");
      auto wrong = operation(code, base, {i64, second}, {result});
      require(failed(verify(wrong.second)), "field admitted as group");
      auto widths = operation(code, group, {i256, second}, {result});
      require(failed(verify(widths.second)), "wide group pointer admitted");
      auto missing = operation(code, {}, {i64, second}, {result});
      require(failed(verify(missing.second)), "untyped group admitted");
      auto stray = operation(
          code, group, {i64, second}, {result},
          {builder.getNamedAttr("parameters", builder.getArrayAttr({}))});
      require(failed(verify(stray.second)),
              "uninterpreted group attributes admitted");
    });
  }
  cases.run(
      "positive verification requires logical field and exact expanded "
      "signature",
      [&] {
        auto missing = operation("field.mul", {}, {i256, i256}, {i256});
        require(failed(verify(missing.second)),
                "width-only admission accepted missing type");
        auto wrong = operation("field.mul", extension, {i256, i256}, {i256});
        require(failed(verify(wrong.second)),
                "extension accepted prime signature");
        auto correct = operation("field.mul", extension, {i64, i64}, {i64});
        require(succeeded(verify(correct.second)),
                "exact extension signature refused");
        auto stray = operation(
            "field.mul", base, {i256, i256}, {i256},
            {builder.getNamedAttr("parameters", builder.getArrayAttr({}))});
        require(failed(verify(stray.second)),
                "uninterpreted invocation attributes admitted");
      });
  cases.run("wrong nominal constant and static selectors refuse", [&] {
    auto literal = algebra::FieldLiteralAttr::get(
        &context, base,
        builder.getIntegerAttr(
            IntegerType::get(&context, 31, IntegerType::Unsigned), 1));
    auto wrong = operation("field.constant", extension, {}, {i64},
                           {builder.getNamedAttr("value", literal)});
    require(failed(verify(wrong.second)),
            "wrong nominal field literal admitted");
    auto value = variant({alternative("empty", {})});
    auto selector = operation(
        "variant.make", value, {}, {i64},
        {builder.getNamedAttr("alternative", builder.getI32IntegerAttr(1))});
    require(failed(verify(selector.second)),
            "out-of-range inactive selector admitted");
  });
  cases.run("construction stores refuse borrowed or mismatched buffers", [&] {
    auto vector = data::FieldVectorType::get(&context, base.getDomain());
    auto borrowed = operation("vector.set", vector, {i64, i64, i64, i256}, {});
    require(failed(verify(borrowed.second)),
            "borrowed immutable vector gained a store");
    auto sequence = data::SequenceType::get(&context, builder.getI1Type());
    auto borrowedSequence = operation("sequence.set", sequence,
                                      {i64, i64, i64, builder.getI1Type()}, {});
    require(failed(verify(borrowedSequence.second)),
            "borrowed sequence gained a store");
    auto module = std::move(borrowed.first);
    builder.setInsertionPoint(borrowed.second);
    auto count = borrowed.second->getOperand(1);
    auto attr = builder.getNamedAttr("value_type", TypeAttr::get(vector));
    auto allocation =
        physicalFixture(builder, loc, {i64}, "vector.alloc", {count}, {attr});
    borrowed.second->setOperand(0, allocation->getResult(0));
    require(succeeded(verify(borrowed.second)),
            "fresh exact construction buffer refused");
    borrowed.second->setOperand(1, borrowed.second->getOperand(2));
    require(failed(verify(borrowed.second)),
            "mismatched construction count admitted");
  });
  cases.run(
      "generated helpers share exact coefficient layouts and selected "
      "algorithms",
      [&] {
        evm::detail::Arithmetic arithmetic(layouts, {});
        auto primeInverse = operation("field.inverse", base, {i256}, {i256});
        auto inverse = operation("field.inverse", extension, {i64}, {i64});
        auto equal = operation("field.equal", extension, {i64, i64},
                               {builder.getI1Type()});
        auto v4 = data::FieldVectorType::get(&context, extension.getDomain());
        auto get4 = operation("vector.get", v4, {i64, i64, i64}, {i64});
        auto v1 = data::FieldVectorType::get(&context, base.getDomain());
        auto get1 = operation("vector.get", v1, {i64, i64, i64}, {i256});
        auto n1 = take(arithmetic.helper(get1.second));
        auto n4 = take(arithmetic.helper(get4.second));
        require(n1 != n4 && n1.find("koala") == std::string::npos &&
                    n4.find("koala") == std::string::npos,
                "helper identity lost layout or used protocol names");
        take(arithmetic.helper(primeInverse.second));
        take(arithmetic.helper(inverse.second));
        take(arithmetic.helper(equal.second));
        auto text = arithmetic.helpers();
        require(text.find("staticcall(gas(), 5") != std::string::npos &&
                    text.find("returndatasize(), 32") != std::string::npos &&
                    text.find("evm_math_polynomial_cancel") !=
                        std::string::npos &&
                    text.find("mul(i,128)") != std::string::npos,
                "missing selected arithmetic or extension stride");
        require(text.find("65536") == std::string::npos &&
                    text.find("inverse_loop") == std::string::npos,
                "experimental allocator or obsolete inverse escaped");
      });
  for (StringRef domain : {"koala-bear", "koala-bear.ext4-binomial3",
                           "koala-bear.ext8-binomial3"}) {
    cases.run(
        "internal polynomial layout and exact physical contracts: " + domain,
        [&] {
          auto polynomial = poly::UnivariateType::get(&context, domain);
          auto *layout = take(layouts.get(polynomial));
          auto *f = take(layouts.field(field(domain)));
          auto lane = f->degree == 1 ? i256 : i64;
          require(layout->kind == evm::ValueLayout::Kind::Univariate &&
                      layout->lanes == ArrayRef<Type>{i64, i64} &&
                      layout->collection->strideBytes == f->coefficientBytes(),
                  "polynomial lost normalized coefficient storage");
          auto error = evm::verifyWireType(layouts, polynomial);
          require(bool(error), "internal polynomial acquired wire ingress");
          consumeError(std::move(error));
          // A vector constructor must not grant a normalized polynomial type.
          for (auto mnemonic : {"vector.append", "vector.alloc", "vector.empty",
                                "vector.sum", "vector.length", "vector.get"}) {
            StringRef code(mnemonic);
            SmallVector<Type> inputs, outputs;
            if (code == "vector.append") {
              inputs = {i64, i64, lane};
              outputs = {i64, i64};
            } else if (code == "vector.alloc") {
              inputs = {i64};
              outputs = {i64};
            } else if (code == "vector.empty") {
              outputs = {i64, i64};
            } else if (code == "vector.get") {
              inputs = {i64, i64, i64};
              outputs = {lane};
            } else {
              inputs = {i64, i64};
              outputs = {code == "vector.sum" ? lane : i64};
            }
            auto malformed = operation(code, polynomial, inputs, outputs);
            require(failed(verify(malformed.second)),
                    "vector acquired a normalized polynomial contract");
          }
          if (f->degree == 1) {
            auto zero = algebra::FieldLiteralAttr::get(
                &context, field(domain),
                builder.getIntegerAttr(
                    IntegerType::get(&context, 31, IntegerType::Unsigned), 0));
            auto one = algebra::FieldLiteralAttr::get(
                &context, field(domain),
                builder.getIntegerAttr(
                    IntegerType::get(&context, 31, IntegerType::Unsigned), 1));
            for (auto values : {builder.getArrayAttr({zero}),
                                builder.getArrayAttr({one, zero})}) {
              auto malformed =
                  operation("vector.constant", polynomial, {}, {i64, i64},
                            {builder.getNamedAttr("values", values)});
              require(failed(verify(malformed.second)),
                      "unnormalized vector literals acquired polynomial type");
            }
          }
          for (auto mnemonic :
               {"poly.domain_root", "poly.domain_point",
                "poly.from_coefficients", "poly.univariate_evaluate"}) {
            StringRef code(mnemonic);
            bool from = code == "poly.from_coefficients",
                 evaluate = code == "poly.univariate_evaluate";
            SmallVector<Type> inputs = from ? SmallVector<Type>{i64, i64}
                                       : evaluate
                                           ? SmallVector<Type>{i64, i64, lane}
                                       : code == "poly.domain_point"
                                           ? SmallVector<Type>{lane, i64, i64}
                                           : SmallVector<Type>{i64};
            SmallVector<Type> outputs =
                from ? SmallVector<Type>{i64, i64} : SmallVector<Type>{lane};
            Type valueType =
                from || evaluate ? Type(polynomial) : Type(field(domain));
            auto good = operation(code, valueType, inputs, outputs);
            require(succeeded(verify(good.second)),
                    "precise polynomial operation refused");
            evm::detail::Arithmetic arithmetic(layouts, {});
            take(arithmetic.helper(good.second));
            auto extra = operation(
                code, valueType, inputs, outputs,
                {builder.getNamedAttr("parameters", builder.getArrayAttr({}))});
            require(failed(verify(extra.second)),
                    "polynomial accepted arbitrary parameters");
            auto missing = operation(code, {}, inputs, outputs);
            require(failed(verify(missing.second)),
                    "polynomial accepted missing logical type");
            auto wrong =
                operation(code, data::FieldVectorType::get(&context, domain),
                          inputs, outputs);
            require(failed(verify(wrong.second)),
                    "vector acquired internal polynomial operation");
            inputs[0] = inputs[0] == i256 ? i64 : i256;
            auto wrongLane = operation(code, valueType, inputs, outputs);
            require(failed(verify(wrongLane.second)),
                    "polynomial accepted wrong physical lane");
          }
        });
    cases.run(
        "Keccak row exact installed scheme and physical shape: " + domain, [&] {
          auto scheme = ("rows.merkle-keccak256." + domain + "/0").str();
          auto root =
              commitment::VectorObjectType::get(&context, scheme, "commitment");
          SmallVector<Type> inputs(9, i64);
          auto good =
              operation("oracle.check", root, inputs, {builder.getI1Type()});
          require(succeeded(verify(good.second)),
                  "Keccak row operation refused");
          evm::detail::Authentication authentication(layouts, {});
          take(authentication.helper(good.second));
          auto missing =
              operation("oracle.check", {}, inputs, {builder.getI1Type()});
          require(failed(verify(missing.second)),
                  "authentication accepted missing root identity");
          auto path =
              commitment::VectorObjectType::get(&context, scheme, "proof");
          auto wrongKind =
              operation("oracle.check", path, inputs, {builder.getI1Type()});
          require(failed(verify(wrongKind.second)),
                  "path acquired root authority");
          auto wrongResult = operation("oracle.check", root, inputs, {i64});
          require(failed(verify(wrongResult.second)),
                  "authentication accepted non-bool result");
          auto extra = operation(
              "oracle.check", root, inputs, {builder.getI1Type()},
              {builder.getNamedAttr("parameters", builder.getArrayAttr({}))});
          require(failed(verify(extra.second)),
                  "authentication accepted stray invocation parameters");
          inputs[4] = i256;
          auto wrongLane =
              operation("oracle.check", root, inputs, {builder.getI1Type()});
          require(failed(verify(wrongLane.second)),
                  "authentication accepted non-index position");
        });
  }
  cases.run("bound require has exact Boolean lanes and no attributes", [&] {
    auto good = operation("control.require", {}, {builder.getI1Type()}, {});
    require(succeeded(verify(good.second)), "bound require refused");
    auto wrong = operation("control.require", {}, {i64}, {});
    require(failed(verify(wrong.second)), "bound require accepted non-Boolean");
    auto site = operation(
        "control.require", {}, {builder.getI1Type()}, {},
        {builder.getNamedAttr("site", builder.getStringAttr("guard"))});
    require(failed(verify(site.second)), "backend require acquired guard site");
  });
  cases.run("Poseidon rows do not acquire Keccak authentication", [&] {
    auto root = commitment::VectorObjectType::get(
        &context, "rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0",
        "commitment");
    auto wrong = operation("oracle.check", root, SmallVector<Type>(9, i64),
                           {builder.getI1Type()});
    require(failed(verify(wrong.second)),
            "Poseidon scheme silently substituted");
  });
  cases.run(
      "root operation refuses fields without an installed coset convention",
      [&] {
        auto wrong = operation("poly.domain_root", field("ristretto255.scalar"),
                               {i64}, {i256});
        require(failed(verify(wrong.second)),
                "arbitrary field acquired guessed two-adic root");
      });
  return cases.result();
}
