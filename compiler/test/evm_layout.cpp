#include "../lib/Target/Evm/Arithmetic.h"
#include "mlir/AsmParser/AsmParser.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/Verifier.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Dialect/Algebra/IR/AlgebraAttrs.h"
#include "zkc/Dialect/Commitment/IR/CommitmentTypes.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Evm/Evm.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#include "zkc/Target/Evm/Layout.h"
#include "zkc/Target/Evm/Wire.h"

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
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
  for (auto facts : protocol::plonky3Fields())
    cases.run("ascending-binomial facts: " + facts.identity, [&] {
      const auto *value = take(layouts.field(field(facts.identity)));
      require(value->degree == facts.degree &&
                  value->base == field(facts.base) &&
                  value->coefficientBytes() == uint64_t(facts.degree) * 32,
              "extension basis facts were lost");
      require(value->beta == APInt(256, facts.nonresidue),
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
    refuses(layouts.get(data::FixedVectorType::get(&context, group, 0)),
            "evm.layout");
    refuses(layouts.get(data::SequenceType::get(&context, group)),
            "evm.layout");
  });
  cases.run("inactive alternatives are fully admitted", [&] {
    auto group = algebra::GroupType::get(&context, "bls12-381.g1");
    auto value =
        variant({alternative("empty", {}), alternative("inactive", {group})});
    refuses(layouts.get(value), "evm.layout");
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
    auto result = evm::CheckedOp::create(builder, loc, outputs, code, arguments,
                                         attributes);
    return std::make_pair(std::move(module), result);
  };
  cases.run(
      "positive verification requires logical field and exact expanded "
      "signature",
      [&] {
        auto missing = operation("field.mul", {}, {i256, i256}, {i256});
        require(failed(missing.second.verify()),
                "width-only admission accepted missing type");
        auto wrong = operation("field.mul", extension, {i256, i256}, {i256});
        require(failed(wrong.second.verify()),
                "extension accepted prime signature");
        auto correct = operation("field.mul", extension, {i64, i64}, {i64});
        require(succeeded(correct.second.verify()),
                "exact extension signature refused");
        auto stray = operation(
            "field.mul", base, {i256, i256}, {i256},
            {builder.getNamedAttr("parameters", builder.getArrayAttr({}))});
        require(failed(stray.second.verify()),
                "uninterpreted invocation attributes admitted");
      });
  cases.run("wrong nominal constant and static selectors refuse", [&] {
    auto literal = algebra::FieldLiteralAttr::get(
        &context, base,
        builder.getIntegerAttr(
            IntegerType::get(&context, 31, IntegerType::Unsigned), 1));
    auto wrong = operation("field.constant", extension, {}, {i64},
                           {builder.getNamedAttr("value", literal)});
    require(failed(wrong.second.verify()),
            "wrong nominal field literal admitted");
    auto value = variant({alternative("empty", {})});
    auto selector = operation(
        "variant.make", value, {}, {i64},
        {builder.getNamedAttr("alternative", builder.getI32IntegerAttr(1))});
    require(failed(selector.second.verify()),
            "out-of-range inactive selector admitted");
  });
  cases.run("construction stores refuse borrowed or mismatched buffers", [&] {
    auto vector = data::FieldVectorType::get(&context, base.getDomain());
    auto borrowed = operation("vector.set", vector, {i64, i64, i64, i256}, {});
    require(failed(borrowed.second.verify()),
            "borrowed immutable vector gained a store");
    auto sequence = data::SequenceType::get(&context, builder.getI1Type());
    auto borrowedSequence = operation("sequence.set", sequence,
                                      {i64, i64, i64, builder.getI1Type()}, {});
    require(failed(borrowedSequence.second.verify()),
            "borrowed sequence gained a store");
    auto module = std::move(borrowed.first);
    builder.setInsertionPoint(borrowed.second);
    auto count = borrowed.second.getOperand(1);
    auto attr = builder.getNamedAttr("value_type", TypeAttr::get(vector));
    auto allocation = evm::CheckedOp::create(builder, loc, {i64},
                                             "vector.alloc", {count}, {attr});
    borrowed.second->setOperand(0, allocation->getResult(0));
    require(succeeded(borrowed.second.verify()),
            "fresh exact construction buffer refused");
    borrowed.second->setOperand(1, borrowed.second.getOperand(2));
    require(failed(borrowed.second.verify()),
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
  return cases.result();
}
