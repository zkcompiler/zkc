#include "support/NativeCases.h"
#include "zkc/Contracts/SourceTerms.h"
#include "zkc/Language/SourceTerms.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace zkc::language;
using zkc::test::require;
using zkc::test::take;
namespace {
using K = Type::Kind;
Type product(std::vector<Type> children = {}) {
  Type result(K::DescriptorProduct);
  result.arguments = std::move(children);
  return result;
}
Type sequence(Type child, std::optional<uint64_t> extent = {}) {
  Type result(K::DescriptorSequence);
  result.arguments.push_back(std::move(child));
  if (extent) {
    Type natural(K::Natural);
    natural.dimension = Natural::constant(*extent);
    result.arguments.push_back(std::move(natural));
  }
  return result;
}
Type finite(Type item) {
  return descriptorType(DescriptorContract(DescriptorFamily::Finite, {item}));
}
json::Value fixtures() {
  json::Array terms;
  auto add = [&](StringRef name, const Type &type) {
    terms.push_back(
        json::Object{{"name", name}, {"term", take(encodeStaticTerm(type))}});
  };
  auto boolean = finite(Type{});
  auto field = finite(domainType("Field", "bls12-381.fr"));
  add("finite-bool", boolean);
  add("finite-field", field);
  add("empty-product", product());
  add("ordered-product", product({boolean, field}));
  add("reversed-product", product({field, boolean}));
  add("unsized", sequence(boolean));
  add("zero", sequence(boolean, 0));
  add("positive", sequence(field, 7));
  add("nested", product({sequence(product({field, boolean}), 2),
                         sequence(product()), product({boolean})}));
  add("boolean", Type{});
  Type tuple(K::Tuple);
  tuple.arguments = {Type{}, Type(K::Index)};
  add("tuple", tuple);
  Type array(K::Array);
  array.arguments = {Type{}};
  array.dimension = Natural::constant(0);
  add("array-zero", array);
  Type formal(K::Formal, "vendor.Family");
  formal.arguments = {domainType("Field", "koala-bear")};
  add("formal", formal);
  Type record(K::LogicalRecord, "sample::Logical");
  record.arguments = {Type{}};
  add("logical-record", record);
  return json::Object{{"format", "zkc.source-term-fixtures/0"},
                      {"terms", std::move(terms)}};
}
void check(const json::Value &term, bool accepted) {
  auto error = zkc::checkStaticTerm(term);
  require(!bool(error) == accepted, "unexpected static term result");
  if (error)
    require(toString(std::move(error)).find("source.static-term") !=
                std::string::npos,
            "unexpected static term diagnostic");
}
json::Value parse(StringRef bytes) { return take(json::parse(bytes)); }
} // namespace
int main(int argc, char **argv) {
  if (argc == 3 && StringRef(argv[1]) == "--emit-fixtures") {
    std::error_code error;
    raw_fd_ostream out(argv[2], error);
    if (error)
      return 1;
    out << formatv("{0:2}\n", fixtures());
    return 0;
  }
  zkc::test::Cases cases;
  cases.run("public producer matches the retained exact current fixtures", [] {
    auto file = MemoryBuffer::getFile(ZKC_SOURCE_TERM_FIXTURES);
    require(bool(file), "cannot read source term fixture");
    require(fixtures() == parse((*file)->getBuffer()), "fixture drift");
    auto emitted = fixtures();
    for (const auto &row : *emitted.getAsObject()->getArray("terms")) {
      const auto &term = *row.getAsObject()->get("term");
      check(term, true);
      if (auto error = zkc::checkProtocolOrigin(
              json::Array{"sample::Run", json::Array{json::Array{"C", term}}}))
        throw std::runtime_error(toString(std::move(error)));
    }
    require(take(encodeStaticTerm(sequence(finite(Type{})))) !=
                take(encodeStaticTerm(sequence(finite(Type{}), 0))),
            "absent extent equals zero");
    require(take(encodeStaticTerm(
                product({finite(Type{}), finite(Type(K::Index))}))) !=
                take(encodeStaticTerm(
                    product({finite(Type(K::Index)), finite(Type{})}))),
            "product order lost");
  });
  for (
      StringRef text :
      {R"(["descriptor-product"])",
       R"(["descriptor-product",[],0])",
       R"(["descriptor-product",{}])",
       R"(["descriptor-product",[["bool"]]])",
       R"(["descriptor-product",[["tuple",[]]]])",
       R"(["descriptor-product",[["array",["bool"],"0"]]])",
       R"(["descriptor-product",[["builtin","descriptor_product",[]]]])",
       R"(["descriptor-product",[["builtin","Constraint",[]]]])",
       R"(["descriptor-product",[["formal","finite",[["bool"]]]]])",
       R"(["descriptor-product",[["builtin","Finite",[["bool"]]]]])",
       R"(["descriptor-product",[["builtin","finite",[]]]])",
       R"(["descriptor-product",[["builtin","finite",[["bool"],["index"]]]]])",
       R"(["descriptor-product",[["builtin","finite",[["bool"]],0]]])",
       R"(["descriptor-sequence",["descriptor-product",[]]])",
       R"(["descriptor-sequence",["descriptor-product",[]],null,0])",
       R"(["descriptor-sequence",["bool"],null])",
       R"(["descriptor-sequence",["descriptor-product",[]],"0"])",
       R"(["descriptor-sequence",["descriptor-product",[]],0])",
       R"(["descriptor-sequence",["descriptor-product",[]],["nat",0]])",
       R"(["descriptor-sequence",["descriptor-product",[]],["nat","00"]])",
       R"(["descriptor-sequence",["descriptor-product",[]],["nat","-1"]])",
       R"(["descriptor-sequence",["descriptor-product",[]],["nat","1e2"]])",
       R"(["descriptor-sequence",["descriptor-product",[]],["nat","0",0]])",
       R"(["descriptor-sequence",["descriptor-product",[]],["index"]])",
       R"(["descriptor-sequence",["descriptor-product",[]],["parameter","N"]])",
       R"(["descriptor_sequence",["descriptor-product",[]],null])"})
    cases.run(Twine("small malformed term: ") + text,
              [&] { check(parse(text), false); });
  cases.run("wire recognition and Type formation remain separate", [] {
    // The wire checks a Finite leaf's exact syntax, not its data eligibility.
    check(
        parse(R"(["descriptor-product",[["builtin","finite",[["nat","0"]]]]])"),
        true);
    // Existing ordinary roots remain the general grammar, including builtin
    // names.
    check(parse(R"(["builtin","finite",[]])"), true);
    check(parse(R"(["builtin","Constraint",[]])"), true);
    require(
        take(encodeStaticTerm(sequence(product(), UINT64_MAX))) ==
            parse(
                R"(["descriptor-sequence",["descriptor-product",[]],["nat","18446744073709551615"]])"),
        "extent identity was expanded or narrowed");
    zkc::test::refuses(encodeStaticTerm(product({Type{}})),
                       "source.descriptor");
    zkc::test::refuses(encodeStaticTerm(sequence(Type{})), "source.descriptor");
    zkc::test::refuses(encodeStaticTerm(Type(K::DescriptorSequence)),
                       "source.descriptor");
    Type wrongExtent = sequence(product(), 0);
    wrongExtent.arguments.back() = Type(K::Index);
    zkc::test::refuses(encodeStaticTerm(wrongExtent), "source.descriptor");
    zkc::test::refuses(encodeStaticTerm(finite(Type(K::Natural))),
                       "source.descriptor");
    Type open = sequence(product(), 0);
    open.arguments.back().dimension = take(Natural::atom("scope::N"));
    open.arguments.back().symbolic = true;
    open.arguments.back().domain = "scope::N";
    zkc::test::refuses(encodeStaticTerm(open), "source.static-term");
  });
  cases.run("wire child and string limits stay inclusive", [] {
    auto tree = product(std::vector<Type>(512, product()));
    check(take(encodeStaticTerm(tree)), true);
    tree.arguments.push_back(product());
    zkc::test::refuses(encodeStaticTerm(tree), "source.limit");
    json::Array children;
    for (unsigned i = 0; i < 513; ++i)
      children.push_back(json::Array{"descriptor-product", json::Array{}});
    check(json::Array{"descriptor-product", std::move(children)}, false);
    for (unsigned size : {512, 513}) {
      check(json::Array{"descriptor-sequence",
                        json::Array{"descriptor-product", json::Array{}},
                        json::Array{"nat", std::string(size, '9')}},
            size == 512);
      check(json::Array{"descriptor-product",
                        json::Array{json::Array{
                            "builtin", "finite",
                            json::Array{json::Array{"field",
                                                    std::string(size, 'x')}}}}},
            size == 512);
    }
  });
  cases.run("named arguments preserve the exact 128 binding limit", [] {
    json::Array bindings;
    for (unsigned i = 0; i < 128; ++i)
      bindings.push_back(
          json::Array{"C" + std::to_string(i),
                      json::Array{"descriptor-product", json::Array{}}});
    json::Value origin = json::Array{"sample::Run", std::move(bindings)};
    auto accepted = zkc::checkProtocolOrigin(origin);
    require(!accepted, "128 origin bindings refused");
    (*origin.getAsArray())[1].getAsArray()->push_back(
        json::Array{"extra", json::Array{"descriptor-product", json::Array{}}});
    auto refused = zkc::checkProtocolOrigin(origin);
    require(bool(refused), "129 origin bindings accepted");
    consumeError(std::move(refused));
  });
  cases.run("descriptor depth counts each term including present Natural", [] {
    Type tree = sequence(product(), 0);
    for (unsigned i = 0; i < 62; ++i)
      tree = sequence(std::move(tree));
    auto wire = take(encodeStaticTerm(tree));
    check(wire, true); // 64 levels, with empty Product and Natural at level 64.
    check(json::Array{"descriptor-sequence", std::move(wire), nullptr}, false);
    tree = sequence(std::move(tree));
    zkc::test::refuses(encodeStaticTerm(tree), "source.limit");
  });
  cases.run("present Natural consumes aggregate budget and null does not", [] {
    std::vector<Type> groups;
    for (unsigned i = 0; i < 8; ++i)
      groups.push_back(
          product(std::vector<Type>(i == 7 ? 508 : 511, product())));
    auto tree = product(std::move(groups));               // 4094 nodes.
    tree.arguments[0].arguments[0] = sequence(product()); // 4095.
    check(take(encodeStaticTerm(tree)), true);
    tree.arguments[0].arguments[0] = sequence(product(), 0); // 4096.
    auto wire = take(encodeStaticTerm(tree));
    check(wire, true);
    json::Value origin =
        json::Array{"sample::Run", json::Array{json::Array{"C", wire}}};
    require(!zkc::checkProtocolOrigin(origin), "4096 origin nodes refused");
    (*(*origin.getAsArray())[1].getAsArray())
        .push_back(json::Array{"N", json::Array{"nat", "0"}});
    auto error = zkc::checkProtocolOrigin(origin);
    require(bool(error), "aggregate 4097 accepted");
    consumeError(std::move(error));
    tree.arguments[0].arguments[1] = sequence(product()); // 4097.
    zkc::test::refuses(encodeStaticTerm(tree), "source.limit");
    auto &first = (*(*wire.getAsArray())[1].getAsArray())[0];
    auto &second = (*(*first.getAsArray())[1].getAsArray())[1];
    second = json::Array{"descriptor-sequence", second, nullptr};
    check(wire, false);
  });
  return cases.result();
}
