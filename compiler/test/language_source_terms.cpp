#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Contracts/SourceTerms.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Protocol/Origins.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/SourceTerms.h"
#include "zkc/Support/Json.h"

using namespace llvm;
using namespace zkc::language;
using zkc::test::require;
using zkc::test::take;
namespace {
json::Value jsonValue(StringRef text) { return take(json::parse(text)); }
void valid(const json::Value &value) {
  if (auto e = zkc::checkProtocolOrigin(value))
    throw std::runtime_error(toString(std::move(e)));
}
void invalid(const json::Value &value) {
  auto e = zkc::checkProtocolOrigin(value);
  require(bool(e), "accepted invalid origin");
  require(toString(std::move(e)).find("source.protocol-origin") !=
              std::string::npos,
          "unexpected origin diagnostic");
}
Type natural(uint64_t value) {
  Type result(Type::Kind::Natural);
  result.dimension = Natural::constant(value);
  return result;
}
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run("closed constructors preserve every public kind", [] {
    using K = Type::Kind;
    auto field = domainType("Field", "bls12-381.fr");
    auto check = [&](const Type &type, StringRef expected) {
      require(take(encodeStaticTerm(type)) == jsonValue(expected),
              "static term differs");
    };
    check(natural(7), R"(["nat","7"])");
    check(Type{}, R"(["bool"])");
    check(Type(K::Index), R"(["index"])");
    check(Type(K::Unit), R"(["unit"])");
    check(field, R"(["field","bls12-381.fr"])");
    check(domainType("Group", "bls12-381.g1"), R"(["group","bls12-381.g1"])");
    check(domainType("Hash", "h"), R"(["domain","Hash","h"])");
    check(assetType("Ring", "r"), R"(["asset","Ring","r"])");
    for (auto [kind, name] : {std::pair{K::Record, "record"},
                              {K::LogicalRecord, "logical_record"},
                              {K::Variant, "variant"},
                              {K::Associated, "associated"},
                              {K::Module, "module"}}) {
      Type nominal(kind, "library::Item");
      nominal.arguments = {field};
      check(nominal, (Twine("[\"nominal\",\"") + name +
                      "\",\"library::Item\",[[\"field\",\"bls12-381.fr\"]]]")
                         .str());
    }
    Type formal(K::Formal, "polynomial");
    formal.arguments = {field, natural(1)};
    check(formal,
          R"(["formal","polynomial",[["field","bls12-381.fr"],["nat","1"]]])");
    Type builtin(K::Builtin, "vector");
    builtin.arguments = {field};
    check(builtin, R"(["builtin","vector",[["field","bls12-381.fr"]]])");
    Type array(K::Array);
    array.arguments = {formal};
    array.dimension = Natural::constant(3);
    Type tuple(K::Tuple);
    tuple.arguments = {array, builtin};
    auto term = take(encodeStaticTerm(tuple));
    valid(json::Array{"source::Run", json::Array{json::Array{"T", term}}});
    require(take(encodeStaticTerm(Type(K::Record, "x"))) !=
                take(encodeStaticTerm(Type(K::Variant, "x"))),
            "nominal kinds collapsed");
  });
  cases.run("symbolic parameters refuse even inside closed constructors", [] {
    using K = Type::Kind;
    zkc::test::refuses(encodeStaticTerm(Type(K::Parameter, "scope::T")),
                       "source.static-term");
    Type symbolic(K::Field, "scope::F");
    symbolic.symbolic = true;
    zkc::test::refuses(encodeStaticTerm(symbolic), "source.static-term");
    Type formal(K::Formal, "polynomial");
    formal.arguments = {symbolic, natural(1)};
    zkc::test::refuses(encodeStaticTerm(formal), "source.static-term");
  });
  cases.run("origin shape, exact tags, decimals and unique names", [] {
    for (StringRef text :
         {R"([])", R"(["x"])", R"(["x",[],[]])", R"(["x",{}])",
          R"(["x",[["N",["nat","01"]]]])", R"(["x",[["N",["nat",1]]]])",
          R"(["x",[["N",["nat","-1"]]]])", R"(["x",[["T",["parameter","T"]]]])",
          R"(["x",[["T",["bool","extra"]]]])",
          R"(["x",[["T",["array",["bool"]]]]])",
          R"(["x",[["T",["nominal","unknown","X",[]]]]])",
          R"(["x",[["T","field<x>"]]])",
          R"(["x",[["T",["bool"]],["T",["index"]]]])", R"(["bad::",[]])",
          R"(["/file/path",[]])", R"(["x",[["a::b",["bool"]]]])",
          R"(["cafe\u0301::Run",[]])"})
      invalid(jsonValue(text));
    valid(jsonValue(R"(["caf\u00e9::Run",[["N",["nat","0"]]]])"));
  });
  cases.run("origin bounds apply before unbounded tree expansion", [] {
    valid(json::Array{std::string(2048, 'a'), json::Array{}});
    invalid(json::Array{std::string(2049, 'a'), json::Array{}});
    invalid(json::Array{
        "x", json::Array{json::Array{
                 "T", json::Array{"field", std::string(513, 'a')}}}});
    json::Value nested = json::Array{"bool"};
    for (unsigned i = 0; i < 63; ++i)
      nested = json::Array{"tuple", json::Array{std::move(nested)}};
    valid(json::Array{"x", json::Array{json::Array{"T", nested}}});
    nested = json::Array{"tuple", json::Array{std::move(nested)}};
    invalid(json::Array{"x", json::Array{json::Array{"T", nested}}});
    json::Array many;
    for (unsigned i = 0; i < 4096; ++i)
      many.push_back(json::Array{"bool"});
    invalid(json::Array{"x", json::Array{json::Array{
                                 "T", json::Array{"tuple", std::move(many)}}}});
    json::Array groups;
    // Root plus eight tuple children plus 4087 leaves is exactly 4096 nodes.
    for (unsigned i = 0; i < 8; ++i) {
      json::Array leaves;
      for (unsigned j = 0; j < (i == 7 ? 510 : 511); ++j)
        leaves.push_back(json::Array{"bool"});
      groups.push_back(json::Array{"tuple", std::move(leaves)});
    }
    json::Value tree = json::Array{"tuple", std::move(groups)};
    valid(json::Array{"x", json::Array{json::Array{"T", tree}}});
    auto &firstGroup = (*tree.getAsArray())[1].getAsArray()->front();
    (*firstGroup.getAsArray())[1].getAsArray()->push_back(json::Array{"bool"});
    invalid(json::Array{"x", json::Array{json::Array{"T", tree}}});
    json::Array bindings;
    for (unsigned i = 0; i < 129; ++i)
      bindings.push_back(
          json::Array{"N" + std::to_string(i), json::Array{"nat", "0"}});
    invalid(json::Array{"x", std::move(bindings)});
  });
  cases.run(
      "source comparison binds template and declaration ordered arguments", [] {
        auto capture = take(zkc::language::capture({{"orig",
                                                     R"(
      module orig;
      domain F=field("bls12-381.fr");
      protocol Run<T:Type,N:nat> roles(P)(flag:bool@P)->(ok:bool@P){return(ok=flag);}
      entry fn Demo(inputs: Run<(F,index),7>::Inputs) { return Run<(F,index),7>::run(inputs); }
    )",
                                                     {}}}));
        auto project = take(analyze(capture).checkedProject());
        auto entry =
            take(zkc::test::closeProtocolDeployment(project, "orig::Demo"));
        auto original = take(prepareOriginal(entry));
        require(
            take(encodeProtocolOrigin(entry, entry.protocol())) ==
                jsonValue(
                    R"(["orig::Run",[["T",["tuple",[["field","bls12-381.fr"],["index"]]]],["N",["nat","7"]]]])"),
            "wrong protocol key");
        mlir::DialectRegistry registry;
        zkc::registerDialects(registry);
        mlir::MLIRContext context(registry);
        auto snapshot = take(json::parse(
            take(zkc::protocol::exportStructuredSource(
                     original.bytes(), entry.protocol().symbol, context))
                .bytes));
        bool found = false;
        for (const auto &row : *(*snapshot.getAsArray())[7].getAsArray()) {
          const auto *a = row.getAsArray();
          if ((*a)[1].getAsString() == entry.protocol().symbol) {
            found = true;
            require((*a)[8] ==
                        take(encodeProtocolOrigin(entry, entry.protocol())),
                    "origin not exported");
          }
        }
        require(found, "protocol not exported");
        for (StringRef malformedOrigin :
             {R"(["orig::Run",[["N",["nat","01"]]]])",
              R"(["orig::Run",[["T",["parameter","T"]]]])"}) {
          auto candidate = mlir::parseSourceString<mlir::ModuleOp>(
              original.bytes(), &context);
          require(bool(candidate),
                  "cannot parse original for malformed origin");
          candidate->walk([&](zkc::protocol_ir::MathematicalOp op) {
            op.setOriginAttr(zkc::protocol_ir::protocolOriginAttr(
                &context, jsonValue(malformedOrigin)));
          });
          require(failed(zkc::admitStage(*candidate)),
                  "malformed protocol origin passed stage admission");
        }
        for (
            StringRef changedOrigin :
            {R"(["orig::Run",[["N",["nat","7"]],["T",["tuple",[["field","bls12-381.fr"],["index"]]]]]])",
             R"(["orig::Run",[["T",["tuple",[["index"],["field","bls12-381.fr"]]]],["N",["nat","7"]]]])",
             R"(["orig::Run",[["T",["tuple",[["field","koala-bear"],["index"]]]],["N",["nat","7"]]]])"}) {
          auto candidate = mlir::parseSourceString<mlir::ModuleOp>(
              original.bytes(), &context);
          require(bool(candidate), "cannot parse original for origin mutation");
          candidate->walk([&](zkc::protocol_ir::MathematicalOp op) {
            op.setOriginAttr(zkc::protocol_ir::protocolOriginAttr(
                &context, jsonValue(changedOrigin)));
          });
          require(succeeded(mlir::verify(*candidate)),
                  "origin mutation is malformed");
          zkc::test::refuses(compareOriginal(entry, *candidate),
                             "source.correspondence");
        }
        for (auto [before, after] : {std::pair{"orig::Run", "orig::Other"},
                                     {"\"nat\", \"7\"", "\"nat\", \"8\""},
                                     {"\"T\", [\"tuple\"", "\"U\", [\"tuple\""},
                                     {"bls12-381.fr", "koala-bear"}}) {
          auto changed = original.bytes().str();
          auto at = changed.find(before);
          require(at != std::string::npos, "mutation missing");
          changed.replace(at, StringRef(before).size(), after);
          zkc::test::refuses(
              admitOriginal(entry, changed, original.interfaceJson()),
              "source.correspondence");
        }
      });
  return cases.result();
}
