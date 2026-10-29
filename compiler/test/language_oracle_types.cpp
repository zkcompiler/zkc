#include "support/NativeCases.h"
#include "zkc/Language/Builtins.h"
#include "zkc/Language/Layout.h"
#include "zkc/Language/Project.h"
#include "zkc/Language/SourceTerms.h"
#include "llvm/Support/JSON.h"
#include <limits>

using namespace llvm;
using namespace zkc::language;
using zkc::test::require;
using zkc::test::take;
namespace {
Expected<CheckedProject> check(StringRef body) {
  auto captureResult =
      capture({{"m", "module m;domain F=field(\"bls12-381.fr\");" + body.str(),
                "oracles.zkc"}});
  if (!captureResult)
    return captureResult.takeError();
  return analyze(*captureResult).checkedProject();
}
const Declaration &declaration(const CheckedProject &project, StringRef name) {
  for (const auto &decl : project.declarations())
    if (decl.name == name)
      return decl;
  throw std::runtime_error("missing declaration: " + name.str());
}
const char *aliases = R"(
type Table<T:Type+Copy+Drop>=builtin("oracle.table",T);
type FixedTable<T:Type+Copy+Drop,N:nat>=builtin("oracle.table",T,N);
type Oracle<K:OracleKind>=builtin("oracle",K);
type Oracles<K:OracleKind,M:nat>=builtin("oracle_sequence",K,M);
type TableKind=Table<F>;
type O=Oracle<TableKind>;
)";
Type natural(uint64_t value) {
  Type result(Type::Kind::Natural);
  result.dimension = Natural::constant(value);
  return result;
}
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run("logical aliases retain kind identity and unsigned cardinality", [] {
    auto project = take(check(std::string(aliases) + R"(
      type Sized=FixedTable<F,18446744073709551615>;
      type Many=Oracles<Sized,18446744073709551615>;
    )"));
    const auto &kind = declaration(project, "TableKind").domain;
    const auto &oracle = declaration(project, "O").domain;
    const auto &many = declaration(project, "Many").domain;
    require(kind.kind == Type::Kind::OracleKind && isStaticOnly(kind),
            "kind became runtime data");
    require(oracle.kind == Type::Kind::Oracle && !isNativeData(oracle),
            "handle became native data");
    require(many.kind == Type::Kind::OracleSequence && !isSequenceElement(many),
            "handle sequence became ordinary sequence data");
    require(
        take(encodeStaticTerm(many)) ==
            take(json::parse(
                R"(["builtin","oracle_sequence",[["builtin","oracle.table",[["field","bls12-381.fr"],["nat","18446744073709551615"]]],["nat","18446744073709551615"]]])")),
        "typed identity lost kind or maximum");
    require(declaration(project, "Oracle").parameters.front().sort ==
                Parameter::Sort::OracleKind,
            "kind parameter lost its static sort");
    require(typeIdentity(kind) !=
                typeIdentity(declaration(project, "Sized").domain),
            "row cardinality disappeared from identity");
  });
  cases.run("kind constructors reject malformed descriptors", [] {
    auto field = domainType("Field", "bls12-381.fr");
    auto kind = take(builtinType("oracle.table", {field}));
    auto handle = take(builtinType("oracle", {kind}));
    for (const auto &arguments : {std::vector<Type>{},
                                  {natural(1)},
                                  {handle},
                                  {field, field},
                                  {field, natural(2), natural(3)}})
      zkc::test::refuses(builtinType("oracle.table", arguments),
                         "source.oracle-kind");
    zkc::test::refuses(builtinType("oracle", {field}), "source.oracle-kind");
    zkc::test::refuses(builtinType("oracle_sequence", {kind}),
                       "source.oracle-kind");
    zkc::test::refuses(builtinType("oracle_sequence", {kind, field}),
                       "source.oracle-kind");
    Type unknown(Type::Kind::OracleKind, "unknown");
    zkc::test::refuses(builtinType("oracle", {unknown}), "source.oracle-kind");
  });
  for (auto [name, source] : {std::pair{"array", "type Bad=[O;2];"},
                              {"empty array", "type Bad=[O;0];"},
                              {"tuple", "type Bad=(O,index);"},
                              {"record", "struct Bad { value:O }"}})
    cases.run(Twine("refuse logical handles in ") + name, [source = source] {
      zkc::test::refuses(check(std::string(aliases) + source),
                         "source.oracle-aggregate");
    });
  for (auto [name, source] :
       {std::pair{"ordinary sequence", "type Bad=builtin(\"sequence\",O);"},
        {"local function", "fn bad(x:O)->O{return x;}"},
        {"math function", "math fn bad(x:O)->O{return x;}"},
        {"generic data",
         "type Wrap<T:Type+Copy+Drop>=(T,index);type Bad=Wrap<O>;"}})
    cases.run(Twine("refuse logical handles at ") + name, [source = source] {
      zkc::test::refuses(check(std::string(aliases) + source),
                         StringRef(source).contains("sequence")
                             ? "source.builtin"
                             : "source.oracle-boundary");
    });
  cases.run("kind parameters cannot accept ordinary types", [] {
    zkc::test::refuses(check(std::string(aliases) + "type Bad=Oracle<F>;"),
                       "source.generic");
  });
  cases.run("oracle kinds require total table contents", [] {
    zkc::test::refuses(check("type State=builtin(\"shake128_state\");type "
                             "Bad=builtin(\"oracle.table\",State);"),
                       "source.mode");
  });
  cases.run("kind specialization rechecks total row semantics", [] {
    zkc::test::refuses(
        check(std::string(aliases) +
              "type NativePolynomial=builtin(\"polynomial\",F);type "
              "Bad=Table<NativePolynomial>;"),
        "source.mode");
  });

  cases.run("associations normalize through generic kind and row aliases", [] {
    auto project = take(check(std::string(aliases) + R"(
      type DataOf<K:OracleKind>=K::Data;
      type QueryOf<K:OracleKind>=K::Query;
      type AnswerOf<K:OracleKind>=K::Answer;
      type RowData<R:Type+Copy+Drop>=DataOf<Table<R>>;
      type FieldData=RowData<F>;
      type RowAnswer=AnswerOf<Table<F>>;
      type Position=QueryOf<FixedTable<F,0>>;
      type IndexData=DataOf<Table<index>>;
      type BoolData=DataOf<Table<bool>>;
      type PairData=DataOf<Table<(F,index)>>;
      type PairKind=Table<(F,index)>;
      type Empty=Oracles<PairKind,0>;
      math fn identity<K:OracleKind>(x:K::Answer)->K::Answer{return x;}
      math fn selected(x:F)->F{return identity<Table<F>>(x);}
    )"));
    auto field = domainType("Field", "bls12-381.fr");
    require(declaration(project, "FieldData").domain ==
                take(builtinType("vector", {field})),
            "symbolic row head prematurely chose sequence");
    require(declaration(project, "RowAnswer").domain == field,
            "answer lost its row type");
    require(declaration(project, "Position").domain == Type(Type::Kind::Index),
            "query changed with zero cardinality");
    require(declaration(project, "IndexData").domain ==
                take(builtinType("indices", {})),
            "index data association differs");
    require(declaration(project, "BoolData").domain ==
                take(builtinType("sequence", {Type{}})),
            "bool data association differs");
    Layouts layouts(project);
    auto kind =
        take(layouts.oracleKind(declaration(project, "PairKind").domain));
    auto data = take(layouts.packed(declaration(project, "PairData").domain));
    require(kind.signature.data == data.carrier,
            "source and common row layouts diverged");
    auto empty = take(layouts.get(declaration(project, "Empty").domain));
    require(empty->leaves.size() == 1 && empty->leaves[0].oracle() &&
                empty->leaves[0].oracle()->maximum == 0 &&
                !empty->constructible && empty->permissions.copy &&
                empty->permissions.drop,
            "empty logical sequence acquired data construction rights");
  });
  cases.run(
      "oracle layouts retain logical identity and cannot become payloads", [] {
        auto project = take(check(aliases));
        Layouts layouts(project);
        const auto &oracle = declaration(project, "O").domain;
        auto layout = take(layouts.get(oracle));
        require(layout->leaves.size() == 1 && layout->leaves[0].oracle() &&
                    !layout->leaves[0].data() &&
                    !layout->leaves[0].oracle()->maximum,
                "oracle became an ordinary data leaf");
        const auto &kind = layout->leaves[0].oracle()->kind;
        require(kind.identity == "table" &&
                    kind.signature.data.spelling() == "vector:bls12-381.fr" &&
                    kind.signature.answer.spelling() == "field:bls12-381.fr" &&
                    kind.signature.query.spelling() == "index",
                "closed common kind associations differ");
        zkc::test::refuses(layouts.packed(oracle), "source.sequence");
        uint64_t budget = 100000;
        LayoutIdentities identities(budget);
        zkc::test::refuses(identities.get(*layout), "source.oracle-boundary");
        Type aggregate(Type::Kind::Array);
        aggregate.arguments = {oracle};
        for (uint64_t size : {0, 1}) {
          aggregate.dimension = Natural::constant(size);
          zkc::test::refuses(layouts.get(aggregate), "source.oracle-aggregate");
        }
        Type tuple(Type::Kind::Tuple);
        tuple.arguments = {oracle};
        zkc::test::refuses(layouts.get(tuple), "source.oracle-aggregate");
      });
  cases.run("kind projections are forward functions rather than inference "
            "constructors",
            [] {
              zkc::test::refuses(check(std::string(aliases) + R"(
      math fn identity<K:OracleKind>(x:K::Answer)->K::Answer{return x;}
      math fn missing(x:F)->F{return identity(x);}
    )"),
                                 "source.inference");
              zkc::test::refuses(
                  check(std::string(aliases) + "type Bad=TableKind::Unknown;"),
                  "source.oracle-kind");
              Type parameter(Type::Kind::OracleKind, "scope::K");
              parameter.symbolic = true;
              auto projection = take(oracleMember(parameter, "Data"));
              require(projection.kind == Type::Kind::OracleProjection &&
                          projection.symbolic,
                      "unknown association was guessed");
              zkc::test::refuses(encodeStaticTerm(projection),
                                 "source.static-term");
            });
  return cases.result();
}
