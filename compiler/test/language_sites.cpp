#include "../lib/Language/Semantics.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/NativeLanguage.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/Names.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Language.h"
using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
constexpr StringLiteral prelude = R"(module m;
domain F=field("bls12-381.fr");
protocol Child roles(A,B)(value:F@A)->(actual:F@B){
  #[site(payload)] let received=send A->B(value);return received;
}
)";
Expected<CheckedProject> checked(StringRef source) {
  auto captured = capture({{"m", (prelude + source).str(), "sites.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
constexpr StringLiteral header =
    "protocol Round roles(P,V)(x:F@P,n:index@(P,V),coins:Random<F>@V)->(){";
} // namespace
int main() {
  zkc::test::Cases cases;
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  cases.run("labelled calls, messages and repeated queries compile", [&] {
    const std::string source = (header + R"(
      #[site(commitment)] let actual=send P->V(x);
      #[site(part)] let child=Child roles(P,V)(x);
      for _ in 0..n roles(P,V) max 2 {
        #[site(challenge)] let c=coins.draw();
        #[site(delivery)] let received=send V->P(c);
      }
      return ();
    }entry fn Demo(inputs: Round::Inputs) { return Round::run(inputs); })")
                                   .str();
    auto project = take(checked(source));
    auto closed = take(zkc::test::closeProtocolDeployment(project, "m::Demo"));
    auto original = take(prepareOriginal(closed));
    for (bool simplify : {false, true})
      take(compileEntry(original, {simplify, false}));
    auto parsed =
        mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
    require(bool(parsed), "parse labelled original");
    take(compareOriginal(closed, *parsed));
    bool mutated = false;
    parsed->walk([&](protocol_ir::ExchangeOp exchange) {
      if (!mutated) {
        exchange.setSite("wrong_selector");
        mutated = true;
      }
    });
    require(mutated, "message present");
    refuses(compareOriginal(closed, *parsed), "source.correspondence");
    require(original.bytes().contains(nativeSiteName("commitment", 0) + "_0"),
            "source label survives independently of its ordinal");
    auto changed = source;
    auto position = changed.find("#[site(commitment)]");
    changed.insert(position, "let unrelated@P=x+x;");
    auto updated = take(prepareOriginal(take(zkc::test::closeProtocolDeployment(
        take(checked(changed)), "m::Demo"))));
    require(updated.bytes().contains(nativeSiteName("commitment", 987) + "_0"),
            "unrelated source operation must not rename a labelled site");
  });
  cases.run("native construction selects labelled challenge deliveries", [&] {
    auto project = take(checked(R"(
      protocol Proof roles(P,V)(x:F@P,coins:Random<F>@V)->(ok:bool@V){
        #[site(약속)] let commitment=send P->V(x);
        #[site(challenge)] let c=coins.draw();
        #[site(delivery)] let received=send V->P(c);
        #[site(response)] let actual=send P->V(x+received);
        return actual==commitment+c;
      }
      proof Demo=Proof {prover P;verifier V;public{};accept ok;
        construction fiat_shamir("merlin3.bls12-381.fr64be/0",coins);}
    )"));
    auto original = take(prepareOriginal(
        take(zkc::test::closeProtocolDeployment(project, "m::Demo"))));
    for (bool simplify : {false, true})
      take(compileEntry(original, {simplify, false}));
  });
  const std::string gated = R"(
    domain Q=field("koala-bear.ext4-binomial3");
    protocol Queries roles(A,B)(coins:Random<Q>@B)->(){
      #[site(positions)] let positions=coins.indices(16,100);
      let delivered=send B->A(positions);
      return ();
    }
    protocol Gated roles(P,V)(n:index@(P,V),coins:Random<Q>@V,other:Random<Q>@V)->(ok:bool@V){
      #[site(first)] let ()=Queries roles(P,V)(coins);
      for _ in 0..n roles(P,V) max 2 {
        #[site(second)] let ()=Queries roles(P,V)(coins);
      }
      return true;
    }
    proof Gates=Gated{prover P;verifier V;public{n};accept ok;
      construction fiat_shamir("hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0",coins);
      gate second.positions bits 0;
      gate first.positions bits 3;
    }
  )";
  cases.run(
      "source gates bind actual nested and repeated block occurrences", [&] {
        auto project = take(checked(gated));
        auto closed =
            take(zkc::test::closeProtocolDeployment(project, "m::Gates"));
        auto original = take(prepareOriginal(closed));
        auto &gates = original.interface().proof->gates;
        require(gates.size() == 2 && gates[0].path.front() == "first" &&
                    gates[0].bits == 3 && gates[1].bits == 0,
                "gates must use source order while retaining explicit zero");
        auto written = take(inspectWrittenSource(project));
        require(StringRef(written).contains("\"kind\":\"gate\""),
                "written gates were lost");
        for (bool simplify : {false, true}) {
          auto compiled = take(compileEntry(original, {simplify, false}));
          auto &policy =
              std::get<CompiledNativeProof>(compiled.artifact()).policy;
          require(policy.gates.size() == 2 && policy.draws.size() == 2,
                  "block or repeated query was expanded or omitted");
          require(policy.gates[0] ==
                      std::pair(mathematical::expandedApplicationSite(
                                    nativeSiteName("first", 0),
                                    nativeSiteName("positions", 0)),
                                3u),
                  "source selector differs from actual expanded site");
        }
        auto doc = take(json::parse(original.interfaceJson()));
        auto *job = doc.getAsObject()->getObject("job");
        (*job->getArray("gates"))[0].getAsObject()->operator[]("bits") = 4;
        require(StringRef(toString(checkInterface(original, printJson(doc))))
                    .contains("source.interface"),
                "altered or missing gate metadata accepted");
        job->erase("gates");
        require(StringRef(toString(checkInterface(original, printJson(doc))))
                    .contains("source.interface"),
                "altered or missing gate metadata accepted");
      });
  cases.run("gate contracts traverse selected generic Protocol members", [&] {
    // The 4.1 reader does not yet project programmable construction choices.
    // Exercise their shared semantic contract on real checked 4.1 bodies.
    CaptureOptions options;
    options.format = "zkc-layout";
    auto captured = take(capture({{"m", R"(module m
domain Q = field("koala-bear.ext4-binomial3")
interface QueryLibrary:
    protocol Queries<N: nat> roles(A, B)(coins: Random<Q> @B) -> bool @B effects()
module QueriesImpl: QueryLibrary:
    protocol Queries<M: nat> roles(X, Y)(coins: Random<Q> @Y) -> bool @Y:
        #[site(positions)]
        positions <- coins.indices<16, 100>()
        delivered <- send positions to X
        return true
protocol Gated<C: QueryLibrary> roles(P, V)(coins: Random<Q> @V) -> bool @V:
    #[site(first)]
    first <- C::Queries<2>(coins) @(P, V)
    #[site(second)]
    second <- C::Queries<3>(coins) @(P, V)
    return second
)",
                                   "generic-sites.zkc"}},
                                 options));
    auto project = take(analyze(captured).checkedProject());
    auto root = llvm::find_if(project.declarations(), [](const auto &d) {
      return d.qualifiedName == "m::Gated";
    });
    require(root != project.declarations().end(), "missing generic protocol");
    ProofEntry proof;
    proof.construction = ProofEntry::Construction::FiatShamir;
    proof.prover = 0;
    proof.verifier = 1;
    proof.services = {0};
    proof.suite =
        "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0";
    proof.gates = {{{"second", "positions"}, 0, {}},
                   {{"first", "positions"}, 3, {}}};
    Limits limits;
    zkc::language::detail::Work work{limits};
    auto declarations = project.declarations().vec();
    auto provided = llvm::find_if(declarations, [](const auto &d) {
      return d.qualifiedName == "m::QueriesImpl::Queries";
    });
    require(provided != declarations.end() && provided->body,
            "missing selected implementation body");
    auto retainedBody = provided->body;
    provided->body.reset();
    zkc::language::detail::Semantics semantics(declarations, project.assets(),
                                               work);
    unsigned completed = 0;
    semantics.completeDispatchBody = [&](DeclarationId id, unsigned) {
      require(id.index == provided->id.index,
              "gate traversal completed the abstract provider");
      declarations[id.index].body = retainedBody;
      ++completed;
      return true;
    };
    std::vector<Type> arguments{Type(Type::Kind::Module, "m::QueriesImpl")};
    auto order = semantics.proofGateOrder(*root, proof, arguments);
    if (!order)
      throw std::runtime_error(toString(semantics.takeError()));
    require(completed > 0, "gate dispatch omitted lazy body completion");
    require(*order == std::vector<unsigned>({1, 0}),
            "selected member gates lost lexical occurrence order");
    proof.gates.front().path.back() = "absent";
    require(!semantics.proofGateOrder(*root, proof, arguments),
            "absent selected implementation gate was admitted");
    require(toString(semantics.takeError()).find("source.gate") !=
                std::string::npos,
            "absent gate had the wrong diagnostic");
  });
  for (const auto &mutation : std::vector<std::pair<std::string, std::string>>{
           {"bits 3", "bits 65"},
           {"gate first.positions", "gate absent.positions"},
           {"gate first.positions", "gate first.absent"},
           {"gate first.positions", "gate first"},
           {"gate first.positions", "gate second.positions"},
           {"#[site(first)] ", ""},
           {"coins.indices(16,100)", "coins.index<16>()"},
           {"Queries roles(P,V)(coins);\n      for",
            "Queries roles(P,V)(other);\n      for"},
           {"construction "
            "fiat_shamir(\"hash-chain.keccak256.koala-bear.ext4-binomial3."
            "rejection31le/0\",coins);",
            "construction authored;"}}) {
    cases.run("gate refuses " + mutation.second, [&] {
      auto source = gated;
      auto at = source.find(mutation.first);
      require(at != std::string::npos, "mutation does not select source");
      source.replace(at, mutation.first.size(), mutation.second);
      refuses(checked(source), "source.gate");
    });
  }
  const std::vector<std::string> invalid = {
      "#[site(a)] let x2=x;",
      "#[site(a)] let c=coins.draw()+coins.draw();",
      "#[site(a)] let c=coins.draw()+1;",
      "#[site(a)] let c=send V->P(coins.draw());",
      "#[site(a)] require @V true;",
      "#[site(a)] for _ in 0..n roles(P,V) max 2 {let r=send P->V(x);}",
      "#[site(a)] let c=coins.draw(); #[site(a)] let r=send V->P(c);",
      "#[site(a)] let r=send P->V(x); for _ in 0..n roles(P,V) max 2 "
      "{#[site(a)] let c=coins.draw();}",
      "#[site(a)] #[site(b)] let r=send P->V(x);",
      "#[site(a)] return ();"};
  for (const auto &body : invalid)
    cases.run(body, [&] {
      refuses(checked((header + body + "return ();}").str()), "source.site");
    });
  cases.run("local label refuses", [&] {
    refuses(checked("fn local(x:F)->F{#[site(a)] let y=x;return y;}"),
            "source.site");
  });
  for (bool oracle : {false, true})
    for (unsigned aliases = 0; aliases < 3; ++aliases)
      for (bool position : {false, true})
        for (bool hint : {false, true})
          cases.run(
              "query operand witness oracle=" + Twine(oracle) +
                  " aliases=" + Twine(aliases) +
                  " position=" + Twine(position) + " hint=" + Twine(hint),
              [=] {
                std::string source = R"(
                        type Fixed<T:Type+Copy+Drop,N:nat>=builtin("oracle.table",T,N);
                        type Oracle<K:OracleKind>=builtin("oracle",K);
                        type O=Oracle<Fixed<F,16>>;
                      )";
                source += oracle ? R"(
                        oracle def Read(source:O,other:O,alternate:index)->O {
                          query(position:index) {
                      )"
                                 : R"(
                        protocol Read roles(P,V)(source:O@P->V,other:O@P->V,
                          position:index@V,alternate:index@V)->(result:F@V){
                      )";
                for (unsigned i = 0; i < aliases; ++i)
                  source += "let alias" + std::to_string(i) + "=" +
                            (i ? "alias" + std::to_string(i - 1) : "source") +
                            ";";
                source += "let answer <- query " +
                          (aliases ? "alias" + std::to_string(aliases - 1)
                                   : "source") +
                          " at position; return answer;}";
                if (oracle)
                  source += "}";
                auto project = take(checked(source));
                cantFail(checkScopedElaboration(project));
                auto declaration =
                    llvm::find_if(project.declarations(), [](const auto &decl) {
                      return decl.name == "Read";
                    });
                require(declaration != project.declarations().end() &&
                            declaration->body,
                        "missing query operand fixture");
                auto &body = const_cast<Body &>(*declaration->body);
                auto operation =
                    llvm::find_if(body.operations, [](const auto &op) {
                      return std::holds_alternative<OracleQuery>(op.action) ||
                             std::holds_alternative<OracleSourceQuery>(
                                 op.action);
                    });
                require(operation != body.operations.end(),
                        "missing authored query action");
                if (!hint) {
                  operation->expression.reset();
                  cantFail(checkScopedElaboration(project));
                }
                if (oracle) {
                  auto &query = std::get<OracleSourceQuery>(operation->action);
                  if (position)
                    query.position = ValueId{2};
                  else
                    query.source = 1;
                } else {
                  auto &query = std::get<OracleQuery>(operation->action);
                  if (position)
                    query.position = ValueId{3};
                  else
                    query.handle = ValueId{1};
                }
                auto error = checkScopedElaboration(project);
                require(bool(error), "query operand replacement passed");
                auto diagnostic = toString(std::move(error));
                require(
                    StringRef(diagnostic).contains("source.binding-witness"),
                    "wrong query operand boundary: " + diagnostic);
              });
  for (bool oracle : {false, true})
    for (unsigned aliases : {1u, 2u})
      for (bool position : {false, true})
        for (bool hint : {false, true})
          cases.run(
              "coordinated query alias oracle=" + Twine(oracle) +
                  " aliases=" + Twine(aliases) +
                  " position=" + Twine(position) + " hint=" + Twine(hint),
              [=] {
                std::string source = R"(
              type Fixed<T:Type+Copy+Drop,N:nat>=builtin("oracle.table",T,N);
              type Oracle<K:OracleKind>=builtin("oracle",K);
              type O=Oracle<Fixed<F,16>>;
            )";
                source +=
                    oracle
                        ? "oracle def "
                          "Read(source:O,other:O,alternate:index)->O{"
                          "query(position:index){"
                        : "protocol Read "
                          "roles(P,V)(source:O@P->V,other:O@P->V,"
                          "position:index@V,alternate:index@V)->(result:F@V){";
                for (unsigned i = 0; i < aliases; ++i)
                  source += "let alias" + std::to_string(i) + "=" +
                            (i          ? "alias" + std::to_string(i - 1)
                             : position ? "position"
                                        : "source") +
                            ";";
                auto name = "alias" + std::to_string(aliases - 1);
                source += "let answer <- query " +
                          (position ? "source" : name) + " at " +
                          (position ? name : "position") + ";return answer;}";
                if (oracle)
                  source += "}";
                auto project = take(checked(source));
                cantFail(checkScopedElaboration(project));
                auto declaration =
                    llvm::find_if(project.declarations(), [](const auto &decl) {
                      return decl.name == "Read";
                    });
                require(declaration != project.declarations().end() &&
                            declaration->body,
                        "missing coordinated alias fixture");
                auto &body = const_cast<Body &>(*declaration->body);
                if (!hint) {
                  for (auto &op : body.operations)
                    if (std::holds_alternative<Projection>(op.action))
                      op.expression.reset();
                  cantFail(checkScopedElaboration(project));
                }
                auto query = llvm::find_if(body.operations, [](const auto &op) {
                  return std::holds_alternative<OracleQuery>(op.action) ||
                         std::holds_alternative<OracleSourceQuery>(op.action);
                });
                require(query != body.operations.end(), "missing query");
                unsigned changed = 0;
                for (auto &op : body.operations) {
                  if (changed == aliases)
                    break;
                  auto *projection = std::get_if<Projection>(&op.action);
                  if (!projection || !projection->path.empty())
                    continue;
                  require(op.results.size() == 1, "missing alias result");
                  if (!changed)
                    projection->input =
                        ValueId{position ? (oracle ? 2u : 3u) : 1u};
                  auto useName = "alias" + std::to_string(changed);
                  auto useSpan = query->span;
                  useSpan.begin = prelude.size() + source.rfind(useName);
                  useSpan.end = useSpan.begin + useName.size();
                  op.span = useSpan;
                  body.values[op.results.front().index].span = useSpan;
                  if (!hint)
                    op.expression.reset();
                  ++changed;
                }
                require(changed == aliases, "missing alias projections");
                if (oracle && !position)
                  std::get<OracleSourceQuery>(query->action).source = 1;
                // Protocol retains the exact mapped alias handle/position.
                // Oracle source indices and identity chains are changed
                // together above.
                auto error = checkScopedElaboration(project);
                require(bool(error),
                        "coordinated query alias redirection passed");
                auto diagnostic = toString(std::move(error));
                require(
                    StringRef(diagnostic).contains("source.binding-witness"),
                    diagnostic);
              });
  for (bool oracle : {false, true})
    cases.run(
        "unauthored query cannot hide behind a retained source " +
            Twine(oracle),
        [=] {
          std::string source = R"(
                  type Fixed<T:Type+Copy+Drop,N:nat>=builtin("oracle.table",T,N);
                  type Oracle<K:OracleKind>=builtin("oracle",K);
                  type O=Oracle<Fixed<F,16>>;
                )";
          source += oracle ? "oracle def Read(source:O)->O{"
                             "query(position:index){"
                           : "protocol Read roles(P,V)(source:O@P->V,"
                             "position:index@V)->(result:F@V){";
          source += "let answer <- query source at position;return answer;}";
          if (oracle)
            source += "}";
          auto project = take(checked(source));
          cantFail(checkScopedElaboration(project));
          auto declaration =
              llvm::find_if(project.declarations(), [](const auto &decl) {
                return decl.name == "Read";
              });
          require(declaration != project.declarations().end() &&
                      declaration->body,
                  "missing query coverage fixture");
          auto &body = const_cast<Body &>(*declaration->body);
          auto query = llvm::find_if(body.operations, [](const auto &op) {
            return std::holds_alternative<OracleQuery>(op.action) ||
                   std::holds_alternative<OracleSourceQuery>(op.action);
          });
          require(query != body.operations.end() && query->results.size() == 1,
                  "missing query producer");
          auto extra = *query;
          auto result = body.values.at(extra.results.front().index);
          extra.results = {ValueId{uint32_t(body.values.size())}};
          extra.expression.reset();
          body.values.push_back(std::move(result));
          body.operations.push_back(std::move(extra));
          auto error = checkScopedElaboration(project);
          require(bool(error), "unauthored query was accepted");
          auto diagnostic = toString(std::move(error));
          require(StringRef(diagnostic)
                      .contains("query has no authored occurrence"),
                  diagnostic);
        });
  return cases.result();
}
