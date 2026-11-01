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
  return cases.result();
}
