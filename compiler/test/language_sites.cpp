#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Names.h"
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
