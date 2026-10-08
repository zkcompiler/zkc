#include "support/NativeCases.h"
#include "zkc/Language/Project.h"
using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
constexpr StringLiteral base = R"(module sample;
 domain F=field("bls12-381.fr");
 relation Equal(statement x:F,witness y:F){return x==y;}
 protocol Round roles(P,V)(x:F@(P,V),y:F@P)
 using(coins:Random<F>@V)->(ok:bool@V)
 spec{target claim=Equal(in.x@V,in.y) accept out.ok;}
 {let ok@V=true;return(ok=ok);}
)";
constexpr StringLiteral setupBase = R"(module sample;
 domain C=commitment("multilinear.kzg.bls12-381/1");
 type PK=builtin("prover_key",C);type VK=builtin("verifier_key",C);
 type Commit=builtin("commitment",C);type Proof=builtin("proof",C);
 struct Statement{pub left:Commit,pub right:Proof,pub ordinary:bool}
 protocol Run roles(P,V)(vk:VK@V,pk:PK@P,statement:Statement@(P,V))->(ok:bool@V){
   let ok@V=true;return(ok=ok);
 }
)";
constexpr StringLiteral setupChoices = R"({setup pcs{vk,pk,statement};
 prover P;verifier V;public{vk,statement};accept ok;construction authored;})";
std::string setupSource(StringRef choices = setupChoices) {
  return (setupBase + "entry Demo=Run" + choices).str();
}
constexpr StringLiteral choices = R"({prover P;verifier V;public{x};accept ok;
 target claim;construction fiat_shamir("merlin3.bls12-381.fr64be/1"){derive coins;}})";
Expected<ClosedEntry> close(StringRef text, const Limits &limits = {}) {
  auto captured = capture({{"sample", text.str(), {}}});
  if (!captured)
    return captured.takeError();
  auto checked = analyze(*captured, limits).checkedProject();
  if (!checked)
    return checked.takeError();
  return closeEntry(*checked, "sample::Demo", limits);
}
std::string source(StringRef body = choices) {
  return (base + "entry Demo=Round" + body).str();
}
std::string replaceText(std::string text, StringRef before, StringRef after) {
  auto position = text.find(before.str());
  require(position != std::string::npos, "test substitution missing");
  text.replace(position, before.size(), after.str());
  return text;
}
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run("closed component dispatch bounds the actual and cached call graph",
            [] {
              const std::string declarations = R"(module sample;
      interface Step { math fn run(x:bool)->bool; }
      component Base:Step {math fn run(x:bool)->bool{return x;}}
      component Wrap<C:Step>:Step {math fn run(x:bool)->bool{return C::run(x);}}
      math fn extra<C:Step>(x:bool)->bool{return C::run(x);}
      protocol Run<C:Step> roles(P)(x:bool@P)->(r:bool@P){
        let first=C::run(x);return(r=first);
      }
    )";
              Limits limits;
              limits.callDepth = 3;
              take(close(declarations + "entry Demo=Run<Wrap<Base>>;", limits));
              refuses(close(declarations + "entry Demo=Run<Wrap<Wrap<Base>>>;",
                            limits),
                      "source.limit");
              auto cached = replaceText(declarations, "return(r=first)",
                                        "return(r=extra<C>(first))");
              // First use caches Wrap<Base>; the second reaches that same
              // instance one level deeper and must include its complete height.
              refuses(close(cached + "entry Demo=Run<Wrap<Base>>;", limits),
                      "source.limit");
              limits.callDepth = 4;
              take(close(cached + "entry Demo=Run<Wrap<Base>>;", limits));
            });
  cases.run("proof choices resolve logical indices and complete aliases", [] {
    auto selected = take(close(source()));
    const auto &proof = *selected.entry().proof;
    require(proof.prover == 0 && proof.verifier == 1 &&
                proof.publicInputs == std::vector<unsigned>{0} &&
                proof.service == 0 && proof.target == 0 &&
                proof.acceptance.port == 0 && proof.acceptance.role == 1 &&
                proof.acceptance.path.empty(),
            "logical Entry choices differ");
    auto alias = take(close(
        (base + "entry Demo=Next;entry Next=Concrete;entry Concrete=Round" +
         choices)
            .str()));
    require(alias.entry().proof->suite == proof.suite &&
                alias.entry().proof->target == proof.target &&
                alias.protocol().symbol == selected.protocol().symbol,
            "complete alias omitted policy choices");
    auto run =
        take(close((base + "entry Demo=Alias;entry Alias=Round;").str()));
    require(!run.entry().proof, "run alias became a proof job");
  });
  cases.run("authored construction and absent relation target are explicit",
            [] {
              auto selected = take(close(R"(module sample;
      protocol Verify roles(P,V)(ok:bool@V)->(accepted:bool@V){return(accepted=ok);}
      entry Demo=Verify{prover P;verifier V;public{ok};accept accepted;construction authored;})"));
              require(selected.entry().proof->construction ==
                              ProofEntry::Construction::Authored &&
                          !selected.entry().proof->service &&
                          !selected.entry().proof->target,
                      "authored choices changed");
            });
  cases.run(
      "acceptance projects a Boolean field with concrete generic arguments",
      [] {
        auto selected = take(close(R"(module sample;
      struct Result<T:Type>{pub accepted:T,pub extra:index}
      protocol Verify<T:Type+Copy+Drop+Share+Wire> roles(P,V)(r:Result<T>@V)->(r:Result<T>@V){return(r=r);}
      entry Demo=Verify<bool>{prover P;verifier V;public{r};accept r.accepted;construction authored;})"));
        require(selected.entry().proof->acceptance.path ==
                    std::vector<unsigned>{0},
                "acceptance product projection lost");
      });
  for (auto change : std::initializer_list<std::pair<StringRef, StringRef>>{
           {"prover P;", ""},
           {"public{x};", ""},
           {"accept ok;", ""},
           {"prover P;", "prover P;prover P;"},
           {"public{x}", "public{x,x}"},
           {"public{x}", "public{}"},
           {"public{x}", "public{x,y}"},
           {"verifier V", "verifier P"},
           {"accept ok", "accept absent"},
           {"target claim", "target absent"},
           {"derive coins", "derive absent"},
           {"merlin3.bls12-381.fr64be/1", "uninstalled"},
           {"construction fiat_shamir(\"merlin3.bls12-381.fr64be/1\"){derive "
            "coins;}",
            "construction authored;"}})
    cases.run(
        "invalid explicit choice: " + change.first + " -> " + change.second,
        [&] {
          refuses(close(replaceText(source(), change.first, change.second)),
                  "source.entry");
        });
  cases.run("public input lists permit a trailing comma", [] {
    take(close(replaceText(source(), "public{x}", "public{x,}")));
  });
  cases.run("aliases cannot override or specialize a complete Entry", [] {
    refuses(close((base + "entry Original=Round" + choices +
                   "entry Demo=Original" + choices)
                      .str()),
            "source.entry");
    refuses(
        close((base + "entry Original=Round;entry Demo=Original<bool>;").str()),
        "source.entry");
    refuses(close((base + "entry Demo=Later;entry Later=Demo;").str()),
            "source.entry");
    Limits limited;
    limited.callDepth = 1;
    take(close((base + "entry Demo=Round;").str(), limited));
    refuses(
        close((base + "entry Demo=Later;entry Later=Round;").str(), limited),
        "source.limit");
    refuses(
        close((base + "entry Later=Round;entry Demo=Later;").str(), limited),
        "source.limit");
    limited.callDepth = 2;
    take(close((base + "entry Demo=Later;entry Later=Round;").str(), limited));
    take(close((base + "entry Later=Round;entry Demo=Later;").str(), limited));
  });
  cases.run("output-bound targets cannot be exported as native statements", [] {
    auto text = source();
    text = replaceText(text, "target claim=Equal(in.x@V,in.y)",
                       "target claim=Equal(out.value,in.y)");
    text = replaceText(text, "->(ok:bool@V)", "->(ok:bool@V,value:F@V)");
    text = replaceText(text, "return(ok=ok)", "return(ok=ok,value=x)");
    refuses(close(text), "source.entry");
  });
  cases.run("target purposes do not authorize public inputs", [] {
    refuses(close(replaceText(source(), "statement x:F,witness y:F",
                              "witness x:F,witness y:F")),
            "source.entry");
  });
  cases.run("setup choices bind closed inputs and complete aliases", [] {
    auto source = setupSource();
    auto entry = take(close(source));
    const auto &setup = entry.entry().setups.front();
    require(setup.name == "pcs" && setup.inputs.size() == 3 &&
                setup.inputs[2].port == 2,
            "setup logical input choices lost");
    auto alias = take(close(
        (setupBase + "entry Demo=Alias;entry Alias=Run" + setupChoices).str()));
    require(alias.entry().setups.front().inputs.size() == 3,
            "Entry alias lost setup choices");
    take(close(setupSource("{setup first{pk};setup "
                           "second{vk,statement.left,statement.right,};}")));
    refuses(close((setupBase + "entry Alias=Run" + setupChoices +
                   "entry Demo=Alias{setup pcs{vk};}")
                      .str()),
            "source.entry");
  });
  cases.run("setup coverage is exact nonoverlapping and nonvacuous", [] {
    for (StringRef choices :
         {";", "{}", "{setup pcs{};}", "{setup pcs{vk,statement};}",
          "{setup pcs{vk,pk,statement.left};}",
          "{setup pcs{vk,pk,statement,statement.left};}",
          "{setup pcs{vk,pk,statement};setup pcs{statement};}",
          "{setup pcs{vk,pk,statement,statement.ordinary};}",
          "{setup pcs{vk,pk,statement,absent};}"}) {
      // Missing key ingress is refused before the coverage check when no slot
      // exists.
      refuses(close(setupSource(choices)),
              choices == ";" || choices == "{setup pcs{vk,statement};}"
                  ? "source.ingress"
                  : "source.entry");
    }
  });
  cases.run("proof keys stay with their declared initializer", [] {
    auto source = replaceText(setupSource(), "pk:PK@P", "pk:PK@V");
    source =
        replaceText(source, "public{vk,statement}", "public{vk,pk,statement}");
    refuses(close(source), "source.entry");
    refuses(close(replaceText(setupSource(), "setup pcs{vk,pk,statement}",
                              "setup pcs{vk,pk@P,statement}")),
            "source.syntax");
  });
  cases.run("each proof setup needs its own public verifier key", [] {
    refuses(close(setupSource(
                "{setup one{vk};setup two{pk,statement};prover P;verifier "
                "V;public{vk,statement};accept ok;construction authored;}")),
            "source.entry");
    refuses(close(replaceText(setupSource(), "vk:VK@V", "vk:VK@P")),
            "source.entry");
    refuses(close(replaceText(setupSource(), "public{vk,statement}",
                              "public{statement}")),
            "source.entry");
  });
  cases.run("setup initialization does not grant nested or state constructors",
            [] {
              for (StringRef type : {"(PK,)", "builtin(\"opening_state\",C)"})
                refuses(close(replaceText(setupSource(), "pk:PK@P",
                                          ("pk:" + type + "@P").str())),
                        "source.ingress");
            });

  cases.run(
      "proof completion selects a prover Boolean and survives aliases", [] {
        const std::string source = R"(module sample;
      struct Result{pub ready:bool,pub count:index}
      protocol Run roles(P,V)(r:Result@P,ok:bool@V)->(result:Result@P,accepted:bool@V){return(result=r,accepted=ok);}
      entry Job=Run{prover P;verifier V;public{ok};accept accepted;complete result.ready;construction authored;}
      entry Demo=Job;
    )";
        auto entry = take(close(source));
        const auto &selected = *entry.entry().proof->completion;
        require(selected.output && selected.port == 0 && selected.role == 0 &&
                    selected.path == std::vector<unsigned>{0},
                "completion selector changed through alias");
        for (StringRef name : {"accepted", "result.count", "missing", "r"})
          refuses(close(replaceText(source, "complete result.ready",
                                    ("complete " + name).str())),
                  "source.entry");
        refuses(
            close(replaceText(source, "complete result.ready;",
                              "complete result.ready;complete result.ready;")),
            "source.entry");
        refuses(close(replaceText(
                    source,
                    "entry Job=Run{prover P;verifier V;public{ok};accept "
                    "accepted;complete result.ready;construction authored;}",
                    "entry Job=Run{complete result.ready;}")),
                "source.entry");
      });

  cases.run("completion respects private field visibility", [] {
    auto captured = take(capture(
        {{"lib", "module lib;pub struct Result{pub ok:bool,ready:bool}", {}},
         {"sample",
          R"(module sample;
        protocol Run roles(P,V)(r:lib::Result@P,ok:bool@V)->(result:lib::Result@P,accepted:bool@V){return(result=r,accepted=ok);}
        entry Demo=Run{prover P;verifier V;public{ok};accept accepted;complete result.ready;construction authored;})",
          {}}}));
    refuses(analyze(captured).checkedProject(), "source.private");
  });

  return cases.result();
}
