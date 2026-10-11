#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Language/Inspection.h"
#include "llvm/Support/JSON.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
Expected<CheckedProject> check(StringRef text) {
  auto source = capture({{"m", "module m;" + text.str(), "admission.zkc"}});
  if (!source)
    return source.takeError();
  return analyze(*source).checkedProject();
}
const Declaration &declaration(const CheckedProject &project, StringRef name) {
  for (const auto &decl : project.declarations())
    if (decl.name == name)
      return decl;
  throw std::runtime_error("missing declaration");
}
void compile(StringRef text) {
  auto closed = take(closeEntry(take(check(text)), "m::Demo"));
  auto original = take(prepareOriginal(closed));
  for (bool simplify : {false, true})
    take(compileEntry(original, {simplify, false}));
}
const std::string relay = R"(
protocol Relay<T:Type> roles(P,V)(x:T@P)->(r:T@V) where () {
 let y=send P->V(x);return y;
}
)";
} // namespace
int main() {
  Cases cases;
  cases.run("generic messages retain separate obligations without usage bounds",
            [] {
              auto project = take(check(relay));
              const auto &decl = declaration(project, "Relay");
              require(decl.permissionBounds.empty(),
                      "transport inferred a usage promise");
              require(decl.admissions.size() == 2,
                      "message lost independent boundaries");
              std::set<Boundary> kinds;
              for (const auto &obligation : decl.admissions) {
                kinds.insert(obligation.boundary);
                require(obligation.type.kind == Type::Kind::Parameter &&
                            obligation.span.end > obligation.span.begin,
                        "obligation lost its type or source");
              }
              require(kinds == std::set<Boundary>{Boundary::Construction,
                                                  Boundary::Message},
                      "wrong message conditions");
            });
  cases.run("nested generic calls propagate boundary origins", [] {
    auto project = take(check(relay + R"(
protocol Forward<T:Type> roles(P,V)(x:T@P)->(r:T@V) where () {let result=Relay(x);return result;}
protocol Outer<T:Type> roles(P,V)(x:T@P)->(r:T@V) where () {let result=Forward(x);return result;}
)"));
    const auto &origin = declaration(project, "Relay");
    for (StringRef name : {"Forward", "Outer"}) {
      const auto &decl = declaration(project, name);
      require(decl.admissions.size() == 2, "propagated conditions differ");
      for (const auto &obligation : decl.admissions) {
        require(obligation.calls.size() == (name == "Forward" ? 1u : 2u),
                "call chain lost");
        require(obligation.span.begin == origin.admissions.front().span.begin,
                "message origin lost");
      }
    }
    compile(relay + R"(
protocol Forward<T:Type> roles(P,V)(x:T@P)->(r:T@V) where () {let result=Relay(x);return result;}
run Demo=Forward<bool>;
)");
  });
  cases.run("shared components derive admission independently of Copy", [] {
    auto project = take(check(R"(
protocol Shared<T:Type> roles(P,V)(x:T@(P,V))->(r:T@(P,V)) where () {return x;}
)"));
    const auto &decl = declaration(project, "Shared");
    require(decl.permissionBounds.empty() && !decl.admissions.empty(),
            "placement became a written usage requirement");
    for (const auto &obligation : decl.admissions)
      require(obligation.boundary == Boundary::Participants,
              "unexpected sharing condition");
    compile(R"(
protocol Shared<T:Type> roles(P,V)(x:T@(P,V))->(r:T@(P,V)) where () {return x;}
run Demo=Shared<bool>;
)");
    refuses(check(R"(
#[linear] struct Token {}
protocol Bad roles(P,V)(x:Token@(P,V))->(r:Token@(P,V)){return x;}
)"),
            "source.participants");
    refuses(check(R"(
domain C=commitment("multilinear.kzg.bls12-381/0");
type Key=builtin("prover_key",C);
protocol Bad roles(P,V)(x:Key@(P,V))->(r:Key@(P,V)){return x;}
)"),
            "source.participants");
  });
  cases.run("transparent aggregates close with installed codecs", [] {
    for (StringRef type :
         {"bool", "[bool;2]", "(bool,bool)", "Record", "Choice"})
      compile(relay +
              "struct Record{pub value:bool}enum Choice{Some(bool),None()}run "
              "Demo=Relay<" +
              type.str() + ">;");
    compile(relay + "type Sequence<T:Type+Copy>=builtin(\"sequence\",T);run "
                    "Demo=Relay<Sequence<bool>>;");
  });
  cases.run("privacy and explicit resources survive generic substitution", [] {
    for (StringRef definition :
         {"struct Secret{value:bool}",
          "#[sealed] struct Secret{pub value:bool}",
          "#[affine] struct Secret{}", "#[linear] struct Secret{}"})
      refuses(check(definition.str() + relay + "run Demo=Relay<Secret>;"),
              "source.ingress");
    refuses(
        check(relay + "struct Secret{value:bool}run Demo=Relay<[Secret;0]>;"),
        "source.ingress");
  });
  cases.run("symbolic array lengths retain element boundary conditions", [] {
    auto project = take(check(R"(
protocol Relay<T:Type,N:nat>roles(P,V)(x:[T;N]@P)->(r:[T;N]@V) where () {let result=send P->V(x);return result;}
)"));
    const auto &decl = declaration(project, "Relay");
    require(decl.admissions.size() == 2, "symbolic aggregate obligations lost");
    compile(R"(
protocol Relay<T:Type,N:nat>roles(P,V)(x:[T;N]@P)->(r:[T;N]@V) where () {let result=send P->V(x);return result;}
run Demo=Relay<bool,2>;
)");
  });
  cases.run("opaque associated constructors cannot be invented by transport",
            [] {
              refuses(check(R"(
interface Family{type Item;}
protocol Bad<C:Family>roles(P,V)(x:C::Item@P)->(r:C::Item@V){let result=send P->V(x);return result;}
)"),
                      "source.ingress");
            });
  cases.run("native usage does not imply external construction or a codec", [] {
    refuses(check(R"(
type State=builtin("shake128_state");
protocol Bad roles(P,V)(x:State@P)->(r:State@V){let result=send P->V(x);return result;}
)"),
            "source.ingress");
    refuses(check(R"(
domain F=field("bls12-381.fr");type Polynomial=builtin("polynomial",F);
protocol Bad roles(P,V)(x:Polynomial@P)->(r:Polynomial@V){let result=send P->V(x);return result;}
)"),
            "source.codec");
  });
  cases.run("sealed reusable data remains copyable and participant-admissible",
            [] {
              compile(R"(
#[sealed] struct Checked{pub value:bool}
fn make()->Checked{return Checked{value:true};}
fn duplicate(x:Checked)->(Checked,Checked){return(x,x);}
protocol Run roles(P,V)()->(p:Checked@P,v:Checked@V){let p@P=make();let v@V=make();return(p,v);}
run Demo=Run;
)");
            });
  cases.run(
      "inspection retains derived contracts and located closure failures", [] {
        auto project = take(check("pub " + relay));
        auto view = take(json::parse(take(inspectDeclarations(project))));
        const json::Object *decl = nullptr;
        for (const auto &item : *view.getAsArray())
          if (item.getAsObject()->getString("name") == "m::Relay")
            decl = item.getAsObject();
        require(decl && decl->getArray("admissions") &&
                    decl->getArray("admissions")->size() == 2,
                "inspection omitted boundary obligations");
        const auto *obligation =
            decl->getArray("admissions")->front().getAsObject();
        require(obligation->getObject("source") &&
                    obligation->getArray("calls"),
                "inspection lost origins");
        auto invalid =
            check(relay + "struct Secret{value:bool}run Demo=Relay<Secret>;");
        require(!invalid, "private generic ingress accepted");
        bool located = false;
        handleAllErrors(invalid.takeError(), [&](const DiagnosticError &error) {
          const auto &diagnostic = error.diagnostic();
          located = diagnostic.code == "source.ingress" &&
                    bool(diagnostic.primary) && !diagnostic.related.empty();
        });
        require(located, "boundary error lost call and origin spans");
      });
  cases.run("obsolete permissions have no compatibility interpretation", [] {
    for (StringRef word : {"Share", "Wire"}) {
      refuses(check("fn id<T:Type+" + word.str() + ">(x:T)->T{return x;}"),
              "source.permission");
      refuses(
          check("fn id<T:Type>(x:T)->T where " + word.str() + "(T){return x;}"),
          "source.capability");
    }
    take(check("struct Share{pub value:bool}struct Wire{pub value:bool}"));
  });
  return cases.result();
}
