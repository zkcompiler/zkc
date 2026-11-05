#include "../lib/Language/Semantics.h"
#include "../lib/Language/TypeInference.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Language/Diagnostics.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
Expected<CheckedProject> check(std::vector<SourceBuffer> sources,
                               Limits limits = {}) {
  auto captured = capture(std::move(sources));
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
Expected<CheckedProject> check(StringRef source) {
  return check({{"m", source.str(), "main.zkc"}});
}
const Declaration &named(const CheckedProject &project, StringRef name) {
  for (const auto &decl : project.declarations())
    if (decl.qualifiedName == name)
      return decl;
  llvm_unreachable("missing test declaration");
}
} // namespace
int main() {
  Cases cases;
  for (StringRef imported : {"use ::m::Lib::{N};", "use ::m::Lib as N;"})
    cases.run(
        "inherited parameters cannot shadow child import " + imported.str(),
        [&] {
          refuses(check("module m;module Lib{pub type N=bool;}"
                        "module M<N:nat>{module Child{" +
                        imported.str() +
                        "pub math fn size(xs:[bool;N])->[bool;N]{return xs;}"
                        "}}"),
                  "source.shadow");
        });
  cases.run("external children check inherited parameters against imports", [] {
    refuses(check(std::vector<SourceBuffer>{
                {"lib", "module lib;", "lib.zkc"},
                {"m", "module m<N:nat>;module Child;", "m.zkc"},
                {"m::Child", "module m::Child;use ::lib as N;", "child.zkc"}}),
            "source.shadow");
  });
  for (StringRef signature :
       {"math fn f<T:Type+Copy+Drop>(x:T)->T;", "math fn f(T:bool)->bool;"})
    cases.run("interface members prevent shadowing in " + signature.str(), [&] {
      refuses(check("module m;interface I{type T;" + signature.str() + "}"),
              "source.shadow");
    });
  cases.run("file and inline modules share declaration identity", [] {
    auto project = take(check(R"(module m;
      module Inner { pub math fn yes()->bool{return true;} }
      protocol Demo roles(P)()->(ok:bool@P){return Inner::yes();}
      entry fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
    )"));
    const auto &root = named(project, "m");
    const auto &inner = named(project, "m::Inner");
    const auto &function = named(project, "m::Inner::yes");
    require(root.kind == Declaration::Kind::Module &&
                inner.kind == Declaration::Kind::Module &&
                inner.parent->index == root.id.index &&
                function.module.index == inner.id.index &&
                root.span.source.index == function.span.source.index,
            "logical module ownership is separate from source identity");
    take(prepareOriginal(
        take(zkc::test::closeProtocolDeployment(project, "m::Run"))));
  });
  cases.run("private names are available to descendants", [] {
    auto project = take(check(R"(module m;
      math fn helper()->bool{return true;}
      module Child { pub math fn call()->bool{return helper();} }
      protocol Demo roles(P)()->(ok:bool@P){return Child::call();}
      entry fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
    )"));
    take(prepareOriginal(
        take(zkc::test::closeProtocolDeployment(project, "m::Run"))));
  });
  for (StringRef path : {"Child::secret", "::m::Child::secret"})
    cases.run("parent cannot read child private member through " + path, [&] {
      refuses(
          check(("module m;module Child{math fn secret()->bool{return true;}}"
                 "math fn bad()->bool{return " +
                 path + "();}")
                    .str()),
          "source.private");
    });
  cases.run("same file does not confer sibling access", [] {
    refuses(check(R"(module m;
      module A {math fn secret()->bool{return true;}}
      module B {math fn bad()->bool{return A::secret();}}
    )"),
            "source.private");
  });
  cases.run("public reexport exposes a route without changing identity", [] {
    auto project =
        take(check(std::vector<SourceBuffer>{{"a", R"(module a;
        module hidden {pub math fn value()->bool{return true;}}
        pub use a::hidden::{value};
      )",
                                              "a.zkc"},
                                             {"b", R"(module b;use a::{value};
        protocol Demo roles(P)()->(ok:bool@P){return value();}entry fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
      )",
                                              "b.zkc"}}));
    take(prepareOriginal(
        take(zkc::test::closeProtocolDeployment(project, "b::Run"))));
    refuses(
        check(std::vector<SourceBuffer>{
            {"a",
             "module a;module hidden{pub math fn value()->bool{return "
             "true;}}pub use a::hidden::{value};",
             "a.zkc"},
            {"b", "module b;math fn bad()->bool{return ::a::hidden::value();}",
             "b.zkc"}}),
        "source.private");
  });
  cases.run("interface is a required contract with private helpers", [] {
    auto project = take(check(R"(module m;
      interface I {math fn value()->bool;}
      module M:I {
        math fn helper()->bool{return true;}
        math fn value()->bool{return helper();}
        pub math fn extra()->bool{return false;}
      }
      math fn apply<C:I>()->bool{return C::value();}
      protocol Demo roles(P)()->(ok:bool@P){return apply<M>();}
      entry fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
    )"));
    require(named(project, "m::M::value").isPublic &&
                !named(project, "m::M::helper").isPublic,
            "only required interface members are implicitly public");
    take(prepareOriginal(
        take(zkc::test::closeProtocolDeployment(project, "m::Run"))));
  });
  cases.run("interface bound hides extra implementation members", [] {
    refuses(check(R"(module m;interface I{math fn value()->bool;}
      math fn bad<C:I>()->bool{return C::extra();}
    )"),
            "source.call");
  });
  cases.run("external child inherits parent scope", [] {
    auto project = take(check(std::vector<SourceBuffer>{
        {"m",
         "module m;math fn helper()->bool{return true;}module Child;protocol "
         "Demo roles(P)()->(ok:bool@P){return Child::value();}entry fn "
         "Run(inputs: Demo::Inputs) { return Demo::run(inputs); }",
         "main.zkc"},
        {"m::Child",
         "module m::Child;pub math fn value()->bool{return helper();}",
         "child.zkc"}}));
    const auto &root = named(project, "m");
    const auto &child = named(project, "m::Child");
    require(child.parent->index == root.id.index &&
                child.span.source.index != root.span.source.index,
            "external module retains its own source");
    take(prepareOriginal(
        take(zkc::test::closeProtocolDeployment(project, "m::Run"))));
  });
  cases.run("nested modules inherit statics and close common helpers", [] {
    auto project = take(check(R"(module m;
      pub module Generic<N:nat> {
        type Buffer=[bool;N];
        math fn count()->index{return index<N>();}
        pub module Inner {
          pub math fn copy(x:Buffer)->Buffer {let n=count();return x;}
        }
      }
      use m::Generic as Alias;
      protocol Demo roles(P)(x:[bool;2]@P)->(out:[bool;2]@P){return Alias::Inner::copy<2>(x);}
      entry fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
    )"));
    take(prepareOriginal(
        take(zkc::test::closeProtocolDeployment(project, "m::Run"))));
  });
  cases.run("associated identity depends on module and static arguments", [] {
    auto project = take(check(R"(module m;
      module M<N:nat> {pub type Token:Copy+Drop=[bool;N];}
      use m::M as Alias;
      math fn same(x:M::Token<2>)->Alias::Token<2>{return x;}
    )"));
    const auto &function = named(project, "m::same");
    require(function.inputs.front().type == function.outputs.front().type,
            "aliases retain associated type identity");
    refuses(check(R"(module m;
      module M<N:nat>{pub type Token:Copy+Drop=[bool;N];}
      math fn wrong(x:M::Token<2>)->M::Token<3>{return x;}
    )"),
            "source.type");
  });
  cases.run("missing external child refuses",
            [] { refuses(check("module m;module Child;"), "source.module"); });
  cases.run("captured descendant requires authored link", [] {
    refuses(check(std::vector<SourceBuffer>{
                {"m", "module m;", "m"},
                {"m::Child", "module m::Child;", "child"}}),
            "source.module");
  });
  cases.run("inline and external duplicate bodies refuse", [] {
    refuses(check(std::vector<SourceBuffer>{
                {"m", "module m;module Child{}", "m"},
                {"m::Child", "module m::Child;", "child"}}),
            "source.duplicate");
  });
  cases.run("installation root cannot be captured", [] {
    refuses(check(std::vector<SourceBuffer>{{"zkc", "module zkc;", "root"}}),
            "source.module");
  });
  cases.run("old component spelling is not accepted", [] {
    refuses(check("module m;interface I{} component M:I{}"), "source.syntax");
  });

  cases.run("public imports cannot publish ancestor private declarations", [] {
    for (StringRef import :
         {"pub use m::{secret};", "pub use m::Hidden as Exposed;"})
      refuses(check("module m;math fn secret()->bool{return true;}module "
                    "Hidden{}module Child{" +
                    import.str() + "}"),
              "source.private");
  });
  cases.run("alias and nominal type meaning is local to their declarations",
            [] {
              auto project = take(check(R"(module m;
      interface I{type Token:Copy+Drop;}
      module M:I {
        type Token:Copy+Drop=bool;
        pub type Alias=bool;
        pub math fn identity(x:Alias)->bool{return x;}
      }
      math fn alias(x:M::Alias)->bool{return x;}
    )"));
              require(named(project, "m::M::Token").kind ==
                              Declaration::Kind::Associated &&
                          named(project, "m::M::Alias").kind ==
                              Declaration::Kind::Alias,
                      "interface changed declaration identity");
              refuses(check(R"(module m;interface I{type Token;}
      module M:I{type Token=bool;})"),
                      "source.conformance");
            });
  cases.run("external descendants share representation authority", [] {
    auto project = take(check(std::vector<SourceBuffer>{
        {"m",
         "module m;type Secret:Copy+Drop=bool;module Child;protocol Demo "
         "roles(P)()->(ok:bool@P){return Child::roundtrip();}entry fn "
         "Run(inputs: Demo::Inputs) { return Demo::run(inputs); }",
         "root"},
        {"m::Child",
         "module m::Child;pub fn roundtrip()->bool{let x=Secret(true);return "
         "unpack(x);}",
         "child"}}));
    take(prepareOriginal(
        take(zkc::test::closeProtocolDeployment(project, "m::Run"))));
    for (StringRef operation : {"Child::Secret(true)", "unpack(x)"}) {
      std::string body =
          operation == "unpack(x)"
              ? "fn wrong(x:Child::Secret)->bool{return unpack(x);}"
              : "fn wrong()->Child::Secret{return Child::Secret(true);}";
      refuses(check("module m;module Child{pub type Secret:Copy+Drop=bool;}" +
                    body),
              "source.private");
    }
  });
  cases.run(
      "generic file and inline children have equivalent closed behavior", [] {
        const std::string child =
            "pub math fn apply(x:[bool;N])->[bool;N]{return x;}";
        const std::string client =
            "module client;use library::Box::{apply};protocol Demo "
            "roles(P)(x:[bool;2]@P)->(out:[bool;2]@P){return "
            "apply<2>(x);}entry fn Run(inputs: Demo::Inputs) { return "
            "Demo::run(inputs); }";
        for (bool external : {false, true}) {
          std::vector<SourceBuffer> files = {
              {"library",
               "module library<N:nat>;pub module Box" +
                   (external ? std::string(";") : "{" + child + "}"),
               "library"},
              {"client", client, "client"}};
          if (external)
            files.push_back(
                {"library::Box", "module library::Box;" + child, "box"});
          auto project = take(check(std::move(files)));
          take(prepareOriginal(take(
              zkc::test::closeProtocolDeployment(project, "client::Run"))));
          require(named(project, "library::Box::apply").parameters.size() == 1,
                  "external child lost the enclosing generic binder");
        }
      });
  cases.run("generic file implements its interface", [] {
    auto project = take(check(std::vector<SourceBuffer>{
        {"api", "module api;pub interface I<N:nat>{math fn count()->index;}",
         "api"},
        {"impl",
         "module impl<N:nat>:api::I<N>;math fn count()->index{return "
         "index<N>();}",
         "impl"},
        {"client",
         "module client;protocol Demo roles(P)()->(out:index@P){return "
         "impl::count<2>();}entry fn Run(inputs: Demo::Inputs) { return "
         "Demo::run(inputs); }",
         "client"}}));
    take(prepareOriginal(
        take(zkc::test::closeProtocolDeployment(project, "client::Run"))));
  });
  cases.run("generic modules do not expose uninstantiated Entries", [] {
    auto project =
        take(check("module m<N:nat>;protocol Demo "
                   "roles(P)()->(ok:bool@P){return true;}entry fn Run(inputs: "
                   "Demo::Inputs) { return Demo::run(inputs); }"));
    require(project.entries().empty(), "generic module acquired an Entry");
    refuses(closeEntry(project, "m::Run"), "source.entry");
  });
  cases.run("captured declaration cannot hijack an authored protocol path", [] {
    refuses(check(std::vector<SourceBuffer>{
                {"m",
                 "module m;protocol Demo roles(P)()->(ok:bool@P){return true;}",
                 "m"},
                {"m::Demo", "module m::Demo;", "other"}}),
            "source.duplicate");
  });
  cases.run(
      "nested notation uses lexical ordering independently of name imports",
      [] {
        auto project = take(check(R"(module m;
      use m::Child::{value};
      pub math fn add(x:bool,y:bool)->bool{return x&&y;}
      operator infixl(60) ⊕ = add;
      operator ⊕ = add;
      module Child {pub math fn value()->bool{return true⊕false;}}
      protocol Demo roles(P)()->(out:bool@P){return value();}entry fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
    )"));
        take(prepareOriginal(
            take(zkc::test::closeProtocolDeployment(project, "m::Run"))));
      });
  cases.run("child notation cannot feed its own inherited parent environment",
            [] {
              refuses(check(R"(module m;use m::Child::{operator +};
      module Child{pub math fn add(x:index,y:index)->index{return x;}pub operator + = add;}
    )"),
                      "source.cycle");
            });
  cases.run("child diagnostics retain captured file coordinates", [] {
    auto result = check(std::vector<SourceBuffer>{
        {"m", "module m;module Child;", "root"},
        {"m::Child", "module m::Child;math fn wrong()->bool{return missing;}",
         "child"}});
    require(!result, "invalid child unexpectedly passed");
    std::optional<Span> primary;
    handleAllErrors(result.takeError(), [&](const DiagnosticError &error) {
      primary = error.diagnostic().primary;
    });
    require(primary && primary->source.index == 1,
            "child diagnostic points into parent file");
  });

  cases.run("import aliases have whole-module scope", [] {
    for (bool reverse : {false, true}) {
      std::string a = "use Alias as Again;", b = "use ::m::Library as Alias;";
      auto project = take(check(
          "module m;module Library{pub math fn value()->bool{return true;}}" +
          (reverse ? b + a : a + b) +
          "protocol Demo roles(P)()->(ok:bool@P){return Again::value();}entry "
          "fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); }"));
      take(prepareOriginal(
          take(zkc::test::closeProtocolDeployment(project, "m::Run"))));
    }
    refuses(check("module m;use A as B;use B as A;"), "source.cycle");
  });
  cases.run("an implicit module alias resolves its enclosing source", [] {
    take(check(std::vector<SourceBuffer>{
        {"library", "module library;pub math fn value()->bool{return true;}",
         "library"},
        {"client",
         "module client;use library;math fn apply()->bool{return "
         "library::value();}",
         "client"}}));
  });
  cases.run("import binding limits do not depend on authored order", [] {
    for (bool reverse : {false, true}) {
      std::string imports = "use ::m::Library as A;use A as B;use B as C;";
      if (reverse)
        imports = "use B as C;use A as B;use ::m::Library as A;";
      std::vector<SourceBuffer> sources{
          {"m", "module m;module Library{}" + imports, "main.zkc"}};
      Limits limits;
      limits.importDepth = 3;
      take(check(sources, limits));
      limits.importDepth = 2;
      refuses(check(sources, limits), "source.limit");
    }
  });
  cases.run("early alias lookup retains its module dependency depth", [] {
    std::vector<SourceBuffer> sources{
        {"m",
         "module m;use B::Alias as Imported;"
         "module B{pub use ::library as Alias;}"
         "module E{use ::m::B;}",
         "m.zkc"},
        {"library", "module library;use leaf;", "library.zkc"},
        {"leaf", "module leaf;", "leaf.zkc"}};
    Limits limits;
    limits.importDepth = 4;
    take(check(sources, limits));
    limits.importDepth = 3;
    refuses(check(sources, limits), "source.limit");
  });
  cases.run("pending imports shadow captured roots in either order", [] {
    for (bool reverse : {false, true}) {
      std::string a = "use Y::{z};", b = "use X::{Y};";
      auto definitions = [&](bool exported) {
        return std::vector<SourceBuffer>{
            {"Y", "module Y;pub math fn z()->bool{return false;}", "Y.zkc"},
            {"X",
             "module X;pub module Y{" +
                 std::string(exported ? "pub math fn z()->bool{return true;}"
                                      : "") +
                 "}",
             "X.zkc"},
            {"m",
             "module m;" + (reverse ? b + a : a + b) +
                 "math fn apply()->bool{return z();}",
             "m.zkc"}};
      };
      refuses(check(definitions(false)), "source.import");
      auto project = take(check(definitions(true)));
      const auto &body = *named(project, "m::apply").body;
      bool checked = false;
      for (const auto &operation : body.operations)
        if (auto call = std::get_if<HelperCall>(&operation.action)) {
          require(project.declarations()[call->callee.index].qualifiedName ==
                      "X::Y::z",
                  "pending import selected a captured root instead");
          checked = true;
        }
      require(checked, "missing imported helper call");
    }
  });
  cases.run("a child resolves a later parent import", [] {
    for (bool reverse : {false, true}) {
      std::string a = "use B::{t};", b = "use X::{Y};";
      take(check(std::vector<SourceBuffer>{
          {"X", "module X;pub module Y{pub math fn t()->bool{return true;}}",
           "X.zkc"},
          {"m",
           "module m;" + (reverse ? b + a : a + b) +
               "module B{pub use Y::{t};}",
           "m.zkc"}}));
    }
  });
  cases.run("associated types cannot introduce unbound member parameters", [] {
    refuses(check("module m;module M<N:nat>{pub type "
                  "Box<K:nat>:Copy+Drop=[bool;K];}"),
            "source.unsupported");
    refuses(check("module m;interface I{type T<K:nat>;}module A:I{type "
                  "T:Copy+Drop=bool;}"),
            "source.unsupported");
  });
  cases.run("type arguments reuse each omitted lexical binder", [] {
    auto project = take(check(R"(module m;
      module M<N:nat>{
        pub struct S<T:Type>{pub x:[T;N]}
        pub type Row=S<T=bool>;
        type Single=S<N=1,T=bool>;
        pub math fn make(x:[bool;N])->Row{return S<T=bool>{x:x};}
      }
      protocol Demo roles(P)(x:[bool;2]@P)->(out:M::Row<2>@P){return M::make<2>(x);}
      entry fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
    )"));
    take(prepareOriginal(
        take(zkc::test::closeProtocolDeployment(project, "m::Run"))));
    refuses(check("module m;module M<N:nat>{struct S<T:Type>{pub x:[T;N]}type "
                  "Bad=S;}"),
            "source.generic");
  });
  cases.run("inline module bodies share one source token pass", [] {
    std::string source = "module m;";
    for (unsigned i = 0; i < 500; ++i)
      source += "module M" + std::to_string(i) +
                "{pub math fn value()->bool{return true;}}";
    take(check(source));
  });
  cases.run("private external child routes obey module visibility", [] {
    refuses(
        check(std::vector<SourceBuffer>{
            {"m", "module m;module Child;", "m.zkc"},
            {"m::Child",
             "module m::Child;pub math fn value()->bool{return true;}",
             "child.zkc"},
            {"client", "module client;use m::Child::{value};", "client.zkc"}}),
        "source.private");
  });
  cases.run("binding depth is independent of target module loading", [] {
    for (bool warm : {false, true}) {
      std::string source = "module m;module Leaf{}"
                           "module Library{use ::m::Leaf as L;}";
      if (warm)
        source += "use ::m::Library as Z;";
      source += "use ::m::Library as A;use A as B;use B as C;";
      Limits limits;
      limits.importDepth = 3;
      take(check({{"m", source, "m.zkc"}}, limits));
      limits.importDepth = 2;
      refuses(check({{"m", source, "m.zkc"}}, limits), "source.limit");
    }
  });
  cases.run("an import excludes its own names from its source path", [] {
    take(check(std::vector<SourceBuffer>{
        {"library", "module library;pub math fn library()->bool{return true;}",
         "library.zkc"},
        {"client",
         "module client;use library::{library};math fn apply()->bool{return "
         "library();}",
         "client.zkc"}}));
    for (bool publicChild : {false, true}) {
      auto result = check(std::vector<SourceBuffer>{
          {"library",
           "module library;" + std::string(publicChild ? "pub " : "") +
               "module sub{pub math fn value()->bool{return true;}}",
           "library.zkc"},
          {"client",
           "module client;use library::sub as library;math fn "
           "apply()->bool{return library::value();}",
           "client.zkc"}});
      if (publicChild)
        take(std::move(result));
      else
        refuses(std::move(result), "source.private");
    }
  });
  cases.run("module ordering does not change lexical alias resolution", [] {
    for (bool reverse : {false, true}) {
      std::string a =
          "module M{use library;pub module C{use library::Sub::{value};}}";
      std::string b = "pub module library{pub module Sub{pub math fn "
                      "value()->bool{return true;}}use ::m::M::C as Child;}";
      take(check("module m;" + (reverse ? b + a : a + b)));
    }
  });
  cases.run(
      "recorded dispatch completes later implementations before summaries", [] {
        auto project = take(check(R"(module m;
      interface Choice {math fn choose(left:bool,right:bool)->bool;}
      math fn selected<C:Choice>(left:bool,right:bool)->bool {
        return C::choose(left,right);
      }
      module Early:Choice {
        math fn choose(left:bool,right:bool)->bool {
          return selected<Later<2>>(left,right);
        }
      }
      module Later<N:nat>:Choice {
        math fn choose(left:bool,right:bool)->bool {return right;}
      }
      module First:Choice {
        math fn choose(left:bool,right:bool)->bool {return left;}
      }
      protocol Demo roles(P,V)(left:bool@P,right:bool@V)->(a:bool@P,b:bool@V) {
        return (a=selected<First>(left,right),b=selected<Early>(left,right));
      }
      entry fn Run(inputs:Demo::Inputs) {return Demo::run(inputs);}
    )"));
        const auto &early = named(project, "m::Early::choose");
        require(
            early.body->values[early.body->results.front().index].components ==
                std::vector<unsigned>{1},
            "summary observed an unchecked later implementation");
        for (StringRef name : {"m::Early", "m::Later", "m::First"}) {
          const auto &module = named(project, name);
          require(module.conformance.size() == 1 &&
                      module.conformance.front().required.index ==
                          named(project, "m::Choice::choose").id.index &&
                      module.conformance.front().provided.index ==
                          named(project, name.str() + "::choose").id.index,
                  "conformance did not retain the actual implementing member");
        }
        auto closed =
            take(zkc::test::closeProtocolDeployment(project, "m::Run"));
        if (auto error = checkScopedSpecialization(closed))
          throw std::runtime_error(toString(std::move(error)));
        take(prepareOriginal(closed));
      });
  cases.run("member dependencies do not create module conformance cycles", [] {
    take(check(R"(module m;
      interface I {math fn first(x:bool)->bool;math fn last(x:bool)->bool;}
      math fn forward<C:I>(x:bool)->bool {return C::last(x);}
      module A:I {
        math fn first(x:bool)->bool {return forward<B>(x);}
        math fn last(x:bool)->bool {return x;}
      }
      module B:I {
        math fn first(x:bool)->bool {return x;}
        math fn last(x:bool)->bool {return forward<A>(x);}
      }
    )"));
    refuses(check(R"(module m;
      interface I {math fn call(x:bool)->bool;}
      math fn forward<C:I>(x:bool)->bool {return C::call(x);}
      module A:I {math fn call(x:bool)->bool {return forward<B>(x);}}
      module B:I {math fn call(x:bool)->bool {return forward<A>(x);}}
    )"),
            "source.cycle");
  });
  cases.run("lazy dispatch completion preserves helper depth boundaries", [] {
    const std::string source = R"(module m;
      interface I {math fn call(x:bool)->bool;}
      math fn forward<C:I>(x:bool)->bool {return C::call(x);}
      module A:I {math fn call(x:bool)->bool {return forward<B>(x);}}
      module B:I {math fn call(x:bool)->bool {return x;}}
    )";
    Limits limits;
    limits.callDepth = 3;
    take(check({{"m", source, "m.zkc"}}, limits));
    limits.callDepth = 2;
    refuses(check({{"m", source, "m.zkc"}}, limits), "source.limit");
  });
  cases.run("conformance signature replay preserves completed alias depth", [] {
    std::string source = "module m;type A0=bool;";
    for (unsigned i = 1; i <= 40; ++i)
      source +=
          "type A" + std::to_string(i) + "=A" + std::to_string(i - 1) + ";";
    take(check(source + R"(
      interface I {math fn call(x:A40)->A40;}
      module M:I {math fn call(x:A40)->A40 {return x;}}
    )"));
  });
  const std::string contracts = R"(module m;
    domain Fr=field("koala-bear");domain Fq=field("baby-bear");
    type Flag=bool;
    interface I<N:nat> {
      type Scalar:Field;
      math fn choose(left:Flag,right:Flag)->Flag;
      domain fn rows(lo:index,hi:index)->domain<index>;
      fn run(x:bool,body:fn(bool)->bool)->bool effects(body);
    }
    module A<N:nat>:I<N> {
      type Scalar:Field=Fr;
      math fn choose(left:Flag,right:Flag)->Flag {return left;}
      domain fn rows(lo:index,hi:index)->domain<index>=domain("range");
      fn run(x:bool,body:fn(bool)->bool)->bool {return body(x);}
    }
    module B<N:nat>:I<N> {
      type Scalar:Field=Fq;
      math fn choose(left:Flag,right:Flag)->Flag {return right;}
      domain fn rows(lo:index,hi:index)->domain<index>=domain("range");
      fn run(x:bool,body:fn(bool)->bool)->bool {return body(x);}
    }
  )";
  cases.run(
      "dispatch binds implementing instances and associated identities", [&] {
        auto project = take(check(contracts));
        std::vector<Declaration> declarations(project.declarations().begin(),
                                              project.declarations().end());
        Limits limits;
        zkc::language::detail::Work work{limits};
        zkc::language::detail::Semantics types(declarations, project.assets(),
                                               work);
        Type two(Type::Kind::Natural);
        two.dimension = Natural::constant(2);
        Type a(Type::Kind::Module, "m::A"), b(Type::Kind::Module, "m::B");
        a.arguments = b.arguments = {two};
        auto required = named(project, "m::I::choose").id;
        auto left = types.dispatch(a, required, {two}, {});
        auto right = types.dispatch(b, required, {two}, {});
        require(left && right &&
                    left->declaration.index ==
                        named(project, "m::A::choose").id.index &&
                    right->declaration.index ==
                        named(project, "m::B::choose").id.index &&
                    left->arguments == std::vector<Type>{two},
                "dispatch confused two implementation instances");
        Type projection(Type::Kind::Field, "m::I::Scalar");
        projection.symbolic = true;
        projection.arguments.push_back(a);
        auto scalarA = types.substitute(projection, {}, {});
        projection.arguments.front() = b;
        auto scalarB = types.substitute(projection, {}, {});
        require(
            scalarA && scalarB && scalarA->domain == "koala-bear" &&
                scalarB->domain == "baby-bear",
            "associated substitution lost the required declaration identity");
        for (const auto &module : {a, b}) {
          zkc::language::detail::TypeInference inference(types);
          auto variable = inference.fresh({});
          Type parameter(Type::Kind::Module, "C");
          parameter.symbolic = true;
          projection.arguments = {parameter};
          auto result =
              inference.instantiate(projection, {{"C", variable}}, {});
          require(inference.equal(variable, inference.known(module, {}), {}) &&
                      inference.solve({}),
                  "deferred associated dispatch did not solve");
          auto actual = inference.get(result, {});
          require(actual && *actual == (module == a ? *scalarA : *scalarB),
                  "inference discarded the required associated member");
        }
        // A concrete target with a retained module annotation must stay
        // concrete.
        auto concrete =
            types.dispatch(b, left->declaration, left->arguments, {});
        require(concrete &&
                    concrete->declaration.index == left->declaration.index,
                "concrete implementation was dispatched a second time");
        Type three(Type::Kind::Natural);
        three.dimension = Natural::constant(3);
        require(!types.dispatch(a, required, {three}, {}),
                "dispatch accepted a different interface instance");
      });
  for (unsigned mutation = 0; mutation < 22; ++mutation)
    cases.run(
        "independent conformance witness mutation " + Twine(mutation), [&] {
          auto project = take(check(contracts));
          if (auto error = checkScopedElaboration(project))
            throw std::runtime_error(toString(std::move(error)));
          auto &a = const_cast<Declaration &>(named(project, "m::A"));
          auto &b = const_cast<Declaration &>(named(project, "m::B"));
          auto &required =
              const_cast<Declaration &>(named(project, "m::I::choose"));
          auto &provided =
              const_cast<Declaration &>(named(project, "m::A::choose"));
          switch (mutation) {
          case 0:
            a.conformance.clear();
            break;
          case 1:
            a.conformance.push_back(a.conformance.front());
            break;
          case 2:
            std::swap(a.conformance[0], a.conformance[1]);
            break;
          case 3:
            a.conformance[1].provided = b.conformance[1].provided;
            break;
          case 4:
            a.conformance[1].required = b.id;
            break;
          case 5:
            a.conformance[1].provided = a.conformance[0].provided;
            break;
          case 6:
            a.conformance[1].provided = DeclarationId{UINT32_MAX};
            break;
          case 7:
            provided.parent = b.id;
            break;
          case 8:
            provided.module = b.id;
            break;
          case 9:
            provided.kind = Declaration::Kind::Local;
            break;
          case 10:
            provided.outputs.front().type = Type(Type::Kind::Index);
            break;
          case 11:
            required.outputs.front().type = provided.outputs.front().type =
                Type(Type::Kind::Index);
            break;
          case 12:
            const_cast<Declaration &>(named(project, "m::A::Scalar"))
                .associatedSort = "Group";
            break;
          case 13:
            const_cast<Declaration &>(named(project, "m::A::rows"))
                .descriptorResult =
                DescriptorContract{DescriptorFamily::Finite, {Type{}}};
            break;
          case 14: {
            auto &allowance =
                const_cast<Declaration &>(named(project, "m::A::run"))
                    .scopedInputs.front()
                    .signature.allowance;
            allowance.mayStop = !allowance.mayStop;
            break;
          }
          case 15:
            a.implementation.reset();
            break;
          case 16:
            a.implementation->arguments.front().dimension =
                Natural::constant(3);
            break;
          case 17:
            provided.conformance = a.conformance;
            break;
          case 18:
            a.members.push_back(provided.id);
            break;
          case 19:
            provided.name = "forged";
            break;
          case 20:
            const_cast<Declaration &>(named(project, "m::Flag")).domain =
                Type(Type::Kind::Index);
            for (const auto &declaration : project.declarations())
              if (declaration.name == "choose") {
                auto &changed = const_cast<Declaration &>(declaration);
                for (auto &input : changed.inputs)
                  input.type = Type(Type::Kind::Index);
                changed.outputs.front().type = Type(Type::Kind::Index);
              }
            break;
          case 21:
            const_cast<Declaration &>(named(project, "m::Fr")).domain =
                named(project, "m::Fq").domain;
            const_cast<Declaration &>(named(project, "m::A::Scalar")).domain =
                named(project, "m::Fq").domain;
            break;
          }
          auto error = checkScopedElaboration(project);
          require(bool(error), "conformance mutation was accepted");
          require(namesIdentifier(toString(std::move(error)),
                                  "source.scoped-witness"),
                  "conformance mutation did not name its witness refusal");
        });
  for (StringRef constructor :
       {"Random", "zkc::prelude::Random", "facade::Random"}) {
    auto sources = [&](const std::string &body) {
      return std::vector<SourceBuffer>{
          {"facade", "module facade;pub use zkc::prelude::{Random};",
           "facade.zkc"},
          {"m",
           "module m;domain F=field(\"koala-bear.ext4-binomial3\");" + body,
           "m.zkc"}};
    };
    cases.run("managed constructor route " + constructor, [&] {
      take(check(
          sources("protocol Run roles(V)(coins:" + constructor.str() +
                  "<F>@V)->(){let a=coins.draw();let b=coins.index<8>();let "
                  "c=coins.indices(8,3);return ();}")));
    });
    cases.run("managed constructor cannot constrain modules " + constructor,
              [&] {
                refuses(check(sources("fn bad<C:" + constructor.str() +
                                      "<F>>()->(){return ();}")),
                        "source.service");
              });
    cases.run("managed constructor cannot be implemented " + constructor, [&] {
      refuses(check(sources("module Bad:" + constructor.str() + "<F>{}")),
              "source.service");
    });
    cases.run("managed constructor is not callable " + constructor, [&] {
      refuses(check(sources("fn bad()->(){let x=" + constructor.str() +
                            "<F>();return ();}")),
              "source.service");
    });
    cases.run("managed method is not callable " + constructor, [&] {
      refuses(check(sources("fn bad()->F{return " + constructor.str() +
                            "::draw<F>();}")),
              "source.service");
    });
    cases.run(
        "managed method grants no notation authority " + constructor, [&] {
          refuses(
              check(sources("operator + = " + constructor.str() + "::draw;")),
              "source.service");
        });
    cases.run(
        "managed method grants no scoped callback authority " + constructor,
        [&] {
          refuses(check(sources("fn apply(body:fn()->F effects())->F{return "
                                "body();}fn bad()->F{return apply(" +
                                constructor.str() + "::draw);}")),
                  "source.service");
        });
    cases.run(
        "managed method cannot be invoked inside a callback " + constructor,
        [&] {
          refuses(check(sources("fn apply(body:fn()->F effects())->F{return "
                                "body();}fn bad()->F{return apply(fn()=>" +
                                constructor.str() + "::draw<F>());}")),
                  "source.service");
        });
  }
  for (StringRef request :
       {"coins.index<0>()", "coins.indices(8,0)", "coins.indices(0,3)"})
    cases.run("managed positive natural refusal " + request, [&] {
      refuses(
          check(
              "module m;domain F=field(\"koala-bear.ext4-binomial3\");protocol "
              "Run roles(V)(coins:Random<F>@V)->(){let x=" +
              request.str() + ";return ();}"),
          "source.service");
    });
  cases.run("an ordinary interface named Random retains ordinary authority",
            [] {
              take(check(R"(
module m;domain F=field("bls12-381.fr");
interface Random<T:Field>{math fn yes()->bool;}
module Ordinary:Random<F>{math fn yes()->bool{return true;}}
math fn through<C:Random<F>>()->bool{return C::yes();}
math fn call()->bool{return through<Ordinary>();}
)"));
            });
  cases.run("managed row capability refusal is unchanged", [] {
    refuses(check("module m;domain F=field(\"koala-bear\");protocol Run "
                  "roles(V)(coins:Random<F>@V)->(){let "
                  "x=coins.index<8>();return ();}"),
            "source.service");
  });
  return cases.result();
}
