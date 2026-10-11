#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Language/Diagnostics.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
Expected<CheckedProject> check(std::vector<SourceBuffer> sources) {
  auto captured = capture(std::move(sources));
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
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
  cases.run("file and inline modules share declaration identity", [] {
    auto project = take(check(R"(module m;
      module Inner { pub math fn yes()->bool{return true;} }
      protocol Demo roles(P)()->(ok:bool@P){return Inner::yes();}
      run Run=Demo;
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
    take(prepareOriginal(take(closeEntry(project, "m::Run"))));
  });
  cases.run("private names are available to descendants", [] {
    auto project = take(check(R"(module m;
      math fn helper()->bool{return true;}
      module Child { pub math fn call()->bool{return helper();} }
      protocol Demo roles(P)()->(ok:bool@P){return Child::call();}
      run Run=Demo;
    )"));
    take(prepareOriginal(take(closeEntry(project, "m::Run"))));
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
        protocol Demo roles(P)()->(ok:bool@P){return value();}run Run=Demo;
      )",
                                              "b.zkc"}}));
    take(prepareOriginal(take(closeEntry(project, "b::Run"))));
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
      run Run=Demo;
    )"));
    require(named(project, "m::M::value").isPublic &&
                !named(project, "m::M::helper").isPublic,
            "only required interface members are implicitly public");
    take(prepareOriginal(take(closeEntry(project, "m::Run"))));
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
         "Demo roles(P)()->(ok:bool@P){return Child::value();}run Run=Demo;",
         "main.zkc"},
        {"m::Child",
         "module m::Child;pub math fn value()->bool{return helper();}",
         "child.zkc"}}));
    const auto &root = named(project, "m");
    const auto &child = named(project, "m::Child");
    require(child.parent->index == root.id.index &&
                child.span.source.index != root.span.source.index,
            "external module retains its own source");
    take(prepareOriginal(take(closeEntry(project, "m::Run"))));
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
      run Run=Demo;
    )"));
    take(prepareOriginal(take(closeEntry(project, "m::Run"))));
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
         "roles(P)()->(ok:bool@P){return Child::roundtrip();}run Run=Demo;",
         "root"},
        {"m::Child",
         "module m::Child;pub fn roundtrip()->bool{let x=Secret(true);return "
         "unpack(x);}",
         "child"}}));
    take(prepareOriginal(take(closeEntry(project, "m::Run"))));
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
            "roles(P)(x:[bool;2]@P)->(out:[bool;2]@P){return apply<2>(x);}run "
            "Run=Demo;";
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
          take(prepareOriginal(take(closeEntry(project, "client::Run"))));
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
         "impl::count<2>();}run Run=Demo;",
         "client"}}));
    take(prepareOriginal(take(closeEntry(project, "client::Run"))));
  });
  cases.run("generic modules do not expose uninstantiated Entries", [] {
    refuses(check("module m<N:nat>;protocol Demo "
                  "roles(P)()->(ok:bool@P){return true;}run Run=Demo;"),
            "source.entry");
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
      protocol Demo roles(P)()->(out:bool@P){return value();}run Run=Demo;
    )"));
        take(prepareOriginal(take(closeEntry(project, "m::Run"))));
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
  return cases.result();
}
