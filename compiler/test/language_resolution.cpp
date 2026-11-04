#include "../lib/Language/State.h"
#include "support/NativeCases.h"
#include "zkc/Language/Inspection.h"
#include "llvm/ADT/STLExtras.h"
#include <algorithm>
#include <set>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
namespace source_detail = zkc::language::detail;
Expected<CheckedProject> check(std::vector<SourceBuffer> sources,
                               const Limits &limits = {}) {
  auto captured = capture(std::move(sources));
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
Expected<CheckedProject> check(StringRef code, const Limits &limits = {}) {
  return check({{"m", code.str(), "m.zkc"}}, limits);
}
const Declaration &named(const CheckedProject &project, StringRef name) {
  auto found = llvm::find_if(project.declarations(), [&](const auto &decl) {
    return decl.qualifiedName == name;
  });
  require(found != project.declarations().end(),
          "missing declaration: " + name);
  return *found;
}
source_detail::CheckedStorage &candidate(const CheckedProject &project) {
  return const_cast<source_detail::CheckedStorage &>(
      source_detail::DeclarationAccess::storage(project));
}
void accepted(const CheckedProject &project) {
  if (auto error = checkScopedElaboration(project))
    throw std::runtime_error(toString(std::move(error)));
}
void rejected(const CheckedProject &project) {
  auto error = checkScopedElaboration(project);
  require(bool(error), "forged candidate passed source replay");
  require(namesIdentifier(toString(std::move(error)), "source.binding-witness"),
          "forged candidate failed with a different refusal code");
}
ResolvedReference selected(const CheckedProject &project, DeclarationId owner,
                           StringRef path) {
  auto result = project.declarationIndex().lookup(SourceAccess{owner}, path);
  auto *reference = std::get_if<ResolvedReference>(&result);
  require(reference != nullptr, "expected authorized resolution: " + path);
  return *reference;
}
std::vector<SourceBuffer> abstractReferences() {
  return {{"library",
           "module library;pub interface I{type Data:Copy+Drop;math fn "
           "id(x:Data)->Data;}",
           {}},
          {"facade", "module facade;pub use library::{I};", {}},
          {"m",
           "module m;module Generic<C:facade::I>{math fn "
           "same(x:C::Data)->C::Data{return C::id(x);}}",
           {}}};
}
std::vector<SourceBuffer> facades() {
  return {{"library", "module library;pub math fn f()->bool{return true;}", {}},
          {"first", "module first;pub use library::{f};", {}},
          {"second", "module second;pub use library::{f};", {}},
          {"m", "module m;math fn read()->bool{return first::f();}", {}}};
}
std::vector<SourceBuffer> service(StringRef spelling, StringRef comment = "",
                                  bool unrelated = false) {
  std::vector<SourceBuffer> sources{
      {"facade",
       "module facade;pub use zkc::prelude::{Random};" + comment.str(),
       {}},
      {"m",
       "module m;domain F=field(\"bls12-381.fr\");"
       "protocol Run roles(P)(coins:" +
           spelling.str() + "<F>@P)->(){return();}",
       {}}};
  if (unrelated)
    sources.push_back({"extra", "module extra;pub struct Token{}", {}});
  return sources;
}
} // namespace
int main() {
  Cases cases;
  cases.run("external short-name lookup ignores unrelated declarations", [] {
    auto cost = [&](unsigned padding) {
      std::string source = "module m;type A=bool;";
      for (unsigned i = 0; i < padding; ++i)
        source += "type Unrelated" + std::to_string(i) + "=bool;";
      auto project = take(check(source));
      uint64_t work = 0;
      LookupTraversal traversal{[&] {
                                  ++work;
                                  return true;
                                },
                                {}};
      for (unsigned i = 0; i < 64; ++i) {
        auto result = project.declarationIndex().lookup(
            ExternalSelectionAccess{}, "A", traversal);
        require(std::holds_alternative<ResolvedReference>(result) &&
                    std::get<ResolvedReference>(result).target.index ==
                        named(project, "m::A").id.index,
                "external index lost its exact target");
      }
      return work;
    };
    require(cost(0) == cost(128),
            "each external argument rescanned unrelated declarations");
  });
  for (StringRef member : {"", "math fn f()->bool{return false;}"})
    cases.run("selected imported root is terminal: " + member, [&] {
      auto sources = [&](StringRef path) {
        return std::vector<SourceBuffer>{
            {"api", "module api;pub math fn f()->bool{return true;}", {}},
            {"other", "module other;pub module api{" + member.str() + "}", {}},
            {"m",
             "module m;use other::{api};math fn read()->bool{return " +
                 path.str() + "();}",
             {}}};
      };
      refuses(check(sources("api::f")),
              member.empty() ? "source.name" : "source.private");
      auto project = take(check(sources("::api::f")));
      accepted(project);
      const auto &owner = named(project, "m::read");
      auto result =
          project.declarationIndex().lookup(SourceAccess{owner.id}, "api::f");
      const auto *failure = std::get_if<LookupFailure>(&result);
      require(failure && failure->selected &&
                  failure->selected->index ==
                      named(project, "other::api").id.index &&
                  failure->kind == (member.empty()
                                        ? LookupFailureKind::NotFound
                                        : LookupFailureKind::Inaccessible),
              "index lost the selected terminal root or typed failure");
    });
  cases.run("private root cannot fall through to a captured homonym", [] {
    auto project = take(
        check({{"api", "module api;pub math fn f()->bool{return true;}", {}},
               {"other",
                "module other;module api{pub math fn f()->bool{return false;}}",
                {}},
               {"m", "module m;", {}}}));
    auto result = project.declarationIndex().lookup(
        SourceAccess{named(project, "m").id}, "other::api::f");
    require(std::holds_alternative<LookupFailure>(result) &&
                std::get<LookupFailure>(result).kind ==
                    LookupFailureKind::Inaccessible,
            "private selected root was not terminal");
    require(
        selected(project, named(project, "m").id, "::api::f").provider.index ==
            named(project, "api").id.index,
        "absolute positive control lost its provider");
  });
  cases.run("wrong-category root cannot expose prelude unpack", [] {
    refuses(check("module m;struct R{a:bool,b:bool}"
                  "fn f<unpack:Type>(x:R)->(bool,bool){return unpack(x);}"),
            "source.call");
    auto project = take(check("module m;struct R{a:bool,b:bool}"
                              "fn f<unpack:Type>(x:R)->(bool,bool){return "
                              "zkc::records::unpack(x);}"));
    accepted(project);
    refuses(check("module m;struct R{a:bool,b:bool}"
                  "math fn unpack()->bool{return true;}"
                  "fn f(x:R)->(bool,bool){return unpack::missing(x);}"),
            "source.name");
  });
  cases.run(
      "alias formation is self-excluding and independent of source order", [] {
        for (bool reverse : {false, true}) {
          std::vector<SourceBuffer> sources{
              {"library",
               "module library;pub module sub{pub math fn f()->bool{return "
               "true;}}",
               {}},
              {"m",
               "module m;" +
                   std::string(
                       reverse
                           ? "use library::sub as library;use library as Again;"
                           : "use library as Again;use library::sub as "
                             "library;") +
                   "math fn read()->bool{return Again::f();}",
               {}}};
          if (reverse)
            std::reverse(sources.begin(), sources.end());
          auto project = take(check(sources));
          auto ref =
              selected(project, named(project, "m::read").id, "Again::f");
          require(ref.provider.index == named(project, "library").id.index &&
                      ref.target.index ==
                          named(project, "library::sub::f").id.index,
                  "alias ordering changed provider or target");
          accepted(project);
        }
        refuses(check("module m;use A as B;use B as A;"), "source.cycle");
        for (bool reverse : {false, true}) {
          auto code =
              "module m;module Library{}" +
              std::string(reverse
                              ? "use B as C;use A as B;use ::m::Library as A;"
                              : "use ::m::Library as A;use A as B;use B as C;");
          Limits limits;
          limits.importDepth = 3;
          take(check(code, limits));
          limits.importDepth = 2;
          refuses(check(code, limits), "source.limit");
        }
      });
  cases.run("external static access is separate from source visibility", [] {
    auto project = take(check(
        {{"library",
          "module library;pub protocol Work<C:Field> roles(P)()->(){return();}",
          {}},
         {"hidden", "module hidden;domain F=field(\"bls12-381.fr\");", {}},
         {"m",
          "module m;module hidden{pub domain F=field(\"koala-bear\");}",
          {}}}));
    require(take(selectEntry(project, "library::Work<hidden::F>")).index <
                project.declarations().size(),
            "private qualified external argument was not selectable");
    auto source = project.declarationIndex().lookup(
        SourceAccess{named(project, "m").id}, "::hidden::F");
    require(std::holds_alternative<LookupFailure>(source) &&
                std::get<LookupFailure>(source).kind ==
                    LookupFailureKind::Inaccessible,
            "external policy leaked into source access");
    auto external = project.declarationIndex().lookup(ExternalSelectionAccess{},
                                                      "hidden::F");
    require(
        std::holds_alternative<ResolvedReference>(external) &&
            std::get<ResolvedReference>(external).target.index ==
                named(project, "hidden::F").id.index,
        "qualified external selection lost its exact root or access exception");
  });
  cases.run("external Entry names are exact before kind eligibility", [] {
    auto project = take(check(
        {{"a",
          "module a;protocol T roles(P)()->(){return();}"
          "entry fn Job(inputs:T::Inputs){return T::run(inputs);}",
          {}},
         {"b",
          "module b;protocol T roles(P,V)(ok:bool@V)->(ok:bool@V){return ok;}"
          "proof Job=T{prover P;verifier V;public{ok};accept ok;construction "
          "authored;}",
          {}}}));
    for (auto kind : {EntryKind::Function, EntryKind::Proof})
      refuses(selectEntry(project, "Job", {}, kind), "source.entry");
    require(
        take(selectEntry(project, "a::Job", {}, EntryKind::Function)).index ==
            named(project, "a::Job").id.index,
        "qualified private Entry selected a different target");
    take(selectEntry(project, "b::Job", {}, EntryKind::Proof));
    refuses(selectEntry(project, "a::Job", {}, EntryKind::Proof),
            "source.entry-kind");
  });
  for (StringRef spelling :
       {"Random", "zkc::prelude::Random", "facade::Random"})
    cases.run(
        "managed constructor preserves its selected provider: " + spelling,
        [&] {
          auto project = take(check(service(spelling)));
          accepted(project);
          const auto &port = named(project, "m::Run").services.front();
          require(port.constructor.target.index ==
                          named(project, "zkc::prelude::Random").id.index &&
                      port.constructor.category ==
                          ResolutionCategory::ServiceConstructor &&
                      port.constructor.provider.index ==
                          named(project, spelling.starts_with("facade")
                                             ? "facade"
                                             : "zkc::prelude")
                              .id.index,
                  "managed port replaced its selected constructor provider");
          for (StringRef use : {"module Bad:", "math fn bad<C:"}) {
            auto sources = service(spelling);
            sources.back().text +=
                use.str() + spelling.str() + "<F>" +
                (use.starts_with("module") ? "{}" : ">()->bool{return true;}");
            refuses(check(sources), "source.service");
          }
        });
  cases.run("import-free constructor facade contributes authority", [] {
    auto project = take(check(service("facade::Random")));
    auto revision = take(sourceAuthority(project, "m::Run"));
    require(revision &&
                *revision !=
                    *take(sourceAuthority(
                        take(check(service("facade::Random", "// changed\n"))),
                        "m::Run")),
            "facade edit did not affect constructor client's authority");
    require(revision == take(sourceAuthority(
                            take(check(service("facade::Random", "", true))),
                            "m::Run")),
            "unrelated capture affected constructor client's authority");
  });
  for (unsigned mutation = 0; mutation < 3; ++mutation)
    cases.run("immutable route rejects provider forgery " + Twine(mutation),
              [&] {
                auto project = take(check(facades()));
                accepted(project);
                auto &storage = candidate(project);
                auto &owner =
                    storage.declarations[named(project, "m::read").id.index];
                auto body = std::make_shared<Body>(*owner.body);
                owner.body = body;
                auto call = llvm::find_if(body->operations, [](const auto &op) {
                  return op.binding.has_value();
                });
                require(call != body->operations.end(), "missing call binding");
                auto forged = selected(project, owner.id, "second::f");
                require(forged.target.index ==
                            call->binding->target.declaration.index,
                        "fixture changed canonical target");
                call->binding->target.reference = forged;
                if (mutation == 1) {
                  for (auto &record : storage.api.references)
                    if (record.owner.index == owner.id.index &&
                        record.written == "first::f") {
                      record.provider = forged.provider;
                      record.reference = forged;
                    }
                  auto &metadata =
                      storage.declarations[named(project, "second").id.index];
                  metadata.name = "first";
                  metadata.qualifiedName = "first";
                } else if (mutation == 2)
                  call->binding->target.reference = {};
                rejected(project);
              });
  for (bool body : {false, true})
    cases.run(
        body ? "body constructor forgery" : "signature constructor forgery",
        [&] {
          auto project = take(check(service("facade::Random")));
          accepted(project);
          auto &decl = candidate(project)
                           .declarations[named(project, "m::Run").id.index];
          if (body) {
            auto changed = std::make_shared<Body>(*decl.body);
            changed->services.front().constructor.provider =
                named(project, "zkc::prelude").id;
            decl.body = std::move(changed);
          } else {
            decl.services.front().constructor.provider =
                named(project, "zkc::prelude").id;
          }
          rejected(project);
        });
  cases.run("tuple children retain every authored type occurrence", [] {
    auto project = take(check(std::vector<SourceBuffer>{
        {"library", "module library;pub type Token=bool;", {}},
        {"m",
         "module m;math fn pair(x:(library::Token,library::Token))"
         "->(library::Token,library::Token){return x;}",
         {}}}));
    accepted(project);
    const auto owner = named(project, "m::pair").id;
    std::set<uint32_t> nodes;
    unsigned occurrences = 0;
    for (const auto &record : candidate(project).api.references)
      if (record.owner.index == owner.index &&
          record.written == "library::Token") {
        ++occurrences;
        require(nodes.insert(record.position.node.index).second,
                "tuple children share an authored reference node");
      }
    require(occurrences == 4, "tuple type occurrence inventory is incomplete");
  });
  cases.run("tuple children preserve distinct abstract binder contexts", [] {
    auto project = take(check(R"(module m;
interface I {type Data:Copy+Drop;}
module Generic<C:I,D:I>{
 math fn pair(x:(C::Data,D::Data))->(C::Data,D::Data){return x;}
})"));
    accepted(project);
    const auto owner = named(project, "m::Generic::pair").id;
    std::set<uint32_t> nodes;
    std::map<unsigned, unsigned> binders;
    for (const auto &record : candidate(project).api.references)
      if (record.owner.index == owner.index && record.reference.abstract) {
        require(nodes.insert(record.position.node.index).second,
                "distinct tuple binders share an authored reference node");
        ++binders[record.reference.abstract->binder];
      }
    require(binders == std::map<unsigned, unsigned>{{0, 2}, {1, 2}},
            "tuple children lost a typed binder occurrence");
  });
  cases.run(
      "abstract associated references retain node positions and typed context",
      [] {
        auto project = take(check(abstractReferences()));
        const auto &storage =
            source_detail::DeclarationAccess::storage(project);
        const auto owner = named(project, "m::Generic::same").id;
        std::set<uint32_t> nodes;
        unsigned associated = 0, calls = 0;
        for (const auto &record : storage.api.references)
          if (record.owner.index == owner.index && record.reference.abstract) {
            require(record.provider.index ==
                            named(project, "facade").id.index &&
                        record.reference.abstract->module.symbolic &&
                        record.reference.abstract->interface.index ==
                            named(project, "library::I").id.index &&
                        record.reference.abstract->binderOwner.index ==
                            named(project, "m::Generic").id.index &&
                        record.reference.abstract->binder == 0,
                    "abstract reference lost its facade or typed interface "
                    "context");
            require(nodes.insert(record.position.node.index).second,
                    "distinct source occurrences share a node identity");
            associated += record.target.index ==
                          named(project, "library::I::Data").id.index;
            calls += record.target.index ==
                     named(project, "library::I::id").id.index;
          }
        require(
            associated == 2 && calls == 1,
            "signature or abstract-call positions were omitted or duplicated");
        auto count = storage.api.references.size();
        accepted(project);
        require(storage.api.references.size() == count,
                "independent replay recorded duplicate references");
      });
  for (unsigned position = 0; position < 3; ++position)
    cases.run("abstract reference coverage at position " + Twine(position),
              [&] {
                auto project = take(check(abstractReferences()));
                accepted(project);
                auto &records = candidate(project).api.references;
                const auto owner = named(project, "m::Generic::same").id;
                unsigned ordinal = 0;
                auto found = llvm::find_if(records, [&](const auto &record) {
                  return record.owner.index == owner.index &&
                         record.reference.abstract && ordinal++ == position;
                });
                require(found != records.end(),
                        "missing abstract positive-control position");
                records.erase(found);
                rejected(project);
              });
  cases.run("reference position cannot be replaced by candidate metadata", [] {
    auto project = take(check(abstractReferences()));
    accepted(project);
    auto &records = candidate(project).api.references;
    const auto owner = named(project, "m::Generic::same").id;
    std::vector<source_detail::ReferenceRecord *> occurrences;
    for (auto &record : records)
      if (record.owner.index == owner.index && record.reference.abstract)
        occurrences.push_back(&record);
    require(occurrences.size() == 3, "missing distinct reference positions");
    occurrences[1]->position = occurrences[0]->position;
    rejected(project);
  });
  cases.run("repeated import names retain distinct position slots", [] {
    auto project = take(check(
        {{"library", "module library;pub math fn f()->bool{return true;}", {}},
         {"m", "module m;use library::{f,f};", {}}}));
    accepted(project);
    auto &records = candidate(project).api.references;
    const auto owner = named(project, "m").id;
    std::vector<source_detail::ReferenceRecord *> names;
    for (auto &record : records)
      if (record.owner.index == owner.index &&
          record.route == source_detail::ReferenceRoute::ImportName)
        names.push_back(&record);
    require(names.size() == 2 &&
                names[0]->position.node.index ==
                    names[1]->position.node.index &&
                names[0]->position.ordinal != names[1]->position.ordinal,
            "selected import positions were coalesced by name or span");
    names[1]->position.ordinal = names[0]->position.ordinal;
    rejected(project);
  });
  struct Position {
    const char *name, *owner, *written;
    source_detail::ReferenceRoute route;
  };
  for (auto position : {Position{"signature", "m::signature", "library::Token",
                                 source_detail::ReferenceRoute::Path},
                        Position{"constraint", "m::Generic", "library::I",
                                 source_detail::ReferenceRoute::Path},
                        Position{"unused import", "m", "library::Unused",
                                 source_detail::ReferenceRoute::ImportName},
                        Position{"callback", "m::read", "library::callback",
                                 source_detail::ReferenceRoute::Path}})
    cases.run("non-call reference coverage: " + Twine(position.name), [&] {
      auto project = take(check(
          {{"library",
            "module library;pub struct Token{pub flag:bool}pub struct Unused{}"
            "pub interface I{type Data:Copy+Drop;}"
            "pub math fn callback(x:bool)->bool{return x;}",
            {}},
           {"m",
            "module m;use library::{Unused};"
            "math fn signature(x:library::Token)->bool{return x.flag;}"
            "module Generic<C:library::I>{}"
            "fn invoke(x:bool,body:fn(bool)->bool effects())->bool "
            "effects(){return body(x);}"
            "fn read(x:bool)->bool effects(){return "
            "invoke(x,fn(y)=>library::callback(y));}",
            {}}}));
      accepted(project);
      auto &records = candidate(project).api.references;
      const auto owner = named(project, position.owner).id;
      auto match = [&](const auto &record) {
        return record.owner.index == owner.index &&
               record.written == position.written &&
               record.route == position.route;
      };
      require(llvm::count_if(records, match) == 1,
              "reference position was omitted or duplicated");
      records.erase(llvm::find_if(records, match));
      rejected(project);
    });
  for (auto route : {source_detail::ReferenceRoute::Import,
                     source_detail::ReferenceRoute::Path,
                     source_detail::ReferenceRoute::Service})
    cases.run("reference inventory is mandatory for route " +
                  Twine(unsigned(route)),
              [&] {
                auto sources = service("facade::Random");
                sources.back().text += "math fn flag(x:F)->F{return x;}";
                auto project = take(check(sources));
                accepted(project);
                auto &records = candidate(project).api.references;
                auto record = llvm::find_if(
                    records, [&](const auto &r) { return r.route == route; });
                require(record != records.end(),
                        "missing positive-control reference");
                records.erase(record);
                rejected(project);
              });
  return cases.result();
}
