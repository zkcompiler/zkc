#include "../lib/Language/ConstructionWitness.h"
#include "support/NativeCases.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
namespace source_detail = zkc::language::detail;
constexpr StringLiteral program = R"(module m;
domain F=field("bls12-381.fr");
interface TestTranscript<T:Field> {
  type State:Copy+Drop;
  fn initialize()->State effects(stop,opaque);
  fn spare()->State effects(stop,opaque);
  fn observe(t:State,v:T)->State effects(stop,opaque);
  fn draw(t:State)->(State,T) effects(stop,opaque);
}
protocol Round<T:Field> roles(P,V)
    (public:T@(P,V),secret:T@P,challenges:Random<T>@V)->(ok:bool@V){
  #[site(commitment)] let first=send P->V(secret);
  #[site(challenge)] let c=challenges.draw();
  #[site(delivery)] let actual=send V->P(c);
  #[site(response)] let last=send P->V(secret+actual);
  return last==first+c;
}
pub module Provider:TestTranscript<F>{
  type State:Copy+Drop=(index,index);
  fn initialize()->State{return State((0,0));}
  fn spare()->State{return State((1,1));}
  fn observe(t:State,v:F)->State{return t;}
  fn draw(t:State)->(State,F){return (t,1);}
}
type Bytes=builtin("bytes");
fn empty()->Bytes=primitive("bytes.empty");
interface RecordCodec<L:Type+Copy+Drop>{
  type Record:Copy+Drop;
  fn initialize(layout:L)->Record effects(stop,opaque);
  fn reset(layout:L)->Record effects(stop,opaque);
  fn write(record:Record)->Bytes effects(stop,opaque);
  fn flush(record:Record)->Bytes effects(stop,opaque);
  fn finish(record:Record,proof:Bytes)->() effects(stop,opaque);
  fn done(record:Record,proof:Bytes)->() effects(stop,opaque);
}
pub module Packing:RecordCodec<F>{
  type Record:Copy+Drop=();
  fn initialize(layout:F)->Record{return Record(());}
  fn reset(layout:F)->Record{return Record(());}
  fn write(record:Record)->Bytes{return empty();}
  fn flush(record:Record)->Bytes{return empty();}
  fn finish(record:Record,proof:Bytes)->(){return ();}
  fn done(record:Record,proof:Bytes)->(){return ();}
}
use ::m::Provider as Alias;
use ::m::Packing as FormatAlias;
module Front{
  pub use ::m::Provider as Transcript;
  pub use ::m::Packing as Format;
}
use ::m::Front as Route;
construction Concrete for Round<F>{
  transcript Provider;
  replace challenges;
  on start(t,public){return Provider::observe(t,public);}
  on message {commitment,response}(t,value){return Provider::observe(t,value);}
  on message delivery(t,value){return t;}
  on query challenge(t){return Provider::draw(t);}
}
construction Derived<T:Field,H:TestTranscript<T>> for Round<T>{
  transcript H;
  replace challenges;
  on start(t,public){return H::observe(t,public);}
  on message {commitment,response}(t,value){return H::observe(t,value);}
  on message delivery(t,value){return t;}
  on query challenge(t){return H::draw(t);}
}
construction AnotherConcrete for Round<F>{
  transcript Provider;
  replace challenges;
  on start(t,public){return Provider::observe(t,public);}
  on message {commitment,response}(t,value){return Provider::observe(t,value);}
  on message delivery(t,value){return t;}
  on query challenge(t){return Provider::draw(t);}
}
construction Layer<T:Field,H:TestTranscript<T>> for Round<T>{base Derived<T,H>;}
construction ConcreteInherited for Round<F>{base Layer<F,Provider>;}
construction Encoded<C:RecordCodec<F>> for Round<F>{
  base Derived<F,Provider>;
  format C(public);
  on encode {commitment,response}(r,value){return (r,empty());}
  on receive {commitment,response}(r,proof){return (r,(0,32));}
  on decode {commitment,response}(wire){return 0;}
  on wire {commitment,response}(t,wire){return t;}
}
construction InheritedCodec<D:RecordCodec<F>> for Round<F>{base Encoded<D>;}
construction ConcreteCodec for Round<F>{base InheritedCodec<Packing>;}
construction Authored for Round<F>{base authored;}
construction Native for Round<F>{
  base fiat_shamir("merlin3.bls12-381.fr64be/0",challenges);
}
proof Demo=Round<F>{prover P;verifier V;public{public};accept ok;
  construction InheritedCodec<Packing>;}
)";
CheckedProject checked(StringRef code = program) {
  return take(analyze(take(capture({{"m", code.str(), "witness.zkc"}})))
                  .checkedProject());
}
source_detail::CheckedStorage &candidate(const CheckedProject &project) {
  return const_cast<source_detail::CheckedStorage &>(
      source_detail::DeclarationAccess::storage(project));
}
Declaration &named(const CheckedProject &project, StringRef name) {
  auto &decls = candidate(project).declarations;
  auto found = llvm::find_if(
      decls, [&](const auto &decl) { return decl.qualifiedName == name; });
  require(found != decls.end(), "missing fixture declaration: " + name);
  return *found;
}
void success(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
Error replay(const CheckedProject &project, const Limits &limits = {}) {
  source_detail::Work work{limits};
  return source_detail::checkConstructionSources(candidate(project), work);
}
void accepted(const CheckedProject &project) {
  success(checkScopedElaboration(project));
  success(replay(project));
}
bool same(const source_detail::ReferenceRecord &a,
          const source_detail::ReferenceRecord &b) {
  return a.owner.index == b.owner.index &&
         a.provider.index == b.provider.index &&
         a.target.index == b.target.index &&
         a.span.source.index == b.span.source.index &&
         a.span.begin == b.span.begin && a.span.end == b.span.end &&
         a.written == b.written && a.abstractModule == b.abstractModule &&
         a.route == b.route && a.reference == b.reference &&
         a.position.node.index == b.position.node.index &&
         a.position.kind == b.position.kind &&
         a.position.slot == b.position.slot &&
         a.position.ordinal == b.position.ordinal && a.site == b.site;
}
void rejected(Error error, StringRef code = "source.binding-witness") {
  require(bool(error), "forged construction projection passed replay");
  auto message = toString(std::move(error));
  require(namesIdentifier(message, code), "unexpected refusal: " + message);
}
void mutation(
    StringRef owner,
    function_ref<void(ConstructionDefinition &, const CheckedProject &)> edit,
    StringRef code = program) {
  auto project = checked(code);
  accepted(project); // Every mutation starts from a fresh positive replay.
  auto &storage = candidate(project);
  auto authored = storage.authoredReferences;
  auto inventory = storage.api.references;
  edit(*named(project, owner).construction, project);
  require(storage.authoredReferences == authored &&
              storage.api.references.size() == inventory.size() &&
              std::equal(inventory.begin(), inventory.end(),
                         storage.api.references.begin(), same),
          "mutation changed a reference inventory");
  rejected(replay(project));
  // The public boundary must invoke the projection witness, too.
  rejected(checkScopedElaboration(project));
}
void replace(std::string &text, StringRef from, StringRef to) {
  auto position = text.find(from.str());
  require(position != std::string::npos, "fixture replacement missing");
  text.replace(position, from.size(), to.str());
}
ConstructionMethod &method(ConstructionDefinition &plan, unsigned slot) {
  require(plan.codec.has_value(), "codec fixture missing");
  switch (slot) {
  case 0:
    return plan.codec->initialize;
  case 1:
    return plan.codec->write;
  default:
    return plan.codec->finish;
  }
}
void retarget(CallableReference &callable, DeclarationId target,
              StringRef name) {
  callable.declaration = target;
  callable.reference.target = target;
  require(!callable.reference.path.empty(), "fixture route is empty");
  callable.reference.path.back().name = name.str();
}
void canonicalize(CallableReference &callable, const CheckedProject &project,
                  DeclarationId owner, StringRef provider) {
  auto selected =
      project.declarationIndex().lookup(SourceAccess{owner}, provider);
  auto *reference = std::get_if<ResolvedReference>(&selected);
  require(reference && !callable.reference.path.empty(),
          "canonical provider route is missing");
  auto route = *reference;
  route.target = callable.reference.target;
  route.category = callable.reference.category;
  route.abstract = callable.reference.abstract;
  route.path.push_back(callable.reference.path.back());
  require(route != callable.reference, "route mutation changed no provenance");
  callable.reference = std::move(route);
}
} // namespace
int main() {
  Cases cases;
  cases.run(
      "direct, generic, inherited, authored and native projections replay", [] {
        accepted(checked());
        accepted(checked("module m;"));
      });
  cases.run(
      "inherited projections retain the author's occurrence and route", [] {
        auto project = checked();
        accepted(project);
        const auto &root =
            *named(project, "m::Derived").construction->initializer;
        const auto &inherited =
            *named(project, "m::ConcreteInherited").construction->initializer;
        require(root.authoredReference &&
                    root.authoredReference == inherited.authoredReference &&
                    root.reference == inherited.reference &&
                    root.module != inherited.module,
                "inheritance lost authored identity or failed to specialize "
                "the module");
        const auto &open = *named(project, "m::Encoded").construction->codec;
        const auto &closed =
            *named(project, "m::ConcreteCodec").construction->codec;
        for (auto [a, b] : {std::pair{&open.initialize, &closed.initialize},
                            std::pair{&open.write, &closed.write},
                            std::pair{&open.finish, &closed.finish}})
          require(a->target.authoredReference &&
                      a->target.authoredReference ==
                          b->target.authoredReference &&
                      a->target.reference == b->target.reference &&
                      a->target.module != b->target.module,
                  "inherited codec rewrote its written route");
      });
  for (StringRef owner :
       {"m::Concrete", "m::Derived", "m::Layer", "m::ConcreteInherited"}) {
    cases.run(owner + " initializer provider forgery", [&] {
      mutation(owner, [](auto &plan, const auto &project) {
        plan.initializer->reference.provider = named(project, "m").id;
      });
    });
    cases.run(
        owner + " compatible initializer target and reference forgery", [&] {
          mutation(owner, [](auto &plan, const auto &project) {
            retarget(*plan.initializer,
                     named(project, "m::TestTranscript::spare").id, "spare");
          });
        });
    cases.run(owner + " initializer module and provider forgery", [&] {
      mutation(owner, [](auto &plan, const auto &project) {
        plan.provider = Type(Type::Kind::Module, "m::Packing");
        plan.initializer->module = plan.provider;
        plan.initializer->reference.abstract->module = *plan.provider;
        plan.initializer->reference.provider = named(project, "m::Packing").id;
      });
    });
    cases.run(owner + " missing initializer projection", [&] {
      mutation(owner,
               [](auto &plan, const auto &) { plan.initializer.reset(); });
    });
    cases.run(owner + " missing initializer occurrence", [&] {
      mutation(owner, [](auto &plan, const auto &) {
        plan.initializer->authoredReference.reset();
      });
    });
    cases.run(owner + " initializer occurrence is outside the inventory", [&] {
      mutation(owner, [](auto &plan, const auto &) {
        plan.initializer->authoredReference = UINT32_MAX;
      });
    });
    cases.run(owner + " initializer declaration alone differs", [&] {
      mutation(owner, [](auto &plan, const auto &project) {
        plan.initializer->declaration =
            named(project, "m::TestTranscript::spare").id;
      });
    });
    cases.run(owner + " initializer arguments differ", [&] {
      mutation(owner, [](auto &plan, const auto &) {
        plan.initializerArguments.clear();
      });
    });
  }
  for (StringRef owner :
       {"m::Encoded", "m::InheritedCodec", "m::ConcreteCodec"}) {
    for (unsigned slot = 0; slot < 3; ++slot) {
      auto name = (owner + " codec slot " + Twine(slot)).str();
      cases.run(name + " provider forgery", [&] {
        mutation(owner, [&](auto &plan, const auto &project) {
          method(plan, slot).target.reference.provider = named(project, "m").id;
        });
      });
      cases.run(name + " compatible target and reference forgery", [&] {
        mutation(owner, [&](auto &plan, const auto &project) {
          const char *names[] = {"reset", "flush", "done"};
          retarget(
              method(plan, slot).target,
              named(project, "m::RecordCodec::" + std::string(names[slot])).id,
              names[slot]);
        });
      });
      cases.run(name + " missing method occurrence", [&] {
        mutation(owner, [&](auto &plan, const auto &) {
          method(plan, slot).target.authoredReference.reset();
        });
      });
      cases.run(name + " missing method projection", [&] {
        mutation(owner, [&](auto &plan, const auto &) {
          method(plan, slot).target = {{UINT32_MAX}, std::nullopt};
        });
      });
      cases.run(name + " argument forgery", [&] {
        mutation(owner, [&](auto &plan, const auto &) {
          method(plan, slot).arguments.clear();
        });
      });
    }
    cases.run(owner + " missing codec projection", [&] {
      mutation(owner, [](auto &plan, const auto &) { plan.codec.reset(); });
    });
    cases.run(owner + " codec provider and all module terms differ", [&] {
      mutation(owner, [](auto &plan, const auto &) {
        plan.codec->provider = Type(Type::Kind::Module, "m::Provider");
        for (unsigned slot = 0; slot < 3; ++slot)
          method(plan, slot).target.module = plan.codec->provider;
      });
    });
  }
  for (StringRef owner : {"m::Authored", "m::Native"}) {
    cases.run(owner + " extra initializer", [&] {
      mutation(owner, [](auto &plan, const auto &project) {
        const auto &other = *named(project, "m::Concrete").construction;
        plan.initializer = other.initializer;
        plan.initializerArguments = other.initializerArguments;
      });
    });
    cases.run(owner + " extra codec", [&] {
      mutation(owner, [](auto &plan, const auto &project) {
        plan.codec = named(project, "m::Encoded").construction->codec;
      });
    });
    cases.run(owner + " extra initializer arguments", [&] {
      mutation(owner, [](auto &plan, const auto &) {
        plan.initializerArguments.push_back(Type{});
      });
    });
  }
  cases.run(
      "actual initializer dispatch cannot replace its written target", [] {
        mutation("m::ConcreteInherited", [](auto &plan, const auto &project) {
          retarget(*plan.initializer,
                   named(project, "m::Provider::initialize").id, "initialize");
          plan.initializer->reference.path.back().owner =
              named(project, "m::Provider").id;
          plan.initializerArguments.clear();
        });
      });
  for (unsigned slot = 0; slot < 3; ++slot)
    cases.run(
        "actual codec dispatch cannot replace its written target " +
            Twine(slot),
        [&] {
          mutation("m::ConcreteCodec", [&](auto &plan, const auto &project) {
            const char *names[] = {"initialize", "write", "finish"};
            auto &selected = method(plan, slot);
            retarget(
                selected.target,
                named(project, "m::Packing::" + std::string(names[slot])).id,
                names[slot]);
            selected.target.reference.path.back().owner =
                named(project, "m::Packing").id;
            selected.arguments.clear();
          });
        });
  cases.run(
      "another valid occurrence cannot authorize a direct initializer", [] {
        mutation("m::Concrete", [](auto &plan, const auto &project) {
          const auto &other =
              *named(project, "m::AnotherConcrete").construction;
          require(
              plan.initializer->module == other.initializer->module &&
                  plan.initializer->declaration.index ==
                      other.initializer->declaration.index &&
                  plan.initializer->authoredReference !=
                      other.initializer->authoredReference,
              "fixture must select the same member at a distinct occurrence");
          plan.initializer->authoredReference =
              other.initializer->authoredReference;
        });
      });
  cases.run("the codec initialize occurrence cannot replace write", [] {
    mutation("m::Encoded", [](auto &plan, const auto &) {
      plan.codec->write.target.authoredReference =
          plan.codec->initialize.target.authoredReference;
    });
  });
  for (StringRef spelling : {"Alias", "Route::Transcript"}) {
    auto code = program.str();
    replace(code, "transcript Provider;", "transcript " + spelling.str() + ";");
    cases.run("written transcript route replays and specializes: " + spelling,
              [&] {
                auto project = checked(code + R"(
proof AliasDemo=Round<F>{prover P;verifier V;public{public};accept ok;
  construction Concrete;}
)");
                accepted(project);
                auto closed = take(closeEntry(project, "m::AliasDemo"));
                success(checkScopedSpecialization(closed));
              });
    cases.run(
        "written transcript route rejects canonicalization: " + spelling, [&] {
          mutation(
              "m::Concrete",
              [](auto &plan, const auto &project) {
                canonicalize(*plan.initializer, project,
                             named(project, "m::Concrete").id, "::m::Provider");
              },
              code);
        });
  }
  for (StringRef spelling : {"FormatAlias", "Route::Format"}) {
    auto code = program.str();
    replace(code, "format C(public);",
            "format " + spelling.str() + "(public);");
    cases.run("written codec route replays and specializes: " + spelling, [&] {
      auto project = checked(code);
      accepted(project);
      auto closed = take(closeEntry(project, "m::Demo"));
      success(checkScopedSpecialization(closed));
    });
    for (unsigned slot = 0; slot < 3; ++slot)
      cases.run("written codec route rejects canonicalization: " + spelling +
                    Twine(slot),
                [&] {
                  mutation(
                      "m::Encoded",
                      [&](auto &plan, const auto &project) {
                        canonicalize(method(plan, slot).target, project,
                                     named(project, "m::Encoded").id,
                                     "::m::Packing");
                      },
                      code);
                });
  }
  cases.run("changing inherited parent and arguments cannot select another "
            "occurrence",
            [] {
              mutation(
                  "m::ConcreteInherited", [](auto &plan, const auto &project) {
                    plan.parent = named(project, "m::Concrete").id;
                    plan.arguments.clear();
                    plan.initializer =
                        named(project, "m::Concrete").construction->initializer;
                  });
            });
  for (unsigned change = 0; change < 4; ++change)
    cases.run("construction source coverage " + Twine(change), [&] {
      auto project = checked();
      accepted(project);
      auto &storage = candidate(project);
      auto id = named(project, "m::Concrete").id.index;
      if (change == 0)
        storage.constructionSources.erase(id);
      if (change == 1)
        storage.constructionSources[id].reset();
      if (change == 2)
        named(project, "m::Concrete").construction.reset();
      if (change == 3)
        storage.constructionSources.emplace(
            named(project, "m::Provider").id.index,
            storage.constructionSources.at(id));
      rejected(replay(project));
    });
  cases.run("generic construction retains deferred boundary requirements", [] {
    auto project = checked();
    accepted(project);
    auto &layer = named(project, "m::Layer");
    require(!layer.admissions.empty(), "fixture has no deferred boundaries");
    layer.admissions.clear();
    rejected(replay(project));
    rejected(checkScopedElaboration(project));
  });
  cases.run("construction replay charges its allowance", [] {
    auto project = checked();
    accepted(project);
    Limits limits;
    source_detail::Work work{limits};
    success(source_detail::checkConstructionSources(candidate(project), work));
    require(work.used > 0, "construction replay did not charge work");
    limits.work = work.used - 1;
    rejected(replay(project, limits), "source.limit");
  });
  for (unsigned slot = 0; slot < 4; ++slot)
    cases.run(
        "specialization preserves authored occurrence " + Twine(slot), [&] {
          auto project = checked();
          accepted(project);
          auto closed = take(closeEntry(project, "m::Demo"));
          success(checkScopedSpecialization(
              closed)); // Fresh positive before editing.
          auto &decls = const_cast<std::vector<Declaration> &>(
              source_detail::DeclarationAccess::get(closed));
          auto &plan =
              *decls[closed.entry().proof()->selectedConstruction->index]
                   .construction;
          auto &callable =
              slot ? method(plan, slot - 1).target : *plan.initializer;
          require(
              callable.authoredReference && callable.module &&
                  !callable.module->symbolic && callable.reference.abstract &&
                  callable.reference.abstract->module.symbolic &&
                  callable.declaration.index != callable.reference.target.index,
              "closed dispatch was conflated with its authored route");
          callable.authoredReference.reset();
          rejected(checkScopedSpecialization(closed),
                   "source.scoped-specialization");
        });
  return cases.result();
}
