#include "../lib/Language/State.h"
#include "support/NativeCases.h"
#include "zkc/Language/DeclarationIndex.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Relation/R1CS.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/MemoryBuffer.h"
#include <functional>
#include <map>
#include <set>
#include <tuple>

using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
CheckedProject check(std::vector<SourceBuffer> sources,
                     std::vector<AssetBuffer> assets = {},
                     StringRef format = "zkc") {
  CaptureOptions options;
  options.format = format.str();
  return take(
      analyze(take(capture(std::move(sources), std::move(assets), options)))
          .checkedProject());
}
json::Value bindings(const CheckedProject &project) {
  return take(json::parse(take(inspectSourceBindings(project))));
}
std::string revision(const json::Value &report, StringRef module) {
  for (const auto &unit : *report.getAsObject()->getArray("units"))
    if (unit.getAsObject()->getString("module") == module)
      return unit.getAsObject()->getString("revision")->str();
  throw std::runtime_error(("no unit " + module).str());
}
std::string revision(const CheckedProject &project, StringRef module) {
  return revision(bindings(project), module);
}

/// An independent check of recorded routes. It walks checked signatures,
/// bodies, constructions and nominal type nodes rather than reading the
/// recorded references, then requires every reached authored declaration to lie
/// in the owner's published closure. It also requires each written occurrence
/// and route to be recorded once, derives each unit's dependencies from the
/// recorded routes and requires them to equal the published rows, and requires
/// a notation or construction route at every such use.
class CrossCheck {
public:
  CrossCheck(const CheckedProject &project, const json::Value &report)
      : project(project), report(*report.getAsObject()) {}
  /// Empty when the records are complete; otherwise a failure naming a unit.
  std::string run() {
    for (const auto &item : *report.getArray("units")) {
      const auto &unit = *item.getAsObject();
      auto &dependencies = published[unit.getString("module")->str()];
      for (const auto &dependency : *unit.getArray("dependencies"))
        dependencies.insert(dependency.getAsString()->str());
    }
    std::set<
        std::tuple<uint32_t, uint32_t, zkc::language::detail::ReferenceRoute,
                   std::string, uint32_t>>
        occurrences;
    for (const auto &record :
         zkc::language::detail::DeclarationAccess::storage(project)
             .api.references) {
      const auto &position = record.position;
      if (!occurrences
               .emplace(record.owner.index, position.node.index, position.kind,
                        position.slot, position.ordinal)
               .second)
        return "owner " +
               project.declarations()[record.owner.index].qualifiedName +
               " records one reference position twice";
    }
    for (const auto &item : *report.getArray("declarations")) {
      const auto &record = *item.getAsObject();
      records.push_back(&record);
    }
    if (auto failure = checkDependencies(); !failure.empty())
      return failure;
    for (const auto &decl : project.declarations()) {
      auto owner = unit(decl.id);
      if (!owner)
        continue;
      auto closure = closed(*owner);
      std::string failure;
      auto reach = [&](DeclarationId target, StringRef why) {
        auto at = unit(target);
        if (failure.empty() && at && !closure.count(*at))
          failure = "unit " + *owner + " reaches " +
                    project.declarations()[target.index].qualifiedName + " (" +
                    why.str() + ") outside its closure";
      };
      walkDeclaration(decl, reach);
      if (!failure.empty())
        return failure;
      if (auto missing = checkUses(decl); !missing.empty())
        return "unit " + *owner + ": " + missing;
    }
    return {};
  }

private:
  const CheckedProject &project;
  const json::Object &report;
  std::map<std::string, std::set<std::string>> published;
  std::vector<const json::Object *> records;
  using Reach = std::function<void(DeclarationId, StringRef)>;

  std::optional<std::string> unit(DeclarationId id) const {
    const auto *decl = &project.declarations()[id.index];
    if (decl->generated)
      decl = &project.declarations()[decl->generated->target.index];
    const auto &source = project.sources()[decl->span.source.index];
    if (source.origin == SourceOrigin::Installation)
      return {};
    return source.module;
  }
  std::optional<std::string> unit(StringRef path) const {
    auto id = project.declarationIndex().canonical(path);
    require(id.has_value(), "recorded declaration is not checked: " + path);
    return unit(*id);
  }
  std::set<std::string> closed(const std::string &start) const {
    std::set<std::string> result{start};
    std::vector<std::string> pending{start};
    while (!pending.empty()) {
      auto at = pending.back();
      pending.pop_back();
      auto found = published.find(at);
      if (found != published.end())
        for (const auto &next : found->second)
          if (result.insert(next).second)
            pending.push_back(next);
    }
    return result;
  }
  std::string checkDependencies() const {
    std::map<std::string, std::set<std::string>> derived;
    for (const auto &[module, dependencies] : published)
      derived[module];
    auto depend = [&](std::optional<std::string> from,
                      std::optional<std::string> to) {
      if (from && to && *from != *to)
        derived[*from].insert(*to);
    };
    for (const auto &decl : project.declarations())
      if (decl.kind == Declaration::Kind::Module && decl.parent) {
        depend(unit(decl.id), unit(*decl.parent));
        depend(unit(*decl.parent), unit(decl.id));
      }
    for (const auto *record : records) {
      auto owner = unit(*record->getString("owner"));
      auto name = [&](StringRef field) {
        return *record->getObject(field)->getString("name");
      };
      depend(owner, unit(name("provider")));
      depend(owner, unit(name("target")));
    }
    for (const auto &[module, dependencies] : derived) {
      auto found = published.find(module);
      if (found == published.end() || found->second != dependencies)
        return "unit " + module +
               " publishes dependencies that differ from its recorded routes";
    }
    if (derived.size() != published.size())
      return "published units differ from the captured units";
    return {};
  }
  void walkType(const Type &type, const Reach &reach) const {
    using K = Type::Kind;
    if ((type.kind == K::Record || type.kind == K::LogicalRecord ||
         type.kind == K::Variant || type.kind == K::Module ||
         type.kind == K::Associated) &&
        !type.symbolic && !StringRef(type.domain).starts_with("self:"))
      if (auto id = project.declarationIndex().canonical(type.domain))
        reach(*id, "type " + type.domain);
    for (const auto &argument : type.arguments)
      walkType(argument, reach);
  }
  void walkReference(const ResolvedReference &reference, const Reach &reach,
                     StringRef why) const {
    reach(reference.provider, why);
    reach(reference.target, why);
    for (const auto &step : reference.path)
      reach(step.owner, why);
    if (reference.abstract)
      walkType(reference.abstract->module, reach);
  }
  void walkCallable(const CallableReference &target, const Reach &reach,
                    StringRef why) const {
    reach(target.declaration, why);
    walkReference(target.reference, reach, why);
    if (target.module)
      walkType(*target.module, reach);
  }
  void walkTypes(ArrayRef<Type> types, const Reach &reach) const {
    for (const auto &type : types)
      walkType(type, reach);
  }
  void walkBody(const Body &body, const Reach &reach) const {
    for (const auto &value : body.values)
      walkType(value.type, reach);
    for (const auto &service : body.services) {
      walkType(service.field, reach);
      walkReference(service.constructor, reach, "service constructor");
    }
    for (const auto &domain : body.domainBindings) {
      walkType(domain.item, reach);
      if (domain.factory)
        walkCallable(*domain.factory, reach, "domain factory");
    }
    for (const auto &scoped : body.scopedBindings)
      if (scoped.computation && scoped.computation->body)
        walkBody(*scoped.computation->body, reach);
    for (const auto &operation : body.operations) {
      if (operation.binding)
        walkCallable(operation.binding->target, reach, "call binding");
      std::visit(
          [&](const auto &action) {
            using A = std::decay_t<decltype(action)>;
            if constexpr (std::is_same_v<A, HelperCall>) {
              reach(action.callee, "helper call");
              walkTypes(action.arguments, reach);
              if (action.module)
                walkType(*action.module, reach);
            } else if constexpr (std::is_same_v<A, BulkApplication> ||
                                 std::is_same_v<A, ProtocolApplication>) {
              reach(action.callee, "application");
              walkTypes(action.arguments, reach);
            } else if constexpr (std::is_same_v<A, HostInvocation>) {
              reach(action.target, "host invocation");
              walkTypes(action.arguments, reach);
            } else if constexpr (std::is_same_v<A, OracleInstantiation>) {
              reach(action.callee, "oracle instantiation");
              walkTypes(action.arguments, reach);
            } else if constexpr (std::is_same_v<A, FiniteComputation>) {
              reach(action.body.helper, "finite body");
              if (action.predicate)
                reach(action.predicate->helper, "finite predicate");
            } else if constexpr (std::is_same_v<A, Control>) {
              for (const auto &region : action.regions)
                if (region)
                  walkBody(*region, reach);
            } else if constexpr (std::is_same_v<A, ProtocolRepeat>) {
              if (action.region)
                walkBody(*action.region, reach);
            } else if constexpr (std::is_same_v<A, LocalPrimitive>) {
              walkTypes(action.staticArguments, reach);
            } else if constexpr (std::is_same_v<A, MathValue>) {
              walkTypes(action.staticArguments, reach);
            }
          },
          operation.action);
    }
  }
  void walkDeclaration(const Declaration &decl, const Reach &reach) const {
    for (const auto *ports : {&decl.inputs, &decl.outputs})
      for (const auto &port : *ports)
        walkType(port.type, reach);
    for (const auto &service : decl.services) {
      walkType(service.field, reach);
      walkReference(service.constructor, reach, "service constructor");
    }
    for (const auto &parameter : decl.parameters) {
      if (parameter.interface)
        reach(*parameter.interface, "parameter bound");
      walkTypes(parameter.arguments, reach);
    }
    for (const auto &field : decl.fields)
      walkType(field.type, reach);
    for (const auto &alternative : decl.alternatives)
      for (const auto &field : alternative.fields)
        walkType(field.type, reach);
    if (decl.kind != Declaration::Kind::Domain)
      walkType(decl.domain, reach);
    if (decl.implementation)
      walkType(*decl.implementation, reach);
    if (decl.domainResult)
      walkType(*decl.domainResult, reach);
    if (decl.target)
      reach(*decl.target, "target");
    walkTypes(decl.staticArguments, reach);
    if (const auto *proof = decl.proof()) {
      if (proof->selectedConstruction)
        reach(*proof->selectedConstruction, "selected construction");
      walkTypes(proof->constructionArguments, reach);
    }
    if (decl.construction) {
      const auto &construction = *decl.construction;
      if (construction.parent)
        reach(*construction.parent, "construction parent");
      walkTypes(construction.arguments, reach);
      if (construction.provider)
        walkType(*construction.provider, reach);
      if (construction.state)
        walkType(*construction.state, reach);
      if (construction.initializer)
        walkCallable(*construction.initializer, reach, "initializer");
      for (const auto &rule : construction.rules) {
        reach(rule.handler, "construction handler");
        walkTypes(rule.arguments, reach);
      }
      for (const auto &application : construction.applications) {
        reach(application.construction, "construction application");
        walkTypes(application.arguments, reach);
      }
      if (construction.codec) {
        const auto &codec = *construction.codec;
        walkType(codec.provider, reach);
        walkType(codec.record, reach);
        for (const auto *method :
             {&codec.initialize, &codec.write, &codec.finish})
          walkCallable(method->target, reach, "codec method");
      }
    }
    if (decl.body)
      walkBody(*decl.body, reach);
  }
  bool recorded(StringRef owner, StringRef route, StringRef target,
                std::optional<Span> span = {}) const {
    for (const auto *record : records) {
      if (record->getString("owner") != owner ||
          record->getString("route") != route ||
          record->getObject("target")->getString("name") != target)
        continue;
      if (!span)
        return true;
      const auto &source = *record->getObject("source");
      if (source.getString("module") ==
              project.sources()[span->source.index].module &&
          source.getInteger("begin") == span->begin &&
          source.getInteger("end") == span->end)
        return true;
    }
    return false;
  }
  std::string checkUses(const Declaration &decl) const {
    std::string failure;
    std::function<void(const Body &)> visit = [&](const Body &body) {
      for (const auto &scoped : body.scopedBindings)
        if (scoped.computation && scoped.computation->body)
          visit(*scoped.computation->body);
      for (const auto &operation : body.operations) {
        if (failure.empty() && operation.binding &&
            operation.binding->notation &&
            !recorded(
                decl.qualifiedName, "notation",
                project
                    .declarations()[operation.binding->target.declaration.index]
                    .qualifiedName,
                operation.span))
          failure = "operator use in " + decl.qualifiedName +
                    " has no notation route";
        if (const auto *control = std::get_if<Control>(&operation.action))
          for (const auto &region : control->regions)
            if (region)
              visit(*region);
        if (const auto *repeat = std::get_if<ProtocolRepeat>(&operation.action))
          if (repeat->region)
            visit(*repeat->region);
      }
    };
    if (decl.body)
      visit(*decl.body);
    if (!failure.empty() || !decl.construction)
      return failure;
    std::vector<const CallableReference *> members;
    if (decl.construction->initializer)
      members.push_back(&*decl.construction->initializer);
    if (const auto &codec = decl.construction->codec)
      for (const auto *method :
           {&codec->initialize, &codec->write, &codec->finish})
        members.push_back(&method->target);
    for (const auto *member : members)
      if (!recorded(
              decl.qualifiedName, "construction",
              project.declarations()[member->declaration.index].qualifiedName))
        return "construction member of " + decl.qualifiedName +
               " has no construction route";
    return {};
  }
};
std::string crossCheck(const CheckedProject &project) {
  return CrossCheck(project, bindings(project)).run();
}

std::string read(StringRef path) {
  auto buffer = MemoryBuffer::getFile(path);
  require(bool(buffer), "cannot read " + path);
  return (*buffer)->getBuffer().str();
}
struct Inputs {
  std::string name, format;
  std::vector<SourceBuffer> sources;
  std::vector<AssetBuffer> assets;
};
/// Every maintained package, then every compiler fixture that checks alone.
std::vector<Inputs> maintainedInputs() {
  auto index = take(json::parse(read(ZKC_SOURCE_PACKAGES)));
  std::vector<Inputs> result;
  for (const auto &[name, value] :
       *index.getAsObject()->getObject("packages")) {
    const auto &package = *value.getAsObject();
    Inputs inputs{name.str(), package.getString("format")->str(), {}, {}};
    for (const auto &[module, path] : *package.getObject("modules"))
      inputs.sources.push_back(
          {module.str(), read(*path.getAsString()), path.getAsString()->str()});
    for (const auto &[asset, entry] : *package.getObject("assets")) {
      const auto &pair = *entry.getAsArray();
      auto path = *pair[1].getAsString();
      inputs.assets.push_back(
          {asset.str(), pair[0].getAsString()->str(), read(path), path.str()});
    }
    result.push_back(std::move(inputs));
  }
  for (const auto &value : *index.getAsObject()->getArray("fixtures")) {
    auto path = *value.getAsString();
    auto text = read(path);
    StringRef rest = text;
    auto at = rest.find("module ");
    if (at == StringRef::npos)
      continue;
    rest = rest.drop_front(at + 7).ltrim();
    auto module = rest.take_while(
        [](char c) { return isAlnum(c) || c == '_' || c == ':'; });
    result.push_back(
        {path.str(), "zkc", {{module.str(), text, path.str()}}, {}});
  }
  return result;
}
std::optional<CheckedProject> checkMaintained(const Inputs &inputs) {
  for (StringRef format : {StringRef(inputs.format), StringRef("zkc-layout")}) {
    CaptureOptions options;
    options.format = format.str();
    auto captured = capture(inputs.sources, inputs.assets, options);
    if (!captured) {
      consumeError(captured.takeError());
      continue;
    }
    auto project = analyze(*captured).checkedProject();
    if (project)
      return std::move(*project);
    consumeError(project.takeError());
  }
  return {};
}

constexpr StringLiteral dependency =
    "module dep;pub fn f(x:bool)->bool{return x;}";
constexpr StringLiteral library = R"(module lib;
pub struct Secret {value:bool}
pub fn g(x:bool)->bool{return ::dep::f(x);}
)";
constexpr StringLiteral client =
    "module client;fn h(x:bool)->bool{return lib::g(x);}";
std::vector<SourceBuffer> clientCapture(StringRef extra = {},
                                        StringRef dependencyText = dependency,
                                        StringRef libraryText = library) {
  return {{"client", (client + extra).str(), "client.zkc"},
          {"dep", dependencyText.str(), "dep.zkc"},
          {"lib", libraryText.str(), "lib.zkc"}};
}
AssetBuffer circuit(StringRef suffix = {}) {
  auto relation =
      take(zkc::relation::R1CS::create("bls12-381.fr", 3, 0, 1, {}));
  return {"circuit",
          "r1cs-json",
          zkc::printJson(relation.encode()) + suffix.str(),
          {}};
}
constexpr StringLiteral relationLibrary = R"(module lib;
domain Fr=field("bls12-381.fr");
pub struct Secret {value:bool}
relation Circuit(statement public:builtin("field_array",Fr,1),witness assignment:builtin("field_array",Fr,3))=r1cs(asset circuit);
)";
constexpr StringLiteral notationModule = R"(module written;
type Vector<F:Field>=builtin("vector",F);
domain Fr=field("koala-bear");
fn fold<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,
    step:fn(S,item:I)->S effects(stop) where item_from(item,rows))->S
    effects(stop)=finite("local.fold");
fn sum<I:Type+Copy+Drop,F:Field>(rows:domain<I>,
    term:fn(item:I)->F effects(stop) where item_from(item,rows))->F
    effects(stop){return fold(rows,0,fn(state,item)=>state+term(item));}
reduction ∑=sum;
fn f(xs:Vector<Fr>,ys:Vector<Fr>)->Fr{return ∑ (x in xs)(y in ys),x*y;}
)";
constexpr StringLiteral constructionModule = R"(module m;
domain F=field("bls12-381.fr");
interface TestTranscript<T:Field> {
  type State:Copy+Drop;
  fn initialize()->State effects(stop, opaque);
  fn observe(t:State,v:T)->State effects(stop, opaque);
  fn draw(t:State)->(State,T) effects(stop, opaque);
}
protocol Round<T:Field> roles(P,V)
    (public:T@(P,V),secret:T@P,challenges:Random<T>@V)->(ok:bool@V){
  #[site(commitment)] let first=send P->V(secret);
  #[site(challenge)] let c=challenges.draw();
  #[site(delivery)] let actual=send V->P(c);
  #[site(response)] let last=send P->V(secret+actual);
  return last==first+c;
}
module Provider:TestTranscript<F>{
  type State:Copy+Drop=(index,index);
  fn initialize()->State{return State((0,0));}
  fn observe(t:State,v:F)->State{return t;}
  fn draw(t:State)->(State,F){return (t,1);}
}
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
)";
const json::Object *only(const json::Value &report, StringRef owner,
                         StringRef route, StringRef target) {
  const json::Object *found = nullptr;
  for (const auto &item : *report.getAsObject()->getArray("declarations")) {
    const auto &record = *item.getAsObject();
    if (record.getString("owner") != owner ||
        record.getString("route") != route ||
        record.getObject("target")->getString("name") != target)
      continue;
    require(!found, "a route was recorded twice: " + owner + " -> " + target);
    found = &record;
  }
  require(found != nullptr,
          "missing " + route + " route: " + owner + " -> " + target);
  return found;
}
} // namespace

int main() {
  zkc::test::Cases cases;
  cases.run("a library revision is shared by its clients", [] {
    auto first = check(clientCapture());
    auto second = check(clientCapture("fn unrelated(x:bool)->bool{return x;}"));
    require(revision(first, "lib") == revision(second, "lib") &&
                revision(first, "dep") == revision(second, "dep"),
            "an unrelated client declaration changed a library revision");
    require(revision(first, "client") != revision(second, "client"),
            "the client revision ignored its own bytes");
    require(take(sourceAuthority(first, "lib::Secret")) ==
                std::optional(revision(first, "lib")),
            "an authored nominal does not take its unit revision");
    auto report = bindings(first);
    for (const auto &item : *report.getAsObject()->getArray("units")) {
      const auto &unit = *item.getAsObject();
      require(unit.getString("revision")->size() == 64,
              "a revision is not a SHA-256 hex digest");
      if (unit.getString("module") == "lib")
        require(unit.getArray("dependencies")->size() == 1 &&
                    (*unit.getArray("dependencies"))[0] == "dep",
                "an import-free qualified path added no dependency");
    }
  });
  cases.run("a library revision binds its whole dependency closure", [] {
    auto base = revision(check(clientCapture()), "lib");
    require(revision(check(clientCapture(
                         {}, "module dep;pub fn f(x:bool)->bool{return !x;}")),
                     "lib") != base,
            "a private dependency body did not change the library");
    require(revision(check(clientCapture({}, dependency,
                                         (library + "// note\n").str())),
                     "lib") != base,
            "a comment did not change the library");
    auto linked = [](StringRef child) {
      return check({{"lib", "module lib;pub module child;pub struct Secret{}",
                     "lib.zkc"},
                    {"lib::child", child.str(), "child.zkc"}});
    };
    require(revision(linked("module lib::child;pub struct A{}"), "lib") !=
                revision(linked("module lib::child;pub struct B{}"), "lib"),
            "a linked child did not change its parent");
    auto assets = [](AssetBuffer asset) {
      return check({{"lib", relationLibrary.str(), "lib.zkc"}}, {asset});
    };
    require(revision(assets(circuit()), "lib") !=
                revision(assets(circuit(" ")), "lib"),
            "a named asset did not change the library");
  });
  cases.run("generated, installed and missing authorities", [] {
    auto project = check({{"m", R"(module m;
      protocol Run roles(P,V)(x:bool@P)->(ok:bool@V){
        let ok@V=send P->V(x);return(ok=ok);}
    )",
                           "m.zkc"}});
    require(!take(sourceAuthority(project, "m::Run::Inputs")).has_value(),
            "a generated declaration received an authored authority");
    require(take(sourceAuthority(project, "m::Run")) ==
                std::optional(revision(project, "m")),
            "an authored protocol lost its unit revision");
    require(take(sourceAuthority(project, "zkc::prelude")) ==
                std::optional(project.installationIdentity().str()),
            "an installed path does not take the installation identity");
    refuses(sourceAuthority(project, "m::Missing"), "source.authority");
    // An authored declaration whose authorities were never computed refuses
    // rather than defaulting to the generated case.
    auto captured = take(capture({{"m", "module m;", "m.zkc"}}));
    zkc::language::detail::CheckedStorage storage(captured,
                                                  installedCatalogIdentity());
    Declaration record;
    record.kind = Declaration::Kind::Record;
    record.id = record.module = {0};
    record.qualifiedName = "m::Secret";
    record.span = {{0}, 0, 1};
    storage.declarations.push_back(record);
    storage.sources = std::make_shared<std::vector<SourceBuffer>>(
        std::vector<SourceBuffer>{{"m", "module m;", "m.zkc"}});
    auto index = std::make_shared<DeclarationIndex>();
    require(index->add(record, SourceOrigin::Captured),
            "failed to index fixture");
    index->finish(storage.declarations, *storage.sources);
    storage.declarationIndex = std::move(index);
    refuses(zkc::language::detail::definingAuthority(storage, "m::Secret"),
            "source.authority");
  });
  cases.run("notation, construction and facade uses record one route", [] {
    auto notation = check({{"written", notationModule.str(), "written.zkc"}});
    auto report = bindings(notation);
    const auto *reduction =
        only(report, "written::f", "notation", "written::sum");
    require(reduction->getObject("provider")->getString("name") == "written" &&
                reduction->getString("written") == "∑",
            "a reduction use lost its declaring module");
    bool prelude = false;
    for (const auto &item : *report.getAsObject()->getArray("declarations")) {
      const auto &record = *item.getAsObject();
      if (record.getString("owner") == "written::f" &&
          record.getString("route") == "notation" &&
          record.getString("written") == "*") {
        require(!prelude, "an operator use was recorded twice");
        prelude = true;
        require(record.getObject("provider")->get("source")->kind() ==
                        json::Value::Null &&
                    record.getObject("target")->get("source")->kind() ==
                        json::Value::Null,
                "a prelude operator was not attributed to the installation");
      }
    }
    require(prelude, "a prelude operator use was not recorded");
    require(crossCheck(notation).empty(), "notation capture fails cross-check");

    auto constructed = check({{"m", constructionModule.str(), "m.zkc"}});
    report = bindings(constructed);
    for (StringRef member : {"State", "initialize"}) {
      const auto *concrete = only(report, "m::Concrete", "construction",
                                  ("m::TestTranscript::" + member).str());
      require(concrete->getObject("provider")->getString("name") ==
                      "m::Provider" &&
                  concrete->get("abstract_module")->kind() == json::Value::Null,
              "a concrete provider lost its module");
      const auto *symbolic = only(report, "m::Derived", "construction",
                                  ("m::TestTranscript::" + member).str());
      require(symbolic->getObject("provider")->getString("name") == "m" &&
                  symbolic->getString("abstract_module").has_value(),
              "a symbolic provider lost its substitution context");
    }
    require(crossCheck(constructed).empty(),
            "construction capture fails cross-check");

    auto facade =
        check({{"lower",
                R"(module lower;
          module Hidden {pub math fn combine(x:bool,y:bool)->bool{return x&&y;}}
          pub use lower::Hidden::{combine};
        )",
                {}},
               {"facade", "module facade;pub use lower::{combine};", {}},
               {"client",
                R"(module client;
          use facade as api;
          math fn helper(x:bool,y:bool)->bool{return api::combine(x,y);}
        )",
                {}}});
    report = bindings(facade);
    const auto *path =
        only(report, "client::helper", "path", "lower::Hidden::combine");
    require(path->getObject("provider")->getString("name") == "facade",
            "a facade path lost its facade provider");
    only(report, "client", "import", "facade");
    only(report, "facade", "import-name", "lower::Hidden::combine");
    require(crossCheck(facade).empty(), "facade capture fails cross-check");
  });
  cases.run(
      "managed method references preserve import-free facade providers", [] {
        auto sources = [](StringRef comment) {
          return std::vector<SourceBuffer>{
              {"facade",
               "module facade;pub use zkc::prelude::{Random};" + comment.str(),
               "facade.zkc"},
              {"client",
               R"(module client;domain F=field("koala-bear.ext4-binomial3");
protocol Run roles(V)(coins:facade::Random<F>@V)->(){
 let alias=coins;let a=alias.draw();let b=alias.index<8>();let c=alias.indices(8,3);return ();})",
               "client.zkc"}};
        };
        auto project = check(sources(""));
        auto report = bindings(project);
        auto constructor =
            project.declarationIndex().canonical("zkc::prelude::Random");
        require(bool(constructor), "missing installed constructor");
        for (const auto &row : zkc::protocol::serviceMethodDeclarations()) {
          if (row.constructor !=
              project.declarationIndex().association(*constructor)->identity)
            continue;
          auto selected = project.declarationIndex().member(
              SourceAccess{*constructor}, *constructor, row.name);
          auto *reference = std::get_if<ResolvedReference>(&selected);
          require(reference &&
                      reference->category == ResolutionCategory::ServiceMethod,
                  "managed row was not installed as an indexed member");
          const auto &target = project.declarations()[reference->target.index];
          const auto *record =
              only(report, "client::Run", "method", target.qualifiedName);
          require(record->getObject("provider")->getString("name") == "facade",
                  "managed method lost its facade provider");
        }
        require(crossCheck(project).empty(),
                "managed facade references fail authority cross-check");
        require(revision(project, "client") !=
                    revision(check(sources("// changed facade")), "client"),
                "managed facade dependency was omitted");
        auto unrelated = sources("");
        unrelated.push_back(
            {"unrelated", "module unrelated;", "unrelated.zkc"});
        require(revision(project, "client") ==
                    revision(check(unrelated), "client"),
                "unrelated capture changed managed client authority");
      });
  cases.run("a discarded lookup records nothing", [] {
    // A data port's type is resolved once by its signature; service
    // classification probes the same name without recording it.
    auto project = check({{"m", R"(module m;
      struct Flag {value:bool}
      protocol Run roles(P,V)(x:Flag@P)->(ok:bool@V){
        let ok@V=true;return(ok=ok);}
    )",
                           "m.zkc"}});
    only(bindings(project), "m::Run", "path", "m::Flag");
  });
  cases.run("dropped routes and edges name their unit", [] {
    auto project = check(clientCapture());
    auto report = bindings(project);
    require(CrossCheck(project, report).run().empty(),
            "complete records fail the cross-check");
    auto dropEdge = report;
    for (auto &item : *dropEdge.getAsObject()->getArray("units"))
      if (item.getAsObject()->getString("module") == "lib")
        item.getAsObject()->getArray("dependencies")->clear();
    auto failure = CrossCheck(project, dropEdge).run();
    require(StringRef(failure).contains("unit lib "),
            "a dropped closure edge was not attributed: " + failure);
    auto dropRecord = report;
    auto &records = *dropRecord.getAsObject()->getArray("declarations");
    for (auto at = records.begin(); at != records.end(); ++at)
      if (at->getAsObject()->getString("owner") == "lib::g" &&
          at->getAsObject()->getString("written") == "::dep::f") {
        records.erase(at);
        break;
      }
    failure = CrossCheck(project, dropRecord).run();
    require(StringRef(failure).contains("unit lib "),
            "a dropped route was not attributed: " + failure);
    auto notation = check({{"written", notationModule.str(), "written.zkc"}});
    auto dropNotation = bindings(notation);
    auto &notationRecords =
        *dropNotation.getAsObject()->getArray("declarations");
    for (auto at = notationRecords.begin(); at != notationRecords.end(); ++at)
      if (at->getAsObject()->getString("route") == "notation" &&
          at->getAsObject()->getString("written") == "*") {
        notationRecords.erase(at);
        break;
      }
    failure = CrossCheck(notation, dropNotation).run();
    require(StringRef(failure).contains("no notation route"),
            "a dropped notation route was not detected: " + failure);
  });
  for (auto route : {zkc::language::detail::ReferenceRoute::Notation,
                     zkc::language::detail::ReferenceRoute::Construction})
    cases.run(
        "independent replay requires retained non-call routes " +
            Twine(unsigned(route)),
        [&] {
          const bool notation =
              route == zkc::language::detail::ReferenceRoute::Notation;
          auto project =
              notation
                  ? check({{"written", notationModule.str(), "written.zkc"}})
                  : check({{"m", constructionModule.str(), "m.zkc"}});
          if (auto error = checkScopedElaboration(project))
            throw std::runtime_error(toString(std::move(error)));
          auto &storage = const_cast<zkc::language::detail::CheckedStorage &>(
              zkc::language::detail::DeclarationAccess::storage(project));
          auto found =
              llvm::find_if(storage.api.references, [&](const auto &record) {
                return record.route == route;
              });
          require(found != storage.api.references.end(),
                  "missing positive-control route");
          storage.api.references.erase(found);
          auto error = checkScopedElaboration(project);
          require(bool(error),
                  "removed non-call route passed independent replay");
          auto message = toString(std::move(error));
          require(namesIdentifier(message, "source.binding-witness"),
                  "wrong replay refusal: " + message);
        });
  cases.run("every maintained package and fixture records complete routes", [] {
    unsigned packages = 0, fixtures = 0;
    for (const auto &inputs : maintainedInputs()) {
      bool package = StringRef(inputs.name).ends_with("zkc.toml");
      auto project = checkMaintained(inputs);
      require(project.has_value() || !package,
              "maintained package does not check: " + inputs.name);
      if (!project)
        continue;
      auto failure = crossCheck(*project);
      require(failure.empty(), inputs.name + ": " + failure);
      ++(package ? packages : fixtures);
    }
    outs() << "cross-checked " << packages << " packages and " << fixtures
           << " fixtures\n";
    require(packages >= 50 && fixtures >= 40,
            "the maintained inputs were not exercised");
  });
  return cases.result();
}
