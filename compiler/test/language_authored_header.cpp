#include "../lib/Language/Semantics.h"
#include "../lib/Language/SignatureWitness.h"
#include "support/NativeCases.h"
#include "zkc/Language/Project.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::language::detail;
using namespace zkc::test;
namespace {
CheckedProject check(const Twine &source, bool layout = false) {
  CaptureOptions options;
  if (layout)
    options.format = "zkc-layout";
  return take(
      analyze(take(capture({{"m", source.str(), "headers.zkc"}}, options)))
          .checkedProject());
}
Declaration &named(const CheckedProject &project,
                   StringRef name = "m::unused") {
  for (const auto &decl : project.declarations())
    if (decl.qualifiedName == name)
      return const_cast<Declaration &>(decl);
  throw std::runtime_error("missing declaration " + name.str());
}
void accepts(const CheckedProject &project) {
  if (auto error = checkScopedElaboration(project))
    throw std::runtime_error(toString(std::move(error)));
}
void rejects(const CheckedProject &project) {
  auto error = checkScopedElaboration(project);
  require(bool(error), "header premise mutation accepted");
  auto message = toString(std::move(error));
  require(namesIdentifier(message, "source.scoped-witness"),
          "wrong header refusal: " + message);
}
const char *mixed = R"(module m;
interface Item {type Value:Type;}
math fn unused<T:Type,D:Item,F:Field,N:nat,M:nat>()->bool
  where N<=M,Copy(T),Drop(D::Value),zkc::algebra::TwoAdicField(F) {return true;}
)";
const char *inference = R"(module m;
type Nonempty<N:nat> where 1<=N=[bool;N];
type Special<F:Field> where zkc::algebra::TwoAdicField(F)=F;
struct Box<T:Type+Drop>{pub value:T}
fn unused<N:nat,F:Field,T:Type>(xs:Nonempty<N>,f:Special<F>,x:Box<T>)->(bool,F,Box<T>,Box<T>){return(xs[0],f,x,x);}
fn result<T:Type>(){return true;}
)";
const char *bodyInference = R"(module m;
fn natural<N:nat>(xs:[bool;N])->bool{return xs[0];}
fn capability<F:Field>(n:index)->F{return kernel<F>("poly.domain_root",n);}
fn unused<T:Type>(x:T)->(T,T){return(x,x);}
)";
const char *used = R"(module m;
math fn unused<T:Type,N:nat,M:nat>(x:T)->T where Copy(T),N<=M{return x;}
math fn client()->bool{return unused<bool,2,3>(true);}
)";
} // namespace
int main() {
  Cases cases;
  for (StringRef premise : {"natural", "usage", "capability"})
    for (StringRef mutation : {"missing", "changed", "added", "inferred"})
      cases.run("unused authored " + premise + " " + mutation, [&] {
        auto project = check(mixed);
        accepts(project);
        auto &decl = named(project);
        require(decl.bounds.size() == 1 && decl.permissionBounds.size() == 1 &&
                    decl.capabilityBounds.size() == 1 &&
                    decl.parameters[0].permissions.copy,
                "missing independent premise controls");
        if (premise == "natural") {
          if (mutation == "missing")
            decl.bounds.clear();
          else if (mutation == "changed")
            decl.bounds[0].rhs = Natural::constant(0);
          else if (mutation == "added")
            decl.bounds.push_back(decl.bounds[0]);
          else
            decl.bounds[0].inferred = true;
        } else if (premise == "usage") {
          if (mutation == "missing")
            decl.permissionBounds.clear();
          else if (mutation == "changed")
            decl.permissionBounds[0].permissions = {true, true};
          else if (mutation == "added")
            decl.permissionBounds.push_back(decl.permissionBounds[0]);
          else
            decl.permissionBounds[0].inferred = true;
        } else {
          if (mutation == "missing")
            decl.capabilityBounds.clear();
          else if (mutation == "changed")
            decl.capabilityBounds[0].arguments[0] = Type(Type::Kind::Boolean);
          else if (mutation == "added")
            decl.capabilityBounds.push_back(decl.capabilityBounds[0]);
          else
            decl.capabilityBounds[0].inferred = true;
        }
        rejects(project);
      });
  for (StringRef mutation :
       {"permissions", "Drop implication", "name", "atom", "sort",
        "domain sort", "interface", "arguments", "missing", "added", "order"})
    cases.run("premise telescope rejects " + mutation, [&] {
      auto project = check(mixed);
      accepts(project);
      auto &parameters = named(project).parameters;
      if (mutation == "permissions")
        parameters[0].permissions = {};
      else if (mutation == "Drop implication")
        parameters[0].permissions.drop = false;
      else if (mutation == "name")
        parameters[0].name = "Other";
      else if (mutation == "atom")
        parameters[0].atom += "Other";
      else if (mutation == "sort")
        parameters[0].sort = Parameter::Sort::Natural;
      else if (mutation == "domain sort")
        parameters[2].domainSort = "Group";
      else if (mutation == "interface")
        parameters[1].interface.reset();
      else if (mutation == "arguments")
        parameters[1].arguments.push_back(Type(Type::Kind::Boolean));
      else if (mutation == "missing")
        parameters.pop_back();
      else if (mutation == "added")
        parameters.push_back(parameters[0]);
      else
        std::swap(parameters[3], parameters[4]);
      rejects(project);
    });
  for (StringRef annotation : {"Type", "Type+Drop", "Type+Copy"})
    for (bool copy : {false, true})
      cases.run(
          "source parameter " + annotation + (copy ? " Copy" : " Drop"), [&] {
            auto project = check("module m;math fn unused<T:" + annotation +
                                 ">()->bool{return true;}");
            accepts(project);
            auto &permissions = named(project).parameters[0].permissions;
            if (copy)
              permissions.copy = !permissions.copy;
            else
              permissions.drop = !permissions.drop;
            rejects(project);
          });
  for (bool explicitEmpty : {false, true})
    for (bool inferred : {false, true})
      for (StringRef premise : {"natural", "usage", "capability"})
        cases.run(
            Twine(explicitEmpty ? "empty where" : "no where") + " injected " +
                premise + (inferred ? " inferred" : " authored"),
            [&] {
              auto project =
                  check(Twine("module m;math fn "
                              "unused<T:Type,F:Field,N:nat>()->bool ") +
                        (explicitEmpty ? "where () " : "") + "{return true;}");
              accepts(project);
              auto &decl = named(project);
              auto sample = check(mixed);
              if (premise == "natural")
                decl.bounds.push_back(
                    {Natural::constant(0),
                     parameterType(decl.parameters[2]).dimension, decl.span,
                     inferred});
              else if (premise == "usage")
                decl.permissionBounds.push_back(
                    {parameterType(decl.parameters[0]),
                     {true, true},
                     decl.span,
                     inferred});
              else {
                auto bound = named(sample).capabilityBounds[0];
                bound.arguments = {parameterType(decl.parameters[1])};
                bound.inferred = inferred;
                decl.capabilityBounds.push_back(std::move(bound));
              }
              rejects(project);
            });
  for (StringRef premise : {"natural", "usage", "capability"})
    cases.run("explicit authored ceiling rejects inferred " + premise, [&] {
      auto project = check(mixed);
      accepts(project);
      auto &decl = named(project);
      if (premise == "natural") {
        auto bound = decl.bounds[0];
        bound.inferred = true;
        decl.bounds.push_back(std::move(bound));
      } else if (premise == "usage") {
        auto bound = decl.permissionBounds[0];
        bound.inferred = true;
        decl.permissionBounds.push_back(std::move(bound));
      } else {
        auto bound = decl.capabilityBounds[0];
        bound.inferred = true;
        decl.capabilityBounds.push_back(std::move(bound));
      }
      rejects(project);
    });
  cases.run("authored usage subject identity", [] {
    auto project = check(mixed);
    accepts(project);
    named(project).permissionBounds[0].type = Type(Type::Kind::Boolean);
    rejects(project);
  });
  cases.run("natural polynomial normalization preserves symbolic identity", [] {
    auto project = check("module m;math fn unused<N:nat,M:nat>()->bool where "
                         "N+M<=M+N{return true;}");
    accepts(project);
    auto &decl = named(project);
    NaturalArithmetic arithmetic;
    decl.bounds[0].lhs =
        take(arithmetic.add(parameterType(decl.parameters[1]).dimension,
                            parameterType(decl.parameters[0]).dimension));
    accepts(project);
    decl.bounds[0].rhs = parameterType(decl.parameters[1]).dimension;
    rejects(project);
  });
  cases.run("authored capability predicate identity", [] {
    auto project = check(mixed);
    accepts(project);
    named(project).capabilityBounds[0].predicate += ".Other";
    rejects(project);
  });
  cases.run("generated classification cannot hide authored premises", [] {
    auto project = check(mixed);
    accepts(project);
    auto &decl = named(project);
    decl.bounds.clear();
    decl.generated = Declaration::Generated{decl.id, "forged"};
    rejects(project);
  });
  cases.run("nongeneric no-where header rejects injected condition", [] {
    auto project = check("module m;math fn unused()->bool{return true;}");
    accepts(project);
    named(project).bounds.push_back(
        {Natural::constant(0), Natural::constant(1), {}, true});
    rejects(project);
  });
  cases.run("signature and body inference preserve omitted body result", [] {
    auto project = check(inference);
    require(named(project).permissionBounds[0].permissions.copy,
            "body failed to strengthen inferred signature Drop");
    require(named(project, "m::result").outputs[0].type.kind ==
                Type::Kind::Boolean,
            "omitted result control missing");
    accepts(project);
  });
  for (StringRef owner : {"m::natural", "m::capability", "m::unused"})
    for (StringRef mutation : {"missing", "changed", "added", "origin"})
      cases.run("body inference " + owner + " " + mutation, [&] {
        auto project = check(bodyInference);
        accepts(project);
        auto &decl = named(project, owner);
        if (owner == "m::natural") {
          require(decl.bounds.size() == 1 && decl.bounds[0].inferred,
                  "no body natural control");
          if (mutation == "missing")
            decl.bounds.clear();
          else if (mutation == "changed")
            decl.bounds[0].lhs = Natural::constant(2);
          else if (mutation == "added")
            decl.bounds.push_back(decl.bounds[0]);
          else
            decl.bounds[0].inferred = false;
        } else if (owner == "m::capability") {
          require(decl.capabilityBounds.size() == 1 &&
                      decl.capabilityBounds[0].inferred,
                  "no body capability control");
          if (mutation == "missing")
            decl.capabilityBounds.clear();
          else if (mutation == "changed")
            decl.capabilityBounds[0].arguments[0] = Type(Type::Kind::Boolean);
          else if (mutation == "added")
            decl.capabilityBounds.push_back(decl.capabilityBounds[0]);
          else
            decl.capabilityBounds[0].inferred = false;
        } else {
          require(decl.permissionBounds.size() == 1 &&
                      decl.permissionBounds[0].inferred,
                  "no body usage control");
          if (mutation == "missing")
            decl.permissionBounds.clear();
          else if (mutation == "changed")
            decl.permissionBounds[0].permissions.copy = false;
          else if (mutation == "added")
            decl.permissionBounds.push_back(decl.permissionBounds[0]);
          else
            decl.permissionBounds[0].inferred = false;
        }
        rejects(project);
      });
  for (StringRef mutation : {"natural", "Copy", "span only"})
    cases.run("used generic contract " + mutation, [&] {
      auto project = check(used);
      accepts(project);
      auto &decl = named(project);
      if (mutation == "natural")
        decl.bounds[0].rhs = Natural::constant(1);
      else if (mutation == "Copy")
        decl.parameters[0].permissions = {};
      else {
        ++decl.bounds[0].span.begin;
        ++decl.bounds[0].span.end;
      }
      if (mutation == "span only")
        accepts(project);
      else
        rejects(project);
    });
  cases.run("unused abstract generic premise", [] {
    auto project = check("module m;interface I<N:nat,M:nat,T:Type>{math fn "
                         "unused()->bool where N<=M,Copy(T);}");
    accepts(project);
    named(project, "m::I::unused").bounds.clear();
    rejects(project);
  });
  for (StringRef owner : {"m::Helpers", "m::Helpers::unused"})
    cases.run("inherited layout premise " + owner, [&] {
      auto project = check(R"(section <N: nat>:
    module Helpers<T: Type, M: nat> where (Copy(T), N <= M):
        def unused() -> bool:
            return true
)",
                           true);
      accepts(project);
      named(project, owner).bounds.clear();
      rejects(project);
    });
  cases.run("explicit empty effect ceiling", [] {
    auto project = check(
        "module m;fn unused<T:Type>()->bool effects() where (){return true;}");
    accepts(project);
    named(project).effectAllowance.reset();
    rejects(project);
  });
  cases.run("source premise retention cannot reauthorize a candidate", [] {
    auto project = check(bodyInference);
    accepts(project);
    named(project).permissionBounds[0].permissions.copy = false;
    auto &storage =
        const_cast<CheckedStorage &>(DeclarationAccess::storage(project));
    Limits limits;
    Work work{limits};
    auto error = retainHeaderPremises(storage, work);
    require(bool(error) && namesIdentifier(toString(std::move(error)),
                                           "source.scoped-witness"),
            "candidate replaced frozen premise authority");
    rejects(project);
  });
  for (bool authored : {false, true})
    cases.run(authored ? "missing authored premise authority"
                       : "missing inference authority",
              [&] {
                auto project = check(bodyInference);
                accepts(project);
                auto &storage = const_cast<CheckedStorage &>(
                    DeclarationAccess::storage(project));
                if (authored)
                  storage.authoredHeaderPremises.reset();
                else
                  storage.inferredHeaderPremises.reset();
                rejects(project);
              });
  cases.run("body strengthening retains its original inference authority", [] {
    auto project = check(inference);
    accepts(project);
    named(project).permissionBounds[0].permissions.copy = false;
    rejects(project);
  });
  cases.run("explicit effect dependencies are charged before comparison", [] {
    auto project = check(
        "module m;fn unused<T:Type>()->bool effects() where (){return true;}");
    accepts(project);
    const auto &storage = DeclarationAccess::storage(project);
    Limits limits;
    Work original{limits};
    auto valid = replayHeaderContracts(storage, original);
    if (!valid)
      throw std::runtime_error(toString(valid.takeError()));
    limits.work = original.used;
    auto &dependencies = named(project).effectAllowance->dependencies;
    for (unsigned i = 0; i <= limits.work; ++i)
      dependencies.emplace(i, Effects{});
    Work bounded{limits};
    auto result = replayHeaderContracts(storage, bounded);
    require(!result &&
                namesIdentifier(toString(result.takeError()), "source.limit"),
            "effect dependencies bypassed work preflight");
    dependencies.clear();
    Work retry{limits};
    auto restored = replayHeaderContracts(storage, retry);
    if (!restored)
      throw std::runtime_error(toString(restored.takeError()));
    require(retry.used == original.used,
            "effect dependency retry changed work");
  });
  cases.run("premise work limits and field growth", [] {
    auto project = check(mixed);
    const auto &storage = DeclarationAccess::storage(project);
    auto replay = [&](uint64_t allowance) {
      Limits limits;
      limits.work = allowance;
      Work work{limits};
      auto result = replayHeaderContracts(storage, work);
      bool accepted = bool(result);
      if (!result)
        require(namesIdentifier(toString(result.takeError()), "source.limit"),
                "growth did not exhaust work before snapshot");
      require(work.used <= allowance, "work exceeded allowance");
      return std::make_pair(work.used, accepted);
    };
    auto original = replay(Limits{}.work);
    auto cost = original.first;
    require(original.second && cost > 0, "original header did not replay");
    require(replay(cost) == original, "exact budget failed");
    require(!replay(cost - 1).second, "one-short budget passed");
    require(replay(cost) == original, "retry changed work");
    auto &decl = named(project);
    auto bounds = decl.bounds;
    decl.bounds.resize(cost + 1, bounds[0]);
    require(!replay(cost).second, "bound count not charged");
    decl.bounds = bounds;
    auto atom = decl.parameters[0].atom;
    decl.parameters[0].atom.resize(cost + 1, 'x');
    require(!replay(cost).second, "parameter atom not charged");
    decl.parameters[0].atom = atom;
    auto natural = decl.bounds[0].lhs;
    Natural oversized;
    auto &terms = const_cast<Natural::Terms &>(oversized.terms());
    terms.emplace(
        Natural::Monomial(cost + 1, {Natural::Factor::Kind::Atom, "n", {}}), 1);
    decl.bounds[0].lhs = std::move(oversized);
    require(!replay(cost).second, "natural factors not charged");
    decl.bounds[0].lhs = natural;
    auto capabilities = decl.capabilityBounds;
    decl.capabilityBounds[0].arguments.resize(cost + 1,
                                              Type(Type::Kind::Boolean));
    require(!replay(cost).second, "capability arguments not charged");
    decl.capabilityBounds = capabilities;
    auto usage = decl.permissionBounds;
    decl.permissionBounds[0].type.arguments.resize(cost + 1,
                                                   Type(Type::Kind::Boolean));
    require(!replay(cost).second, "nested usage type arguments not charged");
    decl.permissionBounds = usage;
    auto arguments = decl.parameters[1].arguments;
    decl.parameters[1].arguments.resize(cost + 1, Type(Type::Kind::Boolean));
    require(!replay(cost).second, "parameter arguments not charged");
    decl.parameters[1].arguments = arguments;
    require(replay(cost) == original, "restored premise changed retry");
    outs() << "authored header exact_work=" << cost
           << " oversized_fields=" << cost + 1 << '\n';
  });
  return cases.result();
}
