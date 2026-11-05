#include "../lib/Language/Semantics.h"
#include "../lib/Language/SignatureWitness.h"
#include "support/NativeCases.h"
#include "zkc/Language/Project.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::language::detail;
using namespace zkc::test;
namespace {
Expected<CheckedProject> check(StringRef source) {
  auto captured = capture({{"m", source.str(), "signatures.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
Declaration &named(const CheckedProject &project, StringRef name) {
  for (const auto &decl : project.declarations())
    if (decl.qualifiedName == name)
      return const_cast<Declaration &>(decl);
  throw std::runtime_error("missing declaration " + name.str());
}
void acceptsWitness(const CheckedProject &project) {
  if (auto error = checkScopedElaboration(project))
    throw std::runtime_error(toString(std::move(error)));
}
void refusesWitness(const CheckedProject &project) {
  auto error = checkScopedElaboration(project);
  require(bool(error), "signature/conformance mutation was accepted");
  auto diagnostic = toString(std::move(error));
  require(namesIdentifier(diagnostic, "source.scoped-witness"),
          "wrong signature/conformance refusal: " + diagnostic);
}
const std::string contracts = R"(module m;
  domain Fr=field("koala-bear");domain Fq=field("baby-bear");
  type Flag=bool;
  type Special<F:Field> where zkc::algebra::TwoAdicField(F)=F;
  interface I<N:nat,T:Type,F:Field> {
    type Scalar:Field;
    math fn choose(left:Flag,right:Flag)->Flag;
    domain fn rows(lo:index,hi:index)->domain<index>;
    fn run(x:bool,body:fn(bool)->bool)->bool effects(body);
  }
  module A<N:nat,T:Type,F:Field>:I<N,T,F> {
    type Scalar:Field=Fr;
    math fn choose(left:Flag,right:Flag)->Flag {return left;}
    domain fn rows(lo:index,hi:index)->domain<index>=domain("range");
    fn run(x:bool,body:fn(bool)->bool)->bool {return body(x);}
  }
  module B<N:nat,T:Type,F:Field>:I<N,T,F> {
    type Scalar:Field=Fq;
    math fn choose(left:Flag,right:Flag)->Flag {return right;}
    domain fn rows(lo:index,hi:index)->domain<index>=domain("range");
    fn run(x:bool,body:fn(bool)->bool)->bool {return body(x);}
  }
)";
enum class Premise { Natural, Permission, Capability };
StringRef name(Premise premise) {
  switch (premise) {
  case Premise::Natural:
    return "natural";
  case Premise::Permission:
    return "permission";
  case Premise::Capability:
    return "capability";
  }
  llvm_unreachable("unknown premise");
}
void forgePremise(const CheckedProject &project, Declaration &decl,
                  Premise premise) {
  switch (premise) {
  case Premise::Natural:
    decl.bounds.push_back({Natural::constant(2),
                           parameterType(decl.parameters[0]).dimension,
                           decl.span, true});
    break;
  case Premise::Permission:
    decl.permissionBounds.push_back(
        {parameterType(decl.parameters[1]), {true, true}, decl.span, true});
    break;
  case Premise::Capability:
    decl.capabilityBounds.push_back(
        {named(project, "m::Special").capabilityBounds.front().predicate,
         {parameterType(decl.parameters[2])},
         decl.span,
         true});
    break;
  }
}
const std::string domainSignature = R"(module m;
  interface Visitor<T:Type> {
    math fn accept(rows:domain<T>)->bool where Copy(T);
  }
  module A<T:Type>:Visitor<T> {
    math fn accept(rows:domain<T>)->bool {return true;}
  }
)";
const std::string usageSignature = R"(module m;
  struct Box<T:Type+Drop>{pub value:T}
  interface Copier<T:Type> {
    fn duplicate(x:Box<T>)->(Box<T>,Box<T>) effects() where Copy(T);
  }
  module A<T:Type>:Copier<T> {
    fn duplicate(x:Box<T>)->(Box<T>,Box<T>){return(x,x);}
  }
)";
const std::string formationSignature = R"(module m;
  type Nonempty<N:nat> where 1<=N=[bool;N];
  type Special<F:Field> where zkc::algebra::TwoAdicField(F)=F;
  interface I<N:nat,F:Field> {
    fn pass(xs:[bool;N],f:F)->([bool;N],F) effects()
      where 1<=N,zkc::algebra::TwoAdicField(F);
  }
  module A<N:nat,F:Field>:I<N,F> {
    fn pass(xs:Nonempty<N>,f:Special<F>)->([bool;N],F){return(xs,f);}
  }
)";
const std::string inferredResults = R"(module m;
  interface I<F:Field> {
    fn flag()->bool effects();
    fn pair(x:bool)->(bool,bool) effects();
    fn unit()->() effects();
    fn root(n:index)->F effects(stop,opaque)
      where zkc::algebra::TwoAdicField(F);
  }
  module A<F:Field>:I<F> {
    fn flag() effects() where () {return true;}
    fn pair(x:bool){return(x,x);}
    fn unit(){return ();}
    fn root(n:index){return kernel<F>("poly.domain_root",n);}
  }
)";
} // namespace
int main() {
  Cases cases;
  cases.run("unrelated domain signature independently infers Copy", [] {
    auto project = take(check(contracts + R"(
      math fn accept<T:Type>(rows:domain<T>)->bool{return true;}
    )"));
    const auto &accept = named(project, "m::accept");
    require(accept.permissionBounds.size() == 1 &&
                accept.permissionBounds.front().inferred &&
                accept.permissionBounds.front().permissions.copy,
            "domain signature did not infer Copy");
    acceptsWitness(project);
    // This unrelated candidate is deliberately stripped of its inference.
    // The conformance replay must still derive its own signature premises.
    named(project, "m::accept").permissionBounds.clear();
    Limits limits;
    Work work{limits};
    if (auto error =
            checkModuleContracts(DeclarationAccess::storage(project), work))
      throw std::runtime_error(toString(std::move(error)));
  });
  cases.run("signature applications infer natural and catalog requirements",
            [] {
              auto project = take(check(contracts + R"(
      type Nonempty<N:nat> where 1<=N=[bool;N];
      fn pass<N:nat,F:Field>(xs:Nonempty<N>,f:Special<F>)->([bool;N],F) {
        return(xs,f);
      }
    )"));
              const auto &pass = named(project, "m::pass");
              require(pass.bounds.size() == 1 && pass.bounds.front().inferred &&
                          pass.capabilityBounds.size() == 1 &&
                          pass.capabilityBounds.front().inferred,
                      "signature application requirements were not inferred");
              acceptsWitness(project);
            });
  cases.run("implemented domain signature keeps independently inferred Copy",
            [] { acceptsWitness(take(check(domainSignature))); });
  cases.run("body usage can strengthen an inferred signature leaf", [] {
    auto project = take(check(usageSignature));
    const auto &member = named(project, "m::A::duplicate");
    require(member.permissionBounds.size() == 1 &&
                member.permissionBounds.front().inferred &&
                member.permissionBounds.front().permissions.copy,
            "body did not strengthen signature Drop to Copy");
    acceptsWitness(project);
  });
  cases.run("body natural requirement follows the reconstructed interface", [] {
    auto project = take(check(R"(module m;
      interface I<N:nat>{fn first(xs:[bool;N])->bool effects() where 1<=N;}
      module A<N:nat>:I<N>{fn first(xs:[bool;N])->bool{return xs[0];}}
    )"));
    const auto &bounds = named(project, "m::A::first").bounds;
    require(bounds.size() == 1 && bounds.front().inferred,
            "body natural requirement was not inferred");
    acceptsWitness(project);
  });
  cases.run("body catalog requirement follows the reconstructed interface", [] {
    auto project = take(check(R"(module m;
      interface I<F:Field>{fn root(n:index)->F effects(stop,opaque)
        where zkc::algebra::TwoAdicField(F);}
      module A<F:Field>:I<F>{fn root(n:index)->F{
        return kernel<F>("poly.domain_root",n);
      }}
    )"));
    const auto &bounds = named(project, "m::A::root").capabilityBounds;
    require(bounds.size() == 1 && bounds.front().inferred,
            "body catalog requirement was not inferred");
    acceptsWitness(project);
  });
  cases.run("authored module premises remain available to implementations", [] {
    auto project = take(check(R"(module m;
      interface I<N:nat,T:Type,F:Field> {
        fn run(xs:[bool;N],x:T,n:index)->(bool,(T,T),F) effects(stop,opaque);
      }
      module A<N:nat,T:Type,F:Field>:I<N,T,F>
        where 1<=N,Copy(T),zkc::algebra::TwoAdicField(F) {
        fn run(xs:[bool;N],x:T,n:index)->(bool,(T,T),F) {
          return(xs[0],(x,x),kernel<F>("poly.domain_root",n));
        }
      }
    )"));
    acceptsWitness(project);
  });
  cases.run("omitted results follow checked bodies and interface promises", [] {
    auto project = take(check(inferredResults));
    for (StringRef name :
         {"m::A::flag", "m::A::pair", "m::A::unit", "m::A::root"}) {
      const auto &member = named(project, name);
      require(
          member.outputs.size() == 1 && member.body &&
              member.body->results.size() == 1 &&
              member.outputs.front().type ==
                  member.body->values[member.body->results.front().index].type,
          "omitted result did not come from its checked body");
    }
    const auto &bounds = named(project, "m::A::root").capabilityBounds;
    require(bounds.size() == 1 && bounds.front().inferred,
            "inferred result lost its body capability obligation");
    acceptsWitness(project);
  });
  for (StringRef mutation : {"scalar type", "tuple type", "unit type",
                             "catalog result type", "arity", "return selector"})
    cases.run("inferred result rejects candidate " + mutation, [&] {
      auto project = take(check(inferredResults));
      acceptsWitness(project);
      auto &flag = named(project, "m::A::flag");
      if (mutation == "scalar type")
        flag.outputs.front().type = Type(Type::Kind::Index);
      else if (mutation == "tuple type")
        named(project, "m::A::pair").outputs.front().type =
            Type(Type::Kind::Index);
      else if (mutation == "unit type")
        named(project, "m::A::unit").outputs.front().type =
            Type(Type::Kind::Boolean);
      else if (mutation == "catalog result type")
        named(project, "m::A::root").outputs.front().type =
            Type(Type::Kind::Boolean);
      else if (mutation == "arity")
        flag.outputs.clear();
      else {
        auto &pair = named(project, "m::A::pair");
        auto body = std::make_shared<Body>(*pair.body);
        require(body->inputs == 1 && body->results.front().index != 0,
                "return selector mutation would not change the result");
        body->results.front() = ValueId{0};
        pair.outputs.front().type = body->values.front().type;
        pair.body = std::move(body);
      }
      refusesWitness(project);
    });
  // Cover both potential premise providers and both member obligations. Each
  // mutation starts from a fresh accepted source and a passing witness.
  for (auto premise :
       {Premise::Natural, Premise::Permission, Premise::Capability})
    for (StringRef owners : {"module", "interface", "bilateral", "provided",
                             "required", "members"})
      cases.run("forged inferred " + name(premise) + " " + owners, [&] {
        auto project = take(check(contracts));
        acceptsWitness(project);
        auto forge = [&](StringRef path) {
          forgePremise(project, named(project, path), premise);
        };
        if (owners == "module" || owners == "bilateral") {
          forge("m::A");
          forge("m::A::choose");
        }
        if (owners == "interface" || owners == "bilateral") {
          forge("m::I");
          forge("m::I::choose");
        }
        if (owners == "provided" || owners == "members")
          forge("m::A::choose");
        if (owners == "required" || owners == "members")
          forge("m::I::choose");
        refusesWitness(project);
      });
  for (StringRef mutation : {"missing Copy", "weakened Copy", "origin flag"})
    cases.run("domain signature rejects " + mutation, [&] {
      auto project = take(check(domainSignature));
      acceptsWitness(project);
      auto &bounds = named(project, "m::A::accept").permissionBounds;
      require(bounds.size() == 1 && bounds.front().permissions.copy,
              "missing domain signature positive control");
      if (mutation == "missing Copy")
        bounds.clear();
      else if (mutation == "weakened Copy")
        bounds.front().permissions.copy = false;
      else
        bounds.front().inferred = false;
      refusesWitness(project);
    });
  for (auto premise : {Premise::Natural, Premise::Capability})
    for (StringRef mutation :
         {"missing", "changed", "origin flag", "authored origin flag"})
      cases.run("signature " + name(premise) + " rejects " + mutation, [&] {
        auto project = take(check(formationSignature));
        acceptsWitness(project);
        auto &provided = named(project, "m::A::pass");
        auto &required = named(project, "m::I::pass");
        require(provided.bounds.size() == 1 &&
                    provided.bounds.front().inferred &&
                    provided.capabilityBounds.size() == 1 &&
                    provided.capabilityBounds.front().inferred,
                "missing inferred signature positive control");
        if (premise == Premise::Natural) {
          if (mutation == "missing")
            provided.bounds.clear();
          else if (mutation == "changed")
            provided.bounds.front().lhs = Natural::constant(2);
          else if (mutation == "origin flag")
            provided.bounds.front().inferred = false;
          else
            required.bounds.front().inferred = true;
        } else {
          if (mutation == "missing")
            provided.capabilityBounds.clear();
          else if (mutation == "changed")
            provided.capabilityBounds.front().arguments.front() =
                Type(Type::Kind::Boolean);
          else if (mutation == "origin flag")
            provided.capabilityBounds.front().inferred = false;
          else
            required.capabilityBounds.front().inferred = true;
        }
        refusesWitness(project);
      });
  cases.run("explicit where forbids even redundant inferred body requirements",
            [] {
              auto project = take(check(R"(module m;
                interface I<N:nat>{math fn choose(x:bool)->bool;}
                module A<N:nat>:I<N>{
                  math fn choose(x:bool)->bool where (){return x;}
                }
              )"));
              acceptsWitness(project);
              auto &provided = named(project, "m::A::choose");
              provided.bounds.push_back(
                  {Natural::constant(0),
                   parameterType(provided.parameters.front()).dimension,
                   provided.span, true});
              refusesWitness(project);
            });
  cases.run("nested candidate permission caches cannot discharge obligations",
            [] {
              auto project = take(check(contracts));
              acceptsWitness(project);
              auto &provided = named(project, "m::A::choose");
              auto leaf = parameterType(provided.parameters[1]);
              leaf.assumptions = {true, true};
              Type product(Type::Kind::Tuple);
              product.arguments = {leaf};
              provided.permissionBounds.push_back(
                  {product, {true, true}, provided.span, true});
              refusesWitness(project);
            });
  for (StringRef owner : {"m::A", "m::I", "m::A::choose", "m::I::choose"})
    cases.run("inline permissions remain source exact for " + owner, [&] {
      auto project = take(check(contracts));
      acceptsWitness(project);
      named(project, owner).parameters[1].permissions = {true, true};
      refusesWitness(project);
    });
  cases.run("bilateral callback item selectors remain source exact", [] {
    auto project = take(check(R"(module m;
      interface I {
        fn run(rows:domain<bool>,other:domain<bool>,
          body:fn(item:bool)->bool where item_from(item,rows))
          ->bool effects(body);
      }
      module A:I {
        fn run(rows:domain<bool>,other:domain<bool>,
          body:fn(item:bool)->bool where item_from(item,rows))
          ->bool{return true;}
      }
    )"));
    acceptsWitness(project);
    for (StringRef owner : {"m::I::run", "m::A::run"}) {
      auto &origins = named(project, owner).scopedInputs.front().itemOrigins;
      require(origins.size() == 1 && origins.at(0) == 0,
              "missing authored item selector positive control");
      origins.at(0) = 1;
    }
    refusesWitness(project);
  });
  for (StringRef mutation :
       {"missing edge", "reordered edges", "foreign edge", "bilateral arity",
        "bilateral input order", "bilateral port type",
        "bilateral callback effects", "bilateral alias", "bilateral domain",
        "bilateral domain result"})
    cases.run("source edge and signature control: " + mutation, [&] {
      auto project = take(check(contracts));
      acceptsWitness(project);
      auto &module = named(project, "m::A");
      auto &required = named(project, "m::I::choose");
      auto &provided = named(project, "m::A::choose");
      if (mutation == "missing edge")
        module.conformance.clear();
      else if (mutation == "reordered edges")
        std::swap(module.conformance[0], module.conformance[1]);
      else if (mutation == "foreign edge")
        module.conformance[1].provided = named(project, "m::B::choose").id;
      else if (mutation == "bilateral arity") {
        required.inputs.pop_back();
        provided.inputs.pop_back();
      } else if (mutation == "bilateral port type") {
        required.outputs.front().type = Type(Type::Kind::Index);
        provided.outputs.front().type = Type(Type::Kind::Index);
      } else if (mutation == "bilateral input order") {
        required.inputOrder.front().index = 1;
        provided.inputOrder.front().index = 1;
      } else if (mutation == "bilateral callback effects") {
        for (StringRef owner : {"m::I::run", "m::A::run"}) {
          auto &allowance =
              named(project, owner).scopedInputs.front().signature.allowance;
          require(allowance.mayStop,
                  "callback effect mutation would not change the ceiling");
          allowance.mayStop = false;
        }
      } else if (mutation == "bilateral alias") {
        named(project, "m::Flag").domain = Type(Type::Kind::Index);
        for (StringRef owner :
             {"m::I::choose", "m::A::choose", "m::B::choose"}) {
          auto &member = named(project, owner);
          for (auto &input : member.inputs)
            input.type = Type(Type::Kind::Index);
          member.outputs.front().type = Type(Type::Kind::Index);
        }
      } else if (mutation == "bilateral domain") {
        named(project, "m::Fr").domain = named(project, "m::Fq").domain;
        named(project, "m::A::Scalar").domain = named(project, "m::Fq").domain;
      } else {
        named(project, "m::I::rows").descriptorResult = DescriptorContract{
            DescriptorFamily::Finite, {Type(Type::Kind::Boolean)}};
        named(project, "m::A::rows").descriptorResult = DescriptorContract{
            DescriptorFamily::Finite, {Type(Type::Kind::Boolean)}};
      }
      refusesWitness(project);
    });
  return cases.result();
}
