#include "../lib/Language/BodyMapping.h"
#include "../lib/Language/BodySummary.h"
#include "../lib/Language/ClosureInputs.h"
#include "../lib/Language/DomainClosure.h"
#include "../lib/Language/DomainWitness.h"
#include "support/NativeCases.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/Project.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
const std::string prelude = R"(module m;
type Vector<F:Field>=builtin("vector",F);
type Groups<G:Group>=builtin("groups",G);
type Matrix<F:Field>=builtin("matrix",F);
type Sequence<T:Type+Copy+Drop>=builtin("sequence",T);
pub domain fn elements<F:Field>(xs:Vector<F>)->scoped domain<F>=domain("elements");
pub domain fn groups<G:Group>(xs:Groups<G>)->scoped domain<G>=domain("elements");
pub domain fn indices<F:Field>(xs:Vector<F>)->scoped domain<index>=domain("indices");
pub domain fn range(lo:index,hi:index)->scoped domain<index>=domain("range");
pub domain fn zip<A:Type+Copy+Drop,B:Type+Copy+Drop>(a:scoped domain<A>,b:scoped domain<B>)->scoped domain<(A,B)>=domain("zip");
)";
Expected<CheckedProject> check(StringRef source) {
  auto captured = capture({{"m", prelude + source.str(), "domains.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
const Declaration &declarationNamed(const CheckedProject &project,
                                    StringRef name) {
  for (const auto &decl : project.declarations())
    if (decl.qualifiedName == name)
      return decl;
  throw std::runtime_error("missing declaration");
}
} // namespace
int main() {
  Cases cases;
  cases.run("domain constructors retain a separate static signature", [] {
    auto project = take(check(""));
    const auto &zip = declarationNamed(project, "m::zip");
    require(zip.inputs.empty() && zip.outputs.empty() &&
                zip.domainInputs.size() == 2 && zip.domainResult &&
                zip.domainDefinition && !zip.body,
            "domain signature became a runtime callable");
    const auto &result =
        zip.domainDefinition->bindings[zip.domainDefinition->result];
    require(result.kind == DomainBinding::Kind::Zip &&
                result.children == std::vector<unsigned>({0, 1}),
            "domain order was lost");
    require(take(inspectDeclarations(project)).find("domain_inputs") !=
                std::string::npos,
            "inspection omitted static domains");
  });
  cases.run(
      "mixed group field factory composition and immutable forwarding", [] {
        auto project = take(check(R"(
pub domain fn paired<G:Group>(points:Groups<G>,scalars:Vector<G::Scalar>)->scoped domain<(G,G::Scalar)>{
 let ps=groups(points);let ss=elements(scalars);return zip(ps,ss);
}
pub domain fn forward<T:Type+Copy+Drop>(rows:scoped domain<T>)->scoped domain<T>{return rows;}
)"));
        const auto &paired =
            *declarationNamed(project, "m::paired").domainDefinition;
        require(paired.bindings.size() == 3 && paired.bindings[0].expression &&
                    paired.bindings[1].expression &&
                    paired.bindings[2].expression,
                "composition lost typed constructor applications");
        require(paired.bindings[0].operands[0].index == 0 &&
                    paired.bindings[1].operands[0].index == 1 &&
                    paired.bindings[2].children ==
                        std::vector<unsigned>({0, 1}),
                "composition changed source operand identities");
        require(declarationNamed(project, "m::forward")
                        .domainDefinition->bindings[0]
                        .parameter == 0,
                "forwarding lost the domain parameter");
      });
  cases.run("matrix coordinates source arrays and record sequences", [] {
    take(check(R"(
domain fn row<F:Field>(xs:Matrix<F>,i:index)->scoped domain<F>=domain("matrix.row");
domain fn column<F:Field>(xs:Matrix<F>,i:index)->scoped domain<F>=domain("matrix.column");
domain fn coordinates<F:Field>(xs:Matrix<F>)->scoped domain<(index,index)>=domain("matrix.coordinates.column_major");
domain fn array<T:Type+Copy+Drop,N:nat>(xs:[T;N])->scoped domain<T>=domain("source_array");
struct Row{pub value:index,pub valid:bool}
domain fn rows(xs:Sequence<Row>)->scoped domain<Row>=domain("elements");
)"));
  });
  cases.run("component factory conformance", [] {
    take(check(R"(
interface Domain<F:Field>{domain fn rows(xs:Vector<F>)->scoped domain<F>;}
component All<F:Field>:Domain<F>{domain fn rows(xs:Vector<F>)->scoped domain<F>=domain("elements");}
)"));
  });
  cases.run("ordinary helpers retain domain aliases and forwarding", [] {
    auto project = take(check(R"(
fn ignore<T:Type+Copy+Drop>(rows:scoped domain<T>,fallback:T)->T{return fallback;}
fn forward<T:Type+Copy+Drop>(rows:scoped domain<T>,fallback:T)->T{return ignore(rows,fallback);}
fn example<F:Field>(xs:Vector<F>,fallback:F)->F {
 let rows=elements(xs); let alias=rows;
 return forward(fallback=fallback,rows=alias);
}
)"));
    const auto &body = *declarationNamed(project, "m::example").body;
    require(body.domainBindings.size() == 1 &&
                body.domainBindings.front().expression.has_value(),
            "domain aliases copied or erased their recipe");
    const auto &call = std::get<HelperCall>(body.operations.back().action);
    require(call.domainArguments == std::vector<unsigned>{0},
            "domain call lost recipe identity");
  });
  cases.run("abstract component factory survives typed composition", [] {
    auto project = take(check(R"(
interface Domain<F:Field>{domain fn rows(xs:Vector<F>)->scoped domain<F>;}
domain fn selected<F:Field,C:Domain<F>>(xs:Vector<F>)->scoped domain<(F,F)> {
 let rows=C::rows(xs); return zip(rows,rows);
}
)"));
    const auto &definition =
        *declarationNamed(project, "m::selected").domainDefinition;
    require(definition.bindings[0].kind == DomainBinding::Kind::Application &&
                definition.bindings[0].factory->component.has_value(),
            "abstract factory selection was not retained");
  });
  cases.run("closure preserves factory admission and operand identity", [] {
    auto project = take(check(R"(
domain Fr=field("koala-bear");
domain fn checked<F:Field>(a:Vector<F>,b:Vector<F>)->scoped domain<F> {
 let left=elements(a); let right=elements(b); let unused=zip(left,right); return left;
}
fn example(a:Vector<Fr>,b:Vector<Fr>)->bool {
 let unrelated=zip(elements(a),elements(b));
 let selected=checked(a,b); let shared=checked(a,a);
 return true;
}
)"));
    const auto &body = *declarationNamed(project, "m::example").body;
    std::vector<Declaration> declarations(project.declarations().begin(),
                                          project.declarations().end());
    zkc::language::detail::Work work{Limits{}};
    zkc::language::detail::Semantics types(declarations, project.assets(),
                                           work);
    auto selected = zkc::language::detail::closeDomain(types, declarations,
                                                       body, 3, {}, {});
    require(selected.has_value(),
            types.diagnostic ? types.diagnostic->message : "closure failed");
    require(selected->shape->nodes.size() == 3 &&
                selected->shape->result == 0 &&
                selected->shape->nodes.back().kind == DomainBinding::Kind::Zip,
            "factory admission lost unused zip or included unrelated caller "
            "domain");
    require(selected->shape->inputs.size() == 2,
            "distinct containers became identical");
    auto shared = zkc::language::detail::closeDomain(types, declarations, body,
                                                     4, {}, {});
    require(shared.has_value() && shared->shape->inputs.size() == 1,
            "aliases of one immutable operand were not preserved");
    require(selected->shape->identity != shared->shape->identity,
            "specialization identity erased alias relationships");
  });
  cases.run("closed abstract factory selects component recipe", [] {
    auto project = take(check(R"(
domain Fr=field("koala-bear");
interface Domain<F:Field>{domain fn rows(xs:Vector<F>)->scoped domain<F>;}
component All<F:Field>:Domain<F>{domain fn rows(xs:Vector<F>)->scoped domain<F>=domain("elements");}
domain fn selected<F:Field,C:Domain<F>>(xs:Vector<F>)->scoped domain<F>{return C::rows(xs);}
fn example(xs:Vector<Fr>)->bool {let rows=selected<Fr,All<Fr>>(xs);return true;}
)"));
    const auto &body = *declarationNamed(project, "m::example").body;
    std::vector<Declaration> declarations(project.declarations().begin(),
                                          project.declarations().end());
    zkc::language::detail::Work work{Limits{}};
    zkc::language::detail::Semantics types(declarations, project.assets(),
                                           work);
    auto selected = zkc::language::detail::closeDomain(types, declarations,
                                                       body, 0, {}, {});
    require(selected.has_value(),
            types.diagnostic ? types.diagnostic->message : "closure failed");
    require(selected->shape->nodes.size() == 1 &&
                selected->shape->nodes[0].kind == DomainBinding::Kind::Elements,
            "component factory did not close to its selected constructor");
  });
  cases.run("named factory arguments preserve child admission order", [] {
    auto project = take(check(R"(
fn example(a:index,b:index,c:index,d:index)->bool {
 let rows=zip(b=range(c,d),a=range(a,b)); return true;
}
)"));
    const auto &body = *declarationNamed(project, "m::example").body;
    std::vector<Declaration> declarations(project.declarations().begin(),
                                          project.declarations().end());
    zkc::language::detail::Work work{Limits{}};
    zkc::language::detail::Semantics types(declarations, project.assets(),
                                           work);
    auto selected = zkc::language::detail::closeDomain(types, declarations,
                                                       body, 2, {}, {});
    require(selected.has_value(),
            types.diagnostic ? types.diagnostic->message : "closure failed");
    require(
        selected->operands[0].index == 2 && selected->operands[1].index == 3 &&
            selected->shape->nodes[2].children == std::vector<unsigned>({1, 0}),
        "named mapping reordered constructor admission or item positions");
  });
  cases.run("scoped and control regions capture static domains", [] {
    auto project = take(check(R"(
fn ignore<T:Type+Copy+Drop>(rows:scoped domain<T>,fallback:T)->T{return fallback;}
fn apply<T:Type+Copy+Drop>(x:T,body:scoped fn(T)->T !{stop})->T !{stop}{return body(x);}
fn example<F:Field>(xs:Vector<F>,x:F,choose:bool)->F {
 let rows=elements(xs);
 return apply(x,fun y=>if choose {ignore(rows,y)} else {y});
}
)"));
    const auto &body = *declarationNamed(project, "m::example").body;
    const auto &binding = body.scopedBindings.front();
    require(binding.domainCaptures == std::vector<unsigned>{0} &&
                binding.computation->domainCaptures.size() == 1,
            "callback lost captured domain identity");
    require(binding.computation->body->domainBindings.front().parameter == 0,
            "captured domain became a data parameter");
  });
  cases.run(
      "domain dependencies survive generic helper and callback forwarding", [] {
        auto project = take(check(R"(
interface Inspect<F:Field>{math fn inspect(rows:scoped domain<F>,fallback:F)->F;}
math fn inner<F:Field,C:Inspect<F>>(rows:scoped domain<F>,fallback:F)->F {
 return C::inspect(rows,fallback);
}
math fn outer<F:Field,C:Inspect<F>>(rows:scoped domain<F>,fallback:F)->F {
 return inner<F,C>(rows,fallback);
}
math fn apply<F:Field>(x:F,body:scoped math fn(F)->F !{})->F{return body(x);}
math fn captured<F:Field,C:Inspect<F>>(rows:scoped domain<F>,fallback:F)->F {
 return apply(fallback,fun x=>inner<F,C>(rows,x));
}
)"));
        std::vector<Declaration> declarations(project.declarations().begin(),
                                              project.declarations().end());
        zkc::language::detail::Work work{Limits{}};
        zkc::language::detail::Semantics types(declarations, project.assets(),
                                               work);
        for (auto name : {"m::outer", "m::captured"}) {
          const auto &body = *declarationNamed(project, name).body;
          require(body.parameterizedSummary,
                  "unknown domain was cached as a constant dependency");
          auto summary = zkc::language::detail::summarizeBody(
              types, declarations, body, {}, {{{7}, false}}, {}, 1,
              {{{3}, false}});
          require(summary.has_value(), types.diagnostic
                                           ? types.diagnostic->message
                                           : "missing summary");
          require(
              summary->results.front().inputs == std::vector<unsigned>({3, 7}),
              "domain operand dependency was lost through generic forwarding");
          require(summary->parameterized,
                  "abstract domain consumer appeared concrete");
        }
      });
  cases.run(
      "closure input layout preserves aliases without merging distinct "
      "containers",
      [] {
        auto project = take(check(R"(
domain Fr=field("koala-bear");
struct Pair{pub left:Vector<Fr>,pub right:Vector<Fr>}
fn example(xs:Pair,other:Vector<Fr>)->(Vector<Fr>,Vector<Fr>,Vector<Fr>){
 return (xs.left,xs.left,xs.right);
}
)"));
        auto body = *declarationNamed(project, "m::example").body;
        std::vector<ValueId> projected;
        for (const auto &op : body.operations)
          if (std::holds_alternative<Projection>(op.action))
            projected.push_back(op.results.front());
        if (projected.size() == 2) {
          auto duplicate = body.operations.front();
          ValueId fresh{uint32_t(body.values.size())};
          body.values.push_back(body.values[projected.front().index]);
          duplicate.results = {fresh};
          body.operations.push_back(std::move(duplicate));
          projected.insert(projected.begin() + 1, fresh);
        }
        require(projected.size() == 3, "missing authored projections");
        std::vector<Declaration> declarations(project.declarations().begin(),
                                              project.declarations().end());
        zkc::language::detail::Work work{Limits{}};
        zkc::language::detail::Semantics types(declarations, project.assets(),
                                               work);
        auto result = zkc::language::detail::closeInputs(
            types, body, {projected[0], projected[1], ValueId{1}},
            {projected[1], projected[2], ValueId{1}, projected[2]}, {});
        require(result.has_value(), types.diagnostic ? types.diagnostic->message
                                                     : "missing layout");
        require(result->layout.inputs == std::vector<unsigned>({0, 0, 2}) &&
                    result->layout.captures ==
                        std::vector<unsigned>({0, 3, 2, 3}) &&
                    result->operands.size() == 4,
                "joint layout lost a projection alias or merged distinct "
                "containers");
        auto callback = zkc::language::detail::closeInputs(
            types, body, {std::nullopt, projected[0]},
            {projected[1], projected[2]}, {});
        require(callback &&
                    callback->layout.inputs == std::vector<unsigned>({0, 1}) &&
                    callback->layout.captures == std::vector<unsigned>({1, 2}),
                "unknown callback parameter interfered with capture identity");
        Body corrupt = body;
        auto &projection =
            std::get<Projection>(corrupt.operations.front().action);
        projection.input = corrupt.operations.front().results.front();
        zkc::language::detail::ValueOrigins origins(types, corrupt);
        require(!origins.get(projection.input),
                "cyclic projection origin was accepted");
      });
  cases.run(
      "shared factory expansion stays bounded across forty forwarding levels",
      [] {
        std::string source = "domain fn layer0(a:index,b:index)->scoped "
                             "domain<index>{return range(a,b);}";
        for (unsigned i = 1; i <= 40; ++i) {
          auto previous = "layer" + std::to_string(i - 1);
          source +=
              "domain fn layer" + std::to_string(i) +
              "(a:index,b:index)->scoped domain<index>{let unused=" + previous +
              "(a,b);return " + previous + "(a,b);}";
        }
        source += "fn example(a:index,b:index)->index{let "
                  "rows=layer40(a,b);return a;}";
        auto project = take(check(source));
        const auto &body = *declarationNamed(project, "m::example").body;
        std::vector<Declaration> declarations(project.declarations().begin(),
                                              project.declarations().end());
        zkc::language::detail::Work work{Limits{}};
        zkc::language::detail::Semantics types(declarations, project.assets(),
                                               work);
        auto result = zkc::language::detail::closeDomain(types, declarations,
                                                         body, 0, {}, {});
        require(result.has_value(), types.diagnostic ? types.diagnostic->message
                                                     : "missing closed domain");
        require(result->shape->nodes.size() == 1 &&
                    result->shape->inputs.size() == 2,
                "shared factory graph expanded repeated selected recipes");
        require(zkc::language::detail::checkDomainClosure(
                    types, declarations, body, 0, {}, {}, *result),
                types.diagnostic ? types.diagnostic->message
                                 : "shared factory witness failed");
      });
  cases.run(
      "inherited domain inputs and descriptor size are checked at closure", [] {
        auto project = take(check("fn forward(a:index,b:index,rows:scoped "
                                  "domain<index>)->index{return a;}"));
        const auto &body = *declarationNamed(project, "m::forward").body;
        std::vector<Declaration> declarations(project.declarations().begin(),
                                              project.declarations().end());
        for (unsigned mutation = 0; mutation < 3; ++mutation) {
          auto shape = std::make_shared<DomainShape>();
          shape->inputs = {Type(Type::Kind::Index), Type(Type::Kind::Index)};
          shape->nodes.push_back({DomainBinding::Kind::Range,
                                  Type(Type::Kind::Index),
                                  {{0}, {1}},
                                  {}});
          shape->result = 0;
          if (mutation == 1)
            shape->inputs.front() = Type{};
          if (mutation == 2)
            shape->nodes.resize(4096, shape->nodes.front());
          zkc::language::detail::Work work{Limits{}};
          zkc::language::detail::Semantics types(declarations, project.assets(),
                                                 work);
          auto result = zkc::language::detail::closeDomain(
              types, declarations, body, 0, {}, {{shape, {{0}, {1}}}});
          if (mutation == 0)
            require(result.has_value(), types.diagnostic
                                            ? types.diagnostic->message
                                            : "valid inherited shape refused");
          else {
            require(!result && types.diagnostic,
                    "invalid inherited descriptor accepted");
            require(
                types.diagnostic->code ==
                    (mutation == 1 ? "source.finite-domain" : "source.limit"),
                "wrong inherited descriptor refusal");
          }
        }
      });
  cases.run(
      "domain call occurrence identity is checked independently of its span",
      [] {
        auto project = take(check(R"(
fn ignore(rows:scoped domain<index>,fallback:index)->index{return fallback;}
fn example(a:index,b:index)->index{return ignore(range(a,b),a);}
)"));
        auto &decl =
            const_cast<Declaration &>(declarationNamed(project, "m::example"));
        auto body = std::make_shared<Body>(*decl.body);
        decl.body = body;
        ++*body->domainBindings.front().expression;
        auto error = checkScopedElaboration(project);
        require(bool(error), "changed domain expression identity was accepted");
        require(toString(std::move(error)).find("source.scoped-witness") !=
                    std::string::npos,
                "wrong source occurrence refusal");
      });
  cases.run(
      "descriptor witness checks admission and operand mappings without its "
      "key",
      [] {
        auto project = take(check(R"(
domain fn prepared(a:index,b:index,c:index,d:index)->scoped domain<index>{
 let checked=zip(range(a,b),range(c,d));return range(a,b);
}
fn example(a:index,b:index,c:index,d:index)->index{let rows=prepared(a,b,c,d);return a;}
)"));
        const auto &body = *declarationNamed(project, "m::example").body;
        std::vector<Declaration> declarations(project.declarations().begin(),
                                              project.declarations().end());
        zkc::language::detail::Work work{Limits{}};
        zkc::language::detail::Semantics types(declarations, project.assets(),
                                               work);
        auto original = zkc::language::detail::closeDomain(types, declarations,
                                                           body, 0, {}, {});
        require(original.has_value(), types.diagnostic
                                          ? types.diagnostic->message
                                          : "closure failed");
        require(original->shape->nodes.size() == 3 &&
                    original->shape->result == 0,
                "missing retained check-only zip");
        Body caller = body;
        caller.values.insert(caller.values.begin(), body.values.front());
        ++caller.inputs;
        auto shifted = [](ValueId value) { return ValueId{value.index + 1}; };
        zkc::language::detail::mapBodyValues(caller, shifted);
        auto inputs = zkc::language::detail::bindDomainInputs(
            types, declarations, body, caller, shifted, 0, {}, {},
            *original->shape);
        require(inputs && inputs->size() == original->operands.size(),
                "mapped descriptor witness failed");
        for (unsigned i = 0; i < inputs->size(); ++i)
          require((*inputs)[i].index == original->operands[i].index + 1,
                  "domain witness confused template and caller SSA spaces");
        for (unsigned mutation = 0; mutation < 9; ++mutation) {
          auto candidate = *original;
          auto shape = std::make_shared<DomainShape>(*candidate.shape);
          candidate.shape = shape;
          shape->identity = "untrusted producer key";
          if (mutation == 1)
            shape->nodes.pop_back();
          if (mutation == 2)
            std::swap(shape->nodes[0], shape->nodes[1]);
          if (mutation == 3)
            std::swap(candidate.operands[0], candidate.operands[2]);
          if (mutation == 4)
            std::swap(shape->nodes[0].operands[0], shape->nodes[0].operands[1]);
          if (mutation == 5)
            shape->result = 1;
          if (mutation == 6)
            shape->nodes.push_back(shape->nodes.front());
          if (mutation == 7)
            shape->inputs.front() = Type{};
          if (mutation == 8)
            shape->nodes.front().expression = 7;
          zkc::language::detail::Work witnessWork{Limits{}};
          zkc::language::detail::Semantics witness(
              declarations, project.assets(), witnessWork);
          bool valid = zkc::language::detail::checkDomainClosure(
              witness, declarations, body, 0, {}, {}, candidate);
          if (mutation == 0)
            require(valid, witness.diagnostic ? witness.diagnostic->message
                                              : "valid descriptor refused");
          else
            require(!valid && witness.diagnostic &&
                        witness.diagnostic->code == "source.domain-witness",
                    "corrupt descriptor accepted or refused for the wrong "
                    "reason: " +
                        std::to_string(mutation));
        }
      });
  const std::vector<std::pair<std::string, std::string>> invalid = {
      {R"(domain fn bad(x:index)->scoped domain<index>=domain("unknown");)",
       "source.finite-domain"},
      {R"(domain fn bad(x:index)->scoped domain<index>=domain("elements");)",
       "source.finite-domain"},
      {R"(domain fn bad(a:index,b:bool)->scoped domain<index>=domain("range");)",
       "source.finite-domain"},
      {R"(domain fn bad<F:Field>(xs:Vector<F>)->scoped domain<index>=domain("indices.columns");)",
       "source.finite-domain"},
      {R"(domain fn bad<A:Type+Copy+Drop,B:Type+Copy+Drop>(a:scoped domain<A>,b:scoped domain<B>)->scoped domain<(B,A)>=domain("zip");)",
       "source.finite-domain"},
      {R"(domain fn bad<T:Type>(a:scoped domain<T>)->scoped domain<T>{return a;})",
       "source.finite-domain"},
      {R"(domain fn bad(lo:index,hi:index)->scoped domain<index>{let mut rows=range(lo,hi);return rows;})",
       "source.finite-domain"},
      {R"(domain fn bad(lo:index,hi:index)->scoped domain<index>{return bad(lo,hi);})",
       "source.cycle"},
      {R"(protocol Bad roles(P)(rows:scoped domain<index>@P)->(){return();})",
       "source.scoped"},
      {R"(interface Bad{fn work(rows:scoped domain<index>,body:scoped fn(bool)->bool !{} on(rows))->bool;})",
       "source.finite-domain"},
  };
  for (unsigned i = 0; i < invalid.size(); ++i)
    cases.run("refuse invalid finite domain " + std::to_string(i), [&, i] {
      auto result = check(invalid[i].first);
      require(!result, "invalid domain accepted");
      require(toString(result.takeError()).find(invalid[i].second) !=
                  std::string::npos,
              "wrong domain refusal diagnostic");
    });
  cases.run("domains close through ordinary generic helper forwarding", [] {
    auto project = take(check(R"(
domain Fr=field("koala-bear");
fn ignore<T:Type+Copy+Drop>(rows:scoped domain<T>,fallback:T)->T{return fallback;}
fn forward<T:Type+Copy+Drop>(rows:scoped domain<T>,fallback:T)->T{return ignore(rows,fallback);}
protocol Demo roles(P)(xs:Vector<Fr>@P,fallback:Fr@P)->(r:Fr@P){return forward(elements(xs),fallback);}run Run=Demo;
)"));
    auto closed = take(closeEntry(project, "m::Run"));
    unsigned forwarded = 0;
    for (const auto &decl : closed.declarations())
      if (decl.body) {
        require(decl.domainInputs.empty() && decl.body->domainBindings.empty(),
                "static domain survived in runtime signature");
        if (decl.name == "forward" || decl.name == "ignore") {
          require(decl.domainArguments.size() == 1 && decl.inputs.size() == 2 &&
                      decl.closureLayout.captures == std::vector<unsigned>{1},
                  "domain operand did not become an explicit helper input");
          ++forwarded;
        }
      }
    require(forwarded == 2, "forwarding helper missing");
  });
  cases.run("domain and callback captures share authored SSA identities", [] {
    auto project = take(check(R"(
domain Fr=field("koala-bear");
fn observe(rows:scoped domain<index>,xs:Vector<Fr>,body:scoped fn(Vector<Fr>)->Vector<Fr> !{})->Vector<Fr>{return body(xs);}
protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Vector<Fr>@P){return observe(indices(xs),xs,fun _=>xs);}run Run=Demo;
)"));
    auto closed = take(closeEntry(project, "m::Run"));
    bool found = false;
    for (const auto &decl : closed.declarations())
      if (decl.body && decl.name == "observe") {
        require(decl.inputs.size() == 1 && decl.closureLayout.captures ==
                                               std::vector<unsigned>({0, 0}),
                "domain and callback capture received independent ports");
        found = true;
      }
    require(found, "missing joint helper");
  });
  cases.run("callbacks capture domains and retain ordinary forwarding", [] {
    auto project = take(check(R"(
domain Fr=field("koala-bear");
fn ignore<T:Type+Copy+Drop>(rows:scoped domain<T>,fallback:T)->T{return fallback;}
fn apply(x:Fr,body:scoped fn(Fr)->Fr !{})->Fr{return body(x);}
fn outer(xs:Vector<Fr>,x:Fr)->Fr{let rows=elements(xs);return apply(x,fun y=>ignore(rows,y));}
protocol Demo roles(P)(xs:Vector<Fr>@P,x:Fr@P)->(r:Fr@P){return outer(xs,x);}run Run=Demo;
)"));
    auto closed = take(closeEntry(project, "m::Run"));
    bool found = false;
    for (const auto &decl : closed.declarations())
      if (decl.body && decl.scopedOrigin) {
        require(decl.domainArguments.size() == 1 && decl.inputs.size() == 2,
                "callback lost static captured domain");
        found = true;
      }
    require(found, "missing callback");
  });
  cases.run("closed domains survive local conditional and loop regions", [] {
    auto project = take(check(R"(
domain Fr=field("koala-bear");
fn ignore(rows:scoped domain<Fr>,fallback:Fr)->Fr{return fallback;}
fn outer(xs:Vector<Fr>,x:Fr,n:index,flag:bool)->Fr{
 let rows=elements(xs);let mut result=x;
 for i in 0..n { result=if flag {ignore(rows,result)} else {result}; }
 return result;
}
protocol Demo roles(P)(xs:Vector<Fr>@P,x:Fr@P,n:index@P,flag:bool@P)->(r:Fr@P){return outer(xs,x,n,flag);}run Run=Demo;
)"));
    take(closeEntry(project, "m::Run"));
  });
  for (unsigned mutation = 0; mutation < 3; ++mutation)
    cases.run("closed domain edge mutation " + std::to_string(mutation), [&] {
      auto project = take(check(R"(
domain Fr=field("koala-bear");
fn ignore(rows:scoped domain<index>,fallback:Fr)->Fr{return fallback;}
protocol Demo roles(P)(a:index@P,b:index@P,x:Fr@P)->(r:Fr@P){return ignore(range(a,b),x);}run Run=Demo;
)"));
      auto closed = take(closeEntry(project, "m::Run"));
      for (const auto &decl : closed.declarations())
        if (decl.body && decl.name == "ignore") {
          auto &candidate = const_cast<Declaration &>(decl);
          if (mutation == 2)
            candidate.closureLayout.captures[1] =
                candidate.closureLayout.captures[0];
          else {
            auto shape = std::make_shared<DomainShape>(
                *candidate.domainArguments.front());
            candidate.domainArguments.front() = shape;
            if (mutation == 0)
              std::swap(shape->nodes.back().operands[0],
                        shape->nodes.back().operands[1]);
            else
              shape->nodes.clear();
          }
        }
      auto error = checkScopedSpecialization(closed);
      require(bool(error), "forged domain specialization accepted");
      auto message = toString(std::move(error));
      require(message.find("source.domain-witness") != std::string::npos ||
                  message.find("source.closure-inputs") != std::string::npos ||
                  message.find("source.scoped-specialization") !=
                      std::string::npos,
              "wrong domain specialization refusal");
    });
  cases.run(
      "protocol repetition captures recipe operands at their participants", [] {
        auto project = take(check(R"(
domain Fr=field("koala-bear");
fn ignore(rows:scoped domain<Fr>,fallback:Fr)->Fr{return fallback;}
protocol Demo roles(P,V)(xs:Vector<Fr>@P,x:Fr@P,n:index@(P,V))->(r:Fr@P){
 let rows=elements(xs);let mut result@P=x;
 for _ in 0..n roles(P,V) max 4 {
   for _ in 0..n roles(P,V) max 4 {result=ignore(rows,result+x);}
 }
 return result;
}run Run=Demo;
)"));
        take(closeEntry(project, "m::Run"));
      });
  cases.run("domain capture cannot introduce an absent protocol participant",
            [] {
              refuses(check(R"(
domain Fr=field("koala-bear");
fn ignore(rows:scoped domain<Fr>,fallback:Fr)->Fr{return fallback;}
protocol Demo roles(P,V)(xs:Vector<Fr>@V,x:Fr@P,n:index@P)->(r:Fr@P){
 let rows=elements(xs);let mut result@P=x;
 for _ in 0..n roles(P) max 4 {result=ignore(rows,result);}
 return result;
}run Run=Demo;
)"),
                      "source.roles");
            });
  cases.run("domain operand availability participates in nested call placement",
            [] {
              refuses(check(R"(
domain Fr=field("koala-bear");
fn ignore(rows:scoped domain<Fr>,fallback:Fr)->Fr{return fallback;}
protocol Demo roles(P,V)(xs:Vector<Fr>@V,x:Fr@P,n:index@(P,V))->(r:Fr@P){
 let rows=elements(xs);let mut result@P=x;
 for _ in 0..n roles(P,V) max 4 {result=ignore(rows,result);}
 return result;
}run Run=Demo;
)"),
                      "source.roles");
            });
  return cases.result();
}
