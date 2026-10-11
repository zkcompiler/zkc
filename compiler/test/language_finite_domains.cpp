#include "../lib/Language/BodySummary.h"
#include "../lib/Language/ClosureInputs.h"
#include "../lib/Language/DomainClosure.h"
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
        require(paired.bindings.size() == 3 && paired.applications.size() == 3,
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
                body.domainApplications.size() == 1,
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
  return cases.result();
}
