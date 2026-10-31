#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Language/Diagnostics.h"
#include "zkc/Language/Inspection.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
using namespace zkc::language;
using zkc::test::require;
using zkc::test::take;
namespace {
const char *prefix = R"(
module m;
domain F=field("bls12-381.fr");
type Fixed<T:Type+Copy+Drop,N:nat>=builtin("oracle.table",T,N);
type Table<T:Type+Copy+Drop>=builtin("oracle.table",T);
type Oracle<K:OracleKind>=builtin("oracle",K);
type Vec=builtin("vector",F);
type O=Oracle<Fixed<F,16>>;
type I=Oracle<Fixed<index,16>>;
math fn same(a:index,b:index)->bool{return intrinsic("index.equal",a,b);}
)";
Expected<CheckedProject> check(StringRef text) {
  auto captured =
      capture({{"m", std::string(prefix) + text.str(), "virtual-oracles.zkc"}});
  if (!captured)
    return captured.takeError();
  auto analysis = analyze(*captured);
  auto project = analysis.checkedProject();
  if (!project) {
    consumeError(project.takeError());
    return createStringError(
        inconvertibleErrorCode(),
        formatDiagnostics(analysis.diagnostics(), analysis.sources()));
  }
  return project;
}
Expected<CheckedProject> checkLayout(StringRef text) {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto captured =
      capture({{"m", text.str(), "virtual-oracles.layout.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  auto analysis = analyze(*captured);
  auto project = analysis.checkedProject();
  if (!project) {
    consumeError(project.takeError());
    return createStringError(
        inconvertibleErrorCode(),
        formatDiagnostics(analysis.diagnostics(), analysis.sources()));
  }
  return project;
}
const Declaration &declarationNamed(ArrayRef<Declaration> declarations,
                                    StringRef name) {
  auto at = llvm::find_if(declarations, [&](const Declaration &decl) {
    return decl.qualifiedName == name && !decl.origin;
  });
  require(at != declarations.end(), "missing authored declaration: " + name);
  return *at;
}
void refusesDefinition(StringRef text) {
  auto project = check(text);
  require(!project, "invalid oracle definition was accepted");
  auto message = toString(project.takeError());
  require(StringRef(message).contains("source."), "missing source diagnostic");
}
const char *identitySource = R"(
oracle def Identity(source:O)->O {
  query(position:index) {
    let alias=source;
    let unused <- oracle.query(alias,position);
    let answer <- query source at position;
    return answer;
  }
}
)";
const char *bounded = R"(
#[shape(source.rows,bound=Max)]
#[shape(result.rows,value=rows,bound=Max)]
pub oracle def Bounded<T:Field,Max:nat>(source:Oracle<Table<T>>,rows:index)
    ->Oracle<Table<T>> {
  requires exact: same(oracle.rows(source),rows);
  requires data: same(intrinsic<T>("vector.length",oracle.data(source)),rows);
  requires true;
  query(position:index) {
    let answer <- oracle.query(source,position);
    return answer;
  }
}
)";
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run("retained role assembly keeps independently owned components", [] {
    auto project = take(check(R"(
protocol Assemble roles(P,V)(p:index @P,v:index @V)->(result:index @(P,V)) {
  let value = @(P = p, V = v);
  return value;
}
)"));
    const auto &body =
        *declarationNamed(project.declarations(), "m::Assemble").body;
    require(llvm::any_of(body.operations,
                         [](const Operation &operation) {
                           return std::holds_alternative<RoleAssembly>(
                               operation.action);
                         }),
            "role assembly was not retained");
    refusesDefinition(R"(
protocol Assemble roles(P,V)(p:index @P,v:index @V)->(result:index @(P,V)) {
  let value = @(P = p, P = v);
  return value;
}
)");
  });
  cases.run("three signatures, direct aliases and every query occurrence", [] {
    auto project = take(check(identitySource));
    const auto &decl = declarationNamed(project.declarations(), "m::Identity");
    require(decl.kind == Declaration::Kind::Oracle && decl.oracleDefinition &&
                decl.inputs.size() == 1 && decl.outputs.size() == 1,
            "constructor signature was replaced by its query signature");
    const auto &definition = *decl.oracleDefinition;
    const auto &body = *decl.body;
    require(body.mode == Body::Mode::Oracle && body.inputs == 2 &&
                body.values[1].type == definition.queryParameter.type &&
                body.values[body.results.front().index].type ==
                    definition.answer,
            "query ABI differs");
    unsigned queries = 0;
    for (const auto &operation : body.operations)
      if (const auto *query =
              std::get_if<OracleSourceQuery>(&operation.action)) {
        require(query->source == 0 && operation.site &&
                    !body.values[operation.results.front().index].oracleHolder,
                "query source or role-free occurrence was lost");
        ++queries;
      }
    require(queries == 2, "unused or repeated source query was dropped");
    const auto &predicate =
        project.declarations()[definition.admissibility.index];
    require(predicate.oraclePredicateOwner && predicate.relation &&
                predicate.relation->kind == RelationDefinition::Kind::Formula &&
                predicate.inputs.size() == 1 &&
                predicate.inputs.front().type.domain == "vector" &&
                predicate.outputs.front().type == Type{} &&
                definition.predicates.empty() && predicate.body,
            "empty conjunction or predicate Data ABI was lost");
    require(
        predicate.body->values[predicate.body->results.front().index].type ==
            Type{},
        "empty conjunction has no checked boolean result");
  });
  cases.run(
      "generic field projections and all labelled/unlabelled clauses", [] {
        auto project = take(check(bounded));
        const auto &decl =
            declarationNamed(project.declarations(), "m::Bounded");
        const auto &definition = *decl.oracleDefinition;
        require(definition.sourceCount == 1 &&
                    definition.sourceBounds.size() == 1 &&
                    definition.sourceBounds.front().source == 0 &&
                    definition.resultShape.size() == 1 &&
                    definition.resultShape.front().input == 1 &&
                    definition.predicates.size() == 3,
                "shape indices or requires clauses differ");
        const auto &predicate =
            project.declarations()[definition.admissibility.index];
        require(predicate.inputs.front().type.domain == "vector" &&
                    predicate.inputs.front().type.arguments.front().symbolic,
                "generic field Data did not project exactly");
        require(llvm::any_of(predicate.body->operations,
                             [](const Operation &operation) {
                               const auto *math =
                                   std::get_if<MathValue>(&operation.action);
                               return math &&
                                      math->identity ==
                                          zkc::MathematicalIdentity::IndexLess;
                             }),
                "declared source bound was erased from admissibility");
        for (unsigned i = 0; i < definition.predicates.size(); ++i) {
          const auto &clause = definition.predicates[i];
          require(clause.ordinal == i &&
                      predicate.body->values[clause.condition.index].type ==
                          Type{},
                  "requires clause has no checked condition");
        }
        auto written = take(inspectWrittenSource(project));
        auto declarations = take(inspectDeclarations(project));
        require(StringRef(written).contains("query_parameter") &&
                    StringRef(written).contains("exact") &&
                    StringRef(declarations).contains("source_bounds"),
                "source inspection omitted oracle metadata");
      });
  cases.run("explicit layout projects the same checked oracle records", [] {
    auto project = take(checkLayout(R"(module m
domain F = field("bls12-381.fr")
type Fixed<T: Type + Copy + Drop, N: nat> = builtin("oracle.table", T, N)
type Oracle<K: OracleKind> = builtin("oracle", K)
pub oracle def Identity(source: Oracle<Fixed<F, 16>>) -> Oracle<Fixed<F, 16>>:
    requires retained:
        true
    requires second: true
    query(position: index):
        unused <- query source at position
        answer <- oracle.query(source, position)
        return answer
)"));
    const auto &decl = declarationNamed(project.declarations(), "m::Identity");
    require(decl.oracleDefinition->predicates.size() == 2 &&
                decl.body->mode == Body::Mode::Oracle && decl.body->inputs == 2,
            "layout oracle did not share checked semantics");
  });
  cases.run("helper result dependencies ignore unrelated answer operands", [] {
    auto project = take(check(R"(
math fn ignore(answer:index,position:index)->index{return position;}
oracle def Independent(source:I)->I {
  query(position:index) {
    let first <- oracle.query(source,position);
    let next=ignore(first,position);
    let second <- oracle.query(source,next);
    return second;
  }
}
)"));
    require(declarationNamed(project.declarations(), "m::Independent").body !=
                nullptr,
            "independent helper position was rejected");
  });
  cases.run("answer adaptation is refused directly and through helpers", [] {
    for (StringRef position : {"first", "keep(first,position)"})
      refusesDefinition(R"(
math fn keep(answer:index,position:index)->index{return answer;}
oracle def Adaptive(source:I)->I { query(position:index) {
  let first <- oracle.query(source,position);
  let second <- oracle.query(source,)" +
                        position.str() + R"();
  return second;
}}
)");
  });
  cases.run(
      "invalid source prefix, query signature and answer are eager errors", [] {
        for (
            StringRef text :
            {R"(oracle def Bad(a:O,n:index,b:O)->O {query(p:index){let x <- query a at p;return x;}})",
             R"(oracle def Bad(a:O)->O {query(p:bool){let x <- query a at 0;return x;}})",
             R"(oracle def Bad(a:O)->O {query(p:index){return true;}})",
             R"(oracle def Bad<T:Field>(a:Oracle<Fixed<T,16>>)->Oracle<Fixed<T,16>> {query(p:index){return true;}})"})
          refusesDefinition(text);
      });
  cases.run("query state, bare sources and unsupported predicate projections",
            [] {
              for (StringRef predicate : {"position", "same(source,source)",
                                          "same(oracle.rows(rows),rows)",
                                          "same(oracle.rows(source),rows)"}) {
                // Index-table Data is 'indices', whose rows projection is
                // unsupported.
                refusesDefinition(
                    "oracle def Bad(source:I,rows:index)->I {requires " +
                    predicate.str() + R"(;query(position:index){
        let x <- query source at position;return x;}})");
              }
              refusesDefinition(R"(
oracle def Bad(source:O)->O {requires unknown(source);query(p:index){
  let x <- query source at p;return x;}}
)");
            });
  cases.run("query suites cannot hide local, control, shape or partial actions",
            [] {
              for (StringRef statement :
                   {"let n=oracle.rows(source);", "let xs=oracle.data(source);",
                    "let mut n=position;", "require true;",
                    "let n=if true { position } else { position };",
                    "let n=intrinsic(\"index.add\",position,position);"})
                refusesDefinition(
                    "oracle def Bad(source:O)->O {query(position:index){" +
                    statement.str() +
                    "let x <- query source at position;return x;}}");
              refusesDefinition(R"(
fn local(x:index)->index{return x;}
oracle def Bad(source:O)->O {query(position:index){
  let p=local(position);let x <- query source at p;return x;}}
)");
              refusesDefinition(R"(
math fn hidden(x:index)->index{return intrinsic("index.add",x,x);}
oracle def Bad(source:O)->O {query(position:index){
  let p=hidden(position);let x <- query source at p;return x;}}
)");
            });
  cases.run("query sites and direct-source aliases are mandatory", [] {
    for (StringRef body :
         {"let _ <- query source at p; return p;",
          "#[site(repeated)] let a <- query source at p; #[site(repeated)] let "
          "b <- query source at p; return b;",
          "let pair=(source,source); let selected=pair.0; let x <- query "
          "selected at p; return x;"})
      refusesDefinition("oracle def Bad(source:I)->I {query(p:index){" +
                        body.str() + "}}");
  });
  cases.run("shape attributes select exact constructor capture slots", [] {
    for (StringRef attributes :
         {"#[shape(source.rows,bound=16)]",
          "#[shape(source.rows,value=rows,bound=16)] "
          "#[shape(result.rows,value=rows,bound=16)]",
          "#[shape(source.rows,bound=16)] "
          "#[shape(result.rows,value=position,bound=16)]",
          "#[shape(source.rows,bound=16)] "
          "#[shape(result.rows,value=rows,bound=F)]"})
      refusesDefinition(attributes.str() + R"(
oracle def Bad(source:Oracle<Table<F>>,rows:index)->Oracle<Table<F>> {
  query(position:index){let x <- query source at position;return x;}}
)");
  });
  cases.run(
      "ordered construction retains custody, canonical args and call evidence",
      [] {
        auto project = take(check(std::string(bounded) + R"(
#[shape(source.rows,bound=16)]
#[shape(out.rows,bound=16)]
protocol Run roles(P,V)(source:Oracle<Table<F>>@P->V,rows:index@(P,V))
  ->(out:Oracle<Table<F>>@P->V) {
  let out <- Bounded<F,16>(rows=rows,source=source);
  return(out=out);
}
)"));
        const auto &body =
            *declarationNamed(project.declarations(), "m::Run").body;
        const OracleInstantiation *construction = nullptr;
        for (const auto &operation : body.operations)
          if (const auto *action =
                  std::get_if<OracleInstantiation>(&operation.action)) {
            construction = action;
            require(action->operands.size() == 2 && action->holder == 0 &&
                        action->receivers == std::vector<unsigned>{1} &&
                        operation.binding &&
                        operation.binding->argumentOrder ==
                            std::vector<unsigned>({1, 0}),
                    "constructor ABI/evaluation/custody evidence differs");
          }
        require(construction, "constructor action was not retained");
        auto closed = take(zkc::test::closeNativeRun(project, "m::Run"));
        bool found = false;
        for (const auto &decl : closed.declarations())
          if (decl.origin && decl.oracleDefinition && decl.body) {
            found = true;
            const auto &definition = *decl.oracleDefinition;
            require(decl.parameters.empty() &&
                        definition.predicates.size() == 3 &&
                        definition.sourceBounds.front()
                                .maximum.dimension.closedValue() == 16 &&
                        definition.resultShape.front().input == 1,
                    "closed oracle metadata was not substituted");
            const auto &predicate =
                closed.declarations()[definition.admissibility.index];
            require(predicate.body && predicate.oraclePredicateOwner &&
                        predicate.oraclePredicateOwner->index == decl.id.index,
                    "closed predicate identitySource differs");
          }
        require(found, "closed oracle instance was omitted");
        take(inspectSourceInstances(closed));
      });
  cases.run(
      "pure construction, missing shared captures and custody mismatch fail",
      [] {
        for (
            StringRef protocol :
            {R"(protocol Run roles(P,V)(source:O@P->V)->(out:O@P->V){let out=Identity(source);return(out=out);})",
             R"(protocol Run roles(P,V)(source:O@P->V,n:index@P)->(out:O@P->V){let out <- Capture(source,n);return(out=out);})",
             R"(protocol Run roles(P,V,W)(a:O@P->V,b:O@P->W)->(out:O@P->V){let out <- Pair(a,b);return(out=out);})"})
          refusesDefinition(std::string(identitySource) + R"(
oracle def Capture(source:O,n:index)->O{query(p:index){let x <- query source at p;return x;}}
oracle def Pair(a:O,b:O)->O{query(p:index){let x <- query a at p;return x;}}
)" + protocol.str());
      });
  cases.run(
      "closed metadata and ordered query mutation cannot pass specialization",
      [] {
        for (unsigned mutation = 0; mutation < 3; ++mutation) {
          auto project = take(check(std::string(identitySource) + R"(
protocol Run roles(P,V)(source:O@P->V)->(out:O@P->V){
  let out <- Identity(source);return(out=out);}
)"));
          auto closed = take(zkc::test::closeNativeRun(project, "m::Run"));
          bool changed = false;
          for (const auto &decl : closed.declarations()) {
            if (!decl.origin || !decl.oracleDefinition || !decl.body)
              continue;
            auto &candidate = const_cast<Declaration &>(decl);
            auto definition =
                std::make_shared<OracleDefinition>(*decl.oracleDefinition);
            if (mutation == 0)
              definition->sourceCount = 0;
            else if (mutation == 1)
              definition->admissibility = decl.id;
            else {
              auto body = std::make_shared<Body>(*decl.body);
              for (auto &operation : body->operations)
                if (auto *query =
                        std::get_if<OracleSourceQuery>(&operation.action)) {
                  query->source = 1;
                  break;
                }
              candidate.body = std::move(body);
            }
            candidate.oracleDefinition = std::move(definition);
            changed = true;
            break;
          }
          require(changed, "no closed oracle mutation target");
          auto error = checkScopedSpecialization(closed);
          require(bool(error), "oracle specialization mutation was accepted");
          consumeError(std::move(error));
        }
      });
  cases.run(
      "dormant closed oracles remain emitted; open templates have no SSA", [] {
        auto project = take(check(std::string(identitySource) + R"(
oracle def Open<T:Field>(source:Oracle<Fixed<T,16>>)->Oracle<Fixed<T,16>> {
  query(p:index){let x <- query source at p;return x;}}
protocol Run roles(P)(x:bool@P)->(out:bool@P){return(out=x);}
)"));
        auto closed = take(zkc::test::closeNativeRun(project, "m::Run"));
        bool dormant = false;
        for (const auto &decl : closed.declarations()) {
          if (decl.origin && decl.oracleDefinition && decl.body)
            dormant |= decl.origin->index ==
                       declarationNamed(project.declarations(), "m::Identity")
                           .id.index;
          if (!decl.origin && decl.oracleDefinition)
            require(!decl.body,
                    "an open/template declaration claimed closed SSA");
        }
        require(dormant, "unused closed definition was omitted");
      });
  return cases.result();
}
