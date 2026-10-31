#include "support/NativeCases.h"
#include "zkc/Language/Diagnostics.h"
#include "zkc/Language/Inspection.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
using zkc::MathematicalIdentity;
namespace {
constexpr StringLiteral proof = R"(
proof Proof=Run{prover P;verifier V;public{source,rows,other};accept ok;construction authored;}
)";
std::string source(bool early = true, bool forwarded = false) {
  std::string text = R"(module m;
domain F=field("koala-bear");
type Table<T:Type+Copy+Drop>=builtin("oracle.table",T);
type Oracle<K:OracleKind>=builtin("oracle",K);
)";
  if (early)
    text += proof;
  text += R"(
#[shape(source.rows,bound=Max)]
#[shape(result.rows,value=rows,bound=Max)]
oracle def Bounded<T:Field,Max:nat>(source:Oracle<Table<T>>,rows:index,other:index)
    ->Oracle<Table<T>> {
  requires exact: intrinsic("index.equal",oracle.rows(source),rows);
  requires captures: intrinsic("index.equal",rows,other);
  requires data: intrinsic("index.equal",intrinsic<T>("vector.length",oracle.data(source)),rows);
  requires true;
  query(position:index) {
    let rows=position;
    let answer <- oracle.query(source,rows);
    return answer;
  }
}
)";
  if (forwarded)
    text += R"(
#[shape(source.rows,bound=Max)]
#[shape(out.rows,bound=Max)]
protocol Forward<T:Field,Max:nat> roles(P,V)
    (source:Oracle<Table<T>>@P->V,rows:index@(P,V),other:index@(P,V))
    ->(out:Oracle<Table<T>>@P->V) {
  let out <- Bounded<T,Max>(other=other,source=source,rows=rows);
  return(out=out);
}
)";
  text += R"(
#[shape(source.rows,bound=16)]
protocol Run roles(P,V)
    (source:Oracle<Table<F>>@P->V,rows:index@(P,V),other:index@(P,V))->(ok:bool@V) {
)";
  text +=
      forwarded
          ? "let out=Forward<F,16>(source,rows,other);\n"
          : "let out <- Bounded<F,16>(other=other,rows=rows,source=source);\n";
  text += "let ok@V=true;return(ok=ok);}\n";
  if (!early)
    text += proof;
  return text;
}
std::string replace(std::string text, StringRef before, StringRef after) {
  auto at = text.find(before.str());
  require(at != std::string::npos, "fixture replacement is absent");
  text.replace(at, before.size(), after.str());
  return text;
}
Expected<CheckedProject> check(StringRef text) {
  auto captured = capture({{"m", text.str(), "oracle-predicate-scope.zkc"}});
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
ClosedEntry close(StringRef text) {
  return take(closeEntry(take(check(text)), "m::Proof"));
}
const Declaration &oracle(const ClosedEntry &entry) {
  auto found = llvm::find_if(entry.declarations(), [](const Declaration &decl) {
    return decl.origin && decl.oracleDefinition;
  });
  require(found != entry.declarations().end(), "closed constructor is absent");
  return *found;
}
void verify(const ClosedEntry &entry) {
  const auto &decl = oracle(entry);
  const auto &definition = *decl.oracleDefinition;
  const auto &predicate = entry.declarations()[definition.admissibility.index];
  require(decl.inputs.size() == 3 && definition.sourceCount == 1 &&
              definition.predicates.size() == 4 && decl.body &&
              decl.body->inputs == 4 && decl.parameters.empty(),
          "constructor captures, query input or requires clauses differ");
  require(predicate.oraclePredicateOwner &&
              predicate.oraclePredicateOwner->index == decl.id.index &&
              predicate.origin && predicate.body && predicate.relation &&
              predicate.relation->kind == RelationDefinition::Kind::Formula &&
              predicate.body->mode == Body::Mode::Math &&
              predicate.inputs.size() == 3 && predicate.body->inputs == 3 &&
              predicate.inputs[0].type.domain == "vector" &&
              predicate.inputs[0].type.arguments ==
                  decl.inputs[0].type.arguments[0].arguments &&
              predicate.inputs[1].type == decl.inputs[1].type &&
              predicate.inputs[2].type == decl.inputs[2].type &&
              predicate.staticArguments == decl.staticArguments,
          "predicate Data/capture ABI or independent static instance differs");
  for (unsigned i = 0; i < predicate.inputs.size(); ++i)
    require(predicate.body->values[i].type == predicate.inputs[i].type,
            "predicate body input differs from its port");
  require(definition.sourceBounds.size() == 1 &&
              definition.sourceBounds[0].source == 0 &&
              definition.sourceBounds[0].maximum.dimension.closedValue() ==
                  16 &&
              definition.resultShape.size() == 1 &&
              definition.resultShape[0].input == 1,
          "static bound or result capture slot differs");
  const char *labels[] = {"exact", "captures", "data", nullptr};
  for (unsigned i = 0; i < definition.predicates.size(); ++i) {
    const auto &clause = definition.predicates[i];
    require(clause.ordinal == i &&
                clause.label == (labels[i]
                                     ? std::optional<std::string>(labels[i])
                                     : std::nullopt) &&
                clause.condition.index < predicate.body->values.size() &&
                predicate.body->values[clause.condition.index].type == Type{},
            "requires label, order or checked condition differs");
  }
  auto condition = definition.predicates[1].condition;
  auto found =
      llvm::find_if(predicate.body->operations, [&](const Operation &op) {
        return op.results.size() == 1 && op.results[0].index == condition.index;
      });
  require(found != predicate.body->operations.end(),
          "capture clause is absent");
  auto *equal = std::get_if<MathValue>(&found->action);
  require(equal && equal->identity == MathematicalIdentity::IndexEqual &&
              equal->operands.size() == 2 && equal->operands[0].index == 1 &&
              equal->operands[1].index == 2,
          "query-local shadow replaced a predicate capture");
  unsigned conjunctions = 0;
  bool maximum = false;
  for (const auto &operation : predicate.body->operations)
    if (const auto *value = std::get_if<MathValue>(&operation.action)) {
      conjunctions += value->identity == MathematicalIdentity::BooleanAnd;
      maximum |= value->identity == MathematicalIdentity::IndexConstant &&
                 value->staticArguments.size() == 1 &&
                 value->staticArguments[0].dimension.closedValue() == 16;
    }
  require(conjunctions == 4 && maximum,
          "requires conjunction or generated source-bound predicate was lost");
  if (auto error = checkScopedSpecialization(entry))
    throw std::runtime_error(toString(std::move(error)));
  take(inspectSourceInstances(entry));
}
} // namespace
int main() {
  Cases cases;
  cases.run("proof checking forms the predicate before resolving captures",
            [] { verify(close(source())); });
  cases.run("completed signatures retain the same predicate ABI",
            [] { verify(close(source(false))); });
  cases.run("forwarded field and bound statics retain canonical capture slots",
            [] { verify(close(source(true, true))); });
  cases.run("a predicate block shadows its capture only within the block", [] {
    auto text = replace(source(), "requires true;", R"(
requires {let rows=other;intrinsic("index.equal",rows,other)};
)");
    auto entry = close(text);
    const auto &decl = oracle(entry);
    const auto &body =
        *entry.declarations()[decl.oracleDefinition->admissibility.index].body;
    const auto &clause = decl.oracleDefinition->predicates.back();
    require(body.values[clause.condition.index].components ==
                std::vector<unsigned>{2},
            "block-local shadow did not resolve to the other capture");
    verify(entry);
  });
  for (StringRef forbidden : {"position", "answer"})
    cases.run("requires cannot capture query-local " + forbidden, [=] {
      refuses(check(replace(source(), "requires true;",
                            "requires intrinsic(\"index.equal\"," +
                                forbidden.str() + ",rows);")),
              "source.name");
    });
  cases.run("direct source handles still require a predicate projection", [] {
    refuses(check(replace(source(), "requires true;", "requires source;")),
            "source.oracle-predicate");
  });
  cases.run(
      "independent substitution rejects a same-type capture replacement", [] {
        auto entry = close(source());
        const auto &decl = oracle(entry);
        auto &predicate = const_cast<Declaration &>(
            entry.declarations()[decl.oracleDefinition->admissibility.index]);
        auto body = std::make_shared<Body>(*predicate.body);
        bool changed = false;
        for (auto &operation : body->operations)
          if (auto *value = std::get_if<MathValue>(&operation.action))
            if (value->identity == MathematicalIdentity::IndexEqual &&
                value->operands.size() == 2 && value->operands[0].index == 1 &&
                value->operands[1].index == 2) {
              value->operands[0] = {2};
              changed = true;
              break;
            }
        require(changed, "capture comparison mutation is absent");
        predicate.body = std::move(body);
        auto error = checkScopedSpecialization(entry);
        require(bool(error), "same-type predicate substitution accepted");
        require(namesIdentifier(toString(std::move(error)),
                                "source.scoped-specialization"),
                "predicate substitution failed outside its checked boundary");
      });
  cases.run("independent substitution rejects a removed source bound", [] {
    auto entry = close(source());
    auto &decl = const_cast<Declaration &>(oracle(entry));
    auto definition =
        std::make_shared<OracleDefinition>(*decl.oracleDefinition);
    definition->sourceBounds.clear();
    decl.oracleDefinition = std::move(definition);
    auto error = checkScopedSpecialization(entry);
    require(bool(error), "removed source bound accepted");
    require(namesIdentifier(toString(std::move(error)),
                            "source.oracle-specialization"),
            "source bound failed outside its checked boundary");
  });
  return cases.result();
}
