#include "Names.h"
#include "zkc/Frontend/Compile.h"
#include "zkc/Frontend/Dependencies.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Protocol/Instantiation.h"
#include "zkc/Source/Relations.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
using namespace llvm;
using namespace zkc;
namespace {
unsigned checks = 0;
void require(bool ok, const Twine &why) {
  ++checks;
  if (!ok) {
    errs() << why << '\n';
    std::exit(1);
  }
}
template <typename T> T take(Expected<T> result) {
  if (!result) {
    errs() << toString(result.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*result);
}
void rejects(Error error, StringRef code) {
  auto actual = toString(std::move(error));
  require(namesIdentifier(actual, code), "wrong refusal: " + actual);
}
template <typename T> void rejects(Expected<T> result, StringRef code) {
  require(!result, "expected rejection");
  rejects(result.takeError(), code);
}
} // namespace
int main() {
  using namespace relation;
  Constraint row{LinearForm{{2, "1"}}, LinearForm{{3, "1"}},
                 LinearForm{{1, "1"}}};
  auto r = take(R1CS::create("bls12-381.fr", 4, 1, 1, {row}));
  std::string asset = printJson(r.encode());
  unsigned loads = 0;
  auto resolver = [&](StringRef path, size_t limit) -> Expected<std::string> {
    ++loads;
    require(path == "circuit.r1cs" && limit == Limits::bytes,
            "bounded resolver request");
    return asset;
  };
  const char *text = R"pir(module {
    relation Circuit = r1cs("circuit.r1cs");
    derive Rows = multilinear(Circuit, specialized);
    fn Use(s: Vector<"bls12-381.fr"::Element>, w: Vector<"bls12-381.fr"::Element>)
        -> (Vector<"bls12-381.fr"::Element>) {
      let a = Rows_Assemble(s, w); return (a);
    }
  })pir";
  require(!frontend::checkProtocolSyntax(text), "pure syntax accepts imports");
  rejects(frontend::parseProtocolDocument(text), "relation-unresolved");
  require(loads == 0, "parser never invokes resolver");
  auto formatted = take(frontend::formatProtocol(text));
  auto first =
      take(frontend::loadProtocolDocument(formatted, "module.pir", resolver));
  require(loads == 1 && first.module()->relations.size() == 1,
          "one explicit load");
  auto encoded = source::encode(first.root());
  auto project = take(frontend::ProjectInput::capture(
      {{{{{}, frontend::Input(formatted, "module.pir")}}}},
      {{0, "circuit.r1cs", asset}}));
  require(source::encode(take(frontend::compileProject(project))) == encoded,
          "asset callbacks use the same captured-project semantics");
  rejects(
      frontend::parseProtocolDocument(
          "[\"zkc.relations/1\",[[],[]],[\"zkc.protocol/1\",[],[],[],[],[]]]"),
      "relation-source-shape");
  row[0][0].coefficient = "2";
  auto other = take(R1CS::create("bls12-381.fr", 4, 1, 1, {row}));
  asset = printJson(other.encode());
  require(source::encode(first.root()) == encoded,
          "resolved snapshot immutable");
  auto second =
      take(frontend::loadProtocolDocument(text, "module.pir", resolver));
  require(relation::identity(first.module()->relations[0]) !=
              relation::identity(second.module()->relations[0]),
          "same shape distinct identities");
  auto alias = std::make_shared<R1CS>(r);
  auto aliased = *first.module();
  aliased.relations[0].value = alias;
  source::Document frozenAlias(aliased);
  *alias = other;
  require(relation::identity(frozenAlias.module()->relations[0]) ==
              r.identity(),
          "programmatic mutable pointer cannot alter frozen document");
  auto library = *first.module();
  library.library = true;
  auto prepared = take(generic::prepareLibrary(library));
  require(prepared.relations.size() == 1 && prepared.relationViews.size() == 1,
          "generic preparation retains relation ownership");
  auto roundtrip = take(frontend::parseProtocolDocument(printJson(encoded)));
  require(source::encode(roundtrip.root()) == encoded && loads == 2,
          "snapshot never reloads paths");
  auto changed = *first.module();
  changed.relations[0] = second.module()->relations[0];
  rejects(protocol::admit(changed, false), "relation-generated-function");
  changed = *first.module();
  changed.functions[1].body->erase(changed.functions[1].body->begin());
  rejects(protocol::admit(changed, false), "relation-generated-function");
  changed = *first.module();
  changed.relations[0].value = std::shared_ptr<const R1CS>();
  rejects(protocol::admit(changed, false), "relation-unresolved");
  changed = *first.module();
  changed.relationViews[0].kind = "arithmetic";
  rejects(protocol::admit(changed, false), "relation-view-family");
  changed = *first.module();
  changed.relationViews[0].staging = "unknown";
  rejects(protocol::admit(changed, false), "relation-view-staging");
  changed = *first.module();
  changed.relationViews[0].relation = "Missing";
  rejects(protocol::admit(changed, false), "relation-view-target");
  changed = *first.module();
  changed.relations.push_back(changed.relations.front());
  rejects(protocol::admit(changed, false), "relation-duplicate-alias");
  changed = *first.module();
  changed.relations[0].name = "not.a.symbol";
  rejects(protocol::admit(changed, false), "relation-symbol");
  changed = *first.module();
  changed.relationViews[0].name = "not.a.symbol";
  rejects(protocol::admit(changed, false), "relation-symbol");
  changed = *first.module();
  auto foreignField = take(R1CS::create("bn254.fr", 4, 1, 1, {row}));
  changed.relations[0].value = std::make_shared<const R1CS>(foreignField);
  auto error = protocol::admit(changed, false);
  require(bool(error), "wrong field must refuse");
  consumeError(std::move(error));
  changed = *first.module();
  auto layout = take(R1CS::create("bls12-381.fr", 4, 0, 2, {row}));
  changed.relations[0].value = std::make_shared<const R1CS>(layout);
  rejects(protocol::admit(changed, false), "relation-generated-function");
  auto oversized = [&](StringRef, size_t limit) -> Expected<std::string> {
    return std::string(limit + 1, ' ');
  };
  rejects(frontend::loadProtocolDocument(text, "module.pir", oversized),
          "relation-dependency-limit");
  auto badPath = std::string(text);
  badPath.replace(badPath.find("circuit.r1cs"), 12, "../escape");
  rejects(frontend::loadProtocolDocument(badPath, "module.pir", resolver),
          "relation-asset-path");
  // An asset larger than the ordinary source budget remains a compact resolved
  // dependency, including JSON/programmatic source admission and roundtrip.
  std::vector<Constraint> rows(40000, row);
  auto large = take(R1CS::create("bls12-381.fr", 4, 1, 1, std::move(rows)));
  source::Module big;
  source::RelationDeclaration declaration;
  declaration.name = "Large";
  declaration.value = std::make_shared<const R1CS>(std::move(large));
  big.relations.push_back(std::move(declaration));
  require(!source::checkStructure(big), "relation bytes have separate limit");
  auto bigText = printJson(source::encode(big));
  require(bigText.size() > 1024 * 1024,
          "fixture exceeds source-artifact limit");
  auto frozen = take(frontend::parseProtocolDocument(bigText));
  require(!frontend::checkProtocolDocument(frozen),
          "large immutable snapshot admits");
  using N = AIRNode;
  AIRConstraint step{
      {AIRScopeKind::Transition, 1},
      {N::read(1, 0), N::read(0, 0), N::mul(1, 1), N::neg(2), N::add(0, 3)},
      {},
      {}};
  auto air = take(AIR::create("bls12-381.fr", 1, 0, {step}));
  std::string airAsset = printJson(air.encode());
  auto airResolver = [&](StringRef, size_t maximum) -> Expected<std::string> {
    require(maximum == AIRLimits::bytes, "AIR has its own limit");
    return airAsset;
  };
  auto airDocument =
      take(frontend::loadProtocolDocument(R"pir(module {
    relation Trace = air("trace.json");
    derive Steps = arithmetic(Trace, specialized, 3);
    fn Use(s: Vector<"bls12-381.fr"::Element>, t: Vector<"bls12-381.fr"::Element>)
        -> (Vector<"bls12-381.fr"::Element>) {
      let r = Steps_Evaluate(s, t); return (r);
    }
  })pir",
                                          "air.pir", airResolver));
  require(airDocument.module()->functions.size() == 2,
          "AIR generated typed interface is called");
  require(source::encode(take(frontend::parseProtocolDocument(printJson(
                                  source::encode(airDocument.root()))))
                             .root()) == source::encode(airDocument.root()),
          "AIR snapshot roundtrip");
  source::Module core;
  source::RelationDeclaration coreRelation;
  coreRelation.name = "Circuit";
  coreRelation.value = std::make_shared<const R1CS>(foreignField);
  core.relations.push_back(coreRelation);
  source::RelationView coreView;
  coreView.name = "Core";
  coreView.relation = "Circuit";
  coreView.kind = "rank_one";
  coreView.staging = "specialized";
  core.relationViews.push_back(coreView);
  require(!materializeViews(core), "BN254 rank-one core view generates");
  require(!protocol::admit(core, false),
          "BN254 core admits without multilinear types");
  require(core.functions.size() == 3 &&
              core.functions[1].results == source::Names(3, "vector:bn254.fr"),
          "rank-one core signature");
  auto data = core;
  data.functions.clear();
  data.bindings.clear();
  data.relationViews[0].staging = "public_matrices";
  require(!materializeViews(data), "immutable matrices generate");
  require(!protocol::admit(data, false),
          "immutable matrices admit with exact identity checks");
  require(matrixIdentity(foreignField, 0, false) !=
              matrixIdentity(foreignField, 0, true),
          "matrix padding participates in exact identity");
  auto operations = airDocument.module()->functions.back().body->size();
  require(operations > 10, "AIR emits actual arithmetic operations");
  auto wide = take(AIR::create("koala-bear", 65536, 0,
                               {{{AIRScopeKind::First, 0},
                                 {AIRNode::read(0, 0)},
                                 std::nullopt,
                                 std::nullopt}}));
  require(bool(wide.compile(65536)), "sparse AIR schedule remains admissible");
  rejects(lowerAIRArithmetic(wide, "Rows", 65536), "air-cell-limit");
  rejects(lowerAIRArithmetic(wide, "bad-name", 1), "relation-symbol");
  auto oneRow = take(lowerAIRArithmetic(wide, "Rows", 1));
  require(!oneRow.functions.empty(), "bounded dense AIR view remains admitted");
  outs() << checks << " relation authoring checks passed\n";
}
