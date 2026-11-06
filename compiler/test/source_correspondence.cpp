#include "../lib/Compiler/ComponentContracts.h"
#include "../lib/Compiler/SourceView.h"
#include "support/NativeCases.h"
#include "support/SourceProject.h"
#include "zkc/Compiler/SourceClaims.h"
#include "zkc/Compiler/SourceCorrespondence.h"
#include "zkc/Language/Names.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/MemoryBuffer.h"
#include <map>
#include <set>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
CheckedOriginal original(StringRef expression = "x",
                         StringRef diagnostic = "") {
  auto text = ("module authored;protocol P roles(A)(x:bool@A)->(ok:bool@A){"
               "return(ok=" +
               expression + ");}")
                  .str();
  auto project =
      take(analyze(take(capture({{"authored", text, diagnostic.str()}})))
               .checkedProject());
  return take(prepareOriginal(take(closeSubject(project, "authored::P"))));
}
json::Value report(const CheckedOriginal &value) {
  return take(json::parse(take(exportSourceCorrespondence(value))));
}
void accepted(Error result) {
  if (result)
    throw std::runtime_error(toString(std::move(result)));
}
void refused(Error result, StringRef code = "source.correspondence.export") {
  require(bool(result), "accepted changed source publication");
  auto message = toString(std::move(result));
  require(message.find(code.str()) != std::string::npos, message);
}
const json::Value &at(const json::Value &value, const json::Array &path) {
  auto *node = &value;
  for (const auto &part : path) {
    auto ordinal = part.getAsInteger();
    require(ordinal && *ordinal >= 0 && node->getAsArray() &&
                uint64_t(*ordinal) < node->getAsArray()->size(),
            "dangling row association");
    node = &(*node->getAsArray())[*ordinal];
  }
  return *node;
}
void associations(const json::Value &document) {
  const auto &root = *document.getAsObject();
  std::map<std::string, const json::Object *> nodes;
  for (const auto &decl :
       *root.getObject("source_ast")->getArray("declarations")) {
    const auto &owner = *decl.getAsObject();
    for (const auto &item : *owner.getArray("nodes")) {
      auto *node = item.getAsObject();
      nodes.emplace(owner.getString("owner")->str() + ':' +
                        zkc::printJson(*node->get("path")),
                    node);
    }
  }
  std::set<std::string> coordinates;
  unsigned joined = 0;
  for (const auto &item : *root.getArray("rows")) {
    const auto &row = *item.getAsObject();
    at(*root.get("snapshot"), *row.getArray("row"));
    require(coordinates.insert(zkc::printJson(*row.get("row"))).second,
            "duplicate structured row");
    for (const auto &source : *row.getArray("sources")) {
      const auto &record = *source.getAsObject();
      ++joined;
      for (const auto &candidate : *record.getArray("candidates")) {
        const auto &address = *candidate.getAsObject();
        auto found = nodes.find(address.getString("owner")->str() + ':' +
                                zkc::printJson(*address.get("path")));
        require(found != nodes.end() &&
                    *found->second->get("span") == *record.get("span"),
                "source search hint is not an exact written node");
      }
    }
  }
  const auto &instances = *root.getObject("instances")->getArray("instances");
  require(root.getArray("instance_rows")->size() == instances.size(),
          "instance row coverage is incomplete");
  unsigned associated = 0;
  for (const auto &item : *root.getArray("instance_rows")) {
    const auto &record = *item.getAsObject();
    auto ordinal = *record.getInteger("instance");
    require(ordinal >= 0 && uint64_t(ordinal) < instances.size(),
            "invalid instance index");
    auto symbol = instances[ordinal].getAsObject()->getString("symbol");
    for (const auto &row : *record.getArray("rows")) {
      ++associated;
      auto &definition =
          *at(*root.get("snapshot"), *row.getAsArray()).getAsArray();
      require(definition[1].getAsString() == symbol,
              "instance selected a different definition");
    }
  }
  require(associated > 0, "no closed definition has an associated row");
  require(joined >= 2, "declaration/body source join absent");
}
const json::Object &member(const json::Value &document, StringRef name) {
  return *document.getAsObject()->getObject(name);
}
json::Array &list(json::Value &document, StringRef name) {
  return *document.getAsObject()->getArray(name);
}
/// The occurrences of one definition, by site.
std::map<std::string, json::Value> occurrences(const json::Value &document,
                                               StringRef definition) {
  std::map<std::string, json::Value> result;
  for (const auto &item : *document.getAsObject()->getArray("occurrences")) {
    const auto &occurrence = *item.getAsObject();
    if (occurrence.getString("definition") == definition)
      result.emplace(occurrence.getString("site")->str(),
                     *occurrence.get("nodes"));
  }
  return result;
}
std::string symbolOf(const json::Value &document, StringRef owner) {
  for (const auto &item :
       *member(document, "instances").getArray("instances")) {
    const auto &instance = *item.getAsObject();
    if (instance.getObject("template")->getString("owner") == owner)
      return instance.getString("symbol")->str();
  }
  throw std::runtime_error(("no instance of " + owner).str());
}
/// The written node kind at an address, from the exported syntax.
std::string nodeKind(const json::Value &document, const json::Value &address) {
  const auto &target = *address.getAsObject();
  for (const auto &decl :
       *member(document, "source_ast").getArray("declarations")) {
    if (decl.getAsObject()->getString("owner") != target.getString("owner"))
      continue;
    for (const auto &node : *decl.getAsObject()->getArray("nodes"))
      if (*node.getAsObject()->get("path") == *target.get("path"))
        return node.getAsObject()->getString("kind")->str();
  }
  return {};
}
constexpr StringLiteral sharedMaps = R"(module maps;
use zkc::vector::{Vector};
domain Fr = field("bls12-381.fr");
math fn scale(s: Fr, x: Fr) -> Fr { return s * x; }
fn left(s: Fr, a: Vector<Fr>) -> Vector<Fr> { return map scale(s, each a); }
fn right(s: Fr, b: Vector<Fr>) -> Vector<Fr> { return map scale(s, each b); }
protocol Both roles(P)(s: Fr @P, a: Vector<Fr> @P, b: Vector<Fr> @P)
    -> (x: Vector<Fr> @P, y: Vector<Fr> @P, z: Vector<Fr> @P) {
  let x @P = left(s, a);
  let y @P = left(s, b);
  let z @P = right(s, b);
  return (x = x, y = y, z = z);
}
)";
CheckedOriginal mapsOriginal(StringRef subject) {
  auto sources = sourceProject(ZKC_SOURCE_PROJECT);
  sources.push_back({"maps", sharedMaps.str(), {}});
  auto project =
      take(analyze(take(capture(std::move(sources)))).checkedProject());
  return take(prepareOriginal(take(closeSubject(project, subject))));
}
CheckedOriginal claimsOriginal() {
  auto file = MemoryBuffer::getFile(ZKC_CORRESPONDENCE_FIXTURES
                                    "/components-local-fields.zkc");
  require(bool(file), "component fixture cannot be read");
  auto project =
      take(analyze(take(capture({{"claims", (*file)->getBuffer().str(), {}}})))
               .checkedProject());
  return take(prepareOriginal(take(closeSubject(project, "claims::Run"))));
}
/// Protocol custody creation, application and destruction.
CheckedOriginal custodyOriginal() {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto project = take(analyze(take(capture({{"m", R"(#[linear]
struct Ticket roles(P, V):
protocol forward roles(P, V)(ticket: Ticket roles(P, V)) -> Ticket roles(P, V):
    return ticket
pub protocol Run roles(P, V)() -> bool @V:
    ticket <- Ticket roles(P, V) {}
    next <- ticket.forward()
    empty <- unpack(next)
    return true
)",
                                             "custody.zkc"}},
                                           options)))
                          .checkedProject());
  return take(prepareOriginal(take(closeSubject(project, "m::Run"))));
}
void inventoryRefuses(const json::Value &document, StringRef reason) {
  auto refusal = checkCorrespondenceInventory(document);
  require(bool(refusal), "an incomplete inventory was accepted");
  auto message = toString(std::move(refusal));
  require(StringRef(message).contains(reason),
          "unexpected refusal: " + message);
}
void generatedOccurrences(Cases &cases) {
  cases.run("every definition row has exactly one inventory entry", [] {
    for (StringRef subject :
         {"map_examples::First", "map_examples::Prefix",
          "map_examples::LinearCombination", "map_examples::ConstantRows",
          "map_examples::RealizeValues", "maps::Both"}) {
      auto value = mapsOriginal(subject);
      auto document = report(value);
      accepted(checkCorrespondenceInventory(document));
      accepted(
          checkSourceCorrespondenceExport(value, zkc::printJson(document)));
      require(list(document, "generated_rows").size() ==
                  list(document, "generated").size(),
              "generated row coverage is incomplete");
    }
    accepted(checkCorrespondenceInventory(report(claimsOriginal())));
    // Protocol custody creation outlines a custody definition.
    auto custody = report(custodyOriginal());
    accepted(checkCorrespondenceInventory(custody));
    unsigned outlined = 0;
    for (unsigned i = 0; i < list(custody, "generated").size(); ++i)
      if (list(custody, "generated")[i].getAsObject()->getString("purpose") ==
          "custody") {
        ++outlined;
        require(!list(custody, "generated_rows")[i]
                     .getAsObject()
                     ->getArray("rows")
                     ->empty(),
                "a custody definition has no snapshot row");
      }
    require(outlined > 0, "custody creation generated no custody definition");
  });
  cases.run("a reused map adapter lists both callers", [] {
    auto document = report(mapsOriginal("maps::Both"));
    auto left = symbolOf(document, "maps::left"),
         right = symbolOf(document, "maps::right");
    unsigned adapters = 0;
    for (const auto &item : list(document, "generated")) {
      const auto &entry = *item.getAsObject();
      if (entry.getString("purpose") != "map")
        continue;
      ++adapters;
      require(StringRef(*entry.getString("symbol")).starts_with("zkl_map_"),
              "a map adapter has another symbol");
      std::set<std::string> callers;
      for (const auto &origin : *entry.getArray("origins"))
        callers.insert(origin.getAsObject()->getString("definition")->str());
      require(callers == std::set<std::string>{left, right},
              "a reused map adapter does not list both callers");
    }
    require(adapters == 2, "the shared map adapter is not domain and body");
  });
  cases.run("two unlabelled calls get distinct sites and nodes", [] {
    auto document = report(mapsOriginal("maps::Both"));
    auto sites = occurrences(document, symbolOf(document, "maps::Both"));
    std::set<std::string> nodes;
    for (const auto &[site, written] : sites) {
      require(written.getAsArray()->size() == 1,
              "an application lost its written node");
      require(nodeKind(document, (*written.getAsArray())[0]) == "expr.call",
              "an application site is not its call expression");
      nodes.insert(zkc::printJson(written));
    }
    require(sites.size() == 3 && nodes.size() == 3,
            "unlabelled calls share a site or a node");
  });
  cases.run("a labelled site resolves to its call", [] {
    auto document = report(claimsOriginal());
    auto run = occurrences(document, symbolOf(document, "claims::Run"));
    auto first = nativeSiteName("first", 0);
    auto found = run.find(first);
    require(found != run.end() && found->second.getAsArray()->size() == 1,
            "the labelled site has no single written node");
    require(nodeKind(document, (*found->second.getAsArray())[0]) == "expr.call",
            "the labelled site does not resolve to its call");
  });
  cases.run("sites derived from one statement share its nodes", [] {
    auto document = report(custodyOriginal());
    auto run = occurrences(document, symbolOf(document, "m::Run"));
    // Creation emits one custody unit per role; both originate from the
    // creating statement, while the next statement's application has its own.
    std::map<std::string, std::set<std::string>> byNodes;
    for (const auto &[site, nodes] : run) {
      require(!nodes.getAsArray()->empty(), "a site lost its written node");
      byNodes[zkc::printJson(nodes)].insert(site);
    }
    unsigned shared = 0;
    for (const auto &[nodes, sites] : byNodes)
      shared += sites.size() > 1;
    require(shared == 2 && byNodes.size() == 3,
            "creation, application and destruction do not keep their own "
            "statement nodes");
  });
  cases.run("inventory and occurrence edits refuse", [] {
    auto value = mapsOriginal("maps::Both");
    auto pristine = report(value);
    auto generated = list(pristine, "generated");
    // An edited node.
    auto edited = pristine;
    for (auto &item : list(edited, "occurrences"))
      if (!item.getAsObject()->getArray("nodes")->empty()) {
        (*item.getAsObject())["nodes"] = json::Array{};
        break;
      }
    refused(checkSourceCorrespondenceExport(value, zkc::printJson(edited)));
    // A repeated symbol.
    auto repeated = pristine;
    list(repeated, "generated").push_back(generated[0]);
    inventoryRefuses(repeated, "repeat");
    refused(checkSourceCorrespondenceExport(value, zkc::printJson(repeated)));
    // A repeated purpose, part and origins under another symbol.
    auto twin = pristine;
    auto copy = generated[0];
    (*copy.getAsObject())["symbol"] = "zkl_twin";
    list(twin, "generated").push_back(std::move(copy));
    inventoryRefuses(twin, "purpose, part and origins repeat");
    refused(checkSourceCorrespondenceExport(value, zkc::printJson(twin)));
    // A function row without an entry: the producer's own invariant refuses
    // a dropped entry before publication.
    auto dropped = pristine;
    list(dropped, "generated").erase(list(dropped, "generated").begin());
    inventoryRefuses(dropped, "is not exactly one instance");
    refused(checkSourceCorrespondenceExport(value, zkc::printJson(dropped)));
    // Retaining only valid occurrences is insufficient when a site is omitted.
    auto missing = pristine;
    auto &sites = list(missing, "occurrences");
    sites.erase(sites.begin());
    inventoryRefuses(missing, "occurrences do not cover every snapshot site");
    // An occurrence of a site the snapshot does not have.
    auto invented = pristine;
    (*list(invented, "occurrences")[0].getAsObject())["site"] = "s9999";
    inventoryRefuses(invented,
                     "occurrence does not match the next snapshot site");
    auto reordered = pristine;
    auto &order = list(reordered, "occurrences");
    std::swap(order[0], order[1]);
    inventoryRefuses(reordered,
                     "occurrence does not match the next snapshot site");
  });
}
} // namespace
int main() {
  Cases cases;
  cases.run("all selected Math arms retain exactly one association", [] {
    auto document = report(original("x && x"));
    accepted(checkCorrespondenceInventory(document));
    associations(document);
    const auto &rows = *document.getAsObject()->getArray("rows");
    auto nested = llvm::find_if(rows, [](const json::Value &value) {
      return value.getAsObject()->getArray("row")->size() > 6;
    });
    require(nested != rows.end(), "selected arm association absent");
    auto ordinal = std::distance(rows.begin(), nested);
    auto dropped = document;
    auto &droppedRows = list(dropped, "rows");
    droppedRows.erase(droppedRows.begin() + ordinal);
    inventoryRefuses(dropped, "cover the complete snapshot");
    auto repeated = document;
    list(repeated, "rows").push_back(*nested);
    inventoryRefuses(repeated, "dangling or repeated");
    auto dangling = document;
    *list(dangling, "rows")[ordinal].getAsObject()->get("row") =
        json::Array{7, 999999, 9, 1, 0, 3, 0};
    inventoryRefuses(dangling, "dangling or repeated");
  });

  cases.run(
      "installed rows retain original association without written spans", [] {
        auto project = take(analyze(take(capture({{"m",
                                                   R"(module m;
      protocol P roles(A)(x:index@A,y:index@A)->(sum:index@A){
        let sum=x+y;return(sum=sum);
      })",
                                                   {}}})))
                                .checkedProject());
        auto subject =
            take(prepareOriginal(take(closeSubject(project, "m::P"))));
        auto document = report(subject);
        auto symbol = symbolOf(document, "zkc::prelude::index_add");
        const auto &root = *document.getAsObject();
        bool found = false;
        for (const auto &item : *root.getArray("rows")) {
          const auto &row = *item.getAsObject();
          const auto &path = *row.getArray("row");
          if (path.size() != 2)
            continue;
          const auto &definition =
              *at(*root.get("snapshot"), path).getAsArray();
          if (definition[1].getAsString() != symbol)
            continue;
          found = true;
          require(row.getObject("original") && row.getArray("sources")->empty(),
                  "installed row lost its original association or gained "
                  "written source");
        }
        require(found, "installed row was not associated");
        accepted(
            checkSourceCorrespondenceExport(subject, zkc::printJson(document)));
      });
  cases.run(
      "syntax, rows and claims share the checked original association", [] {
        auto value = original();
        auto document = report(value);
        const auto &root = *document.getAsObject();
        auto claims = take(json::parse(take(exportSourceClaims(value))));
        require(root.getString("format") == "zkc.source-correspondence/0" &&
                    *root.get("admission") ==
                        *claims.getAsObject()->get("admission"),
                "source proposals invented another admission association");
        auto *admission = root.getObject("admission");
        require(admission->getString("original_sha256") ==
                    (*root.getArray("snapshot"))[2].getAsString(),
                "snapshot belongs to different original bytes");
        for (StringRef field : {"capture", "installation"})
          require(root.getObject("source_ast")->getString(field) ==
                          admission->getString(field) &&
                      root.getObject("bindings")->getString(field) ==
                          admission->getString(field),
                  "source components belong to different captures");
        associations(document);
        accepted(
            checkSourceCorrespondenceExport(value, zkc::printJson(document)));
      });
  cases.run("component context and seams retain the same actual snapshot", [] {
    auto file = MemoryBuffer::getFile(ZKC_CORRESPONDENCE_FIXTURES
                                      "/components-local-fields.zkc");
    require(bool(file), "component fixture cannot be read");
    auto project = take(
        analyze(take(capture({{"claims", (*file)->getBuffer().str(), {}}})))
            .checkedProject());
    auto value =
        take(prepareOriginal(take(closeSubject(project, "claims::Run"))));
    auto document = report(value);
    auto &root = *document.getAsObject();
    auto claims = take(json::parse(take(exportSourceClaims(value))));
    require(*root.get("admission") == *claims.getAsObject()->get("admission"),
            "component claims acquired a different association");
    require(!claims.getAsObject()->getArray("seams")->empty(),
            "component seams disappeared during integration");
    cantFail(checkComponentContracts(
        take(zkc::language::detail::OriginalAccess::read(value)),
        *claims.getAsObject()));
    const auto &declarations = *(*root.getArray("snapshot"))[10].getAsArray();
    std::set<std::string> expected, actual;
    for (unsigned table : {0, 1, 2})
      for (unsigned i = 0; i < declarations[table].getAsArray()->size(); ++i)
        expected.insert(zkc::printJson(json::Array{10, table, i}));
    for (const auto &item : *root.getArray("rows")) {
      const auto &row = *item.getAsObject();
      const auto &path = *row.getArray("row");
      if (path.front().getAsInteger() == 10) {
        require(row.getString("operation") == "protocol.module",
                "declaration context has an invented executable origin");
        actual.insert(zkc::printJson(json::Array(path)));
      }
    }
    require(!expected.empty() && expected == actual,
            "retained source declarations lack row associations");
    associations(document);
    accepted(checkSourceCorrespondenceExport(value, zkc::printJson(document)));
  });
  cases.run(
      "a different body with the same signature has different evidence", [] {
        auto first = original("x"), second = original("!x");
        auto a = report(first), b = report(second);
        require(*a.getAsObject()->get("snapshot") !=
                    *b.getAsObject()->get("snapshot"),
                "different body kept the same snapshot");
        refused(checkSourceCorrespondenceExport(second, zkc::printJson(a)));
        associations(b);
      });
  cases.run("proposal edits cannot change the original or its publication", [] {
    auto value = original();
    auto pristine = report(value);
    for (StringRef field :
         {"source_ast", "bindings", "instances", "instance_rows", "generated",
          "generated_rows", "occurrences", "rows", "snapshot", "admission"}) {
      auto changed = pristine;
      (*changed.getAsObject())[field] = nullptr;
      refused(checkSourceCorrespondenceExport(value, zkc::printJson(changed)));
    }
    require(report(value) == pristine,
            "checking proposals mutated the original");
  });
  cases.run("unknown fields and duplicate JSON keys refuse", [] {
    auto value = original();
    auto document = report(value);
    (*document.getAsObject())["authority"] = true;
    refused(checkSourceCorrespondenceExport(value, zkc::printJson(document)));
    refused(checkSourceCorrespondenceExport(value, R"({"rows":[],"rows":[]})"));
  });
  cases.run("diagnostic filenames do not enter the artifact", [] {
    auto a = original("x", "/private/one.zkc");
    auto b = original("x", "/unrelated/two.zkc");
    auto bytes = take(exportSourceCorrespondence(a));
    require(bytes == take(exportSourceCorrespondence(b)) &&
                bytes.find("/private/") == std::string::npos,
            "diagnostic path changed source correspondence");
  });
  cases.run("aggregate publication and component limits refuse atomically", [] {
    auto value = original();
    auto bytes = take(exportSourceCorrespondence(value));
    auto limits = Limits{};
    limits.apiInspectionBytes = bytes.size();
    require(take(exportSourceCorrespondence(value, limits)) == bytes,
            "exact publication limit refused");
    --limits.apiInspectionBytes;
    refuses(exportSourceCorrespondence(value, limits), "source.limit");
    limits = Limits{};
    limits.work = value.entry().project().checkedWork() - 1;
    refuses(exportSourceCorrespondence(value, limits), "source.limit");
    limits = Limits{};
    limits.irBytes = value.bytes().size() - 1;
    refuses(exportSourceCorrespondence(value, limits), "source.limit");
  });
  cases.run("claim inspection respects retained original byte limits", [] {
    auto value = original();
    auto bytes = take(exportSourceClaims(value));
    auto limits = Limits{};
    limits.irBytes = value.bytes().size();
    limits.interfaceBytes = value.interfaceJson().size();
    require(bytes.size() <= limits.interfaceBytes,
            "fixture does not separate input and publication limits");
    require(take(exportSourceClaims(value, limits)) == bytes,
            "exact retained input limits refused");
    --limits.irBytes;
    refuses(exportSourceClaims(value, limits), "source.limit");
    refused(checkSourceClaims(value, bytes, limits), "source.limit");
    limits.irBytes = value.bytes().size();
    --limits.interfaceBytes;
    refuses(exportSourceClaims(value, limits), "source.limit");
    refused(checkSourceClaims(value, bytes, limits), "source.limit");
  });
  cases.run(
      "ordinary Host entries are outside the structured protocol profile", [] {
        auto project = take(
            analyze(
                take(capture(
                    {{"host", "module host;entry fn Main(){return ();}", {}}})))
                .checkedProject());
        auto value =
            take(prepareOriginal(take(closeEntry(project, "host::Main"))));
        refuses(exportSourceCorrespondence(value),
                "source.correspondence.export");
      });
  generatedOccurrences(cases);
  return cases.result();
}
