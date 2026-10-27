#include "../lib/Compiler/ComponentContracts.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/SourceClaims.h"
#include "zkc/Compiler/SourceCorrespondence.h"
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
} // namespace
int main() {
  Cases cases;
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
    cantFail(
        checkComponentContracts(*root.get("snapshot"), *claims.getAsObject()));
    const auto &declarations = *(*root.getArray("snapshot"))[10].getAsArray();
    std::set<std::string> expected, actual;
    for (unsigned table : {0, 1})
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
    for (StringRef field : {"source_ast", "bindings", "instances",
                            "instance_rows", "rows", "snapshot", "admission"}) {
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
  return cases.result();
}
