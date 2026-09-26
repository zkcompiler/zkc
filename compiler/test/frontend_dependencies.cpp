#include "support/NativeCases.h"
#include "zkc/Frontend/Dependencies.h"
#include <algorithm>

using namespace llvm;
using namespace zkc;
using namespace zkc::frontend;
using namespace zkc::test;

namespace {
DependencyDeclarations inspect(std::string text) {
  return inspectDependencies(Input::withoutFile(std::move(text)), 7);
}
void diagnosticIs(const DependencyDeclarations &result, StringRef code) {
  require(std::any_of(result.diagnostics.begin(), result.diagnostics.end(),
                      [&](const auto &d) { return d.code == code; }),
          "missing diagnostic: " + code);
  require(!result.complete, "a diagnostic must prevent completion");
}
} // namespace

int main() {
  Cases cases;
  cases.run("owned dependency spelling and exact source spans", [] {
    std::string text = R"(module {
      library(namespace="sample", name="root", version="1", resolution="local");
      dependency util = library(namespace="sample", name="utils", version="2", resolution="pin");
      pub mod child;
      relation Circuit = r1cs("absent.json");
      relation Trace = air("trace.json");
    })";
    auto result = inspect(text);
    require(result.complete && result.recoverable && result.diagnostics.empty(),
            "unresolved dependency spelling is valid for pure inspection");
    require(result.form == SourceForm::Module && result.modules.size() == 1 &&
                result.relations.size() == 2 && result.libraries.size() == 1 &&
                result.libraryIdentities.size() == 1,
            "declaration classification");
    auto span = result.relations.front().location;
    require(span && span->file == 7 &&
                text.substr(span->offset, span->length) ==
                    "relation Circuit = r1cs(\"absent.json\");",
            "relation span covers its exact declaration");
    require(result.modules.front().location->file == 7 &&
                result.libraries.front().location->file == 7 &&
                result.libraryIdentities.front().location->file == 7,
            "all dependency origins retain the supplied file ID");
    text.assign("caller storage replaced");
    auto copy = result;
    result = {};
    require(copy.modules.front().name == "child" &&
                copy.relations.front().name == "Circuit" &&
                copy.relations.front().path == "absent.json" &&
                copy.relations.back().family == "air" &&
                copy.libraries.front().name == "util" &&
                copy.libraries.front().identity.nameSpace == "sample" &&
                copy.libraries.front().identity.name == "utils" &&
                copy.libraries.front().identity.version == "2" &&
                copy.libraries.front().identity.resolution == "pin" &&
                copy.libraryIdentities.front().name == "root",
            "result owns names and identity fields after input teardown");
  });
  cases.run("pure query leaves portable asset paths to loading", [] {
    auto result = inspect(R"(module { relation R = air("../outside"); })");
    require(result.complete && result.relations.front().path == "../outside",
            "inspection does not canonicalize or admit physical paths");
  });
  cases.run("file-labelled input is inspected without opening its file", [] {
    auto result = inspectDependencies(
        Input(R"(module { mod absent; relation R = air("absent.json"); })",
              "/absent/dependency-inspection/app.pir"));
    require(result.complete && result.modules.size() == 1 &&
                result.relations.size() == 1,
            "even file-backed snapshots are queried entirely in memory");
  });
  cases.run("recovery publishes only completely recognized declarations", [] {
    auto result = inspect(R"(module {
      relation Before = r1cs("before.json");
      relation Broken = r1cs("never.json";
      mod child;
      relation After = air("after.json");
    })");
    diagnosticIs(result, "source-syntax");
    require(result.recoverable && result.modules.size() == 1 &&
                result.relations.size() == 2 &&
                result.relations[0].name == "Before" &&
                result.relations[1].name == "After" &&
                result.diagnostics.front().location->file == 7,
            "malformed request is omitted while later declarations survive");
  });
  cases.run("malformed duplicate remains incomplete", [] {
    auto result = inspect(R"(module {
      relation R = r1cs("safe.json"); relation R = r1cs("never.json";
    })");
    diagnosticIs(result, "source-syntax");
    require(result.recoverable && result.relations.size() == 1,
            "parser recovery must not turn the entire document complete");
  });
  cases.run("duplicate relation aliases invalidate recovered declarations", [] {
    auto result = inspect(R"(module {
      relation R = r1cs("a"); relation R = air("b");
    })");
    diagnosticIs(result, "relation-duplicate-alias");
    require(!result.recoverable && result.relations.size() == 2,
            "invalid declarations stay inspectable without authorizing loads");
  });
  cases.run("unsupported relation family is a pure declaration refusal", [] {
    auto result = inspect(R"(module { relation R = future("a"); })");
    diagnosticIs(result, "relation-import-family");
    require(!result.recoverable, "unsupported family is not loadable");
  });
  cases.run("duplicate child modules", [] {
    auto result = inspect("module { mod child; mod child; }");
    diagnosticIs(result, "project-module-duplicate");
    require(!result.recoverable, "duplicate child is not loadable");
  });
  cases.run("module name length boundary", [] {
    require(inspect("module { mod " + std::string(128, 'a') + "; }").complete,
            "128-byte logical name is accepted");
    auto result = inspect("module { mod " + std::string(129, 'a') + "; }");
    diagnosticIs(result, "project-module-name");
    require(!result.recoverable, "oversized module name is not loadable");
  });
  cases.run("duplicate library dependency aliases", [] {
    const std::string declaration =
        "dependency dep = library(namespace=\"x\", name=\"y\", "
        "version=\"1\", resolution=\"r\");";
    auto result = inspect("module {" + declaration + declaration + "}");
    diagnosticIs(result, "source-dependency-duplicate");
    require(!result.recoverable, "duplicate dependency is not loadable");
  });
  cases.run("multiple root identities", [] {
    const std::string declaration = "library(namespace=\"x\", name=\"y\", "
                                    "version=\"1\", resolution=\"r\");";
    auto result = inspect("module {" + declaration + declaration + "}");
    diagnosticIs(result, "source-library-identity");
    require(!result.recoverable, "multiple root identities are not loadable");
  });
  cases.run("module profile classification", [] {
    auto result = inspect("module example {}");
    require(result.complete && result.form == SourceForm::Module &&
                result.profile == "example",
            "profile spelling is retained without semantic profile lookup");
  });
  cases.run("carrier classification", [] {
    auto result = inspect("carrier module {}");
    require(result.complete && result.form == SourceForm::CarrierModule,
            "carrier is distinct from an authored project module");
  });
  cases.run("construction classification", [] {
    auto result = inspect("construction main { producer P; validator V; "
                          "random R at (); accept 0; suite S; }");
    require(result.complete && result.form == SourceForm::Construction &&
                result.modules.empty() && result.relations.empty(),
            "construction classification needs no name resolution");
  });
  cases.run("unrecognized document has no recoverable declarations", [] {
    auto result = inspect("not a document");
    diagnosticIs(result, "source-syntax");
    require(result.form == SourceForm::Unknown && !result.recoverable,
            "unknown input cannot authorize dependency discovery");
  });
  cases.run("lexical failure has no recoverable declarations", [] {
    auto result = inspect("module { mod child; /* unterminated");
    require(!result.complete && !result.recoverable && result.modules.empty() &&
                !result.diagnostics.empty() &&
                result.diagnostics.front().location->file == 7,
            "lexical refusal is owned and never guessed by text scanning");
  });
  cases.run("source byte budget precedes inspection", [] {
    auto result = inspect(std::string(ProjectInput::maxSourceBytes + 1, ' '));
    diagnosticIs(result, "source-limit");
    require(!result.recoverable, "oversized source is not recoverable");
  });
  return cases.result();
}
