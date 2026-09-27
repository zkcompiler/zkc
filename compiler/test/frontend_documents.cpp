#include "support/NativeCases.h"
#include "zkc/Frontend/Analysis.h"
#include "zkc/Frontend/Dependencies.h"
#include "zkc/Frontend/Loading.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Source/Codec.h"
#include "zkc/Support/Json.h"

using namespace llvm;
using namespace zkc;
using namespace zkc::frontend;
using namespace zkc::test;

int main() {
  Cases cases;
  cases.run("document classification does not require a valid body", [] {
    require(classifyDocument("[ malformed") == SourceForm::CommonJSON,
            "malformed JSON must remain JSON");
    require(
        classifyDocument(
            " // heading\n /* outer /* inner */ */ carrier /* x */ module {") ==
            SourceForm::CarrierModule,
        "comments cannot hide the carrier grammar");
    require(classifyDocument("/* heading */ construction Entry {") ==
                SourceForm::Construction,
            "construction has its own grammar");
    for (auto text : {"", "// comment", "fn carrier() {}", "carrier_module {}",
                      "r#carrier module {}", "/* unterminated", "/*x*/ ["})
      require(classifyDocument(text) == SourceForm::Module,
              "prefix lookalikes and invalid source stay with source reader");
  });
  cases.run("common inputs never create authored analysis", [] {
    for (auto text :
         {"carrier module { fn src_identity(x: bool) -> bool { return x; } }",
          "[\"zkc.protocol/1\",[],[],[],[],[]]"}) {
      auto analysis = analyzeProtocol(Input::withoutFile(text));
      require(!analysis.complete() && !analysis.resolutionComplete(),
              "common input is not source checked");
      require(analysis.diagnostics().size() == 1 &&
                  analysis.diagnostics()[0].code ==
                      "source-analysis-unsupported",
              "explicit unsupported-input judgment");
      require(analysis.declarations().empty(),
              "no invented source declarations");
      auto lowered = analysis.lower();
      require(!lowered, "unsupported analysis cannot lower");
      consumeError(lowered.takeError());
      auto dependencies = inspectDependencies(Input::withoutFile(text), 7);
      require(dependencies.complete && dependencies.modules.empty() &&
                  dependencies.relations.empty() &&
                  dependencies.libraries.empty(),
              "common documents have no authored dependencies");
      require(dependencies.location && dependencies.location->file == 7,
              "dependency query retains caller file coordinate");
    }
  });
  cases.run("carrier loading does not call the asset resolver", [] {
    bool called = false;
    auto load = [&](StringRef text) {
      return loadProtocolDocument(
          text, "<test>", [&](StringRef, size_t) -> Expected<std::string> {
            called = true;
            return zkc::error("unexpected-asset-read");
          });
    };
    auto valid =
        load("carrier module { fn identity(x: bool) -> bool { return x; } }");
    require(bool(valid), valid ? "" : toString(valid.takeError()));
    require(!called, "self-contained carrier never requests assets");
    auto invalid =
        load("carrier module { relation R = air(\"absent.json\"); }");
    require(!invalid, "carrier refuses authored relation imports");
    consumeError(invalid.takeError());
    require(!called, "rejected carrier never requests assets");
  });
  cases.run("direct carrier parsing retains its own byte budget", [] {
    std::string text = "carrier module { /*";
    text.append(1024 * 1024, 'x');
    text += "*/ }";
    auto document = parseProtocolDocument(text);
    require(!document, "direct API rejects overlarge carrier text");
    require(
        toString(document.takeError()).find("source-limit") !=
            std::string::npos,
        "direct reader owns source-limit independently of driver byte-limit");
  });
  cases.run(
      "formatting preserves raw names and comment-separated projections", [] {
        StringRef text = R"(
struct R { r#return: bool }
fn X(r: R) -> bool {
  // A keyword is a field name only through its raw spelling.
  return r /* receiver */ . /* field */ r#return;
}
)";
        auto formatted = formatProtocol(text);
        require(bool(formatted),
                formatted ? "" : toString(formatted.takeError()));
        for (auto spelling :
             {"r#return", "/* receiver */", "/* field */",
              "// A keyword is a field name only through its raw spelling."})
          require(StringRef(*formatted).contains(spelling),
                  "formatting retains exact names and comments");
        auto repeated = formatProtocol(*formatted);
        require(bool(repeated), repeated ? "" : toString(repeated.takeError()));
        require(*formatted == *repeated, "formatting is idempotent");
        auto original = parseProtocolDocument(text);
        auto reparsed = parseProtocolDocument(*formatted);
        require(bool(original), original ? "" : toString(original.takeError()));
        require(bool(reparsed), reparsed ? "" : toString(reparsed.takeError()));
        require(source::encode(original->root()) ==
                    source::encode(reparsed->root()),
                "formatting preserves elaborated records");
      });
  cases.run("line comments retain trailing whitespace and CRLF bytes", [] {
    for (StringRef text : {"// note  \n", "// note \t\r\n",
                           "carrier module { // note  \r\n }"}) {
      auto formatted = formatProtocol(text);
      require(bool(formatted),
              formatted ? "" : toString(formatted.takeError()));
      auto start = text.find("//");
      auto comment = text.slice(start, text.find('\n', start));
      require(StringRef(*formatted).contains(comment),
              "comment bytes are tokens, including trailing layout");
      auto repeated = formatProtocol(*formatted);
      require(bool(repeated), repeated ? "" : toString(repeated.takeError()));
      require(*repeated == *formatted, "comment formatting is idempotent");
    }
  });
  cases.run("captured projects cannot import common carriers", [] {
    auto root = Input::withoutFile("fn Id(x: bool) -> bool { return x; }");
    auto child = Input::withoutFile("carrier module { }");
    auto project = ProjectInput::capture({{{{{}, root}, {{"child"}, child}}}});
    require(bool(project), project ? "" : toString(project.takeError()));
    auto analysis = analyzeProject(*project);
    require(!analysis.complete() && analysis.diagnostics().size() == 1,
            "programmatic project input has the same common boundary");
    require(analysis.diagnostics()[0].location &&
                analysis.diagnostics()[0].location->file == 1,
            "diagnostic points to the common child");
  });
  return cases.result();
}
