#include "support/NativeCases.h"
#include "zkc/Frontend/Analysis.h"
#include "zkc/Frontend/Compile.h"
#include "zkc/Frontend/Dependencies.h"
#include "zkc/Frontend/Loading.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/FileSystem.h"
#include <filesystem>
#include <fstream>

using namespace llvm;
using namespace zkc;
using namespace zkc::frontend;
using namespace zkc::test;
namespace fs = std::filesystem;

namespace {
const char *asset = R"(["zkc.relation.r1cs/1","bls12-381.fr","4","1","1",
  [[[["2","1"]],[["3","1"]],[["1","1"]]]]])";

std::string imports(size_t count, StringRef family = "r1cs",
                    StringRef path = "data.json") {
  std::string text = "module {";
  for (size_t i = 0; i < count; ++i)
    text += "relation R" + std::to_string(i) + " = " + family.str() + "(\"" +
            path.str() + "\");";
  return text + "}";
}

struct Directory {
  fs::path path;
  Directory() {
    SmallString<128> temporary;
    auto error = sys::fs::createUniqueDirectory("/tmp/zkc-loading", temporary);
    require(!error, "create isolated fixture directory");
    path = temporary.str().str();
  }
  ~Directory() {
    std::error_code ignored;
    fs::remove_all(path, ignored);
  }
  fs::path write(StringRef name, StringRef text) {
    auto target = path / name.str();
    fs::create_directories(target.parent_path());
    std::ofstream stream(target, std::ios::binary);
    stream.write(text.data(), text.size());
    stream.close();
    require(bool(stream), "write fixture");
    return target;
  }
  Input input(StringRef name, StringRef text) {
    return Input(text.str(), write(name, text).string());
  }
};

void noCallback(StringRef text, StringRef code) {
  unsigned calls = 0;
  auto result = loadProtocolDocument(
      text, "memory.pir", [&](StringRef, size_t) -> Expected<std::string> {
        ++calls;
        return zkc::error("unexpected-callback");
      });
  // Check the side effect even when the refusal itself is wrong.
  std::string error = result ? std::string() : toString(result.takeError());
  require(calls == 0, "invalid request must refuse before resolver invocation");
  require(namesIdentifier(error, code), "unexpected refusal: " + error);
}
} // namespace

int main() {
  Cases cases;
  for (
      const auto &text :
      {R"(module { relation R = r1cs("a"); relation R = r1cs("b"; })",
       R"(module { relation R = r1cs("a"); relation S = r1cs(unquoted); })",
       R"(module { relation R = r1cs("a"); fn Broken(x: bool) -> bool { let y = ; } })",
       R"(module { relation R = r1cs("a"); } trailing)",
       R"(module { relation R = r1cs("a");)"})
    cases.run("strict parse refusal: " + StringRef(text),
              [&] { noCallback(text, "source-syntax"); });

  cases.run("strict duplicate relation preflight", [] {
    noCallback(R"(module { relation R = r1cs("a"); relation R = air("b"); })",
               "relation-duplicate-alias");
  });
  cases.run("strict family preflight", [] {
    noCallback(
        R"(module { relation R = r1cs("a"); relation S = future("b"); })",
        "relation-import-family");
  });
  cases.run("strict child name preflight", [] {
    noCallback("module { relation R = air(\"a\"); mod " +
                   std::string(129, 'a') + "; }",
               "project-module-name");
  });
  cases.run("strict dependency count preflight", [] {
    noCallback(imports(relation::DependencyLimits::count + 1),
               "relation-dependency-limit");
  });
  cases.run("strict source byte limit", [] {
    noCallback(std::string(ProjectInput::maxSourceBytes + 1, ' '),
               "source-limit");
  });
  for (const std::string &path : std::vector<std::string>{
           "", "/absolute", "../outside", "a/../outside", "back\\slash",
           std::string("nul\0suffix", 10), std::string(4097, 'a')}) {
    cases.run("portable request preflight: " + path, [&] {
      const auto text = "module { relation First = r1cs(\"missing.json\"); "
                        "relation Bad = air(" +
                        printJson(json::Value(path)) + "); }";
      noCallback(text, "relation-asset-path");
      Directory directory;
      refuses(captureProject(directory.input("app.pir", text)),
              "relation-asset-path");
    });
  }
  for (const std::string family : {"r1cs", "air"}) {
    cases.run("family callback bound: " + family, [&] {
      unsigned calls = 0;
      size_t maximum = 0;
      auto result = loadProtocolDocument(
          imports(1, family), "memory.pir",
          [&](StringRef path, size_t limit) -> Expected<std::string> {
            ++calls;
            maximum = limit;
            require(path == "data.json", "original relative request");
            return zkc::error("resolver-refusal");
          });
      refuses(std::move(result), "resolver-refusal");
      require(calls == 1 &&
                  maximum == (family == "air" ? relation::AIRLimits::bytes
                                              : relation::Limits::bytes),
              "family budget reaches the resolver unchanged");
    });
  }
  cases.run("resolver result is bounded before later calls", [] {
    unsigned calls = 0;
    auto result = loadProtocolDocument(
        imports(2, "air"), "memory.pir",
        [&](StringRef, size_t maximum) -> Expected<std::string> {
          ++calls;
          return std::string(maximum + 1, ' ');
        });
    refuses(std::move(result), "relation-dependency-limit");
    require(calls == 1, "oversized bytes prevent the next resolver call");
  });
  cases.run("aggregate bytes stop before an exhausted callback", [] {
    unsigned calls = 0;
    auto count = relation::DependencyLimits::bytes / relation::AIRLimits::bytes;
    auto result = loadProtocolDocument(
        imports(count + 1, "air"), "memory.pir",
        [&](StringRef, size_t maximum) -> Expected<std::string> {
          ++calls;
          require(maximum == relation::AIRLimits::bytes,
                  "never issue a zero-budget callback");
          return std::string(maximum, ' ');
        });
    refuses(std::move(result), "relation-dependency-limit");
    require(calls == count,
            "every alias charges bytes even for repeated paths");
  });
  cases.run("callback loading remains independent of the filesystem", [] {
    unsigned calls = 0;
    auto document = take(
        loadProtocolDocument(imports(1), "/absent/project/app.pir",
                             [&](StringRef, size_t) -> Expected<std::string> {
                               ++calls;
                               return std::string(asset);
                             }));
    require(calls == 1 && document.module() &&
                document.module()->relations.size() == 1,
            "explicit callback owns memory-only dependency bytes");
    auto encoded = source::encode(document.root());
    auto roundtrip = take(
        loadProtocolDocument(printJson(encoded), "snapshot.json",
                             [&](StringRef, size_t) -> Expected<std::string> {
                               ++calls;
                               return zkc::error("unexpected-callback");
                             }));
    require(calls == 1 && source::encode(roundtrip.root()) == encoded,
            "portable snapshots never resolve external paths");
  });
  cases.run("recovering capture keeps safe imports and child modules", [] {
    Directory directory;
    directory.write("data.json", asset);
    directory.write("child.pir",
                    "module { pub fn Keep(x: bool) -> bool { return x; } }");
    auto input = directory.input("app.pir", R"(module {
      relation R = r1cs("data.json");
      relation R = r1cs("never-read.json";
      mod child;
      fn Good(x: bool) -> bool { return x; }
    })");
    auto project = take(captureProject(input));
    require(project.libraries().front().sources.size() == 2 &&
                project.assets().size() == 1 &&
                project.assets().front().file == 0,
            "capture follows only the parser's safe recovered subset");
    auto analysis = analyzeProject(project);
    require(!analysis.complete(),
            "recovered capture cannot authorize compilation");
    refuses(compileProject(project), "source-syntax");
  });
  cases.run("capture duplicate alias precedes missing assets", [] {
    Directory directory;
    refuses(captureProject(directory.input("app.pir", R"(module {
      relation R = r1cs("absent"); relation R = air("also-absent");
    })")),
            "relation-duplicate-alias");
  });
  cases.run("capture family refusal precedes missing assets", [] {
    Directory directory;
    refuses(captureProject(directory.input("app.pir", R"(module {
      relation R = r1cs("absent"); relation S = future("also-absent");
    })")),
            "relation-import-family");
  });
  cases.run("capture count preflight precedes missing assets", [] {
    Directory directory;
    refuses(captureProject(directory.input(
                "app.pir", imports(relation::DependencyLimits::count + 1))),
            "relation-dependency-limit");
  });
  cases.run("capture byte accounting includes repeated paths", [] {
    Directory directory;
    auto data = directory.write("large.json", "");
    fs::resize_file(data, relation::AIRLimits::bytes);
    auto count = relation::DependencyLimits::bytes / relation::AIRLimits::bytes;
    refuses(captureProject(directory.input(
                "app.pir", imports(count + 1, "air", "large.json"))),
            "byte-limit");
  });
  cases.run("file family byte limit", [] {
    Directory directory;
    auto data = directory.write("large.json", "");
    fs::resize_file(data, relation::AIRLimits::bytes + 1);
    auto input = directory.input("app.pir", imports(1, "air", "large.json"));
    refuses(captureProject(input), "byte-limit");
    refuses(loadProtocolFile(input), "byte-limit");
  });
  cases.run("nested modules retain root-relative paths and file IDs", [] {
    Directory directory;
    directory.write("outer.pir", "module { mod inner; }");
    directory.write("outer/inner.pir", imports(1));
    directory.write("outer/data.json", asset);
    directory.write("inner.pir", "invalid decoy");
    auto project = take(
        captureProject(directory.input("app.pir", "module { mod outer; }")));
    const auto &sources = project.libraries().front().sources;
    require(
        sources.size() == 3 &&
            sources[2].module == std::vector<std::string>({"outer", "inner"}) &&
            project.assets().size() == 1 && project.assets().front().file == 2,
        "logical paths and declaring file identity remain distinct");
  });
  for (const std::string metadata :
       {"library(namespace=\"x\", name=\"y\", version=\"1\", "
        "resolution=\"r\");",
        "dependency d = library(namespace=\"x\", name=\"y\", version=\"1\", "
        "resolution=\"r\");"}) {
    cases.run("child cannot own root declarations: " + metadata, [&] {
      Directory directory;
      directory.write("child.pir", "module {" + metadata +
                                       "relation R = air(\"never-read\"); }");
      refuses(
          captureProject(directory.input("app.pir", "module { mod child; }")),
          "project-library-root");
    });
  }
  cases.run("child construction is not a module root", [] {
    Directory directory;
    directory.write("child.pir", "construction main { producer P; validator V; "
                                 "random R at (); accept 0; suite S; }");
    refuses(captureProject(directory.input("app.pir", "module { mod child; }")),
            "project-module-root");
  });
  cases.run("child diagnostic preserves file and spelling", [] {
    Directory directory;
    auto child = directory.write("child.pir", "module { mod x; mod x; }");
    auto project =
        captureProject(directory.input("app.pir", "module { mod child; }"));
    require(!project, "duplicate child declarations refuse");
    bool located = false;
    handleAllErrors(
        project.takeError(),
        [&](const SourceDiagnostic &error) {
          located = error.code == "project-module-duplicate" &&
                    error.location.file == 1 &&
                    error.rendered.find(child.string()) != std::string::npos;
        },
        [&](const ErrorInfoBase &) {});
    require(located,
            "child diagnostic uses the child input and project file ID");
  });
  cases.run("memory labels never supply a filesystem base", [] {
    Directory directory;
    auto path = directory.write("app.pir", "module {}");
    auto input = Input::withoutFile("module {}", path.string());
    require(inspectDependencies(input).complete,
            "pure inspection accepts memory input");
    refuses(captureProject(input), "project-source-base");
    refuses(loadProtocolFile(input), "relation-asset-base");
    auto project = take(ProjectInput::capture({{{{{}, input}}}}));
    take(compileProject(project));
  });
  cases.run("a file named stdin retains physical file identity", [] {
    Directory directory;
    auto project =
        take(captureProject(directory.input("<stdin>", "module {}")));
    require(project.file(0) && project.file(0)->file(),
            "input kind governs file identity");
  });
  cases.run("all explicit roots seed the physical cache", [] {
    Directory directory;
    auto path = directory.write("child.pir", "disk bytes must not be reopened");
    Input child("module {}", path.string());
    auto project = take(captureProject(
        directory.input("app.pir", "module { mod child; }"), {child}));
    require(project.libraries().size() == 2 &&
                project.libraries()[0].sources[1].input.text() == "module {}" &&
                project.libraries()[1].sources[0].input.text() == "module {}",
            "explicit snapshots win over later physical reads");
  });
  cases.run("conflicting snapshots of one physical root refuse", [] {
    Directory directory;
    auto first = directory.input("app.pir", "module {}");
    auto alias = directory.path / "alias.pir";
    fs::create_symlink(directory.path / "app.pir", alias);
    Input second("module { mod child; }", alias.string());
    refuses(captureProject(first, {second}), "project-source-conflict");
  });
  cases.run("module symlink escape refuses", [] {
    Directory directory;
    auto outside = directory.write("outside.pir", "module {}");
    auto input = directory.input("inside/app.pir", "module { mod child; }");
    fs::create_symlink(outside, directory.path / "inside/child.pir");
    refuses(captureProject(input), "project-source-path");
  });
  cases.run("asset symlink escape refuses in both file loaders", [] {
    Directory directory;
    auto outside = directory.write("outside.json", asset);
    auto input = directory.input("inside/app.pir", imports(1));
    fs::create_symlink(outside, directory.path / "inside/data.json");
    refuses(captureProject(input), "relation-asset-path");
    refuses(loadProtocolFile(input), "relation-asset-path");
  });
  cases.run("physical module cycle refuses", [] {
    Directory directory;
    auto input = directory.input("app.pir", "module { mod child; }");
    fs::create_symlink(directory.path / "app.pir",
                       directory.path / "child.pir");
    refuses(captureProject(input), "project-module-cycle");
  });
  cases.run("source count refuses before the absent extra child", [] {
    Directory directory;
    std::string text = "module {";
    for (size_t i = 0; i < ProjectInput::maxSources; ++i) {
      auto name = "m" + std::to_string(i);
      text += "mod " + name + ";";
      if (i + 1 < ProjectInput::maxSources)
        directory.write(name + ".pir", "module {}");
    }
    refuses(captureProject(directory.input("app.pir", text + "}")),
            "project-source-limit");
  });
  cases.run("programmatic project admission remains independent", [] {
    const auto text =
        R"(module { relation R = r1cs("a"); relation R = r1cs("b"); })";
    auto project =
        take(ProjectInput::capture({{{{{}, Input::withoutFile(text)}}}},
                                   {{0, "a", asset}, {0, "b", asset}}));
    refuses(compileProject(project), "relation-duplicate-alias");
  });
  cases.run("programmatic unsupported family remains independently refused",
            [] {
              auto project = take(ProjectInput::capture(
                  {{{{{},
                      Input::withoutFile(
                          R"(module { relation R = future("a"); })")}}}},
                  {{0, "a", asset}}));
              refuses(compileProject(project), "relation-import-family");
            });
  return cases.result();
}
