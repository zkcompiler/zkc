#include "../lib/Language/Internal.h"
#include "support/NativeCases.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace zkc::language;
using namespace zkc::language::detail;
using zkc::test::require;
using zkc::test::take;
namespace {
SyntaxDeclaration read(StringRef module,
                       ArrayRef<zkc::protocol::FrontendDeclaration> rows =
                           zkc::protocol::frontendDeclarations(),
                       ArrayRef<zkc::protocol::FrontendNotation> notations =
                           zkc::protocol::frontendNotations()) {
  SourceBuffer source{module.str(), "",
                      "<installation>/catalog/" + module.str(),
                      SourceOrigin::Installation};
  Limits limits;
  Work work{limits};
  return take(readInstalledModule(source, SourceId{0}, work, rows, notations));
}
void refuses(StringRef module,
             ArrayRef<zkc::protocol::FrontendDeclaration> rows,
             ArrayRef<zkc::protocol::FrontendNotation> notations,
             StringRef reason) {
  SourceBuffer source{module.str(), "",
                      "<installation>/catalog/" + module.str(),
                      SourceOrigin::Installation};
  Limits limits;
  Work work{limits};
  auto result = readInstalledModule(source, SourceId{0}, work, rows, notations);
  require(!result, "reader accepted " + reason.str());
  auto message = toString(result.takeError());
  require(StringRef(message).starts_with("source.installation"),
          "unexpected refusal: " + message);
}
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run("the prelude installs its functions, interface and notations", [] {
    auto prelude = read("zkc::prelude");
    require(prelude.members.size() == 13 && prelude.operators.size() == 12 &&
                read("zkc::records").members.size() == 3,
            "installed inventory differs");
  });
  cases.run("installed modules are the declaration owners", [] {
    require(installedModules() ==
                std::vector<std::string>{"zkc::prelude", "zkc::records"},
            "installed module inventory differs");
  });
  cases.run("rows the frontend cannot express refuse", [] {
    std::vector<zkc::protocol::FrontendDeclaration> rows(
        zkc::protocol::frontendDeclarations().begin(),
        zkc::protocol::frontendDeclarations().end());
    std::vector<zkc::protocol::FrontendNotation> notations(
        zkc::protocol::frontendNotations().begin(),
        zkc::protocol::frontendNotations().end());
    auto absent = rows;
    for (auto &row : absent)
      if (row.name == "field_add")
        row.inputs[0].type.index = 3;
    refuses("zkc::prelude", absent, notations, "an absent static");
    auto symbol = notations;
    symbol.front().symbol = "plus";
    refuses("zkc::prelude", rows, symbol, "a word as an operator");
    auto fixity = notations;
    fixity.front().fixity = "right";
    fixity.front().precedence = 65;
    refuses("zkc::prelude", rows, fixity, "changed ASCII operator syntax");
    refuses("zkc::elsewhere", rows, notations, "an empty installed module");
  });
  return cases.result();
}
