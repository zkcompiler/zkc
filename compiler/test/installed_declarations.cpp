#include "../lib/Language/Internal.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Language/Builtins.h"
#include "zkc/Language/Types.h"
#include "llvm/ADT/STLExtras.h"
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
  cases.run("each frontend constructor row forms and spells its head", [] {
    // The rows own the spellings; the frontend gives each form its meaning.
    auto kind = take(builtinType("oracle.table", {Type(Type::Kind::Index)}));
    Type maximum(Type::Kind::Natural);
    maximum.dimension = Natural::constant(4);
    std::vector<Type::Kind> formed;
    for (const auto &row : zkc::protocol::frontendConstructors()) {
      std::vector<Type> arguments{kind};
      if (row.form ==
          zkc::protocol::FrontendConstructorForm::OracleHandleSequence)
        arguments.push_back(maximum);
      auto type = take(builtinType(row.name, arguments));
      require(isOracleHandle(type) && type.kind == logicalHeadKind(row.form),
              "row formed another head: " + row.name);
      require(oracleConstructor(type) == row.name &&
                  StringRef(spelling(type))
                      .starts_with("builtin(\"" + row.name + "\", "),
              "head is not spelled by its row: " + row.name);
      formed.push_back(type.kind);
    }
    llvm::sort(formed);
    require(formed == std::vector<Type::Kind>{Type::Kind::Oracle,
                                              Type::Kind::OracleSequence},
            "a logical handle has no frontend constructor row");
  });
  cases.run("a spelling no frontend constructor row names is not a head", [] {
    auto kind = take(builtinType("oracle.table", {Type(Type::Kind::Index)}));
    Type maximum(Type::Kind::Natural);
    maximum.dimension = Natural::constant(4);
    for (StringRef spelling :
         {"oracle_handle", "Oracle", "oracles", "oracle_sequence_handle"}) {
      require(!zkc::protocol::frontendConstructor(spelling),
              "unexpected frontend constructor row: " + spelling.str());
      for (const auto &arguments :
           {std::vector<Type>{kind}, std::vector<Type>{kind, maximum}}) {
        auto result = builtinType(spelling, arguments);
        require(!result, "spelling formed a head: " + spelling.str());
        consumeError(result.takeError());
      }
    }
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
