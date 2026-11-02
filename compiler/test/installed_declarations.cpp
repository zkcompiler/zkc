#include "../lib/Language/Internal.h"
#include "support/NativeCases.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace zkc::language;
using namespace zkc::language::detail;
using zkc::test::require;
using zkc::test::take;
namespace {
std::string spelling(const SyntaxType &type) {
  std::string result = std::to_string(unsigned(type.kind)) + ":" + type.name;
  for (const auto &argument : type.arguments)
    result += "(" + spelling(argument) + ")";
  return result;
}
/// Everything the checker reads from an installed declaration, without spans.
std::string summary(const SyntaxDeclaration &module) {
  std::string result;
  raw_string_ostream out(result);
  out << module.name << '\n';
  for (const auto &d : module.members) {
    out << unsigned(d.kind) << ' ' << d.name << " public=" << d.isPublic << '/'
        << d.explicitPublic << " primitive=" << d.primitive.value_or("-")
        << " abstract=" << d.abstract << " members=" << d.members.size()
        << " requirements=" << d.requirements.size() << '\n';
    for (const auto &p : d.parameters)
      out << "  static " << p.name << ':' << spelling(p.constraint)
          << " copy=" << p.permissions.copy << " drop=" << p.permissions.drop
          << '\n';
    for (const auto &p : d.inputs)
      out << "  input " << p.name << ':' << spelling(p.type) << '\n';
    for (const auto &slot : d.inputOrder)
      out << "  slot " << unsigned(slot.kind) << ':' << slot.index << '\n';
    for (const auto &p : d.outputs)
      out << "  output " << p.name << ':' << spelling(p.type) << '\n';
  }
  for (const auto &o : module.operators) {
    out << "operator " << o.symbol << " = " << spelling(o.target)
        << " public=" << o.isPublic << " explicit=" << o.explicitNotation;
    if (o.notation)
      out << " position=" << unsigned(o.notation->position)
          << " association=" << unsigned(o.notation->association)
          << " arity=" << o.notation->arity
          << " precedence=" << o.notation->precedence
          << " symbol=" << o.notation->symbol;
    out << '\n';
  }
  return result;
}
SyntaxDeclaration parsed(StringRef module, StringRef path) {
  auto file = take(errorOrToExpected(MemoryBuffer::getFile(path)));
  SourceBuffer source{module.str(), file->getBuffer().str(), path.str(),
                      SourceOrigin::Installation};
  Limits limits;
  Work work{limits};
  std::vector<Token> tokens;
  if (auto error = lex(source, SourceId{0}, work, tokens))
    throw std::runtime_error(toString(std::move(error)));
  return take(parse(source, SourceId{0}, tokens, work));
}
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
  for (const auto &installed :
       {std::pair<StringRef, StringRef>{"zkc::prelude", ZKC_INSTALLED_PRELUDE},
        {"zkc::records", ZKC_INSTALLED_RECORDS}})
    cases.run("catalog rows read as the embedded source: " +
                  installed.first.str(),
              [module = installed.first, path = installed.second] {
                auto expected = summary(parsed(module, path));
                auto actual = summary(read(module));
                if (expected != actual)
                  throw std::runtime_error("embedded:\n" + expected +
                                           "catalog:\n" + actual);
              });
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
