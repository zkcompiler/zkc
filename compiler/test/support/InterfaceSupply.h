#ifndef ZKC_TEST_SUPPORT_INTERFACE_SUPPLY_H
#define ZKC_TEST_SUPPORT_INTERFACE_SUPPLY_H

#include "ExternalSupply.h"
#include "zkc/Compiler/LanguageInterface.h"

namespace zkc::test {
/// The same coordinates read from the decoded interface view.
inline std::vector<std::string>
withheldSupply(const language::InterfacePort &port) {
  std::vector<std::string> result;
  withheldSupply(
      *port.schema, port.name, result,
      [](const language::InterfaceField &field)
          -> const language::InterfaceSchema & { return *field.schema; },
      [](const language::InterfaceSchema &node) {
        return node.sealed || node.custody || node.oracle;
      },
      [](const language::InterfaceSchema &node) {
        return node.kind == language::Type::Kind::LogicalRecord;
      });
  return result;
}
/// Every withheld coordinate of the selected Protocol's input ports.
inline std::vector<std::string>
withheldSupply(const language::LanguageInterface &interface) {
  std::vector<std::string> result;
  for (const auto &port : interface.selectedProtocol().inputs) {
    auto withheld = withheldSupply(port);
    result.insert(result.end(), withheld.begin(), withheld.end());
  }
  return result;
}
} // namespace zkc::test
#endif
