#ifndef ZKC_TEST_SUPPORT_EXTERNAL_SUPPLY_H
#define ZKC_TEST_SUPPORT_EXTERNAL_SUPPLY_H

#include "zkc/Language/Layout.h"
#include "zkc/Language/Types.h"
#include <stdexcept>
#include <string>
#include <vector>

namespace zkc::test {
/// Source closure publishes exact schemas and never judges external supply:
/// the SDK's Entry admission owns that judgment for the selected operation and
/// supply mode. These are the published coordinates at which fresh external
/// decoding needs an authority that the schema withholds: a missing
/// constructor, a private field, sealing, custody or a logical handle. A
/// sealed, custody or handle node hides its interior, as does a private field.
/// A logical record is never constructed whole; its components are supplied
/// separately. Alternative payloads and zero-extent element templates are
/// included.
template <typename Schema, typename Child, typename Hidden, typename Logical>
void withheldSupply(const Schema &schema, const std::string &at,
                    std::vector<std::string> &result, Child child,
                    Hidden hidden, Logical logical) {
  if (hidden(schema)) {
    result.push_back(at);
    return;
  }
  if (!schema.constructible && !logical(schema))
    result.push_back(at);
  auto visit = [&](const auto &field, const std::string &path) {
    if (!field.isPublic)
      result.push_back(path);
    else
      withheldSupply(child(field), path, result, child, hidden, logical);
  };
  for (const auto &field : schema.fields)
    visit(field, at + "." + field.name);
  for (const auto &alternative : schema.alternatives)
    for (const auto &field : alternative.fields)
      visit(field, at + "." + alternative.name + "." + field.name);
  if (schema.element && schema.fields.empty())
    withheldSupply(*schema.element, at + ".element", result, child, hidden,
                   logical);
}
/// Compare withheld coordinates, naming the actual ones on a mismatch.
inline void requireWithheld(const std::vector<std::string> &actual,
                            const std::vector<std::string> &expected,
                            const std::string &message) {
  if (actual == expected)
    return;
  std::string found;
  for (const auto &coordinate : actual)
    found += (found.empty() ? "" : ", ") + coordinate;
  throw std::runtime_error(message + ": [" + found + "]");
}
/// The compiler's schema for a closed port, before interface publication.
inline std::vector<std::string> withheldSupply(const language::Layout &schema,
                                               const std::string &name) {
  std::vector<std::string> result;
  withheldSupply(
      schema, name, result,
      [](const language::LayoutField &field) -> const language::Layout & {
        return *field.layout;
      },
      [](const language::Layout &node) {
        return node.sealed || node.custody ||
               language::isOracleHandle(node.type);
      },
      [](const language::Layout &node) {
        return node.type.kind == language::Type::Kind::LogicalRecord;
      });
  return result;
}
} // namespace zkc::test

#endif
