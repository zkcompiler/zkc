#include "zkc/Target/Selection.h"
#include "zkc/Contracts/Implementations.h"
#include "zkc/Support/Json.h"
#include <limits>
#include <set>
#include <tuple>
namespace zkc::target {
namespace {
constexpr unsigned selectionLimit = 2048;
llvm::Expected<llvm::json::Value> parseSelections(llvm::StringRef text) {
  return parseNaturalJson(text, 1024 * 1024, 4, "binding-selection-option",
                          "binding-selection-limit");
}
bool selectionName(llvm::StringRef value) {
  return !value.empty() && value.size() <= 4096;
}
} // namespace
llvm::Expected<protocol::Assignments>
parseImplementationSelections(llvm::StringRef text) {
  auto value = parseSelections(text);
  if (!value)
    return value.takeError();
  auto *rows = value->getAsArray();
  if (!rows || rows->size() > selectionLimit)
    return error("binding-selection-option");
  protocol::Assignments result;
  std::set<std::string> seen;
  for (const auto &row : *rows) {
    auto *pair = row.getAsArray();
    if (!pair || pair->size() != 2)
      return error("binding-selection-option");
    auto name = (*pair)[0].getAsString(),
         implementation = (*pair)[1].getAsString();
    if (!name || !implementation || !selectionName(*name) ||
        !selectionName(*implementation) || !seen.insert(name->str()).second)
      return error("binding-selection-option");
    result.emplace_back(name->str(), implementation->str());
  }
  return result;
}
std::string printImplementationSelections(const protocol::Assignments &values) {
  llvm::json::Array rows;
  for (const auto &[name, implementation] : values)
    rows.push_back(llvm::json::Array{name, implementation});
  return printJson(std::move(rows));
}
llvm::Expected<std::vector<FunctionPortSelection>>
parseFunctionPortSelections(llvm::StringRef text) {
  auto value = parseSelections(text);
  if (!value)
    return value.takeError();
  auto *rows = value->getAsArray();
  if (!rows || rows->size() > selectionLimit)
    return error("binding-selection-option");
  std::vector<FunctionPortSelection> result;
  std::set<std::tuple<std::string, bool, unsigned>> seen;
  for (const auto &row : *rows) {
    auto *record = row.getAsObject();
    if (!record || record->size() != 4)
      return error("binding-selection-option");
    auto name = record->getString("function"), type = record->getString("type");
    auto output = record->getBoolean("output");
    auto port = record->getInteger("port");
    if (!name || !type || !output || !port || !selectionName(*name) ||
        type->empty() || type->size() > 65536 || *port < 0 ||
        uint64_t(*port) > std::numeric_limits<unsigned>::max() ||
        !seen.emplace(name->str(), *output, unsigned(*port)).second)
      return error("binding-selection-option");
    result.push_back({name->str(), *output, unsigned(*port), type->str()});
  }
  return result;
}
std::string
printFunctionPortSelections(llvm::ArrayRef<FunctionPortSelection> values) {
  llvm::json::Array rows;
  for (const auto &value : values)
    rows.push_back(llvm::json::Object{{"function", value.function},
                                      {"output", value.output},
                                      {"port", value.port},
                                      {"type", value.physicalType}});
  return printJson(std::move(rows));
}

llvm::Expected<ImplementationChoice>
selectImplementation(NativeBindingApplication application,
                     std::optional<llvm::StringRef> requested,
                     const CpuTarget &cpuTarget) {
  const bool fixed =
      requested.has_value() || !application.implementation.empty();
  if (requested) {
    if (!application.implementation.empty() &&
        application.implementation != *requested)
      return error("binding-selection-conflict");
    if (requested->empty())
      return error("binding-implementation");
    application.implementation = requested->str();
  } else if (application.implementation.empty()) {
    auto selected = defaultNativeImplementation(application);
    if (!selected)
      return selected.takeError();
    application.implementation = std::move(*selected);
  }
  auto descriptor = protocol::installedImplementations().find(
      application.contract, application.implementation);
  if (!fixed && descriptor && descriptor->requiresExplicitSelection)
    return error("binding-implementation");
  if (descriptor &&
      descriptor->family != protocol::ImplementationDescriptor::Family::Exact &&
      !application.valueType) {
    auto logical = resolveNativeApplication(application, false);
    if (!logical)
      return logical.takeError();
    if (auto e = cpuTarget.checkNativeImplementation(application))
      return e;
  } else {
    auto installed = resolveNativeApplication(application);
    if (!installed)
      return installed.takeError();
    if (auto e = cpuTarget.checkNativeApplication(application))
      return e;
  }
  return ImplementationChoice{std::move(application), fixed};
}
} // namespace zkc::target
