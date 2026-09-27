#include "TypeBindings.h"
#include "Contributions.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TableGen/Error.h"
#include "llvm/TableGen/Record.h"
#include <map>
#include <set>
#include <string>
#include <vector>

using namespace llvm;
namespace {
cl::opt<std::string>
    selectedOwner("type-binding-owner",
                  cl::desc("Emit one adapter owner instead of assembly"),
                  cl::init(""));

bool identifier(StringRef value) {
  if (value.empty() || !(isAlpha(value.front()) || value.front() == '_'))
    return false;
  return llvm::all_of(value, [](char c) { return isAlnum(c) || c == '_'; });
}
bool qualifiedName(StringRef value, bool absolute) {
  if (absolute && !value.consume_front("::"))
    return false;
  SmallVector<StringRef> parts;
  value.split(parts, "::");
  return llvm::all_of(parts, identifier);
}
std::string nativeHead(const Record *type) {
  auto ns = type->getValueAsDef("dialect")->getValueAsString("cppNamespace");
  // Native TypeDef class names inherit their namespace from the dialect.
  std::string result = ns.str();
  if (!StringRef(result).starts_with("::"))
    result = "::" + result;
  return result + "::" + type->getValueAsString("cppClassName").str();
}
void quote(raw_ostream &os, StringRef value) {
  os << '"';
  os.write_escaped(value);
  os << '"';
}
struct Binding {
  const Record *record;
  const Record *logical;
  const Record *owner;
  std::string key;
  bool direct;
};
} // namespace

bool emitTypeBindings(raw_ostream &os, const RecordKeeper &records) {
  // Native-only fragments may not smuggle logical declarations outside the
  // neutral installation's ownership and dependency checks.
  const DeclarationOrder order(records);
  const auto logicalTypes = order.sort("ZKC_Type");
  // Special bindings describe pre-existing non-generic carrier syntax
  // (variant), not neutral ZKC_Declaration records or new source type
  // constructors.
  const auto specialTypes = records.getAllDerivedDefinitions("ZKC_SpecialType");
  std::vector<Binding> bindings;
  std::map<const Record *, const Record *> coverage;
  std::map<std::string, const Record *> keys;
  std::map<std::string, const Record *> directHeads;
  std::map<std::string, const Record *> customHeads;
  std::set<std::string> functions;
  auto owners = records.getAllDerivedDefinitions("ZKC_TypeAdapterOwner");
  for (auto *owner : owners) {
    auto ns = owner->getValueAsString("cppNamespace");
    auto function = owner->getValueAsString("cppFunction");
    if (!qualifiedName(ns, false) || !identifier(function))
      PrintFatalError(owner, "invalid adapter owner C++ namespace or function");
    if (!functions.insert((ns + "::" + function).str()).second)
      PrintFatalError(owner, "duplicate adapter owner function");
  }
  auto collect = [&](const Record *record, bool special) {
    auto *logical =
        record->getValueAsDef(special ? "specialType" : "logicalType");
    if (!coverage.emplace(logical, record).second)
      PrintFatalError(record, "duplicate native binding decision");
    auto key = logical->getValueAsString("name").str();
    if (!keys.emplace(key, record).second)
      PrintFatalError(record, "duplicate native binding constructor: " + key);
    bool direct = record->isSubClassOf("ZKC_DirectBinding");
    bool custom = record->isSubClassOf("ZKC_CustomBinding");
    bool unavailable = record->isSubClassOf("ZKC_UnavailableBinding");
    if (!special &&
        unsigned(direct) + unsigned(custom) + unsigned(unavailable) != 1)
      PrintFatalError(
          record, "expected direct, custom or unavailable binding decision");
    if (unavailable) {
      if (record->getValueAsString("reason").trim().empty())
        PrintFatalError(record, "unavailable binding requires a reason");
      return;
    }
    auto *owner = record->getValueAsDef("owner");
    if (direct) {
      auto head = nativeHead(record->getValueAsDef("nativeType"));
      if (!qualifiedName(head, true))
        PrintFatalError(record, "invalid direct native head");
      if (!directHeads.emplace(head, record).second)
        PrintFatalError(record, "duplicate direct native head: " + head);
      if (record->getValueAsString("cppHelper").trim().empty())
        PrintFatalError(record, "direct binding requires a typed helper");
      for (auto *parameter : logical->getValueAsListOfDefs("parameters")) {
        auto kind = parameter->getValueAsDef("kind")->getValueAsString("name");
        if (kind != "Domain" && kind != "Type" && kind != "Nat")
          PrintFatalError(record, "unsupported direct logical parameter kind");
      }
    } else {
      auto heads = record->getValueAsListOfStrings("nativeHeads");
      if (heads.empty())
        PrintFatalError(record,
                        "custom binding requires declared native heads");
      std::set<std::string> seen;
      for (auto head : heads) {
        if (!qualifiedName(head, true) || !seen.insert(head.str()).second)
          PrintFatalError(record, "invalid or repeated custom native head");
        customHeads.emplace(head.str(), record);
      }
      if (record->getValueAsString("cppDecode").trim().empty() ||
          record->getValueAsString("cppEncode").trim().empty())
        PrintFatalError(record,
                        "custom binding requires decode and encode callbacks");
    }
    bindings.push_back({record, logical, owner, std::move(key), direct});
  };
  for (auto *record : records.getAllDerivedDefinitions("ZKC_TypeBinding"))
    collect(record, false);
  for (auto *record : records.getAllDerivedDefinitions("ZKC_SpecialBinding"))
    collect(record, true);
  for (const auto types :
       {ArrayRef<const Record *>(logicalTypes), specialTypes})
    for (auto *logical : types)
      if (!coverage.count(logical))
        PrintFatalError(logical, "missing native binding decision: " +
                                     logical->getValueAsString("name"));
  for (const auto &[head, record] : directHeads)
    if (customHeads.count(head))
      PrintFatalError(record, "direct/custom native head overlap: " + head);

  // Registration order is deterministic but not semantic dispatch priority.
  llvm::sort(bindings,
             [](const Binding &a, const Binding &b) { return a.key < b.key; });
  os << "// Generated native type bindings. Do not edit.\n";
  if (selectedOwner.empty()) {
    for (auto *owner : owners)
      os << "namespace " << owner->getValueAsString("cppNamespace")
         << " { ::llvm::ArrayRef<::zkc::protocol::type_adapters::TypeAdapter> "
         << owner->getValueAsString("cppFunction") << "(); }\n";
    os << "namespace zkc::protocol::type_adapters {\n"
          "llvm::ArrayRef<llvm::ArrayRef<TypeAdapter>> installedAdapters() {\n"
          "  static const std::array<llvm::ArrayRef<TypeAdapter>, "
       << owners.size() << "> tables = {{\n";
    for (auto *owner : owners)
      os << "    ::" << owner->getValueAsString("cppNamespace")
         << "::" << owner->getValueAsString("cppFunction") << "(),\n";
    os << "  }};\n  return tables;\n}\n} // namespace "
          "zkc::protocol::type_adapters\n";
    return false;
  }
  const Record *owner = nullptr;
  for (auto *candidate : owners)
    if (candidate->getName() == selectedOwner)
      owner = candidate;
  if (!owner)
    PrintFatalError("unknown type binding owner: " + selectedOwner);
  os << "namespace " << owner->getValueAsString("cppNamespace") << " {\n";
  for (const auto &binding : bindings) {
    if (binding.owner != owner || !binding.direct)
      continue;
    auto helper = binding.record->getValueAsString("cppHelper");
    os << "static_assert(std::is_same_v<typename " << helper << "::Native, "
       << nativeHead(binding.record->getValueAsDef("nativeType"))
       << ">, \"native binding helper type mismatch\");\n"
          "static_assert(std::is_same_v<typename "
       << helper
       << "::Parameters, ::zkc::protocol::type_adapters::ParameterKinds<";
    bool first = true;
    for (auto *parameter :
         binding.logical->getValueAsListOfDefs("parameters")) {
      if (!first)
        os << ", ";
      first = false;
      os << "::zkc::protocol::type_adapters::ParameterKind::"
         << parameter->getValueAsDef("kind")->getValueAsString("name");
    }
    os << ">>, \"native binding helper parameter kinds mismatch\");\n";
  }
  size_t count = llvm::count_if(
      bindings, [&](const Binding &binding) { return binding.owner == owner; });
  os << "::llvm::ArrayRef<::zkc::protocol::type_adapters::TypeAdapter> "
     << owner->getValueAsString("cppFunction")
     << "() {\n"
        "  static constexpr "
        "std::array<::zkc::protocol::type_adapters::TypeAdapter, "
     << count << "> adapters = {{\n";
  for (const auto &binding : bindings) {
    if (binding.owner != owner)
      continue;
    os << "    {";
    quote(os, binding.key);
    if (binding.direct) {
      auto helper = binding.record->getValueAsString("cppHelper");
      os << ", " << helper << "::decode, " << helper << "::encode";
    } else {
      os << ", " << binding.record->getValueAsString("cppDecode") << ", "
         << binding.record->getValueAsString("cppEncode");
    }
    os << "},\n";
  }
  os << "  }};\n  return adapters;\n}\n} // namespace "
     << owner->getValueAsString("cppNamespace") << "\n";
  return false;
}
