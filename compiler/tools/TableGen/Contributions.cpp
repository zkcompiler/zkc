#include "Contributions.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TableGen/Error.h"
#include "llvm/TableGen/Record.h"
#include <functional>
#include <set>
#include <string>

using namespace llvm;
namespace {
std::string semanticKey(const Record *r) {
  std::string key;
  raw_string_ostream os(key);
  auto part = [&](StringRef value) { os << value.size() << ':' << value; };
  auto reference = [&](StringRef field) {
    part(r->getValueAsDef(field)->getValueAsString("name"));
  };
  if (r->getValue("module")) {
    part(r->getValueAsString("module"));
    part(r->getValueAsString("name"));
  } else if (r->isSubClassOf("ZKC_AssociatedType")) {
    part(r->getValueAsDef("owner")->getValueAsString("sort"));
    part(r->getValueAsString("member"));
    reference("constructor");
  } else if (r->isSubClassOf("ZKC_TypeFamilyCase")) {
    reference("family");
    reference("elementConstructor");
    reference("resultConstructor");
  } else if (r->isSubClassOf("ZKC_Implication")) {
    reference("premise");
    reference("conclusion");
  } else if (r->isSubClassOf("ZKC_Operator")) {
    part(r->getValueAsString("symbol"));
    for (const auto *operand : r->getValueAsListOfDefs("operands"))
      part(operand->getValueAsString("name"));
    reference("operation");
    for (auto index : r->getValueAsListOfInts("order"))
      part(std::to_string(index));
  } else if (r->isSubClassOf("ZKC_Member")) {
    const auto *owner = r->getValueAsDef("owner");
    part(owner->getValueAsDef("kind")->getValueAsString("name"));
    part(owner->getValueAsString("sort"));
    part(r->getValueAsString("name"));
  } else if (r->isSubClassOf("ZKC_Parameter")) {
    reference("kind");
    part(r->getValueAsString("sort"));
  } else {
    part(r->getValueAsString("name"));
  }
  return key;
}
} // namespace

DeclarationOrder::DeclarationOrder(const RecordKeeper &records)
    : records(records) {
  if (!records.getClass("ZKC_Contribution"))
    return;
  const auto contributions =
      records.getAllDerivedDefinitions("ZKC_Contribution");
  if (contributions.empty())
    return;
  composed = true;
  std::map<std::string, const Record *> pending;
  for (const auto *contribution : contributions) {
    auto id = contribution->getValueAsString("identifier");
    if (id.empty() || !all_of(id, [](char c) {
          return isAlnum(c) || c == '_' || c == '-' || c == '.';
        }))
      PrintFatalError(contribution, "invalid contribution identifier");
    if (!pending.emplace(id.str(), contribution).second)
      PrintFatalError(contribution, "duplicate contribution identifier: " + id);
  }
  if (!pending.count("base"))
    PrintFatalError("composed declarations require the base contribution");
  for (const auto &[id, contribution] : pending) {
    const auto dependencies = contribution->getValueAsListOfStrings("requires");
    if (id == "base" && !dependencies.empty())
      PrintFatalError(contribution,
                      "base contribution cannot depend on an extension");
    for (auto dependency : dependencies)
      if (!pending.count(dependency.str()))
        PrintFatalError(contribution,
                        "missing contribution dependency: " + dependency);
  }
  std::set<std::string> installed;
  std::map<std::string, std::set<unsigned>> requirements;
  std::map<std::string, unsigned> positions;
  std::vector<std::set<unsigned>> accessible;
  unsigned index = 0;
  while (!pending.empty()) {
    auto next = pending.end();
    for (auto it = pending.begin(); it != pending.end(); ++it) {
      if (index == 0 && it->first != "base")
        continue;
      if (all_of(it->second->getValueAsListOfStrings("requires"),
                 [&](StringRef dependency) {
                   return installed.count(dependency.str());
                 })) {
        next = it;
        break;
      }
    }
    if (next == pending.end())
      PrintFatalError(pending.begin()->second,
                      "cyclic contribution dependencies");
    for (const auto *declaration :
         next->second->getValueAsListOfDefs("declarations"))
      if (!owners.emplace(declaration, index).second)
        PrintFatalError(declaration,
                        "declaration has multiple contribution owners");
    std::set<unsigned> dependencies{0, index};
    for (auto dependency : next->second->getValueAsListOfStrings("requires")) {
      dependencies.insert(positions.at(dependency.str()));
      const auto &inherited = requirements.at(dependency.str());
      dependencies.insert(inherited.begin(), inherited.end());
    }
    accessible.push_back(dependencies);
    requirements.emplace(next->first, std::move(dependencies));
    positions.emplace(next->first, index);
    installed.insert(next->first);
    pending.erase(next);
    ++index;
  }
  // Catch accidental cross-contribution use even if an include happened to
  // make the referenced declaration visible. Anonymous applications are
  // traversed, while named declarations form the ownership boundary.
  for (const auto &entry : owners) {
    const auto *declaration = entry.first;
    unsigned source = entry.second;
    std::set<const Record *> seen;
    std::function<void(const Init *)> inspect;
    std::function<void(const Record *)> visit = [&](const Record *record) {
      if (!seen.insert(record).second)
        return;
      auto found = owners.find(record);
      if (found != owners.end() && record != declaration) {
        if (!accessible[source].count(found->second))
          PrintFatalError(
              declaration,
              "reference requires an undeclared contribution dependency");
        return;
      }
      for (const auto &field : record->getValues())
        inspect(field.getValue());
    };
    inspect = [&](const Init *value) {
      if (const auto *reference = dyn_cast<DefInit>(value))
        visit(reference->getDef());
      else if (const auto *list = dyn_cast<ListInit>(value))
        for (const auto *element : list->getElements())
          inspect(element);
      else if (const auto *dag = dyn_cast<DagInit>(value)) {
        inspect(dag->getOperator());
        for (const auto *argument : dag->getArgs())
          inspect(argument);
      }
    };
    visit(declaration);
  }
}

std::vector<const Record *> DeclarationOrder::sort(StringRef category) const {
  std::vector<const Record *> result =
      records.getAllDerivedDefinitions(category);
  auto owner = [&](const Record *r) {
    auto found = owners.find(r);
    // Schema parameter constants precede composition and are not emitted rows.
    if (found == owners.end()) {
      if (composed && category != "ZKC_Parameter")
        PrintFatalError(r, "declaration has no contribution owner");
      return 0u;
    }
    return found->second;
  };
  auto ordinal = [](const Record *r) {
    return r->getValue("ordinal") ? r->getValueAsInt("ordinal") : int64_t(-1);
  };
  for (const auto *r : result)
    (void)owner(r);
  stable_sort(result, [&](const Record *a, const Record *b) {
    auto left = owner(a), right = owner(b);
    if (left != right)
      return left < right;
    // Preserve every base row's historic ordering. Extension records use
    // semantic keys, never anonymous TableGen names or author-chosen ordinals.
    return left == 0 ? ordinal(a) < ordinal(b)
                     : semanticKey(a) < semanticKey(b);
  });
  return result;
}
