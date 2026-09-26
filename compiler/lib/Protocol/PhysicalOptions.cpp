#include "zkc/Protocol/PhysicalOptions.h"
#include "zkc/Source/Snapshot.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"
#include <set>

using namespace llvm;
namespace zkc::protocol {
namespace {
Error validate(const ImplementationSelection &selection) {
  const auto &snapshot = selection.sourceSnapshot;
  if (!snapshot.empty() &&
      (snapshot.size() != 64 || !all_of(snapshot, [](char c) {
         return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f');
       })))
    return error("binding-selection-snapshot");
  if (selection.choices.size() > 4096)
    return error("binding-selection-format");
  size_t bytes = 0;
  std::set<std::string> names;
  for (const auto &[name, implementation] : selection.choices) {
    if (implementation.empty())
      return error("binding-stage");
    for (const auto *value : {&name, &implementation}) {
      if (value->empty() || value->size() > 4096 ||
          bytes > 1024 * 1024 - value->size() || !json::isUTF8(*value) ||
          value->find('\0') != std::string::npos)
        return error("binding-selection-format");
      bytes += value->size();
    }
    if (!names.insert(name).second)
      return error("binding-duplicate-selection");
  }
  return Error::success();
}
} // namespace

Expected<ImplementationSelection>
decodeImplementationSelection(const json::Value &value) {
  ImplementationSelection selection;
  auto *choices = value.getAsArray();
  if (choices && choices->size() == 3 &&
      (*choices)[0].getAsString() == "zkc.implementation-selection/1") {
    auto snapshot = (*choices)[1].getAsString();
    if (!snapshot || snapshot->empty())
      return error("binding-selection-snapshot");
    selection.sourceSnapshot = snapshot->str();
    choices = (*choices)[2].getAsArray();
  }
  if (!choices || choices->size() > 4096)
    return error("binding-selection-format");
  for (const auto &item : *choices) {
    auto *pair = item.getAsArray();
    if (!pair || pair->size() != 2 || !(*pair)[0].getAsString() ||
        !(*pair)[1].getAsString())
      return error("binding-selection-format");
    selection.choices.emplace_back((*pair)[0].getAsString()->str(),
                                   (*pair)[1].getAsString()->str());
  }
  if (auto e = validate(selection))
    return e;
  return selection;
}

Error checkImplementationSelection(const ImplementationSelection &selection,
                                   const source::Content &source) {
  if (auto e = validate(selection))
    return e;
  if (selection.sourceSnapshot.empty())
    return Error::success();
  auto snapshot = source::snapshot(source);
  if (!snapshot)
    return snapshot.takeError();
  if (selection.sourceSnapshot != *snapshot)
    return error("binding-stale-selection");
  return Error::success();
}
} // namespace zkc::protocol
