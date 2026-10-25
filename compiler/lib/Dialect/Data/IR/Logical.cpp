#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/JSON.h"
#include <set>
using namespace mlir;
namespace zkc::data {
LogicalResult MatchOp::verify() {
  auto fail = [&] {
    return diagnostics::emit(emitOpError(), "data-match-formation",
                             "sum alternatives or payload types differ");
  };
  auto parsed = llvm::json::parse(getInput().getType().getSchema());
  if (!parsed) {
    llvm::consumeError(parsed.takeError());
    return fail();
  }
  auto *schema = parsed->getAsObject();
  auto *alternatives = schema ? schema->getArray("alternatives") : nullptr;
  if (!alternatives || alternatives->size() != getArms().size() ||
      getAlternatives().size() != getArms().size() || alternatives->empty())
    return fail();
  std::set<StringRef> names;
  for (auto [name, block] : llvm::zip(getAlternatives(), getArms())) {
    auto label = cast<StringAttr>(name).getValue();
    if (!names.insert(label).second)
      return fail();
    auto found = llvm::find_if(*alternatives, [&](const auto &a) {
      return a.getAsObject() && a.getAsObject()->getString("name") == label;
    });
    if (found == alternatives->end())
      return fail();
    auto *fields = found->getAsObject()->getArray("fields");
    if (!fields ||
        block->getNumArguments() != fields->size() + getCaptures().size())
      return fail();
    for (auto [field, argument] :
         llvm::zip(*fields, block->getArguments().take_front(fields->size()))) {
      auto *value =
          field.getAsObject() ? field.getAsObject()->get("schema") : nullptr;
      auto *object = value ? value->getAsObject() : nullptr;
      auto kind = object ? object->getString("kind") : std::nullopt;
      if (!kind)
        return fail();
      Type expected =
          *kind == "boolean" ? Type(IntegerType::get(getContext(), 1))
          : (*kind == "Index" || *kind == "index")
              ? Type(IntegerType::get(getContext(), 64))
              : Type(ValueType::get(getContext(), zkc::printJson(*value)));
      if (argument.getType() != expected)
        return fail();
    }
    if (TypeRange(block->getArguments().drop_front(fields->size())) !=
        getCaptures().getTypes())
      return fail();
  }
  return success();
}
SuccessorOperands MatchOp::getSuccessorOperands(unsigned index) {
  auto count = getArms()[index]->getNumArguments();
  return SuccessorOperands(
      count >= getCaptures().size() ? count - getCaptures().size() : 0,
      getCapturesMutable());
}
} // namespace zkc::data
