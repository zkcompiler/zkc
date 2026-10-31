#include "zkc/Analysis/ProtocolConstants.h"
#include "mlir/IR/Matchers.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "llvm/ADT/DenseMap.h"

using namespace mlir;
using namespace llvm;
namespace zkc {
namespace {
using Result = facts::Result<uint64_t>;
using Status = facts::Status;
namespace pir = protocol_ir;
struct Observation {
  StringRef participant;
  MathematicalFactAnalysis &mathematics;
  facts::Work &work;
  llvm::DenseMap<Value, Result> constants;
  Observation(StringRef participant, MathematicalFactAnalysis &mathematics,
              facts::Work &work)
      : participant(participant), mathematics(mathematics), work(work) {}

  Result unknown() const {
    return {work.exhausted() ? Status::Capacity : Status::Unknown,
            std::nullopt};
  }
  bool includes(ArrayAttr roles) {
    if (!work.charge(roles.size()))
      return false;
    return participant.empty() ||
           is_contained(roles,
                        StringAttr::get(roles.getContext(), participant));
  }
  Result read(Value value, unsigned depth) {
    if (depth >= 64)
      work.exhaust();
    if (!work.charge())
      return unknown();
    auto *owner = mathematics.getRoot();
    if (!value || !owner ||
        (!value.getType().isUnsignedInteger(64) &&
         !value.getType().isSignlessInteger(1)))
      return unknown();
    auto *scope = value.getParentRegion()->getParentOp();
    if (scope != owner && !owner->isAncestor(scope))
      return unknown();
    if (auto found = constants.find(value); found != constants.end())
      return found->second;
    auto result = interpret(value, depth);
    if (result.status != Status::Capacity)
      constants.try_emplace(value, result);
    return result;
  }
  Result interpret(Value value, unsigned depth) {
    if (auto view = value.getDefiningOp<pir::RestrictRolesOp>())
      return includes(view.getRoles()) ? read(view.getInput(), depth + 1)
                                       : unknown();
    if (auto assembly = value.getDefiningOp<pir::AssembleRolesOp>()) {
      if (!includes(assembly.getRoles()))
        return unknown();
      if (!participant.empty())
        return read(assembly.getComponent(participant), depth + 1);
      std::optional<uint64_t> common;
      for (Value component : assembly.getInputs()) {
        auto observed = read(component, depth + 1);
        if (observed.status != Status::Proven || !observed.value)
          return observed;
        if (common && common != observed.value)
          return unknown();
        common = observed.value;
      }
      return common ? Result{Status::Proven, common} : unknown();
    }
    if (auto argument = dyn_cast<BlockArgument>(value)) {
      auto repeat = dyn_cast<pir::RepeatOp>(argument.getOwner()->getParentOp());
      if (repeat && includes(repeat.getRoles()) &&
          argument.getArgNumber() > uint64_t(repeat.getCarried()))
        return read(repeat.getInputs()[argument.getArgNumber()], depth + 1);
      return unknown();
    }
    auto origin = mathematics.origin(value, work, depth);
    if (origin.status == Status::Capacity)
      return unknown();
    if (origin.value && *origin.value != value)
      return read(*origin.value, depth + 1);
    Attribute literal;
    if (matchPattern(value, m_Constant(&literal)))
      if (auto integer = dyn_cast<IntegerAttr>(literal))
        return {Status::Proven, integer.getValue().getZExtValue()};
    return value.getType().isUnsignedInteger(64)
               ? mathematics.integer(value, work, depth)
               : unknown();
  }
};
} // namespace
facts::Result<uint64_t>
observeProtocolConstant(Value value, StringRef participant,
                        MathematicalFactAnalysis &mathematics,
                        facts::Work &work, unsigned depth) {
  return Observation(participant, mathematics, work).read(value, depth);
}
} // namespace zkc
