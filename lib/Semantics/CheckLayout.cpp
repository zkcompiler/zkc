//===- CheckLayout.cpp - check operand segmentation -------------*- C++ -*-===//

#include "zkc/Semantics/CheckLayout.h"

#include "zkc/ChallengeShape.h"
#include "zkc/Dialect/Pir/PirOps.h"

using namespace mlir;
using namespace zkc::registry;

namespace zkc {
namespace semantics {

/// Whether a value satisfies a declared operand class.
///
/// A profiled value carries a commitment, not an element of the class its
/// content is drawn from, so it matches no concrete class: `bareClass()` is
/// empty for one and an operand slot never declares an empty class. Reading
/// the profile name here instead would let a profile spelled like a class
/// stand in for one element of it.
static bool classMatches(Value value, llvm::StringRef expected) {
  return expected == "*" ||
         cast<zkc::pir::ValType>(value.getType()).bareClass() == expected;
}

llvm::StringRef selfMaterialRef(Value value) {
  auto bind = dyn_cast_or_null<zkc::pir::BindOp>(value.getDefiningOp());
  if (!bind || bind.getStage() != zkc::pir::Stage::Seal)
    return {};
  // A binding that carries a profile absorbs the digest of what the profile
  // describes; a binding that fills a contract role absorbs the reference of
  // the material the role claims. Either way the value is the reference, and
  // resolving it through a material binding as well would let the transcript
  // hold one thing while the claim named another.
  if (!bind.getProfiled() && !bind.getMembership())
    return {};
  // An instance-stage binding has no value at seal time and so carries no
  // reference; the seal-stage form is the one whose value is the digest.
  return bind.getValue().value_or(llvm::StringRef());
}

uint64_t checkOperandUnits(Value value) {
  Operation *producer = value.getDefiningOp();
  if (auto slot = dyn_cast_or_null<zkc::pir::SlotOp>(producer))
    return zkc::challenge::parseCount(slot.getCount()).value_or(1);
  if (auto capability =
          dyn_cast_or_null<zkc::pir::ChallengeCapabilityOpInterface>(producer))
    if (capability.getChallengeValue() == value)
      return zkc::challenge::parseCount(capability.getChallengeCount())
          .value_or(1);
  return 1;
}

static void solve(const CheckContract &contract, ValueRange inputs,
                  size_t segmentIndex, size_t inputIndex,
                  std::map<std::string, uint64_t, std::less<>> captures,
                  OperandView current,
                  llvm::SmallVectorImpl<OperandView> &answers) {
  if (answers.size() > 1)
    return;
  if (segmentIndex == contract.operands.size()) {
    if (inputIndex == inputs.size())
      answers.push_back(std::move(current));
    return;
  }

  uint64_t unitsAvailable = 0;
  for (size_t index = inputIndex; index < inputs.size(); ++index)
    unitsAvailable += checkOperandUnits(inputs[index]);

  const CheckOperandSegment &segment = contract.operands[segmentIndex];
  llvm::SmallVector<uint64_t> candidates;
  switch (segment.multiplicity.kind) {
  case OperandMultiplicityKind::Exact:
    candidates.push_back(segment.multiplicity.value);
    break;
  case OperandMultiplicityKind::SameAs: {
    auto found = captures.find(segment.multiplicity.name);
    if (found == captures.end())
      return;
    candidates.push_back(found->second);
    break;
  }
  case OperandMultiplicityKind::Capture: {
    auto found = captures.find(segment.multiplicity.name);
    if (found != captures.end()) {
      candidates.push_back(found->second);
      break;
    }
    for (uint64_t count = segment.multiplicity.value; count <= unitsAvailable;
         ++count)
      candidates.push_back(count);
    break;
  }
  }

  for (uint64_t count : candidates) {
    if (count > unitsAvailable)
      continue;
    // A segment consumes whole SSA operands, each contributing its
    // element count of units; the sum must land exactly on the
    // segment's multiplicity — splitting one vector value across two
    // segments has no meaning.
    uint64_t units = 0;
    size_t consumed = 0;
    bool classesMatch = true;
    while (units < count && inputIndex + consumed < inputs.size()) {
      Value value = inputs[inputIndex + consumed];
      classesMatch &= classMatches(value, segment.valueClass);
      units += checkOperandUnits(value);
      ++consumed;
    }
    if (!classesMatch || units != count)
      continue;

    auto nextCaptures = captures;
    if (segment.multiplicity.kind == OperandMultiplicityKind::Capture)
      nextCaptures[segment.multiplicity.name] = count;
    OperandView next = current;
    auto &roleValues = next.roles[segment.role];
    for (size_t index = 0; index < consumed; ++index) {
      roleValues.push_back(inputs[inputIndex + index]);
      next.positions.push_back({segment.role, index});
    }
    solve(contract, inputs, segmentIndex + 1, inputIndex + consumed,
          std::move(nextCaptures), std::move(next), answers);
  }
}

void solveCheckLayout(const CheckContract &contract, ValueRange inputs,
                      llvm::SmallVectorImpl<OperandView> &answers) {
  solve(contract, inputs, 0, 0, {}, {}, answers);
}

} // namespace semantics
} // namespace zkc
