#include "NumericalSelection.h"
#include "ComputationSelection.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/STLExtras.h"
#include <limits>

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
RecipeConstructionWork::RecipeConstructionWork(const RealizationWork &work)
    : helpers(work.helperOperations), expressions(work.finiteExpressions),
      slots(work.helperSlots), polynomial(work.polynomial),
      requiredMaps(work.requiredMapConstruction) {}
bool RecipeConstructionWork::canDiscard(const RealizationWork &work) const {
  // Reserve the upper bound without overflowing caller-controlled quotas.
  uint64_t remaining = work.discardedRecipeExpansion;
  for (uint64_t amount : {uint64_t(helpers), uint64_t(expressions), slots,
                          polynomial, requiredMaps}) {
    if (amount > remaining)
      return false;
    remaining -= amount;
  }
  return true;
}
bool RecipeConstructionWork::discard(RealizationWork &work) const {
  assert(work.helperOperations <= helpers &&
         work.finiteExpressions <= expressions && work.helperSlots <= slots &&
         work.polynomial <= polynomial &&
         work.requiredMapConstruction <= requiredMaps);
  uint64_t remaining = work.discardedRecipeExpansion;
  for (uint64_t amount :
       {uint64_t(helpers - work.helperOperations),
        uint64_t(expressions - work.finiteExpressions),
        slots - work.helperSlots, polynomial - work.polynomial,
        requiredMaps - work.requiredMapConstruction}) {
    if (amount > remaining)
      return false;
    remaining -= amount;
  }
  work.discardedRecipeExpansion = remaining;
  work.helperOperations = helpers;
  work.finiteExpressions = expressions;
  work.helperSlots = slots;
  work.polynomial = polynomial;
  work.requiredMapConstruction = requiredMaps;
  return true;
}

RealizationSubject
NumericalSelection::childSubject(const RealizationSubject &parent,
                                 StringRef operation, unsigned child) {
  auto subject = parent;
  subject.operation = operation.str();
  subject.position.push_back(std::numeric_limits<unsigned>::max());
  subject.position.push_back(child);
  return subject;
}
Expected<NumericalOccurrence>
NumericalSelection::discover(const RealizationSubject &subject,
                             bool replaceable, NumericalExpressionMode mode) {
  if (!chargeCatalog())
    return error("finite-analysis-limit");
  auto found = coordinates.find({invocation, subject});
  if (found != coordinates.end()) {
    auto &occurrence = occurrences[found->second];
    // Replacement permission can only become more restrictive.
    occurrence.replaceable &= replaceable;
    if (!canSpeculate())
      occurrence.alternative = NumericalAlternative::Ordered;
    return found->second;
  }
  occurrences.push_back({invocation,
                         subject,
                         replaceable && canSpeculate()
                             ? NumericalAlternative::Specialized
                             : NumericalAlternative::Ordered,
                         replaceable,
                         mode,
                         {true, mode == NumericalExpressionMode::PreferNative,
                          false, true, true}});
  auto id = occurrences.size() - 1;
  coordinates.emplace(Coordinate{invocation, subject}, id);
  return id;
}
Expected<NumericalOccurrence>
NumericalSelection::discoverMap(const RealizationSubject &subject, bool dot,
                                bool sum, NumericalExpressionMode mode) {
  auto id = discover(subject, true, mode);
  if (!id)
    return id.takeError();
  auto &occurrence = occurrences[*id];
  bool native = mode == NumericalExpressionMode::PreferNative;
  occurrence.legal = {dot, sum && native, native, true, false};
  // Maps have a required vector endpoint, never an invented ordered loop.
  if (!canSpeculate() ||
      occurrence.alternative == NumericalAlternative::Ordered)
    occurrence.alternative = NumericalAlternative::Vector;
  auto index = static_cast<unsigned>(occurrence.alternative);
  while (!occurrence.legal[index])
    ++index;
  occurrence.alternative = static_cast<NumericalAlternative>(index);
  return *id;
}
NumericalAlternative
NumericalSelection::alternative(NumericalOccurrence id) const {
  return occurrences.at(id).alternative;
}
MathematicalSelectionPolicy
NumericalSelection::policy(NumericalOccurrence id,
                           MathematicalSelectionPolicy effective) const {
  auto choice = alternative(id);
  if (choice == NumericalAlternative::Ordered)
    effective.finiteBulk = false;
  if (choice == NumericalAlternative::Vector)
    effective.numericalExpressions = NumericalExpressionMode::VectorOnly;
  return effective;
}
void NumericalSelection::select(NumericalOccurrence id,
                                ComputationSelection &selected,
                                const MathematicalRecipes &recipes) {
  auto &occurrence = occurrences.at(id);
  // Never undo a replacement or policy refusal established by the recognizer.
  auto status = selected.diagnostic.outcome.status;
  if (!selected.view || status == OptimizationStatus::Capacity ||
      status == OptimizationStatus::PolicyDisabled ||
      status == OptimizationStatus::ReplacementRestricted ||
      !canReplacePayload(*selected.view)) {
    occurrence.replaceable = false;
    occurrence.alternative = NumericalAlternative::Ordered;
    return;
  }
  bool formula = selected.equations.pointwiseReduction.has_value() ||
                 selected.equations.elementwise.has_value();
  occurrence.legal = {selected.kind == RealizationKind::Bilinear ||
                          selected.kind == RealizationKind::Reduction,
                      formula && occurrence.expressionMode ==
                                     NumericalExpressionMode::PreferNative,
                      false, formula, true};
  auto index = static_cast<unsigned>(occurrence.alternative);
  while (!occurrence.legal[index])
    ++index;
  occurrence.alternative = static_cast<NumericalAlternative>(index);
  auto choice = occurrence.alternative;
  if (choice == NumericalAlternative::Specialized)
    return;
  selected.kind = RealizationKind::Ordered;
  selected.reduction.reset();
  selected.matrix = nullptr;
  selected.pointwiseReduction = nullptr;
  if (choice == NumericalAlternative::Ordered)
    return;
  if (selected.equations.pointwiseReduction) {
    selected.pointwiseReduction =
        recipes.reduction(selected.equations.pointwiseReduction->combine, {},
                          ReductionForm::Direct);
    if (selected.pointwiseReduction)
      selected.kind = RealizationKind::PointwiseReduction;
  } else if (selected.equations.elementwise)
    selected.kind = RealizationKind::Elementwise;
}
Expected<bool>
NumericalSelection::advance(ArrayRef<NumericalOccurrence> implicated) {
  SmallVector<NumericalOccurrence> ordered(implicated);
  llvm::sort(ordered);
  ordered.erase(std::unique(ordered.begin(), ordered.end()), ordered.end());
  for (auto id : ordered) {
    auto &occurrence = occurrences.at(id);
    auto next = static_cast<unsigned>(occurrence.alternative) + 1;
    while (next < occurrence.legal.size() && !occurrence.legal[next])
      ++next;
    if (!occurrence.replaceable || next == occurrence.legal.size())
      continue;
    if (!chargeCatalog())
      return error("finite-analysis-limit");
    occurrence.alternative = static_cast<NumericalAlternative>(next);
    return true;
  }
  return false;
}
Expected<bool>
NumericalSelection::advanceSubject(const RealizationSubject &subject,
                                   std::optional<size_t> invocation) {
  SmallVector<NumericalOccurrence> owners;
  for (auto [id, occurrence] : enumerate(occurrences))
    if (occurrence.subject == subject &&
        (!invocation || occurrence.invocation == *invocation))
      owners.push_back(id);
  return advance(owners);
}
Expected<bool> NumericalSelection::advanceAll() {
  SmallVector<NumericalOccurrence> owners;
  for (auto [id, occurrence] : enumerate(occurrences))
    owners.push_back(id);
  return advance(owners);
}
Expected<bool> NumericalSelection::advanceInvocation() {
  SmallVector<NumericalOccurrence> owners;
  for (auto [id, occurrence] : enumerate(occurrences))
    if (occurrence.invocation == invocation)
      owners.push_back(id);
  return advance(owners);
}
bool NumericalSelection::hasAlternatives(
    std::optional<size_t> coordinate) const {
  return any_of(occurrences, [&](const auto &occurrence) {
    if (!occurrence.replaceable ||
        (coordinate && occurrence.invocation != *coordinate))
      return false;
    auto first = static_cast<unsigned>(occurrence.alternative);
    return any_of(ArrayRef<bool>(occurrence.legal).drop_front(first + 1),
                  [](bool legal) { return legal; });
  });
}
Expected<bool> NumericalSelection::order(const RealizationSubject &subject) {
  if (!chargeCatalog())
    return error("finite-analysis-limit");
  auto found = coordinates.find({invocation, subject});
  if (found == coordinates.end())
    return false;
  auto &occurrence = occurrences[found->second];
  if (!occurrence.replaceable ||
      occurrence.alternative == NumericalAlternative::Ordered)
    return false;
  occurrence.alternative = NumericalAlternative::Ordered;
  return true;
}
bool NumericalSelection::canSpeculate() const {
  return optionalConstructionAllowed && account().discardedRecipeCopy &&
         account().discardedRecipeSiteBytes;
}
bool NumericalSelection::chargeCatalog(uint64_t amount) {
  auto &remaining = account().selectionBookkeeping;
  if (amount > remaining) {
    remaining = 0;
    return false;
  }
  remaining -= amount;
  return true;
}
void NumericalSelection::record(Operation *op, NumericalOccurrence id) {
  auto &owners = origins[op];
  if (!is_contained(owners, id))
    owners.push_back(id);
}
SmallVector<NumericalOccurrence>
NumericalSelection::owners(Operation *op) const {
  auto found = origins.find(op);
  return found == origins.end() ? SmallVector<NumericalOccurrence>{}
                                : found->second;
}
void applyNumericalSelection(RealizationWork &work,
                             ComputationSelection &selected,
                             const MathematicalRecipes &recipes) {
  if (work.numericalSelection && work.numericalOccurrence)
    work.numericalSelection->select(*work.numericalOccurrence, selected,
                                    recipes);
}
} // namespace zkc::mathematical
