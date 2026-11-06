#ifndef ZKC_LIB_COMPILER_NATIVE_CODEC_CAPACITY_H
#define ZKC_LIB_COMPILER_NATIVE_CODEC_CAPACITY_H

#include "../Dialect/NativeTypeWork.h"
#include "NativeProofVerification.h"
#include "mlir/IR/AffineMap.h"
#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/BuiltinDialect.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/DialectResourceBlobManager.h"
#include "mlir/IR/IntegerSet.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Commitment/IR/CommitmentTypes.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Exec/IR/ExecTypes.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialTypes.h"
#include "zkc/Dialect/Runtime/IR/RuntimeAttrs.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/TypeSwitch.h"
#include <algorithm>
#include <utility>

namespace zkc::detail {
namespace {
// Private to the two codec translation units. One allowance follows the whole
// phase, including setup. A work unit is a structural slot or eight field
// bytes. Preflight reserves eight visits per input occurrence: inspection plus
// clone / admission, symbol and site indexing, closure, comparison, rewriting
// and output copies. These are conservative traversal costs, not allocator byte
// counts. Variable fanout and generated work debit the same allowance at their
// use sites. Completed native roots share only their structural inspection;
// native semantic callbacks debit this same allowance in addition to the
// unchanged reservation. Owned expansion never uses the root cache.
class CodecCapacity {
  uint64_t remaining = 1000000;
  bool limited = false;
  static constexpr uint64_t visits = 8;

  // Native roots always start at depth zero, independently of operation or
  // control depth. Height includes every type, attribute and affine edge.
  struct RootSummary {
    unsigned height;
  };
  llvm::DenseMap<mlir::Type, RootSummary> rootTypes;
  llvm::DenseMap<mlir::Attribute, RootSummary> rootAttributes;
  unsigned maximumDepth = 0;
  bool nativePreflight = true;

  // Only operation() uses these roots, during consecutive read-only preflight
  // walks. The caller must keep the context and all inspected type/resource
  // payloads stable until finishNativePreflight(); generic MLIR Type storage
  // is not necessarily immutable. Descendants always use the expanded walker.
  template <class Value, class Inspect>
  bool root(Value value, llvm::DenseMap<Value, RootSummary> &cache,
            Inspect inspect) {
    if (!charge(0))
      return false;
    if (!value)
      return true;
    if (!nativePreflight)
      return inspect();
    if (!slots()) // Every root reference and cache lookup.
      return false;
    if (auto found = cache.find(value); found != cache.end())
      return found->second.height <= 64 || refuse();
    const unsigned outerDepth = maximumDepth;
    maximumDepth = 0;
    auto restore = llvm::scope_exit([&] { maximumDepth = outerDepth; });
    if (!inspect() || !slots()) // Charge insertion before publishing a result.
      return false;
    // No entry iterator/reference survives inspection. Failed inspections and
    // failed insertions publish nothing, even if some children were visited.
    cache.try_emplace(value, RootSummary{maximumDepth});
    return true;
  }
  bool root(mlir::Type value) {
    return root(value, rootTypes, [&] { return type(value); });
  }
  bool root(mlir::Attribute value) {
    return root(value, rootAttributes, [&] { return attribute(value); });
  }

  bool slots(uint64_t count = 1) {
    return count <= remaining / visits ? charge(count * visits) : refuse();
  }
  bool field(llvm::StringRef value) {
    return slots(value.size() / 8 + unsigned(value.size() % 8 != 0));
  }
  bool elements(mlir::ShapedType value) {
    if (!value.hasRank() || !slots(value.getRank()))
      return refuse();
    // A resource's physical blob need not cover its logical shape. Never ask
    // MLIR to form an unchecked signed element product, even for a splat.
    // Scan the entire shape first: a trailing zero makes any product empty.
    bool empty = false;
    for (int64_t extent : value.getShape()) {
      if (extent < 0)
        return refuse();
      empty |= extent == 0;
    }
    if (empty)
      return true;
    uint64_t count = 1;
    const uint64_t limit = remaining / visits;
    for (int64_t extent : value.getShape()) {
      const uint64_t width = static_cast<uint64_t>(extent);
      if (width > limit / count)
        return refuse();
      count *= width;
    }
    return slots(count);
  }
  bool affine(mlir::AffineExpr expression, unsigned depth) {
    if (depth > 64 || !slots())
      return refuse();
    maximumDepth = std::max(maximumDepth, depth);
    if (auto binary = mlir::dyn_cast<mlir::AffineBinaryOpExpr>(expression))
      return affine(binary.getLHS(), depth + 1) &&
             affine(binary.getRHS(), depth + 1);
    return true;
  }
  template <class Value> bool children(Value value, unsigned depth) {
    bool ok = true;
    value.walkImmediateSubElements(
        [&](mlir::Attribute child) { ok = ok && attribute(child, depth + 1); },
        [&](mlir::Type child) { ok = ok && type(child, depth + 1); });
    return ok;
  }

public:
  // End the stable-storage borrow before admission, callbacks or rewriting.
  // This is one-way: later operation() calls expand afresh, without resetting
  // either the allowance or a sticky refusal.
  void finishNativePreflight() {
    rootTypes.clear();
    rootAttributes.clear();
    nativePreflight = false;
  }

  bool refuse() {
    limited = true;
    return false;
  }
  bool charge(uint64_t count = 1) {
    if (limited || count > remaining)
      return refuse();
    remaining -= count;
    return true;
  }
  bool text(llvm::StringRef value) {
    return charge(value.size() / 8 + unsigned(value.size() % 8 != 0));
  }
  bool exhausted() const { return limited; }

  bool type(mlir::Type value, unsigned depth = 0) {
    using namespace mlir;
    if (!charge(0))
      return false;
    if (!value)
      return true;
    if (depth > 64 || !slots())
      return refuse();
    maximumDepth = std::max(maximumDepth, depth);
    // StringRef parameters are not MLIR subelements. Inspect their native
    // accessors before a catalog adapter can intern or print them.
    bool ok =
        llvm::TypeSwitch<Type, bool>(value)
            .Case<algebra::FieldType, algebra::GroupType, data::FieldVectorType,
                  data::GroupVectorType, data::FieldMatrixType,
                  data::FieldArrayType, poly::MultilinearType, poly::PointType,
                  poly::QuadraticType, poly::UnivariateType,
                  poly::PolynomialType>(
                [&](auto t) { return field(t.getDomain()); })
            .Case<poly::ResidualType, poly::TableType>([&](auto t) {
              return field(t.getDomain()) && field(t.getRank());
            })
            .Case<commitment::PolynomialObjectType,
                  commitment::VectorObjectType>([&](auto t) {
              return field(t.getScheme()) && field(t.getKind());
            })
            .Case<runtime::CapabilityType>(
                [&](auto t) { return field(t.getIdentity()); })
            .Case<runtime::RepresentedType>(
                [&](auto t) { return field(t.getRepresentation()); })
            .Case<protocol_ir::ServiceReferenceType>(
                [&](auto t) { return field(t.getContract()); })
            .Case<OpaqueType>([&](auto t) { return field(t.getTypeData()); })
            .Default(true);
    if (!ok)
      return false;
    if (auto variant = dyn_cast<data::VariantType>(value))
      if (variant.getAlternatives().size() > 512 ||
          !slots(variant.getAlternatives().size()))
        return refuse();
    if (auto tuple = dyn_cast<TupleType>(value))
      if (!slots(tuple.size()))
        return false;
    if (auto domain = dyn_cast<data::DomainType>(value))
      if (!slots(domain.getItemTypes().size()))
        return false;
    if (auto represented = dyn_cast<runtime::RepresentedType>(value))
      if (!slots(represented.getChildren().size()))
        return false;
    if (auto outcome = dyn_cast<exec::OutcomeType>(value))
      if (!slots(outcome.getPayload().size()))
        return false;
    if (auto transfer = dyn_cast<runtime::TransferType>(value))
      if (!slots(transfer.getPayload().size()))
        return false;
    if (auto f = dyn_cast<FunctionType>(value)) {
      if (!slots(f.getNumInputs()) || !slots(f.getNumResults()))
        return false;
    }
    if (auto shaped = dyn_cast<ShapedType>(value))
      if (shaped.hasRank() && !slots(shaped.getRank()))
        return false;
    return children(value, depth);
  }

  bool attribute(mlir::Attribute value, unsigned depth = 0) {
    using namespace mlir;
    if (!charge(0))
      return false;
    if (!value)
      return true;
    if (depth > 64 || !slots())
      return refuse();
    maximumDepth = std::max(maximumDepth, depth);
    if (auto array = dyn_cast<ArrayAttr>(value)) {
      if (!slots(array.size()))
        return false;
      for (Attribute item : array)
        if (!attribute(item, depth + 1))
          return false;
      return true;
    }
    if (auto dict = dyn_cast<DictionaryAttr>(value)) {
      if (!slots(dict.size()))
        return false;
      for (auto item : dict)
        if (!field(item.getName().getValue()) ||
            !attribute(item.getValue(), depth + 1))
          return false;
      return true;
    }
    if (auto map = dyn_cast<AffineMapAttr>(value)) {
      auto affineMap = map.getValue();
      if (!slots(affineMap.getNumDims()) || !slots(affineMap.getNumSymbols()) ||
          !slots(affineMap.getNumResults()))
        return false;
      for (auto expression : affineMap.getResults())
        if (!affine(expression, depth + 1))
          return false;
    }
    if (auto set = dyn_cast<IntegerSetAttr>(value)) {
      auto integerSet = set.getValue();
      if (!slots(integerSet.getNumDims()) ||
          !slots(integerSet.getNumSymbols()) ||
          !slots(integerSet.getNumConstraints()))
        return false;
      for (auto expression : integerSet.getConstraints())
        if (!affine(expression, depth + 1))
          return false;
    }
    if (auto alternative = dyn_cast<data::AlternativeAttr>(value))
      if (!slots(alternative.getPayload().size()))
        return false;
    if (auto layout = dyn_cast<data::LayoutAttr>(value))
      if (!slots(layout.getFields().size()) ||
          !slots(layout.getAlternatives().size()) ||
          !slots(layout.getLeaves().size()))
        return false;
    if (auto alternative = dyn_cast<data::LayoutAlternativeAttr>(value))
      if (!slots(alternative.getFields().size()))
        return false;
    if (auto expression = dyn_cast<algebra::RingExpressionAttr>(value))
      if (!slots(expression.getInputs().size()) ||
          !slots(expression.getNodes().size()))
        return false;
    if (auto fused = dyn_cast<FusedLoc>(value))
      if (!slots(fused.getLocations().size()))
        return false;
    if (auto origin = dyn_cast<runtime::NativeOriginAttr>(value))
      if (!slots(origin.getPath().size()))
        return false;
    bool ok =
        llvm::TypeSwitch<Attribute, bool>(value)
            .Case<StringAttr>([&](auto a) { return field(a.getValue()); })
            .Case<OpaqueAttr>([&](auto a) { return field(a.getAttrData()); })
            .Case<IntegerAttr>([&](auto a) {
              return slots((uint64_t(a.getValue().getBitWidth()) + 63) / 64);
            })
            .Case<DenseArrayAttr>([&](auto a) {
              return slots(a.size()) &&
                     field(llvm::StringRef(a.getRawData().data(),
                                           a.getRawData().size()));
            })
            .Case<DenseResourceElementsAttr>([&](auto a) {
              if (!elements(a.getType()))
                return false;
              auto data = a.getData();
              return field(a.getRawHandle().getKey()) &&
                     field(llvm::StringRef(data.data(), data.size()));
            })
            .Case<runtime::AssetReferenceAttr>(
                [&](auto a) { return field(a.getFormat()); })
            .Case<runtime::OriginStepAttr>([&](auto a) {
              return field(a.getProtocol()) && field(a.getSite()) &&
                     field(a.getAlternative());
            })
            .Case<runtime::QueryOriginAttr>([&](auto a) {
              return field(a.getProtocol()) && field(a.getSite()) &&
                     field(a.getService()) && field(a.getMethod()) &&
                     field(a.getOwner());
            })
            .Case<runtime::MessageOriginAttr>([&](auto a) {
              return field(a.getProtocol()) && field(a.getSite()) &&
                     field(a.getSchema()) && field(a.getSender()) &&
                     field(a.getReceiver());
            })
            .Case<runtime::StartOriginAttr>([&](auto a) {
              return field(a.getProtocol()) && field(a.getSite());
            })
            .Case<runtime::NativeOriginAttr>(
                [&](auto a) { return field(a.getEntry()); })
            .Case<protocol_ir::OracleKindAttr>(
                [&](auto a) { return field(a.getIdentity()); })
            .Default(true);
    if (!ok)
      return false;
    if (auto dense = dyn_cast<DenseElementsAttr>(value)) {
      if (!elements(dense.getType()))
        return false;
      if (auto strings = dyn_cast<DenseStringElementsAttr>(dense)) {
        // Even an empty iterator may ask MLIR for an unchecked element count.
        if (llvm::is_contained(dense.getType().getShape(), int64_t(0))) {
          for (auto item : strings.getRawStringData())
            if (!field(item))
              return false;
        } else
          for (auto item : strings.getValues<llvm::StringRef>())
            if (!field(item))
              return false;
      } else if (!field(llvm::StringRef(dense.getRawData().data(),
                                        dense.getRawData().size())))
        return false;
    }
    if (auto symbol = dyn_cast<SymbolRefAttr>(value))
      if (!slots(symbol.getNestedReferences().size()))
        return false;
    return children(value, depth);
  }

  bool operation(mlir::Operation *op, unsigned controlDepth = 0,
                 unsigned depth = 0) {
    using namespace mlir;
    if (!charge(0) || !op || controlDepth > 64 || depth > 128 ||
        (isa<protocol_ir::ParticipantBranchOp>(op) &&
         op->getNumRegions() > 512) ||
        !slots() || !slots(op->getNumOperands()) ||
        !slots(op->getNumResults()) || !slots(op->getNumRegions()) ||
        !field(op->getName().getStringRef()) ||
        // NamedAttrList copies/edits physical slots even on a dictionary hit.
        !slots(op->getAttrs().size()) ||
        !root(mlir::Attribute(op->getAttrDictionary())) ||
        !root(mlir::Attribute(op->getLoc())))
      return refuse();
    for (Type t : op->getOperandTypes())
      if (!root(t))
        return false;
    for (Type t : op->getResultTypes())
      if (!root(t))
        return false;
    for (Region &region : op->getRegions())
      for (Block &block : region) {
        if (!slots() || !slots(block.getNumArguments()))
          return false;
        for (auto arg : block.getArguments())
          if (!root(arg.getType()) || !root(mlir::Attribute(arg.getLoc())))
            return false;
        for (Operation &child : block)
          if (!operation(
                  &child,
                  controlDepth +
                      unsigned(isa<protocol_ir::ProtocolLoopOp,
                                   protocol_ir::ParticipantBranchOp>(op)),
                  depth + 1))
            return false;
      }
    return true;
  }

  bool jsonArray(const llvm::json::Array &array, unsigned depth = 0) {
    if (depth > 64 || !slots(array.size()))
      return refuse();
    for (const auto &item : array)
      if (!jsonValue(item, depth + 1))
        return false;
    return true;
  }
  bool jsonValue(const llvm::json::Value &value, unsigned depth) {
    if (depth > 64 || !slots())
      return refuse();
    if (auto string = value.getAsString())
      return field(*string);
    if (auto array = value.getAsArray())
      return jsonArray(*array, depth);
    if (auto object = value.getAsObject()) {
      if (!slots(object->size()))
        return false;
      for (const auto &item : *object)
        if (!field(llvm::StringRef(item.first)) ||
            !jsonValue(item.second, depth + 1))
          return false;
    }
    return true;
  }

  template <class Types> bool types(const Types &values) {
    if (!slots(values.size()))
      return false;
    for (auto value : values)
      if (!type(value))
        return false;
    return true;
  }
  bool inputs(const NativeProofPolicy &policy,
              const protocol::ConstructionPlan &plan,
              llvm::ArrayRef<NativeTranscriptEvent> events,
              const llvm::json::Array &transcript) {
    if (!field(policy.entry) || !field(policy.producer) ||
        !field(policy.validator) || !field(policy.suite) ||
        !field(policy.construction) || !slots(policy.services.size()) ||
        !slots(policy.publicInputs.size()) || !slots(policy.draws.size()) ||
        !slots(policy.gates.size()))
      return false;
    for (const auto &draw : policy.draws)
      if (!field(draw.first) || !field(draw.second))
        return false;
    for (const auto &gate : policy.gates)
      if (!field(gate.first))
        return false;
    if (!attribute(plan.symbol) || !attribute(plan.target) ||
        !attribute(plan.initializer) || !field(plan.provider) ||
        !field(plan.suite) || !slots(plan.services.size()) ||
        !types(plan.state) || !slots(plan.rules.size()) ||
        !slots(plan.applications.size()) || !slots(events.size()) ||
        !jsonArray(transcript))
      return false;
    for (const auto &application : plan.applications)
      if (!attribute(application.construction) || !field(application.site))
        return false;
    for (const auto &rule : plan.rules) {
      if (!attribute(rule.handler) || !slots(rule.sites.size()) ||
          !slots(rule.inputs.size()) || !types(rule.payload) ||
          !types(rule.chunks))
        return false;
      for (const auto &site : rule.sites)
        if (!field(site))
          return false;
    }
    if (plan.codec) {
      const auto &codec = *plan.codec;
      if (!field(codec.provider) || !types(codec.record) ||
          !attribute(codec.initialize) || !attribute(codec.write) ||
          !attribute(codec.finish) || !slots(codec.inputs.size()))
        return false;
    }
    for (const auto &event : events)
      if (!field(event.site) || !field(event.origin) ||
          !field(event.witnessSite) || !type(event.payload) ||
          (event.startInputs && !types(*event.startInputs)))
        return false;
    return true;
  }
};

// Private terminal cancellation for native callbacks with value-returning
// signatures. Existing NativeTypeWork facts are separate from root summaries
// and live only for this scope; neither predicates nor stage admission migrate
// between the two subjects. Unrelated exceptions retain their normal behavior.
struct CodecAccountingLimit {};
inline llvm::Error codecWorkResult(llvm::Error result, CodecCapacity &capacity,
                                   llvm::StringRef refusal) {
  if (capacity.exhausted()) {
    llvm::consumeError(std::move(result));
    return error(refusal);
  }
  return result;
}
template <class T>
llvm::Expected<T> codecWorkResult(llvm::Expected<T> result,
                                  CodecCapacity &capacity,
                                  llvm::StringRef refusal) {
  if (capacity.exhausted()) {
    if (!result)
      llvm::consumeError(result.takeError());
    return error(refusal);
  }
  return result;
}
template <class F>
auto codecWithNativeWork(CodecCapacity &capacity, llvm::StringRef refusal,
                         F &&action) -> decltype(action()) {
  using Result = decltype(action());
  capacity.finishNativePreflight();
  NativeTypeWork work;
  try {
    NativeTypeWorkScope scope(work, [&](uint64_t amount) {
      if (!capacity.charge(amount))
        throw CodecAccountingLimit{};
    });
    if (!capacity.charge(0))
      return Result(error(refusal));
    return codecWorkResult(action(), capacity, refusal);
  } catch (const CodecAccountingLimit &) {
    return Result(error(refusal));
  }
}
} // namespace
} // namespace zkc::detail
#endif
