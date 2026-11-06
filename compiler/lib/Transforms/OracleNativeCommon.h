#ifndef ZKC_TRANSFORMS_ORACLENATIVECOMMON_H
#define ZKC_TRANSFORMS_ORACLENATIVECOMMON_H
#include "../Dialect/NativeTypeWork.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/AffineMap.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/DialectResourceBlobManager.h"
#include "mlir/IR/IntegerSet.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Dialect/Algebra/IR/AlgebraAttrs.h"
#include "zkc/Dialect/Commitment/IR/CommitmentTypes.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Exec/IR/ExecTypes.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialTypes.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeAttrs.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#include "zkc/Dialect/SelectedControl.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/TypeSwitch.h"
#include "llvm/Support/raw_ostream.h"
#include <memory>
#include <optional>
#include <type_traits>

namespace zkc::protocol {
struct SourceExecutionClosure;
// Work includes setup, operand/result inspection, environment copies and joins.
// The operation and SSA ceilings of the previous native profile remain intact.
// The additional cumulative bound also limits walks which produce no
// operations.
struct OracleAccountingLimit {};
class OracleEmissionSession;
struct OracleNativeWork {
  OracleEmissionSession *emission = nullptr;
  zkc::detail::NativeTypeWork types;

  uint64_t remaining = 1000000;
  unsigned operations = 100000;
  bool exhausted = false;
  // Native types/attributes are immutable. This cache holds only results
  // constructed for the exact kind under this allowance, never module indexes.
  llvm::DenseMap<mlir::Attribute, mlir::Type> references;
  using SymbolLeaves = llvm::SmallVector<mlir::SymbolRefAttr>;
  struct StorageSummary {
    unsigned height = 0;
    std::shared_ptr<const SymbolLeaves> symbols;
  };
  // Exact immutable storage summaries survive source cloning within this
  // allowance. They contain neither resolved symbols nor operation pointers.
  llvm::DenseMap<mlir::Attribute, StorageSummary> attributeStorage;
  llvm::DenseMap<mlir::Type, StorageSummary> typeStorage;
  bool charge(uint64_t amount = 1) {
    if (exhausted || amount > remaining) {
      exhausted = true;
      remaining = 0;
      return false;
    }
    remaining -= amount;
    return true;
  }
  bool chargeProduct(uint64_t count, uint64_t width) {
    if (exhausted || (width && count > remaining / width)) {
      exhausted = true;
      remaining = 0;
      return false;
    }
    return charge(count * width);
  }
  bool operation(uint64_t width) {
    if (!operations || !charge() || !charge(width)) {
      exhausted = true;
      remaining = 0;
      return false;
    }
    --operations;
    return true;
  }
  bool traversal(uint64_t amount, unsigned count) {
    if (count > operations || !charge(amount)) {
      exhausted = true;
      remaining = 0;
      return false;
    }
    operations -= count;
    return true;
  }
};

// Cloning and OperationEquivalence copy/compare interned attribute and type
// handles. They do not recursively copy those immutable DAGs. Record their
// actual structural work during the storage inspection, before either runs.
struct OracleNativeTraversal {
  uint64_t work = 0;
  unsigned operations = 0;
};
using OracleNativeTraversals =
    llvm::DenseMap<mlir::Operation *, OracleNativeTraversal>;

// AttrTypeWalker deduplicates nodes, but still visits every immediate slot.
// Debit variable-width native storage in preorder, before its cached traversal.
// Raw strings and scalar buffers are not attribute/type subelements at all.
inline bool chargeOracleNativeAffine(OracleNativeWork &work,
                                     mlir::AffineExpr expression,
                                     unsigned depth = 0) {
  if (depth > 64 || !work.charge())
    return false;
  if (auto binary = mlir::dyn_cast<mlir::AffineBinaryOpExpr>(expression))
    return chargeOracleNativeAffine(work, binary.getLHS(), depth + 1) &&
           chargeOracleNativeAffine(work, binary.getRHS(), depth + 1);
  return true;
}
inline bool chargeOracleNativeImmediate(OracleNativeWork &work,
                                        mlir::Type value) {
  using namespace mlir;
  if (!work.charge())
    return false;
  bool fields =
      llvm::TypeSwitch<Type, bool>(value)
          .Case<algebra::FieldType, algebra::GroupType, data::FieldVectorType,
                data::GroupVectorType, data::FieldMatrixType,
                data::FieldArrayType, poly::MultilinearType, poly::PointType,
                poly::QuadraticType, poly::UnivariateType,
                poly::PolynomialType>(
              [&](auto t) { return work.charge(t.getDomain().size()); })
          .Case<poly::ResidualType, poly::TableType>([&](auto t) {
            return work.charge(t.getDomain().size()) &&
                   work.charge(t.getRank().size());
          })
          .Case<commitment::PolynomialObjectType, commitment::VectorObjectType>(
              [&](auto t) {
                return work.charge(t.getScheme().size()) &&
                       work.charge(t.getKind().size());
              })
          .Case<runtime::CapabilityType>(
              [&](auto t) { return work.charge(t.getIdentity().size()); })
          .Case<runtime::RepresentedType>([&](auto t) {
            return work.charge(t.getRepresentation().size()) &&
                   work.charge(t.getChildren().size());
          })
          .Case<protocol_ir::ServiceReferenceType>(
              [&](auto t) { return work.charge(t.getContract().size()); })
          .Case<OpaqueType>(
              [&](auto t) { return work.charge(t.getTypeData().size()); })
          .Case<IntegerType>([&](auto t) { return work.charge(t.getWidth()); })
          .Case<data::VariantType>(
              [&](auto t) { return work.charge(t.getAlternatives().size()); })
          .Case<data::DomainType>(
              [&](auto t) { return work.charge(t.getItemTypes().size()); })
          .Case<exec::OutcomeType, runtime::TransferType>(
              [&](auto t) { return work.charge(t.getPayload().size()); })
          .Case<TupleType>([&](auto t) { return work.charge(t.size()); })
          .Case<FunctionType>([&](auto t) {
            return work.charge(t.getNumInputs()) &&
                   work.charge(t.getNumResults());
          })
          .Default(true);
  if (!fields)
    return false;
  if (auto vector = dyn_cast<VectorType>(value))
    if (!work.charge(vector.getScalableDims().size()))
      return false;
  if (auto shaped = dyn_cast<ShapedType>(value))
    if (shaped.hasRank() && !work.charge(shaped.getRank()))
      return false;
  return true;
}
// Do not multiply an untrusted shape in ShapedType::getNumElements before
// checking its product against the remaining allowance.
inline bool chargeOracleNativeElements(OracleNativeWork &work,
                                       mlir::ShapedType type) {
  if (!type.hasRank() || !work.charge(type.getRank()))
    return false;
  auto shape = type.getShape();
  if (llvm::is_contained(shape, int64_t(0)))
    return true;
  uint64_t count = 1;
  for (int64_t extent : shape) {
    if (extent < 0)
      return false;
    if (uint64_t(extent) > work.remaining / count)
      return work.chargeProduct(count, uint64_t(extent));
    count *= uint64_t(extent);
  }
  return work.charge(count);
}
inline bool chargeOracleNativeImmediate(OracleNativeWork &work,
                                        mlir::Attribute value) {
  using namespace mlir;
  if (!work.charge())
    return false;
  bool fields =
      llvm::TypeSwitch<Attribute, bool>(value)
          .Case<ArrayAttr>([&](auto a) { return work.charge(a.size()); })
          .Case<DictionaryAttr>([&](auto a) {
            // Named attributes contain both a name and a value.
            return work.chargeProduct(a.size(), 2);
          })
          .Case<StringAttr>(
              [&](auto a) { return work.charge(a.getValue().size()); })
          .Case<OpaqueAttr>(
              [&](auto a) { return work.charge(a.getAttrData().size()); })
          .Case<IntegerAttr>(
              [&](auto a) { return work.charge(a.getValue().getBitWidth()); })
          .Case<FloatAttr>([&](auto a) {
            return work.charge(llvm::APFloat::semanticsSizeInBits(
                a.getValue().getSemantics()));
          })
          .Case<DenseArrayAttr>([&](auto a) {
            return work.charge(a.size()) && work.charge(a.getRawData().size());
          })
          .Case<SymbolRefAttr>([&](auto a) {
            return work.charge(a.getNestedReferences().size());
          })
          .Case<FusedLoc>(
              [&](auto a) { return work.charge(a.getLocations().size()); })
          .Case<StridedLayoutAttr>(
              [&](auto a) { return work.charge(a.getStrides().size()); })
          .Case<data::AlternativeAttr>(
              [&](auto a) { return work.charge(a.getPayload().size()); })
          .Case<data::LayoutAttr>([&](auto a) {
            return work.charge(a.getFields().size()) &&
                   work.charge(a.getAlternatives().size()) &&
                   work.charge(a.getLeaves().size());
          })
          .Case<data::LayoutAlternativeAttr>(
              [&](auto a) { return work.charge(a.getFields().size()); })
          .Case<algebra::RingExpressionAttr>([&](auto a) {
            return work.charge(a.getInputs().size()) &&
                   work.charge(a.getNodes().size());
          })
          .Case<runtime::AssetReferenceAttr>(
              [&](auto a) { return work.charge(a.getFormat().size()); })
          .Case<runtime::OriginStepAttr>([&](auto a) {
            return work.charge(a.getProtocol().size()) &&
                   work.charge(a.getSite().size()) &&
                   work.charge(a.getAlternative().size());
          })
          .Case<runtime::QueryOriginAttr>([&](auto a) {
            return work.charge(a.getProtocol().size()) &&
                   work.charge(a.getSite().size()) &&
                   work.charge(a.getService().size()) &&
                   work.charge(a.getMethod().size()) &&
                   work.charge(a.getOwner().size());
          })
          .Case<runtime::MessageOriginAttr>([&](auto a) {
            return work.charge(a.getProtocol().size()) &&
                   work.charge(a.getSite().size()) &&
                   work.charge(a.getSchema().size()) &&
                   work.charge(a.getSender().size()) &&
                   work.charge(a.getReceiver().size());
          })
          .Case<runtime::StartOriginAttr>([&](auto a) {
            return work.charge(a.getProtocol().size()) &&
                   work.charge(a.getSite().size());
          })
          .Case<runtime::NativeOriginAttr>([&](auto a) {
            return work.charge(a.getEntry().size()) &&
                   work.charge(a.getPath().size());
          })
          .Case<protocol_ir::OracleKindAttr>(
              [&](auto a) { return work.charge(a.getIdentity().size()); })
          .Default(true);
  if (!fields)
    return false;
  if (auto dense = dyn_cast<DenseElementsAttr>(value)) {
    if (!chargeOracleNativeElements(work, dense.getType()))
      return false;
    if (auto strings = dyn_cast<DenseStringElementsAttr>(dense)) {
      // Avoid MLIR logical element-count multiplication for zero shapes.
      if (llvm::is_contained(strings.getType().getShape(), int64_t(0)))
        return true;
      for (auto text : strings.getValues<llvm::StringRef>())
        if (!work.charge(text.size()))
          return false;
    } else if (!work.charge(dense.getRawData().size()))
      return false;
  }
  if (auto resource = dyn_cast<DenseResourceElementsAttr>(value))
    if (!chargeOracleNativeElements(work, resource.getType()) ||
        !work.charge(resource.getRawHandle().getKey().size()) ||
        !work.charge(resource.getData().size()))
      return false;
  if (auto map = dyn_cast<AffineMapAttr>(value)) {
    auto affine = map.getValue();
    if (!work.charge(affine.getNumDims()) ||
        !work.charge(affine.getNumSymbols()) ||
        !work.charge(affine.getNumResults()))
      return false;
    for (auto expression : affine.getResults())
      if (!chargeOracleNativeAffine(work, expression))
        return false;
  }
  if (auto set = dyn_cast<IntegerSetAttr>(value)) {
    auto integerSet = set.getValue();
    if (!work.charge(integerSet.getNumDims()) ||
        !work.charge(integerSet.getNumSymbols()) ||
        !work.charge(integerSet.getNumConstraints()))
      return false;
    for (auto expression : integerSet.getConstraints())
      if (!chargeOracleNativeAffine(work, expression))
        return false;
  }
  return true;
}

// Bound recursive native subelement traversal before admission can recurse.
// Caching retains each node's full height, so a shared node reached later at a
// deeper position cannot bypass the depth limit. Every reference is charged.
class OracleNativeElements {
  OracleNativeWork &work;

  template <class Value, class Cache>
  bool visit(Value value, Cache &cache, unsigned depth,
             OracleNativeWork::StorageSummary &summary) {
    if (depth > 64 || !work.charge())
      return false;
    auto found = cache.find(value);
    if (found != cache.end()) {
      summary = found->second;
      return summary.height <= 64 - depth;
    }
    if (!chargeOracleNativeImmediate(work, value))
      return false;
    summary = {};
    OracleNativeWork::SymbolLeaves symbols;
    llvm::DenseSet<mlir::SymbolRefAttr> seen;
    auto append = [&](mlir::SymbolRefAttr symbol) {
      if (!work.charge(2))
        return false;
      if (seen.insert(symbol).second)
        symbols.push_back(symbol);
      return true;
    };
    bool ok = true;
    auto child = [&](auto nested, auto &heights) {
      if (!ok)
        return;
      OracleNativeWork::StorageSummary nestedSummary;
      ok = visit(nested, heights, depth + 1, nestedSummary);
      if (ok) {
        summary.height = std::max(summary.height, nestedSummary.height + 1);
        if (nestedSummary.symbols)
          for (auto symbol : *nestedSummary.symbols)
            if (!(ok = append(symbol)))
              break;
      }
    };
    value.walkImmediateSubElements(
        [&](mlir::Attribute nested) { child(nested, work.attributeStorage); },
        [&](mlir::Type nested) { child(nested, work.typeStorage); });
    if constexpr (std::is_same_v<Value, mlir::Attribute>)
      if (ok)
        if (auto symbol = mlir::dyn_cast<mlir::SymbolRefAttr>(value))
          ok = append(symbol);
    if (ok) {
      if (!work.charge(1 + !symbols.empty()))
        return false;
      if (!symbols.empty())
        summary.symbols =
            std::make_shared<const OracleNativeWork::SymbolLeaves>(
                std::move(symbols));
      cache.try_emplace(value, summary);
    }
    return ok;
  }

public:
  explicit OracleNativeElements(OracleNativeWork &work) : work(work) {}
  bool walk(mlir::Attribute value) {
    OracleNativeWork::StorageSummary summary;
    return visit(value, work.attributeStorage, 0, summary);
  }
  bool walk(mlir::Type value) {
    OracleNativeWork::StorageSummary summary;
    return visit(value, work.typeStorage, 0, summary);
  }
};

// Symbol leaves are collected in postorder by the required storage walk.
// Each exact immutable summary keeps the first observation of every symbol.
// Resolved operations and mutable symbol tables never enter this cache.
class OracleNativeReferences {
  OracleNativeWork &work;

public:
  explicit OracleNativeReferences(OracleNativeWork &work) : work(work) {}
  llvm::Expected<llvm::ArrayRef<mlir::SymbolRefAttr>>
  borrow(mlir::Attribute value) {
    if (!work.charge())
      return error("oracle-common-limit");
    auto found = work.attributeStorage.find(value);
    if (found == work.attributeStorage.end()) {
      OracleNativeElements elements(work);
      if (!elements.walk(value))
        return error("oracle-common-limit");
      found = work.attributeStorage.find(value);
    }
    if (!found->second.symbols)
      return llvm::ArrayRef<mlir::SymbolRefAttr>{};
    // Borrowers charge each consumed leaf in their own loop. The owned read
    // below additionally charges its actual vector copy.
    return llvm::ArrayRef<mlir::SymbolRefAttr>(*found->second.symbols);
  }
  llvm::Expected<OracleNativeWork::SymbolLeaves> read(mlir::Attribute value) {
    auto leaves = borrow(value);
    if (!leaves)
      return leaves.takeError();
    if (!work.charge(leaves->size()))
      return error("oracle-common-limit");
    return OracleNativeWork::SymbolLeaves(leaves->begin(), leaves->end());
  }
};

// Run before cloning, admission or building symbol/dominance inventories. This
// is a size bound, not admission or authority derived from producer metadata.
inline llvm::Error
boundOracleNativeIR(mlir::Operation *root, OracleNativeWork *shared = nullptr,
                    OracleNativeTraversals *traversals = nullptr) {
  if (!root)
    return error("oracle-common-body");
  OracleNativeWork local;
  OracleNativeWork &work = shared ? *shared : local;
  OracleNativeElements elements(work);
  llvm::SmallVector<mlir::Operation *> order;
  llvm::SmallVector<std::pair<mlir::Operation *, unsigned>> pending{{root, 0}};
  while (!pending.empty()) {
    auto [op, depth] = pending.pop_back_val();
    if (depth > 64 ||
        !work.operation(uint64_t(op->getNumOperands()) + op->getNumResults() +
                        op->getAttrs().size() + op->getNumRegions()))
      return error("oracle-common-limit");
    OracleNativeTraversal traversal{
        1 + uint64_t(op->getNumOperands()) + op->getNumResults() +
            op->getAttrs().size() + op->getNumRegions(),
        1};
    if (isSelectedControl(op) && op->getNumRegions() > selectedRegionArmLimit)
      return error("oracle-common-limit");
    // Nested attributes and types are input work too, including alternatives,
    // role rows and nominal storage layouts. Do this before any inventory copy.
    if (!elements.walk(op->getName().getIdentifier()) ||
        !elements.walk(op->getAttrDictionary()) || !elements.walk(op->getLoc()))
      return error("oracle-common-limit");
    for (auto type : op->getOperandTypes())
      if (!elements.walk(type))
        return error("oracle-common-limit");
    for (auto type : op->getResultTypes())
      if (!elements.walk(type))
        return error("oracle-common-limit");
    if (work.exhausted)
      return error("oracle-common-limit");
    unsigned nestedDepth =
        depth +
        !mlir::isa<mlir::ModuleOp, mlir::func::FuncOp,
                   protocol_ir::ProtocolModuleOp, protocol_ir::MathematicalOp>(
            op);
    for (auto &region : op->getRegions())
      for (auto &block : region) {
        if (!work.charge(1 + block.getNumArguments()))
          return error("oracle-common-limit");
        traversal.work += 1 + block.getNumArguments();
        for (auto argument : block.getArguments())
          if (!elements.walk(argument.getType()) ||
              !elements.walk(argument.getLoc()))
            return error("oracle-common-limit");
        for (auto &nested : block) {
          if (!work.charge())
            return error("oracle-common-limit");
          pending.emplace_back(&nested, nestedDepth);
        }
      }
    if (traversals) {
      if (!work.charge(2))
        return error("oracle-common-limit");
      traversals->try_emplace(op, traversal);
      order.push_back(op);
    }
  }
  if (traversals)
    for (auto *op : llvm::reverse(order)) {
      if (!work.charge())
        return error("oracle-common-limit");
      if (op == root)
        continue;
      auto &parent = (*traversals)[op->getParentOp()];
      const auto &child = traversals->find(op)->second;
      parent.work += child.work;
      parent.operations += child.operations;
    }
  return llvm::Error::success();
}

// Retained isolated Math must not hide logical Oracle values requiring a
// representation rewrite. Admission owns totality; this check owns the native
// preservation profile and charges every arm before cloning or comparison.
inline llvm::Error checkOracleNativeMathRegion(mlir::Operation *root,
                                               OracleNativeWork &work) {
  if (!mlir::isa_and_nonnull<data::BranchOp>(root))
    return error("oracle-common-profile");
  if (auto failure = boundOracleNativeIR(root, &work))
    return failure;
  auto ordinary = [&](mlir::Type type) {
    llvm::SmallVector<mlir::Type> types{type};
    llvm::SmallVector<mlir::Attribute> attributes;
    bool bounded = true;
    auto attribute = [&](mlir::Attribute child) {
      if (bounded && (bounded = work.charge()))
        attributes.push_back(child);
    };
    auto nestedType = [&](mlir::Type child) {
      if (bounded && (bounded = work.charge()))
        types.push_back(child);
    };
    while (bounded && (!types.empty() || !attributes.empty())) {
      if (!work.charge())
        return false;
      if (!types.empty()) {
        auto current = types.pop_back_val();
        if (mlir::isa<protocol_ir::OracleHandleType,
                      protocol_ir::OracleSequenceType>(current))
          return false;
        current.walkImmediateSubElements(attribute, nestedType);
      } else {
        attributes.pop_back_val().walkImmediateSubElements(attribute,
                                                           nestedType);
      }
    }
    return bounded;
  };
  auto checked = root->walk([&](mlir::Operation *op) {
    if (!work.charge() || !llvm::all_of(op->getOperandTypes(), ordinary) ||
        !llvm::all_of(op->getResultTypes(), ordinary))
      return mlir::WalkResult::interrupt();
    for (auto &region : op->getRegions())
      for (auto &block : region)
        if (!work.charge() || !llvm::all_of(block.getArgumentTypes(), ordinary))
          return mlir::WalkResult::interrupt();
    return mlir::WalkResult::advance();
  });
  if (checked.wasInterrupted())
    return error(work.exhausted ? "oracle-common-limit"
                                : "oracle-common-interface");
  return llvm::Error::success();
}

// Borrowed only within one composed operation while this exact module remains
// immutable. Never store this on an owner/context or reuse it after mutation.
// It records a size preflight, not source admission or count-law authority.
class OracleNativeSourcePreflight {
  friend class OracleVerificationContext;
  mlir::ModuleOp source;
  OracleNativeWork *work;
  std::unique_ptr<mlir::SymbolTableCollection> symbols;
  OracleNativeTraversals traversals;
  mutable OracleNativeReferences references;
  mutable llvm::DenseSet<mlir::Operation *> checkedSources;
  mutable bool admitted = false;
  mutable std::shared_ptr<const SourceExecutionClosure> admittedClosure;
  OracleNativeSourcePreflight(mlir::ModuleOp source, OracleNativeWork &work,
                              OracleNativeTraversals traversals)
      : source(source), work(&work),
        symbols(std::make_unique<mlir::SymbolTableCollection>()),
        traversals(std::move(traversals)), references(work) {}

public:
  OracleNativeSourcePreflight(const OracleNativeSourcePreflight &) = delete;
  OracleNativeSourcePreflight(OracleNativeSourcePreflight &&) = default;
  static llvm::Expected<OracleNativeSourcePreflight>
  read(mlir::ModuleOp source, OracleNativeWork &work) {
    OracleNativeTraversals traversals;
    if (auto e = boundOracleNativeIR(source, &work, &traversals))
      return std::move(e);
    // Reserve symbol indexing before lazily constructing any table. Reuse the
    // same collection across entry closures so lazy lookup cannot rescan the
    // entire unit independently for every entry.
    for (const auto &item : traversals) {
      if (!work.charge())
        return error("oracle-common-limit");
      auto *op = item.first;
      if (op->hasTrait<mlir::OpTrait::SymbolTable>())
        for (auto &region : op->getRegions())
          for (auto &block : region)
            for (auto &nested : block)
              if (!work.charge(1 + nested.getAttrDictionary().size()))
                return error("oracle-common-limit");
    }
    return OracleNativeSourcePreflight(source, work, std::move(traversals));
  }
  bool matches(mlir::ModuleOp module, OracleNativeWork &allowance) const {
    return source == module && work == &allowance;
  }
  mlir::SymbolTableCollection &getSymbols() const { return *symbols; }
  llvm::Expected<llvm::SmallVector<mlir::SymbolRefAttr>>
  getReferences(mlir::Attribute value) const {
    return references.read(value);
  }
  llvm::Expected<llvm::ArrayRef<mlir::SymbolRefAttr>>
  borrowReferences(mlir::Attribute value) const {
    return references.borrow(value);
  }
  bool reserveTraversal(mlir::Operation *root) const {
    if (!work->charge())
      return false;
    auto found = traversals.find(root);
    return found != traversals.end() &&
           work->traversal(found->second.work, found->second.operations);
  }
  // This borrow is valid only while the exact source remains immutable.
  // Cache successful ordinary admission, never candidate count equations.
  mlir::LogicalResult admit() const;
  bool sourceChecked(mlir::Operation *program) const {
    return checkedSources.contains(program);
  }
  bool rememberSource(mlir::Operation *program) const {
    if (!work->charge())
      return false;
    checkedSources.insert(program);
    return true;
  }
};
inline llvm::Error checkOracleNativePreflight(
    mlir::ModuleOp source, OracleNativeWork &work,
    const OracleNativeSourcePreflight *preflight = nullptr) {
  if (!work.charge())
    return error("oracle-common-limit");
  if (preflight)
    return preflight->matches(source, work) ? llvm::Error::success()
                                            : error("oracle-common-body");
  return boundOracleNativeIR(source, &work);
}

// Protocol branches are materialized by this consumer. Mathematical branches
// need no second interpreter: ordinary admission checks every arm. Retained
// Func definitions are compared by the final inventory; inline Math is cloned
// with native operand remapping and recursively checked against actual SSA.
inline llvm::Error checkOracleNativeSource(
    mlir::ModuleOp source, protocol_ir::MathematicalOp program,
    OracleNativeWork *shared = nullptr,
    const OracleNativeSourcePreflight *preflight = nullptr) {
  OracleNativeWork local;
  OracleNativeWork &work = shared ? *shared : local;
  std::optional<OracleNativeSourcePreflight> bounded;
  if (!preflight) {
    auto read = OracleNativeSourcePreflight::read(source, work);
    if (!read)
      return read.takeError();
    bounded.emplace(std::move(*read));
    preflight = &*bounded;
  }
  if (auto e = checkOracleNativePreflight(source, work, preflight))
    return e;
  if (!program || program->getParentOfType<mlir::ModuleOp>() != source)
    return error("oracle-common-body");
  // The same exact entry is requested again by requirements after emission's
  // early source check. Reuse only that completed native profile inspection;
  // distinct entry closures still debit all of their actual visits.
  if (preflight->sourceChecked(program))
    return llvm::Error::success();
  auto &symbols = preflight->getSymbols();
  llvm::DenseSet<mlir::Operation *> visited;
  llvm::SmallVector<mlir::Operation *> pending{program};
  while (!pending.empty()) {
    auto *op = pending.pop_back_val();
    if (!work.charge())
      return error("oracle-common-limit");
    if (!visited.insert(op).second)
      continue;
    if (!work.charge(op->getNumOperands()) || !work.charge(op->getNumResults()))
      return error("oracle-common-limit");
    if (isSelectedControl(op)) {
      bool common =
          mlir::isa<protocol_ir::BranchOp>(op) &&
          op->getParentOfType<protocol_ir::MathematicalOp>() == program;
      bool retained = mlir::isa<data::BranchOp>(op);
      if (!common && !retained)
        return error("oracle-realization-control-profile");
    }
    auto references = preflight->getReferences(op->getAttrDictionary());
    if (!references)
      return references.takeError();
    for (auto symbol : *references) {
      if (!work.charge(1 + symbol.getRootReference().getValue().size()))
        return error("oracle-common-limit");
      if (auto *callee = symbols.lookupNearestSymbolFrom(op, symbol))
        pending.push_back(callee);
    }
    for (auto &region : op->getRegions())
      for (auto &block : region) {
        if (!work.charge())
          return error("oracle-common-limit");
        for (auto &nested : block) {
          if (!work.charge())
            return error("oracle-common-limit");
          pending.push_back(&nested);
        }
      }
  }
  return preflight->rememberSource(program) ? llvm::Error::success()
                                            : error("oracle-common-limit");
}
} // namespace zkc::protocol
#endif
