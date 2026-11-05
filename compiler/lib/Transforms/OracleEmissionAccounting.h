#ifndef ZKC_TRANSFORMS_ORACLEEMISSIONACCOUNTING_H
#define ZKC_TRANSFORMS_ORACLEEMISSIONACCOUNTING_H

#include "OracleAccounting.h"
#include "OracleVirtualFunctions.h"
#include "RealizationEmission.h"
#include "mlir/IR/Builders.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "llvm/ADT/SmallPtrSet.h"
#include <functional>

namespace zkc::protocol {
inline void reserveOracleEmission(OracleNativeWork &work, uint64_t amount) {
  if (!work.charge(amount))
    throw OracleAccountingLimit{};
}
inline std::function<void(uint64_t)>
oracleEmissionReservation(OracleNativeWork &work) {
  return [&work](uint64_t amount) { reserveOracleEmission(work, amount); };
}
// One binding inventory for a composite private candidate. It stores only
// exact bindings created by this emitter. New names always use live lookup.
// The scope ends before its candidate is destroyed, including cancellation.
class OracleEmissionSession {
  friend class OracleOwnedRealization;
  friend class OraclePrivateComposite;
  OracleNativeWork &work;
  mlir::Operation *unit;
  OracleEmissionSession *previous;
  unsigned next = 0;
  bool transactional = false, committed = false;
  llvm::SmallPtrSet<mlir::Operation *, 32> original;
  std::unique_ptr<mlir::SymbolTable> symbols;
  std::unique_ptr<mathematical::RealizationEmitter> emitter;
  llvm::DenseMap<mlir::FunctionType, mlir::func::FuncOp> identityRegions;
  bool privateOwned = false;
  llvm::DenseMap<mlir::ArrayAttr, mlir::func::FuncOp> anchorLookups;
  llvm::DenseMap<mlir::ArrayAttr, mlir::func::FuncOp> controllerCounts;
  llvm::DenseMap<mlir::Attribute, mlir::func::FuncOp> tableReads;
  llvm::DenseMap<mlir::Operation *, OracleVirtualFunctions> virtualFunctions;
  void own() { privateOwned = true; }

public:
  bool ownsCandidate(mlir::Operation *owner) const {
    return privateOwned && owner == unit && bool(symbols);
  }
  OracleEmissionSession(OracleNativeWork &work, mlir::Operation *unit,
                        bool transactional = false)
      : work(work), unit(unit), previous(work.emission),
        transactional(transactional) {
    // This table is maintained by every insertion listener in the private
    // generation scope. It is the current live inventory, not a reused module
    // snapshot. No direct root insertion/rename/erase is permitted in scope.
    for (auto &declaration : unit->getRegion(0).front()) {
      reserveOracleEmission(work, 1 + declaration.getAttrDictionary().size());
      if (transactional) {
        reserveOracleEmission(work, 1);
        original.insert(&declaration);
      }
      if (auto name = mlir::SymbolTable::getSymbolName(&declaration))
        reserveOracleEmission(work, name.size());
    }
    symbols = std::make_unique<mlir::SymbolTable>(unit);
    work.emission = this;
  }
  ~OracleEmissionSession() {
    finish();
    if (!transactional || committed)
      return;
    // Insertion notification runs after linking the operation. Even the
    // operation whose debit threw must be removed. Two allocation-free walks
    // first break all references, then erase additions. Original roots and
    // their bodies are never changed by these standalone producers.
    for (auto &op : unit->getRegion(0).front())
      if (!original.contains(&op))
        op.dropAllReferences();
    for (auto &op : llvm::make_early_inc_range(unit->getRegion(0).front()))
      if (!original.contains(&op))
        op.erase();
  }
  void commit() { committed = true; }
  void finish() {
    if (!symbols)
      return;
    identityRegions.clear();
    anchorLookups.clear();
    controllerCounts.clear();
    tableReads.clear();
    virtualFunctions.clear();
    emitter.reset();
    symbols.reset();
    work.emission = previous;
  }
  mlir::Operation *lookup(mlir::Operation *owner, llvm::StringRef name) {
    assert(owner == unit && symbols);
    (void)owner;
    reserveOracleEmission(work, 1 + name.size());
    return symbols->lookup(name);
  }
  mlir::Operation *lookup(mlir::Operation *owner, mlir::StringAttr name) {
    assert(owner == unit && symbols);
    (void)owner;
    reserveOracleEmission(work, 1);
    return symbols->lookup(name);
  }
  mlir::func::FuncOp findAnchorLookup(mlir::ArrayAttr key) {
    if (!privateOwned)
      return {};
    reserveOracleEmission(work, 1);
    auto found = anchorLookups.find(key);
    if (found == anchorLookups.end())
      return {};
    auto function = found->second;
    auto *live = lookup(unit, function.getSymNameAttr());
    assert(live == function.getOperation());
    (void)live;
    return function;
  }
  void rememberAnchorLookup(mlir::ArrayAttr key, mlir::func::FuncOp function) {
    if (privateOwned) {
      reserveOracleEmission(work, 1);
      anchorLookups.try_emplace(key, function);
    }
  }
  mlir::func::FuncOp findControllerCount(mlir::ArrayAttr key) {
    if (!privateOwned)
      return {};
    reserveOracleEmission(work, 1);
    auto found = controllerCounts.find(key);
    if (found == controllerCounts.end())
      return {};
    auto function = found->second;
    auto *live = lookup(unit, function.getSymNameAttr());
    assert(live == function.getOperation());
    (void)live;
    return function;
  }
  void rememberControllerCount(mlir::ArrayAttr key,
                               mlir::func::FuncOp function) {
    if (privateOwned) {
      reserveOracleEmission(work, 1);
      controllerCounts.try_emplace(key, function);
    }
  }
  mlir::func::FuncOp findTableRead(mlir::Attribute kind) {
    if (!privateOwned)
      return {};
    reserveOracleEmission(work, 1);
    auto found = tableReads.find(kind);
    if (found == tableReads.end())
      return {};
    auto function = found->second;
    auto *live = lookup(unit, function.getSymNameAttr());
    assert(live == function.getOperation());
    (void)live;
    return function;
  }
  void rememberTableRead(mlir::Attribute kind, mlir::func::FuncOp function) {
    if (privateOwned) {
      reserveOracleEmission(work, 1);
      tableReads.try_emplace(kind, function);
    }
  }
  std::optional<OracleVirtualFunctions>
  findVirtualFunctions(mlir::Operation *source) {
    if (!privateOwned)
      return std::nullopt;
    reserveOracleEmission(work, 1);
    auto found = virtualFunctions.find(source);
    if (found == virtualFunctions.end())
      return std::nullopt;
    auto &functions = found->second;
    auto check = [&](mlir::func::FuncOp function) {
      auto *live = lookup(unit, function.getSymNameAttr());
      assert(live == function.getOperation());
      (void)live;
    };
    check(functions.answer);
    for (const auto &query : functions.queries) {
      reserveOracleEmission(work, 4 + query.site.size());
      check(query.position);
    }
    return functions;
  }
  void rememberVirtualFunctions(mlir::Operation *source,
                                const OracleVirtualFunctions &functions) {
    if (!privateOwned)
      return;
    reserveOracleEmission(work, 1);
    for (const auto &query : functions.queries)
      reserveOracleEmission(work, 4 + query.site.size());
    virtualFunctions.try_emplace(source, functions);
  }
  void inserted(mlir::Operation *op) {
    if (op->getParentOp() != unit)
      return;
    auto name = mlir::SymbolTable::getSymbolName(op);
    if (!name)
      return;
    reserveOracleEmission(work, 2 + name.size());
    auto *existing = symbols->lookup(name);
    assert((!existing || existing == op) && "generated symbol collision");
    if (!existing) {
      auto insertedName = symbols->insert(op);
      assert(insertedName == name && "live insertion must not rename");
      (void)insertedName;
    }
  }
  // A closed identity region has no caller callback or predicate. Completed
  // functions are private to this generation scope; every reuse checks the
  // maintained live symbol inventory before returning the exact created body.
  mlir::func::FuncOp identityRegion(mlir::OpBuilder &builder,
                                    mlir::Location loc,
                                    mlir::TypeRange fields) {
    reserveOracleEmission(work, 8 + 4 * fields.size());
    auto key = builder.getFunctionType(fields, fields);
    auto found = identityRegions.find(key);
    if (found != identityRegions.end()) {
      auto function = found->second;
      auto *live = lookup(unit, function.getSymNameAttr());
      assert(live == function.getOperation());
      (void)live;
      return function;
    }
    std::string name;
    do {
      reserveOracleEmission(work, 40);
      name = "_oracle_identity_region_" + std::to_string(ordinal());
    } while (lookup(unit, name));
    mlir::OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToEnd(&unit->getRegion(0).front());
    llvm::SmallVector<mlir::Type> inputs{
        runtime::ScopeType::get(builder.getContext())};
    llvm::append_range(inputs, fields);
    auto outcome = exec::OutcomeType::get(
        builder.getContext(), llvm::SmallVector<mlir::Type>(fields));
    auto function = mlir::func::FuncOp::create(
        builder, loc, name, builder.getFunctionType(inputs, outcome));
    function.setPrivate();
    function.setNoInline(true);
    function->setAttr("runtime.region", builder.getUnitAttr());
    reserveOracleEmission(work, 1 + function.getNumArguments());
    builder.setInsertionPointToEnd(function.addEntryBlock());
    exec::ScopedExecutionBuilder body(builder, function);
    body.complete(function.getArguments().drop_front());
    reserveOracleEmission(work, 1);
    identityRegions.try_emplace(key, function);
    return function;
  }
  OracleEmissionSession(const OracleEmissionSession &) = delete;
  unsigned ordinal() { return next++; }
  mathematical::RealizationEmitter &get(mlir::Operation *owner) {
    assert(owner == unit && "binding session belongs to its exact candidate");
    (void)owner;
    if (!emitter)
      emitter = std::make_unique<mathematical::RealizationEmitter>(
          unit, "_oracle_binding_", oracleEmissionReservation(work),
          [this](llvm::StringRef name) { return lookup(unit, name); });
    return *emitter;
  }
};
// Standalone primitive generation owns the same private live inventory as a
// composed candidate. Nested producers borrow the existing session; raw
// admission and final primitive readers keep their independent checks.
inline std::unique_ptr<OracleEmissionSession>
startOracleEmissionSession(OracleNativeWork &work, mlir::Operation *unit) {
  if (work.emission)
    return {};
  return std::make_unique<OracleEmissionSession>(work, unit, true);
}
inline void commitOracleEmissionSession(
    const std::unique_ptr<OracleEmissionSession> &session) {
  if (session)
    session->commit();
}
// Observe actual native builder insertions, including scoped outcome plumbing
// generated inside builder helpers. The operation is already linked to private
// scratch when MLIR notifies us; cancellation immediately unwinds its owner or
// rollback guard. No builder work continues and no partial result escapes.
// Primitive capacity reservations remain separate, conservative ceilings.
class OracleEmissionListener final : public mlir::OpBuilder::Listener {
  OracleNativeWork &work;

public:
  explicit OracleEmissionListener(OracleNativeWork &work) : work(work) {}
  void notifyOperationInserted(mlir::Operation *op,
                               mlir::OpBuilder::InsertPoint) override {
    if (!work.operation(1 + op->getNumOperands() + op->getNumResults() +
                        op->getNumRegions() + op->getAttrDictionary().size()))
      throw OracleAccountingLimit{};
    if (work.emission)
      work.emission->inserted(op);
  }
  void notifyBlockInserted(mlir::Block *block, mlir::Region *,
                           mlir::Region::iterator) override {
    if (!work.charge(1 + block->getNumArguments()))
      throw OracleAccountingLimit{};
  }
};
// Coordinate generated spellings across private emitters. Each chosen name
// still gets a charged collision check against the maintained live inventory.
inline unsigned oracleEmissionOrdinal(OracleNativeWork &work, unsigned &local) {
  return work.emission ? work.emission->ordinal() : local++;
}
class OracleBindingEmitter {
  std::unique_ptr<mathematical::RealizationEmitter> owned;
  mathematical::RealizationEmitter *emitter;

public:
  OracleBindingEmitter(mlir::Operation *unit, llvm::StringRef prefix,
                       OracleNativeWork &work) {
    if (work.emission)
      emitter = &work.emission->get(unit);
    else {
      owned = std::make_unique<mathematical::RealizationEmitter>(
          unit, prefix, oracleEmissionReservation(work));
      emitter = owned.get();
    }
  }
  mlir::FlatSymbolRefAttr binding(mlir::OpBuilder &builder, mlir::Location loc,
                                  const NativeBindingApplication &application) {
    return emitter->binding(builder, loc, application);
  }
};
// The private session maintains every live insertion. Outside that scope,
// reserve the actual inventory inspection and MLIR's static scan first.
inline mlir::Operation *lookupOracleEmissionSymbol(mlir::Operation *unit,
                                                   llvm::StringRef name,
                                                   OracleNativeWork &work) {
  if (work.emission)
    return work.emission->lookup(unit, name);
  reserveOracleEmission(work, 1 + name.size());
  for (auto &declaration : unit->getRegion(0).front()) {
    reserveOracleEmission(work, 2);
    if (!work.chargeProduct(2, declaration.getAttrDictionary().size()))
      throw OracleAccountingLimit{};
  }
  return mlir::SymbolTable::lookupSymbolIn(unit, name);
}
} // namespace zkc::protocol
#endif
