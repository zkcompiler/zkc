#ifndef ZKC_TRANSFORMS_ORACLECOMMONPLAN_H
#define ZKC_TRANSFORMS_ORACLECOMMONPLAN_H
#include "../Dialect/AdmissionPrivate.h"
#include "NativeBindingApplication.h"
#include "OracleCommonRealization.h"
#include "OracleQueryCapacity.h"
#include "OracleQueryExchange.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include <memory>
#include <optional>
namespace zkc::mathematical {
class RealizationEmitter;
}
namespace zkc::protocol {
// Only scoped local helper specifications retain numeric formal slots. Common
// bodies are native MLIR with explicit borrowed original/candidate
// associations.
struct OracleLocalInstruction {
  NativeBindingApplication binding;
  std::vector<mlir::Attribute> parameters;
  std::vector<unsigned> inputs, outputs;
  std::vector<mlir::Type> types;
};
struct OracleLocalRecipe : OracleHelperSignature {
  std::vector<OracleLocalInstruction> instructions;
  std::vector<unsigned> results;
  unsigned nextResult = 0;
};
struct OracleNativeWork;
class OracleNativeSourcePreflight;
// Charge before copying any signature or instruction storage. Failed appends
// leave the recipe unchanged and the shared allowance remains exhausted.
llvm::Expected<OracleLocalRecipe> oracleLocalRecipe(mlir::TypeRange inputs,
                                                    mlir::TypeRange outputs,
                                                    OracleNativeWork &);
llvm::Expected<std::vector<unsigned>>
appendOracleLocalInstruction(OracleLocalRecipe &, NativeBindingApplication,
                             mlir::TypeRange, llvm::ArrayRef<unsigned>,
                             llvm::ArrayRef<mlir::Attribute>,
                             OracleNativeWork &);
// Actual local emission, including the current candidate's name inventory.
// Refusal leaves only private scratch IR, never a publishable helper.
llvm::Expected<mlir::func::FuncOp>
emitOracleLocalHelper(protocol_ir::ProtocolModuleOp, const OracleLocalRecipe &,
                      OracleNativeWork &);
llvm::Expected<mlir::func::FuncOp>
emitOracleLocalHelper(protocol_ir::ProtocolModuleOp, const OracleLocalRecipe &,
                      OracleNativeWork &,
                      std::unique_ptr<mathematical::RealizationEmitter> &);
using OracleCommonLocal = OracleLocalRecipe;
inline const OracleHelperSignature &
localSignature(const OracleCommonLocal &local) {
  return local;
}
struct OracleCommonRequirements;
struct OracleCommonAnalysis {
  std::shared_ptr<const OracleCommonRequirements> requirements;
  // Private scratch only: the model reader publishes no equations until all
  // helpers, actual bodies and the complete declaration inventory agree.
  std::vector<detail::OracleRepeatCount> repeatCounts;
  mlir::DictionaryAttr attributes;
  std::vector<OracleCommonLocal> locals;
  std::vector<OracleCommonOccurrence> occurrences;
  std::vector<OracleCommonQueryBlock> queryBlocks;
  std::vector<OracleInputShape> inputShapes;
  std::vector<OracleResultStore> resultStores;
  std::vector<OracleResultReference> resultReferences;
};
struct OracleCommonPlan : OracleCommonAnalysis {
  // source is borrowed from the immutable admitted owner retained by emission.
  protocol_ir::MathematicalOp source;
  std::unique_ptr<mlir::Block> body;
  std::vector<std::pair<mlir::Operation *, mlir::Operation *>> associations;
};
struct OracleControllerRequirement {
  std::string role;
  protocol_ir::OracleKindAttr kind;
  OracleControllerAccess access;
};
struct OracleCommonRequirements {
  OracleAnchorStorage storage;
  std::vector<OracleTableRealization> realizations;
  OracleQuerySize capacity;
  OracleQueryCapacity queryCapacity;
  std::vector<OracleControllerRequirement> controllers;
};
// Original declaration order determines the complete oracle-entry inventory.
llvm::Expected<std::vector<std::string>>
oracleEntries(mlir::ModuleOp, OracleNativeWork *work = nullptr,
              const OracleNativeSourcePreflight *preflight = nullptr);
llvm::Expected<OracleCommonRequirements>
oracleRequirements(mlir::ModuleOp prepared, llvm::StringRef entry,
                   llvm::ArrayRef<OracleRootSelection> selections,
                   OracleNativeWork *work = nullptr,
                   const OracleNativeSourcePreflight *preflight = nullptr);
llvm::Expected<OracleCommonPlan> materializeOracleCommon(
    mlir::ModuleOp prepared, llvm::StringRef entry,
    const OracleCommonRequirements &, llvm::ArrayRef<OracleCommonController>,
    llvm::ArrayRef<std::vector<mlir::func::FuncOp>> allocators,
    llvm::ArrayRef<OracleMerkleFunctions> merkle,
    OracleAuthentication authentication, llvm::ArrayRef<OracleCommonRemote>,
    llvm::ArrayRef<OracleCommonBatch>, OracleNativeWork *work = nullptr,
    const OracleNativeSourcePreflight *preflight = nullptr);
// Read the actual candidate against the original and checked primitive models.
// The caller must validate the helpers through checkOracleRealizationModel;
// this entry point is also the record encoder's source of derived fields.
// It never constructs expected IR or consults emitter occurrence metadata.
llvm::Expected<OracleCommonAnalysis> readOracleCommon(
    mlir::ModuleOp prepared, mlir::ModuleOp candidate, llvm::StringRef entry,
    const OracleCommonRequirements &, llvm::ArrayRef<OracleCommonController>,
    llvm::ArrayRef<std::vector<mlir::func::FuncOp>> allocators,
    llvm::ArrayRef<OracleMerkleFunctions> merkle,
    OracleAuthentication authentication, llvm::ArrayRef<OracleCommonRemote>,
    llvm::ArrayRef<OracleCommonBatch>, OracleNativeWork *work = nullptr,
    const OracleNativeSourcePreflight *sourcePreflight = nullptr,
    const OracleNativeSourcePreflight *candidatePreflight = nullptr);
// Independent native reader, shared by the typed edge and external record
// boundary. Facts and optional analyses are output-only and written only after
// the complete candidate has passed. They grant no unchecked public API entry.
class OracleVerificationContext;
llvm::Expected<OracleCommonRealization>
emitOracleRealizationWithWork(mlir::ModuleOp, const OracleRealizationPolicy &,
                              OracleNativeWork &);
llvm::Expected<OracleRealizationFacts> checkOracleRealizationWithWork(
    mlir::ModuleOp, const OracleCommonRealization &,
    const OracleRealizationPolicy &, OracleNativeWork &,
    const OracleNativeSourcePreflight *sourcePreflight = nullptr,
    const OracleNativeSourcePreflight *candidatePreflight = nullptr,
    std::vector<OracleCommonAnalysis> *analyses = nullptr,
    std::vector<OracleRootSelection> *checkedSelections = nullptr);
llvm::Expected<OracleRealizationPublication>
exportOracleRealizationWithWork(mlir::ModuleOp, const OracleCommonRealization &,
                                const OracleRealizationPolicy &,
                                OracleNativeWork &);
llvm::Expected<llvm::json::Array>
writeOracleRecordedTypesWithWork(mlir::TypeRange, OracleNativeWork &);
llvm::Expected<llvm::SmallVector<mlir::Type>>
readOracleRecordedTypesWithWork(mlir::MLIRContext *, const llvm::json::Array &,
                                OracleNativeWork &, bool *canonical = nullptr);
llvm::Error checkOracleRealizationRecordWithWork(
    mlir::ModuleOp, mlir::ModuleOp, llvm::StringRef,
    const OracleRealizationPolicy &, OracleNativeWork &);
llvm::Error checkOracleRealizationModel(
    const OracleVerificationContext &source,
    const OracleVerificationContext &target,
    llvm::ArrayRef<OracleCommonEntryRealization> entries,
    llvm::ArrayRef<OracleRootSelection> selections,
    OracleAuthentication authentication,
    OracleRealizationFacts *facts = nullptr, OracleNativeWork *work = nullptr,
    const OracleNativeSourcePreflight *sourcePreflight = nullptr,
    const OracleNativeSourcePreflight *candidatePreflight = nullptr,
    std::vector<OracleCommonAnalysis> *analyses = nullptr);
} // namespace zkc::protocol
#endif
