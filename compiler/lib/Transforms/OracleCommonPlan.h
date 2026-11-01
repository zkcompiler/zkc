#ifndef ZKC_TRANSFORMS_ORACLECOMMONPLAN_H
#define ZKC_TRANSFORMS_ORACLECOMMONPLAN_H
#include "NativeBindingApplication.h"
#include "OracleCommonRealization.h"
#include "OracleQueryCapacity.h"
#include "OracleQueryExchange.h"
#include <memory>
#include <optional>
namespace zkc::protocol {
// A finite declarative recipe, derived only from the original and checked
// primitive identities. IDs are lexical SSA coordinates, never native handles.
// The emitter constructs MLIR; a separate reader interprets this grammar
// against actual source-execution closures and common operations.
struct OracleCommonBlock;
struct OracleCommonInstruction {
  std::string name;
  mlir::DictionaryAttr attributes;
  std::vector<unsigned> inputs, outputs;
  std::vector<mlir::Type> types;
  std::shared_ptr<OracleCommonBlock> region;
};
struct OracleCommonBlock {
  std::vector<unsigned> arguments;
  std::vector<mlir::Type> types;
  std::vector<OracleCommonInstruction> instructions;
};
struct OracleLocalInstruction {
  NativeBindingApplication binding;
  std::vector<mlir::Attribute> parameters;
  std::vector<unsigned> inputs, outputs;
  std::vector<mlir::Type> types;
};
struct OracleLocalRecipe : OracleHelperSignature {
  std::vector<OracleLocalInstruction> instructions;
  std::vector<unsigned> results;
};
using OracleCommonLocal = OracleLocalRecipe;
inline const OracleHelperSignature &
localSignature(const OracleCommonLocal &local) {
  return local;
}
struct OracleCommonPlan {
  mlir::DictionaryAttr attributes;
  OracleCommonBlock body;
  std::vector<OracleCommonLocal> locals;
  std::vector<OracleCommonOccurrence> occurrences;
  std::vector<OracleCommonQueryBlock> queryBlocks;
  std::vector<OracleInputShape> inputShapes;
  std::vector<OracleResultStore> resultStores;
  std::vector<OracleResultReference> resultReferences;
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
llvm::Expected<std::vector<std::string>> oracleEntries(mlir::ModuleOp);
llvm::Expected<OracleCommonRequirements>
oracleRequirements(mlir::ModuleOp prepared, llvm::StringRef entry,
                   llvm::ArrayRef<OracleRootSelection> selections);
llvm::Expected<OracleCommonPlan> planOracleCommon(
    mlir::ModuleOp prepared, llvm::StringRef entry,
    const OracleCommonRequirements &, llvm::ArrayRef<OracleCommonController>,
    llvm::ArrayRef<std::vector<mlir::func::FuncOp>> allocators,
    llvm::ArrayRef<OracleMerkleFunctions> merkle,
    OracleAuthentication authentication, llvm::ArrayRef<OracleCommonRemote>,
    llvm::ArrayRef<OracleCommonBatch>);
// Independent native reader, shared by the typed edge and external record
// boundary. Facts are written only after the complete candidate has passed.
class OracleVerificationContext;
llvm::Error checkOracleRealizationModel(
    const OracleVerificationContext &source,
    const OracleVerificationContext &target,
    llvm::ArrayRef<OracleCommonEntryRealization> entries,
    llvm::ArrayRef<OracleRootSelection> selections,
    OracleAuthentication authentication,
    OracleRealizationFacts *facts = nullptr);
} // namespace zkc::protocol
#endif
