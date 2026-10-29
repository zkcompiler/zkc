#ifndef ZKC_TRANSFORMS_ORACLECOMMONPLAN_H
#define ZKC_TRANSFORMS_ORACLECOMMONPLAN_H
#include "OracleCommonRealization.h"
#include "OracleQueryExchange.h"
#include "zkc/Contracts/Binding.h"
#include <memory>
#include <variant>
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
  BindingApplication binding;
  std::vector<std::string> parameters;
  std::vector<unsigned> inputs, outputs;
  std::vector<mlir::Type> types;
};
struct OracleLocalRecipe : OracleHelperSignature {
  std::vector<OracleLocalInstruction> instructions;
  std::vector<unsigned> results;
};
// Wire packets may carry non-mathematical proof values. Packing and matching
// therefore retain the existing scoped execution and outcome boundary.
struct OraclePacketRecipe : OracleHelperSignature {
  bool pack;
};
using OracleCommonLocal =
    std::variant<OracleLocalRecipe, OracleExchangeRecipe, OraclePacketRecipe>;
inline const OracleHelperSignature &
localSignature(const OracleCommonLocal &local) {
  return std::visit(
      [](const auto &recipe) -> const OracleHelperSignature & {
        return recipe;
      },
      local);
}
// Generated identifiers use the program grammar. Full source coordinates stay
// separate from their short spelling, for the eventual realization record.
struct OracleCommonOccurrence {
  std::string site, purpose, role;
  std::vector<unsigned> sourcePath;
};
struct OracleCommonQueryBlock {
  std::vector<std::vector<unsigned>> queries;
  // Logical query -> physical request slot for a fixed base-query block.
  // Null for ideal evaluation or a dynamic virtual controller.
  std::optional<std::vector<unsigned>> requestGroups;
};
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
  std::vector<OracleControllerRequirement> controllers;
};
// Original declaration order determines the complete oracle-entry inventory.
llvm::Expected<std::vector<std::string>> oracleEntries(mlir::ModuleOp);
llvm::Expected<OracleCommonRequirements>
oracleRequirements(mlir::ModuleOp prepared, llvm::StringRef entry,
                   llvm::ArrayRef<OracleRootSelection> selections);
llvm::Expected<OracleCommonPlan>
planOracleCommon(mlir::ModuleOp prepared, llvm::StringRef entry,
                 const OracleCommonRequirements &,
                 llvm::ArrayRef<OracleCommonController>,
                 llvm::ArrayRef<std::vector<mlir::func::FuncOp>> allocators,
                 llvm::ArrayRef<OracleMerkleFunctions> merkle,
                 OracleAuthentication authentication);
// Internal parsed-model reader. Only the record reader publishes its result.
class OracleVerificationContext;
llvm::Error checkOracleRealizationModel(
    const OracleVerificationContext &source,
    const OracleVerificationContext &target,
    llvm::ArrayRef<OracleCommonEntryRealization> entries,
    llvm::ArrayRef<OracleRootSelection> selections,
    OracleAuthentication authentication);
} // namespace zkc::protocol
#endif
