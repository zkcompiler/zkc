#ifndef ZKC_TRANSFORMS_ORACLECOMMONPLAN_H
#define ZKC_TRANSFORMS_ORACLECOMMONPLAN_H
#include "OracleCommonRealization.h"
#include "zkc/Contracts/Binding.h"
#include <memory>
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
struct OracleLocalRecipe {
  std::string name;
  std::vector<mlir::Type> inputs, outputs;
  std::vector<OracleLocalInstruction> instructions;
  std::vector<unsigned> results;
};
// Generated identifiers use the program grammar. Full source coordinates stay
// separate from their short spelling, for the eventual realization record.
struct OracleCommonOccurrence {
  std::string site, purpose, role;
  std::vector<unsigned> sourcePath;
};
struct OracleCommonPlan {
  mlir::DictionaryAttr attributes;
  OracleCommonBlock body;
  std::vector<OracleLocalRecipe> locals;
  std::vector<OracleCommonOccurrence> occurrences;
};
struct OracleControllerRequirement {
  std::string role;
  protocol_ir::OracleKindAttr kind;
  OracleControllerAccess access;
};
struct OracleCommonRequirements {
  OracleAnchorStorage storage;
  OracleQuerySize capacity;
  std::vector<OracleControllerRequirement> controllers;
};
// Original declaration order determines the complete oracle-entry inventory.
llvm::Expected<std::vector<std::string>> idealOracleEntries(mlir::ModuleOp);
llvm::Expected<OracleCommonRequirements>
idealOracleRequirements(mlir::ModuleOp prepared, llvm::StringRef entry);
llvm::Expected<OracleCommonPlan> planIdealOracleCommon(
    mlir::ModuleOp prepared, llvm::StringRef entry,
    const OracleCommonRequirements &, llvm::ArrayRef<OracleCommonController>,
    llvm::ArrayRef<std::vector<mlir::func::FuncOp>> allocators);
} // namespace zkc::protocol
#endif
