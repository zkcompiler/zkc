#ifndef ZKC_TRANSFORMS_ORACLEQUERYEXCHANGE_H
#define ZKC_TRANSFORMS_ORACLEQUERYEXCHANGE_H
#include "OracleMerkle.h"
#include "OracleQueryController.h"
#include <memory>
namespace zkc::protocol {
struct OracleHelperSignature {
  std::string name;
  std::vector<mlir::Type> inputs, outputs;
};
// A closed dispatch specification derived from checked source constructors and
// primitive identities. It is not an executable local language or a wire
// reader.
struct OracleQueryExchange {
  struct Arm {
    unsigned constructor, kind, receiverSlot;
    std::string alternative;
    mlir::Type reference;
    std::vector<mlir::Type> opened;
    unsigned openingState, holderRows, root, receiverRows;
    mlir::func::FuncOp holderLookup, receiverLookup, open, authenticate, resume;
  };
  mlir::Type request, response;
  std::string holder;
  std::vector<mlir::Type> state, receiverStores, holderStores;
  std::vector<Arm> arms;
};
// One exchange dispatches at most this many base constructors. Each arm opens
// one base constructor of the receiver controller at its holder and is one
// alternative of the opening response and checked answer variants. The
// planner, the response and packet helpers and their verifiers share this
// limit, which lies below the portable descriptor's 64 alternatives.
inline constexpr size_t oracleExchangeConstructorLimit = 32;
enum class OracleExchangeAction { Open };
struct OracleExchangeRecipe : OracleHelperSignature {
  OracleExchangeAction action;
  std::shared_ptr<const OracleQueryExchange> exchange;
};
llvm::Expected<OracleQueryExchange> planOracleQueryExchange(
    const OracleAnchorStorage &, const OracleQueryController &receiver,
    const OracleQueryController &holder, llvm::ArrayRef<OracleMerkleFunctions>);
struct OracleNativeWork;
llvm::Expected<OracleQueryExchange> planOracleQueryExchangeWithWork(
    const OracleAnchorStorage &, const OracleQueryController &,
    const OracleQueryController &, llvm::ArrayRef<OracleMerkleFunctions>,
    OracleNativeWork &);
mlir::func::FuncOp emitOracleQueryExchange(mlir::ModuleOp,
                                           const OracleExchangeRecipe &);
class OracleVerificationContext;
bool checkOracleQueryExchange(const OracleVerificationContext &,
                              mlir::func::FuncOp, const OracleExchangeRecipe &);
struct OracleNativeWork;
llvm::Expected<mlir::func::FuncOp>
emitOracleQueryExchangeWithWork(mlir::ModuleOp, const OracleExchangeRecipe &,
                                OracleNativeWork &);
} // namespace zkc::protocol
#endif
