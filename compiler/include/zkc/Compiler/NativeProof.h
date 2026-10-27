#ifndef ZKC_COMPILER_NATIVEPROOF_H
#define ZKC_COMPILER_NATIVEPROOF_H
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Compiler/Compilation.h"
#include "zkc/Contracts/ProofFormat.h"
#include "zkc/Transforms/MathematicalSelection.h"
#include "llvm/Support/JSON.h"
#include <optional>
#include <variant>
namespace zkc {
class CompilationObservation;
/// Current deployment policy. The source remains independently owned.
struct NativeProofPolicy {
  std::string entry, producer, validator, suite;
  /// Empty selects the installed native/authored construction. Otherwise this
  /// names the exact protocol.construction symbol in the original module.
  std::string construction;
  protocol::ProofFormat format = protocol::ProofFormat::Native;
  unsigned acceptance = 0;
  /// Replaced verifier authorities, in strictly increasing source input order.
  std::vector<unsigned> services;
  std::vector<unsigned> publicInputs;
  std::vector<std::pair<std::string, std::string>> draws;
};
llvm::Expected<NativeProofPolicy> parseNativeProofPolicy(llvm::StringRef text);
llvm::json::Value encodeNativeProofPolicy(const NativeProofPolicy &policy);
/// Resolve the ordered query/delivery occurrences of the explicitly selected
/// verifier services. All other policy choices remain explicit; input draws
/// must be empty. Uses the same source preparation and event admission as
/// construction, including roles, public inputs, exact delivered values and
/// ordering. Returns a complete strict policy without mutating the source.
llvm::Expected<NativeProofPolicy>
selectNativeProofDraws(mlir::ModuleOp source,
                       const NativeProofPolicy &selection,
                       MathematicalSelectionPolicy mathematicalSelection = {});
struct NativeProofConstruction {
  mlir::OwningOpRef<mlir::ModuleOp> module;
  llvm::json::Value descriptor;
  /// Source message origin to lowered wire site; excluded from transcript
  /// roots.
  llvm::json::Array wireSites;
};
/// Admit original source, prepare/project without simplification and construct
/// role-local transcripts. No source IR is mutated and no cryptographic theorem
/// is asserted. Empty suite and construction selectors select the authored
/// profile; a construction symbol selects its checked scoped handler plan.
llvm::Expected<NativeProofConstruction>
constructNativeProof(mlir::ModuleOp source, const NativeProofPolicy &policy,
                     MathematicalSelectionPolicy mathematicalSelection = {});
/// Construct with an independent projected-to-constructed postcondition, then
/// compare the entire supplied candidate, including SSA and retained records,
/// ignoring locations. Source policy/occurrence admission remains a premise.
llvm::Error
checkNativeProof(mlir::ModuleOp source, mlir::ModuleOp candidate,
                 const NativeProofPolicy &policy,
                 MathematicalSelectionPolicy mathematicalSelection = {});
enum class ConstructedParticipantRole { Producer, Validator };
/// Check the supplied candidate as `checkNativeProof` does, then export its
/// explicitly selected policy role as a flat `zkc.constructed-participant/0`
/// record. The default preserves validator-only callers.
/// Construction-inserted helpers expand through the admitted source execution
/// closure at their actual data operands; original helper calls retain their
/// callee. Operations keep their name, attributes and binding, with checked
/// data inputs and successful payload results. Administrative scope/outcome
/// edges are checked natively and excluded from the logical carrier.
/// Exporter correctness and the meaning of each primitive remain explicit
/// boundaries of the formal consumer.
llvm::Expected<llvm::json::Value> exportConstructedParticipant(
    mlir::ModuleOp source, mlir::ModuleOp candidate,
    llvm::StringRef sourceBytes, const NativeProofPolicy &policy,
    MathematicalSelectionPolicy mathematicalSelection = {},
    ConstructedParticipantRole role = ConstructedParticipantRole::Validator);
/// Check once, then export both actual candidate participants in policy order
/// as `["zkc.constructed-pair/0", producer, validator]`. Child records retain
/// exactly the same source/candidate identities and full policy.
llvm::Expected<llvm::json::Value>
exportConstructedPair(mlir::ModuleOp source, mlir::ModuleOp candidate,
                      llvm::StringRef sourceBytes,
                      const NativeProofPolicy &policy,
                      MathematicalSelectionPolicy mathematicalSelection = {});
/// Request service-based occurrence selection inside the owned compiler
/// context. The policy fixes every choice except draws, which must be empty.
struct NativeProofSelection {
  NativeProofPolicy policy;
};
enum class NativeProofOperation { Prove, Verify };
struct NativeProofOptions {
  std::variant<std::string, NativeProofSelection> policy;
  bool simplify = true, releaseStorage = false;
  MathematicalSelectionPolicy mathematicalSelection = {};
  /// Absent preserves the existing complete declarative deployment API.
  std::optional<NativeProofOperation> operation = std::nullopt;
  CompilationObservation *observations = nullptr;
};
struct CompiledNativeProof {
  Compilation compilation;
  std::string deployment;
  /// Complete policy after occurrence selection and strict admission.
  NativeProofPolicy policy;
};
/// Owned, source-checked compilation. A host must authenticate the resulting
/// deployment independently; hashes inside a supplied artifact are not
/// authority.
llvm::Expected<CompiledNativeProof>
compileNativeProof(llvm::StringRef source, llvm::StringRef filename,
                   const NativeProofOptions &options,
                   const mlir::DialectRegistry &registry);
} // namespace zkc
#endif
