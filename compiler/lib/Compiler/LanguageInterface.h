#ifndef ZKC_COMPILER_INTERNAL_LANGUAGEINTERFACE_H
#define ZKC_COMPILER_INTERNAL_LANGUAGEINTERFACE_H
#include "mlir/IR/BuiltinOps.h"
#include "zkc/Compiler/LanguageInterface.h"
#include "llvm/Support/JSON.h"
namespace zkc::language {
class CheckedOriginal;
struct Layout;
struct ProtocolPortLayout;
} // namespace zkc::language
namespace zkc::language::detail {
llvm::Expected<std::vector<InterfaceCommonRequirement>>
sourceCommonRequirements(const ClosedEntry &, const Declaration &, uint64_t &,
                         const Limits &);
llvm::json::Value
encodeCommonRequirements(llvm::ArrayRef<InterfaceCommonRequirement>,
                         llvm::ArrayRef<std::string> roles);
llvm::Expected<std::vector<InterfaceCommonRequirement>>
decodeCommonRequirements(const llvm::json::Value &, const InterfaceProtocol &,
                         uint64_t &, const Limits &);
llvm::Error checkNativeCommonRequirements(mlir::Operation *,
                                          const InterfaceProtocol &, uint64_t &,
                                          const Limits &);
bool sameCommonRequirements(llvm::ArrayRef<InterfaceCommonRequirement>,
                            llvm::ArrayRef<InterfaceCommonRequirement>);
llvm::Expected<std::string> emitInterface(const ClosedEntry &,
                                          llvm::StringRef original,
                                          llvm::StringRef toolchain,
                                          const Limits &);
/// The caller has verified this exact original module and computed its digest.
llvm::Expected<LanguageInterface> decodeInterface(mlir::ModuleOp,
                                                  llvm::StringRef digest,
                                                  const llvm::json::Value &,
                                                  const Limits &,
                                                  llvm::ArrayRef<Asset> = {});
llvm::Error withInterface(
    llvm::StringRef original, llvm::StringRef interface, const Limits &,
    llvm::ArrayRef<Asset>,
    llvm::function_ref<llvm::Error(mlir::ModuleOp, LanguageInterface &&)>);
/// Reuse admitted immutable metadata and inspect an independent module clone.
/// Tighter limits require fresh byte admission under the requested policy.
llvm::Error withInterface(
    const CheckedOriginal &, const Limits &,
    llvm::function_ref<llvm::Error(mlir::ModuleOp, const LanguageInterface &)>);
llvm::Expected<ValuePlacement> sourcePortPlacement(const Port &,
                                                   const ProtocolPortLayout &);
llvm::Expected<std::vector<InterfaceComponent>>
sourcePortComponents(const Port &, const ProtocolPortLayout &, unsigned base,
                     uint64_t &remaining);
bool logicalLayout(const Layout &);
bool logicalSchema(const InterfaceSchema &);
llvm::json::Value encodeInterfacePlacement(const ValuePlacement &);
llvm::StringRef componentFacetName(InterfaceComponentFacet);
/// Convert internal kind-framed instances once, using their exact layout.
llvm::Expected<ValuePlacement> externalPlacement(const Layout &,
                                                 const ValuePlacement &,
                                                 uint64_t &, const Limits &,
                                                 unsigned depth = 0);
struct InterfaceEntryField {
  EntryInputSelection selection;
  std::shared_ptr<const InterfaceSchema> schema;
  std::vector<unsigned> native;
  std::string name;
};
llvm::Expected<std::vector<unsigned>>
interfacePublicNative(const InterfaceProtocol &,
                      llvm::ArrayRef<EntryInputSelection>, unsigned verifier,
                      uint64_t &remaining, const Limits &);
/// Reconstruct generated ordinary fields from decoded schemas and placements.
/// This does not invoke source checking or trust producer alias associations.
llvm::Expected<std::vector<InterfaceEntryField>>
interfaceEntryFields(const LanguageInterface &, bool inputs,
                     std::optional<unsigned> role, bool publicOnly,
                     bool witness, uint64_t &remaining, const Limits &);
llvm::json::Value encodeInterfaceSchema(const InterfaceSchema &);
llvm::json::Value encodeInterfaceOracle(const InterfaceOracle &);
llvm::Expected<std::shared_ptr<const InterfaceSchema>>
decodeHostSchema(const llvm::json::Value &, const Limits &);
/// Independent full schema hash, useful at consumer conformance boundaries.
llvm::Expected<std::string> interfaceSchemaIdentity(const llvm::json::Value &,
                                                    const Limits &);
llvm::Expected<llvm::json::Value> parseInterface(llvm::StringRef,
                                                 const Limits &);
/// Common lexical bounds for interfaces and executable Host carriers. Embedded
/// program/package strings use the carrier ceiling instead of the metadata cap.
llvm::Expected<llvm::json::Value> parseEntryJson(llvm::StringRef,
                                                 size_t byteLimit,
                                                 size_t stringLimit,
                                                 llvm::StringRef invalidCode);
} // namespace zkc::language::detail
#endif
