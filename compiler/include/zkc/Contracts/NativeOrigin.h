#ifndef ZKC_CONTRACTS_NATIVEORIGIN_H
#define ZKC_CONTRACTS_NATIVEORIGIN_H
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <array>
#include <cstdint>
#include <string>
#include <variant>
#include <vector>
namespace zkc::protocol {
struct NativeOriginStep {
  enum class Kind { Apply, Repeat } kind = Kind::Apply;
  std::string protocol, site;
};
struct NativeQueryOrigin {
  std::string protocol, site;
  uint64_t serviceInput = 0;
  std::string service, method, owner;
};
struct NativeMessageOrigin {
  std::string protocol, site, schema, sender, receiver;
};
struct NativeStartOrigin {
  std::string protocol, site;
};
struct NativeOriginTemplate {
  std::string entry;
  std::vector<NativeOriginStep> path;
  std::variant<NativeQueryOrigin, NativeMessageOrigin, NativeStartOrigin> event;
};
/// Typed neutral byte boundary. Native MLIR holds its own structured
/// attributes.
llvm::Expected<NativeOriginTemplate>
decodeNativeOriginTemplate(llvm::StringRef hex);
llvm::Expected<std::string>
encodeNativeOriginTemplate(const NativeOriginTemplate &);
/// Bounded source occurrence syntax. Does not establish source correspondence.
/// A nonempty method also fixes a query event's service method, separating
/// field challenges from UniformIndex transitions.
llvm::Error checkNativeOrigin(llvm::StringRef hex, llvm::StringRef kind,
                              llvm::StringRef method = {});
llvm::Expected<std::string>
encodeNativeOriginTemplate(llvm::StringRef entry,
                           llvm::ArrayRef<std::array<std::string, 3>> path,
                           llvm::ArrayRef<std::string> event);
} // namespace zkc::protocol
#endif
