#ifndef ZKC_CONTRACTS_NATIVEORIGIN_H
#define ZKC_CONTRACTS_NATIVEORIGIN_H
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <string>
#include <variant>
#include <vector>
namespace zkc::protocol {
struct NativeOriginStep {
  enum class Kind { Apply, Repeat, Branch } kind = Kind::Apply;
  std::string protocol, site;
  std::string alternative = {};
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
enum class NativeOriginFormat { Template, Dynamic };
/// Owning canonical logical-tree byte fragments, not hex strings. No part
/// borrows from the source template; the layout survives its
/// mutation/destruction. The prefix contains the five-element array header,
/// selected format tag, entry and complete path. The suffix contains the event.
/// Neither fragment contains the coordinate array header or its elements.
///
/// Complete a Template layout with an encoded empty array between the
/// fragments. Complete a Dynamic layout with an encoded array of exactly
/// `coordinates` canonical u64 decimal strings, in outermost-first repeat
/// order. Branch labels remain in the prefix and add no coordinate. Consumers
/// must check that count and the complete dynamic encoding's 4096-byte limit
/// when splicing operands. A zero coordinate count does not imply a branch-free
/// path or raw-proof transport eligibility.
struct NativeOriginLayout {
  std::string prefix;
  uint64_t coordinates = 0;
  std::string suffix;
};
/// Validate the typed template under the current /0 syntax and limits, then
/// decompose it for the selected format. Both formats require an admissible
/// template (at most 64 steps, 128-byte names and 2048 encoded template bytes).
/// Invalid names, step/format enums, alternatives or limits return
/// `interactive-native-origin`; no source correspondence is established.
llvm::Expected<NativeOriginLayout>
layoutNativeOrigin(const NativeOriginTemplate &, NativeOriginFormat);
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
} // namespace zkc::protocol
#endif
