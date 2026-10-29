#ifndef ZKC_SOURCE_SOURCE_H
#define ZKC_SOURCE_SOURCE_H

#include "llvm/ADT/StringRef.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <vector>

namespace zkc::source {
struct SourceId {
  uint32_t index;
};
struct Span {
  SourceId source;
  uint32_t begin, end;
};
struct Diagnostic {
  std::string code, message;
  std::optional<Span> primary;
  std::vector<Span> related;
};
enum class SourceOrigin { Captured, Installation };
struct SourceBuffer {
  std::string module, text, diagnosticPath;
  SourceOrigin origin = SourceOrigin::Captured;
};

/// Cancellation is shared by a request and its computations, never reset.
class Cancellation {
public:
  Cancellation() : state(std::make_shared<std::atomic<bool>>(false)) {}
  void cancel() const { state->store(true, std::memory_order_relaxed); }
  bool cancelled() const { return state->load(std::memory_order_relaxed); }

private:
  std::shared_ptr<std::atomic<bool>> state;
};

enum class PositionEncoding { UTF8, UTF16 };
struct Position {
  uint32_t line, character;
};

/// An immutable, byte-owned revision. Paths are labels and are never opened.
class Revision {
public:
  explicit Revision(SourceBuffer buffer, uint64_t version = 0);
  const SourceBuffer &buffer() const;
  llvm::StringRef text() const;
  uint64_t version() const;
  size_t lineCount() const;
  /// Overlong columns clamp to end of line. Interior scalars/surrogates and
  /// nonexistent lines fail. CRLF is one line ending, outside the text column.
  std::optional<uint32_t> offset(Position, PositionEncoding) const;
  std::optional<Position> position(uint32_t, PositionEncoding) const;
  /// A failed edit leaves this and every shared revision unchanged.
  std::optional<Revision> edit(Position begin, Position end, PositionEncoding,
                               llvm::StringRef replacement, uint64_t newVersion,
                               uint64_t maxBytes) const;

private:
  struct Storage;
  std::shared_ptr<const Storage> storage;
};
} // namespace zkc::source
#endif
