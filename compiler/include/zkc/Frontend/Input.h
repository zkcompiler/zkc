#ifndef ZKC_FRONTEND_INPUT_H
#define ZKC_FRONTEND_INPUT_H
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <memory>
#include <string>
#include <vector>

namespace zkc::frontend {
/// Immutable source snapshot. No filesystem access or driver state is retained.
class Input {
  enum class Kind { File, Stream };
  struct Contents {
    std::string text, filename;
    Kind kind;
  };
  std::shared_ptr<const Contents> contents;
  Input(std::string text, std::string filename, Kind kind);

public:
  /// Text read from the file at `filename`, which locates diagnostics and is
  /// the base of the paths the source names relative to itself.
  Input(std::string text, std::string filename);
  /// Text with no file behind it, such as standard input. `label` only names
  /// it in diagnostics; nothing is read relative to it.
  static Input withoutFile(std::string text, std::string label = "<stdin>");
  llvm::StringRef text() const;
  llvm::StringRef filename() const;
  bool file() const;
};

/// Logical module paths are independent of the physical source filename.
/// Each library has exactly one root (the empty path). Library identities and
/// dependency bindings are declared by that root and checked by resolution.
struct ProjectSource {
  std::vector<std::string> module;
  Input input;
};
struct ProjectLibrary {
  std::vector<ProjectSource> sources;
};
struct ProjectAsset {
  uint32_t file;
  std::string path, bytes;
};

/// All source and asset bytes needed for analysis, captured before checking.
/// File IDs enumerate sources in library/source order; the first library is
/// the application. Neither filenames nor File IDs enter semantic identity.
class ProjectInput {
  struct Contents {
    std::vector<ProjectLibrary> libraries;
    std::vector<ProjectAsset> assets;
  };
  std::shared_ptr<const Contents> contents;
  explicit ProjectInput(Contents);

public:
  static constexpr size_t maxLibraries = 64, maxSources = 256;
  static constexpr size_t maxSourceBytes = 1 << 20;
  static constexpr size_t maxTotalSourceBytes = 16 << 20;
  static llvm::Expected<ProjectInput> capture(std::vector<ProjectLibrary>,
                                              std::vector<ProjectAsset> = {});
  static ProjectInput single(Input);
  llvm::ArrayRef<ProjectLibrary> libraries() const;
  llvm::ArrayRef<ProjectAsset> assets() const;
  const Input *file(uint32_t) const;
};
} // namespace zkc::frontend
#endif
