#ifndef ZKC_LANGUAGE_ASSETS_H
#define ZKC_LANGUAGE_ASSETS_H
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <memory>
#include <string>
#include <variant>
namespace llvm::json {
class Value;
}
namespace zkc::relation {
class R1CS;
class AIR;
} // namespace zkc::relation
namespace zkc::language {
/// Explicit captured input. The diagnostic path is a label, never an import.
struct AssetBuffer {
  std::string name, format, bytes, diagnosticPath;
};
/// An immutable relation admitted by its existing bounded native reader.
/// Definition identity excludes the capture name, transport and diagnostic
/// path.
class RelationAsset {
public:
  static llvm::Expected<RelationAsset> read(const AssetBuffer &);
  llvm::StringRef name() const { return name_; }
  llvm::StringRef identity() const { return identity_; }
  const relation::R1CS *r1cs() const;
  const relation::AIR *air() const;
  llvm::json::Value encode() const;

private:
  using Definition = std::variant<std::shared_ptr<const relation::R1CS>,
                                  std::shared_ptr<const relation::AIR>>;
  RelationAsset(std::string name, Definition definition);
  std::string name_, identity_;
  Definition definition;
};
} // namespace zkc::language
#endif
