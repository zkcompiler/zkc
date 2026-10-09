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
class Bundle;
} // namespace zkc::relation
namespace zkc::ring {
class Expression;
}
namespace zkc::language {
/// Explicit captured input. The diagnostic path is a label, never an import.
struct AssetBuffer {
  std::string name, format, bytes, diagnosticPath;
};
/// Immutable captured mathematics admitted by its bounded native reader.
/// Definition identity excludes the capture name, transport and diagnostic
/// path.
class Asset {
public:
  static llvm::Expected<Asset> read(const AssetBuffer &);
  llvm::StringRef name() const { return name_; }
  llvm::StringRef identity() const { return identity_; }
  const relation::R1CS *r1cs() const;
  const relation::AIR *air() const;
  const ring::Expression *ring() const;
  const relation::Bundle *bundle() const;
  llvm::json::Value encode() const;

private:
  using Definition = std::variant<std::shared_ptr<const relation::R1CS>,
                                  std::shared_ptr<const relation::AIR>,
                                  std::shared_ptr<const ring::Expression>,
                                  std::shared_ptr<const relation::Bundle>>;
  Asset(std::string name, Definition definition);
  std::string name_, identity_;
  Definition definition;
};
} // namespace zkc::language
#endif
