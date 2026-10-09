#include "zkc/Relation/Matrices.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/SHA256.h"

using namespace llvm;
namespace zkc::relation {
namespace {
std::string digest(const json::Value &value) {
  auto bytes = zkc::printJson(value);
  return toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
}
} // namespace
json::Value matrixValues(const R1CS &relation, bool padded) {
  json::Array matrices;
  for (unsigned k = 0; k < 3; ++k) {
    json::Array entries;
    for (auto [row, constraint] : enumerate(relation.constraints()))
      for (const auto &term : constraint[k])
        entries.push_back(json::Array{std::to_string(row),
                                      std::to_string(term.column),
                                      term.coefficient});
    matrices.push_back(json::Array{
        std::to_string(padded ? PowerOf2Ceil(std::max<size_t>(
                                    2, relation.constraints().size()))
                              : relation.constraints().size()),
        std::to_string(
            padded ? PowerOf2Ceil(std::max<uint32_t>(2, relation.columns()))
                   : relation.columns()),
        std::move(entries)});
  }
  return matrices;
}

std::string matrixIdentity(const R1CS &r, unsigned index, bool padded) {
  auto values = matrixValues(r, padded);
  return digest(json::Array{"zkc.matrix/1", r.field().str(),
                            std::move((*values.getAsArray())[index])});
}
} // namespace zkc::relation
