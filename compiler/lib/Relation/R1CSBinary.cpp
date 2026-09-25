#include "Field.h"
#include "zkc/Relation/R1CS.h"
#include "llvm/Support/Endian.h"
#include <map>

using namespace llvm;
namespace zkc::relation {
namespace {
class Reader {
public:
  explicit Reader(StringRef input) : remaining(input) {}
  Expected<StringRef> take(size_t count) {
    if (count > remaining.size())
      return zkc::error("relation-truncated");
    StringRef result = remaining.take_front(count);
    remaining = remaining.drop_front(count);
    return result;
  }
  Expected<uint32_t> u32() {
    auto bytes = take(4);
    if (!bytes)
      return bytes.takeError();
    return support::endian::read32le(bytes->data());
  }
  Expected<uint64_t> u64() {
    auto bytes = take(8);
    if (!bytes)
      return bytes.takeError();
    return support::endian::read64le(bytes->data());
  }
  Expected<std::string> integer(size_t width) {
    auto bytes = take(width);
    if (!bytes)
      return bytes.takeError();
    APInt value(width * 8, 0);
    for (size_t i = 0; i < width; ++i)
      value |= APInt(width * 8, static_cast<uint8_t>((*bytes)[i])) << (8 * i);
    return Field::print(value);
  }
  bool empty() const { return remaining.empty(); }
  size_t size() const { return remaining.size(); }

private:
  StringRef remaining;
};
} // namespace

Expected<R1CS> readR1CS(StringRef bytes) {
  if (bytes.size() > Limits::bytes)
    return zkc::error("relation-byte-limit");
  Reader input(bytes);
  auto magic = input.take(4);
  if (!magic)
    return magic.takeError();
  if (*magic != "r1cs")
    return zkc::error("relation-magic");
  auto version = input.u32();
  if (!version)
    return version.takeError();
  if (*version != 1)
    return zkc::error("relation-version");
  auto sectionCount = input.u32();
  if (!sectionCount)
    return sectionCount.takeError();
  if (*sectionCount != 3)
    return zkc::error("relation-sections");
  std::map<uint32_t, StringRef> sections;
  for (unsigned i = 0; i < *sectionCount; ++i) {
    auto kind = input.u32();
    if (!kind)
      return kind.takeError();
    auto length = input.u64();
    if (!length)
      return length.takeError();
    if (*kind < 1 || *kind > 3 || sections.count(*kind))
      return zkc::error("relation-sections");
    if (*length > input.size())
      return zkc::error("relation-truncated");
    auto section = input.take(*length);
    if (!section)
      return section.takeError();
    sections.emplace(*kind, *section);
  }
  if (!input.empty())
    return zkc::error("relation-trailing-data");

  Reader header(sections.at(1));
  auto width = header.u32();
  if (!width)
    return width.takeError();
  if (!*width || *width > 32)
    return zkc::error("relation-field-width");
  auto prime = header.integer(*width);
  if (!prime)
    return prime.takeError();
  StringRef field;
  for (StringRef candidate :
       {"bls12-381.fr", "ristretto255.scalar", "koala-bear", "bn254.fr"})
    if (Field::primeModulus(candidate) == *prime) {
      field = candidate;
      break;
    }
  if (field.empty())
    return zkc::error("relation-field");
  // External exporters may round field storage to a machine-word boundary.
  // Storage padding does not change the exact mathematical field identity.
  if (*width < (APInt::getBitsNeeded(*prime, 10) + 7) / 8)
    return zkc::error("relation-field-width");
  auto columns = header.u32();
  if (!columns)
    return columns.takeError();
  auto outputs = header.u32();
  if (!outputs)
    return outputs.takeError();
  auto publicInputs = header.u32();
  if (!publicInputs)
    return publicInputs.takeError();
  auto privateInputs = header.u32();
  if (!privateInputs)
    return privateInputs.takeError();
  auto labels = header.u64();
  if (!labels)
    return labels.takeError();
  auto count = header.u32();
  if (!count)
    return count.takeError();
  if (!header.empty() || !*columns || *columns > Limits::columns ||
      *count > Limits::rows ||
      uint64_t(*outputs) + *publicInputs + *privateInputs >= *columns ||
      *labels < *columns)
    return zkc::error("relation-dimension");

  Reader wires(sections.at(3));
  if (wires.size() != size_t(*columns) * 8)
    return zkc::error("relation-wire-map");
  for (uint32_t i = 0; i < *columns; ++i) {
    auto label = wires.u64();
    if (!label)
      return label.takeError();
    if (*label >= *labels || (i == 0 && *label != 0))
      return zkc::error("relation-wire-map");
  }
  Reader constraints(sections.at(2));
  size_t terms = 0;
  std::vector<Constraint> rows;
  rows.reserve(*count);
  for (uint32_t i = 0; i < *count; ++i) {
    Constraint row;
    for (auto &form : row) {
      auto entries = constraints.u32();
      if (!entries)
        return entries.takeError();
      if (*entries > Limits::terms - terms ||
          *entries > constraints.size() / (4 + *width))
        return zkc::error("relation-term-limit");
      terms += *entries;
      form.reserve(*entries);
      for (uint32_t j = 0; j < *entries; ++j) {
        auto column = constraints.u32();
        if (!column)
          return column.takeError();
        auto coefficient = constraints.integer(*width);
        if (!coefficient)
          return coefficient.takeError();
        form.push_back({*column, std::move(*coefficient)});
      }
    }
    rows.push_back(std::move(row));
  }
  if (!constraints.empty())
    return zkc::error("relation-trailing-data");
  return R1CS::create(field.str(), *columns, *outputs, *publicInputs,
                      std::move(rows));
}
} // namespace zkc::relation
