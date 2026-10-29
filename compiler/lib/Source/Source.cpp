#include "zkc/Source/Source.h"
#include "zkc/Source/Names.h"
#include <algorithm>
#include <limits>

namespace zkc::source {
struct Revision::Storage {
  SourceBuffer buffer;
  uint64_t version;
  std::vector<size_t> lines;
  size_t lineEnd(size_t line) const {
    auto end =
        line + 1 < lines.size() ? lines[line + 1] - 1 : buffer.text.size();
    if (end > lines[line] && buffer.text[end - 1] == '\r')
      --end;
    return end;
  }
};
Revision::Revision(SourceBuffer buffer, uint64_t version) {
  auto data = std::make_shared<Storage>();
  data->buffer = std::move(buffer);
  data->version = version;
  data->lines.push_back(0);
  for (size_t i = 0; i < data->buffer.text.size(); ++i)
    if (data->buffer.text[i] == '\n')
      data->lines.push_back(i + 1);
  storage = std::move(data);
}
const SourceBuffer &Revision::buffer() const { return storage->buffer; }
llvm::StringRef Revision::text() const { return buffer().text; }
uint64_t Revision::version() const { return storage->version; }
size_t Revision::lineCount() const { return storage->lines.size(); }
std::optional<uint32_t> Revision::offset(Position pos,
                                         PositionEncoding encoding) const {
  if (pos.line >= lineCount())
    return std::nullopt;
  size_t cursor = storage->lines[pos.line];
  size_t end = storage->lineEnd(pos.line);
  uint64_t column = 0;
  while (cursor < end && column < pos.character) {
    auto scalar = decodeSourceScalar(text(), cursor);
    if (!scalar || cursor + scalar->bytes > end)
      return std::nullopt;
    auto width = encoding == PositionEncoding::UTF8
                     ? scalar->bytes
                     : (scalar->value > 0xffff ? 2 : 1);
    if (column + width > pos.character)
      return std::nullopt;
    column += width;
    cursor += scalar->bytes;
  }
  if (cursor > std::numeric_limits<uint32_t>::max())
    return std::nullopt;
  return uint32_t(cursor);
}
std::optional<Position> Revision::position(uint32_t offset,
                                           PositionEncoding encoding) const {
  if (offset > text().size())
    return std::nullopt;
  auto line =
      std::upper_bound(storage->lines.begin(), storage->lines.end(), offset) -
      storage->lines.begin() - 1;
  size_t cursor = storage->lines[line];
  size_t end = storage->lineEnd(line);
  uint64_t column = 0;
  while (cursor < std::min<size_t>(offset, end)) {
    auto scalar = decodeSourceScalar(text(), cursor);
    if (!scalar || cursor + scalar->bytes > offset)
      return std::nullopt;
    column += encoding == PositionEncoding::UTF8
                  ? scalar->bytes
                  : (scalar->value > 0xffff ? 2 : 1);
    cursor += scalar->bytes;
  }
  if (column > std::numeric_limits<uint32_t>::max())
    return std::nullopt;
  return Position{uint32_t(line), uint32_t(column)};
}
std::optional<Revision> Revision::edit(Position begin, Position end,
                                       PositionEncoding encoding,
                                       llvm::StringRef replacement,
                                       uint64_t newVersion,
                                       uint64_t maxBytes) const {
  auto first = offset(begin, encoding), last = offset(end, encoding);
  if (!first || !last || *first > *last || newVersion <= version())
    return std::nullopt;
  size_t retained = text().size() - (*last - *first);
  if (retained > maxBytes || replacement.size() > maxBytes - retained)
    return std::nullopt;
  for (size_t i = 0; i < replacement.size();) {
    auto scalar = decodeSourceScalar(replacement, i);
    if (!scalar)
      return std::nullopt;
    i += scalar->bytes;
  }
  auto next = buffer();
  next.text.replace(*first, *last - *first, replacement.data(),
                    replacement.size());
  return Revision(std::move(next), newVersion);
}
} // namespace zkc::source
