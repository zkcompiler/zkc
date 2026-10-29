#include "Server.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/Errc.h"
#include "llvm/Support/FileSystem.h"
#include <cerrno>
#include <cstdio>
#include <fstream>

using namespace llvm;
namespace zkc::editor {
Error error(StringRef message, lsp::ErrorCode code) {
  return make_error<lsp::LSPError>(message.str(), code);
}
LogicalResult Input::stop() {
  invalid = ended = true;
  errno = EINVAL;
  return failure();
}
LogicalResult Input::readDelimitedMessage(std::string &) { return stop(); }
LogicalResult Input::readStandardMessage(std::string &text) {
  requestKey.clear();
  std::optional<uint64_t> length;
  size_t headerBytes = 0;
  for (;;) {
    std::string line;
    for (;;) {
      int byte = std::fgetc(stdin);
      if (byte == EOF) {
        ended = true;
        return failure();
      }
      if (++headerBytes > 8192 || byte == 0)
        return stop();
      line.push_back(char(byte));
      if (byte == '\n')
        break;
    }
    if (!StringRef(line).ends_with("\r\n"))
      return stop();
    StringRef header = StringRef(line).drop_back(2);
    if (header.empty())
      break;
    auto [name, value] = header.split(':');
    if (!header.contains(':'))
      return stop();
    if (name.equals_insensitive("Content-Length")) {
      uint64_t count;
      if (length || value.trim().getAsInteger(10, count) || count == 0 ||
          count > 16 * 1024 * 1024)
        return stop();
      length = count;
    }
  }
  if (!length)
    return stop();
  text.resize(*length);
  if (std::fread(text.data(), 1, text.size(), stdin) != text.size())
    return stop();
  // Bound recursion before LLVM parses. Strings are skipped with JSON escape
  // rules; the actual JSON parser still owns grammar/UTF-8 validation.
  unsigned depth = 0;
  std::vector<size_t> containers;
  size_t paramsBegin = SIZE_MAX;
  bool invalidCancellationId = false;
  bool string = false, escape = false;
  size_t stringStart = 0, writtenKeys = 0;
  for (size_t i = 0; i < text.size(); ++i) {
    char c = text[i];
    if (string) {
      if (escape)
        escape = false;
      else if (c == '\\')
        escape = true;
      else if (c == '"') {
        string = false;
        auto token = StringRef(text).slice(stringStart, i + 1);
        if (!validStringEncoding(token))
          return stop();
        size_t next = i + 1;
        while (next < text.size() &&
               isspace(static_cast<unsigned char>(text[next])))
          ++next;
        if (next < text.size() && text[next] == ':') {
          ++writtenKeys;
          auto key = json::parse(token);
          if (!key) {
            consumeError(key.takeError());
            return stop();
          }
          while (++next < text.size() &&
                 isspace(static_cast<unsigned char>(text[next]))) {
          }
          if (depth == 1 && key->getAsString() == "params")
            paramsBegin = next;
          if (key->getAsString() == "id" &&
              (depth == 1 ||
               (depth == 2 && containers.back() == paramsBegin))) {
            if (next < text.size() && text[next] != '"') {
              size_t end = next;
              while (end < text.size() && text[end] != ',' &&
                     text[end] != '}' &&
                     !isspace(static_cast<unsigned char>(text[end])))
                ++end;
              auto spelling = StringRef(text).slice(next, end);
              int32_t integer;
              auto digits = spelling;
              digits.consume_front("-");
              if (digits.empty() ||
                  (digits.size() > 1 && digits.front() == '0') ||
                  !all_of(digits,
                          [](char c) { return c >= '0' && c <= '9'; }) ||
                  spelling.getAsInteger(10, integer)) {
                if (depth == 1)
                  return stop();
                invalidCancellationId = true;
              }
            }
          }
        }
      }
    } else if (c == '"') {
      string = true;
      stringStart = i;
    } else if (c == '{' || c == '[') {
      if (++depth > 64)
        return stop();
      containers.push_back(i);
    } else if (c == '}' || c == ']') {
      if (!depth)
        return stop();
      --depth;
      containers.pop_back();
    }
  }
  auto parsed = json::parse(text);
  if (!parsed) {
    consumeError(parsed.takeError());
    return stop();
  }
  // LLVM discards duplicate object keys. Count decoded keys independently to
  // reject ambiguity, including differently escaped spellings of one key.
  std::function<size_t(const json::Value &)> countKeys =
      [&](const json::Value &value) {
        size_t count = 0;
        if (auto *object = value.getAsObject()) {
          count = object->size();
          for (const auto &item : *object)
            count += countKeys(item.second);
        } else if (auto *array = value.getAsArray())
          for (const auto &item : *array)
            count += countKeys(item);
        return count;
      };
  if (countKeys(*parsed) != writtenKeys)
    return stop();
  auto *object = parsed->getAsObject();
  if (!object || object->getString("jsonrpc") != "2.0")
    return stop();
  // Only envelope IDs and cancellation IDs are protocol identities. Client
  // extension data may contain unrelated fields named "id".
  if (object->getString("method") == "$/cancelRequest") {
    if (invalidCancellationId)
      return stop();
    if (auto *params = object->getObject("params"))
      if (auto id = params->getString("id"); id && id->size() > 1024)
        return stop();
  }
  if (auto *id = object->get("id")) {
    if (auto name = id->getAsString()) {
      if (name->size() > 1024)
        return stop();
      requestKey = "s:" + name->str();
    } else if (auto integer = id->getAsInteger())
      requestKey = "i:" + std::to_string(*integer);
    else
      return stop();
  }
  exitSeen = !object->get("id") && object->getString("method") == "exit";
  return success();
}
Expected<std::string> canonicalURI(StringRef uri) {
  if (uri.size() > 8192)
    return error("file URI exceeds the source service limit");
  auto decoded = lsp::URIForFile::fromURI(uri);
  if (!decoded)
    return decoded.takeError();
  if (decoded->scheme() != "file")
    return error("expected a file URI");
  auto encoded = lsp::URIForFile::fromFile(decoded->file());
  if (!encoded)
    return encoded.takeError();
  return encoded->uri().str();
}
Expected<source::SourceBuffer> readDocument(StringRef uri, StringRef module) {
  auto decoded = lsp::URIForFile::fromURI(uri);
  if (!decoded)
    return decoded.takeError();
  sys::fs::file_status status;
  if (auto failure = sys::fs::status(decoded->file(), status))
    return errorCodeToError(failure);
  if (!sys::fs::is_regular_file(status))
    return error("configured module is not a regular file");
  std::ifstream file(decoded->file().str(), std::ios::binary);
  if (!file)
    return error(("cannot read configured module: " + uri).str());
  std::string text(1048577, '\0');
  file.read(text.data(), text.size());
  text.resize(file.gcount());
  if (file.bad() || text.size() > 1048576)
    return error("configured module exceeds the source byte limit");
  return source::SourceBuffer{module.str(), std::move(text), uri.str()};
}
std::optional<source::Position> position(const json::Value *value) {
  auto *object = value ? value->getAsObject() : nullptr;
  if (!object)
    return {};
  auto line = object->getInteger("line"),
       character = object->getInteger("character");
  if (!line || !character || *line < 0 || *character < 0 ||
      uint64_t(*line) > UINT32_MAX || uint64_t(*character) > UINT32_MAX)
    return {};
  return source::Position{uint32_t(*line), uint32_t(*character)};
}
json::Value range(const source::Revision &revision, source::Span span,
                  source::PositionEncoding encoding) {
  auto begin =
      revision.position(span.begin, encoding).value_or(source::Position{0, 0});
  auto end = revision.position(span.end, encoding).value_or(begin);
  return json::Object{
      {"start",
       json::Object{{"line", begin.line}, {"character", begin.character}}},
      {"end", json::Object{{"line", end.line}, {"character", end.character}}}};
}
} // namespace zkc::editor
