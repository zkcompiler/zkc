#include "zkc/Frontend/Diagnostic.h"
#include "zkc/Frontend/Input.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>

using namespace llvm;
namespace zkc::frontend {
char SourceDiagnostic::ID = 0;
bool isResourceLimitDiagnostic(StringRef code) {
  // These identifiers belong to bounded frontend/checker work. Do not classify
  // arbitrary messages (or a user function's name) as exhaustion.
  return code == "source-diagnostic-limit" || code == "source-limit" ||
         code == "source-depth" || code == "source-resolution-limit" ||
         code == "source-staging-limit" || code == "source-inference-limit" ||
         code == "source-constant-depth" || code == "source-type-depth" ||
         code == "source-struct-limit" || code == "source-product-limit" ||
         code == "requirements-limit" || code == "library-limit" ||
         code == "library-source-limit" ||
         code == "relation-dependency-limit" || code == "relation-byte-limit" ||
         code == "project-source-limit" || code == "project-library-limit" ||
         code == "project-module-depth" || code == "source-origin-limit";
}
void SourceDiagnostic::log(raw_ostream &out) const { out << rendered; }
Error diagnostic(const ProjectInput &project, const Diagnostic &value) {
  auto error = diagnostic(project, value.location.value_or(source::Span{}),
                          value.code, value.message);
  Error result = Error::success();
  handleAllErrors(std::move(error), [&](const SourceDiagnostic &d) {
    std::string rendered = d.rendered;
    for (const auto &related : value.related) {
      rendered += "\n";
      if (related.location) {
        const auto *file = project.file(related.location->file);
        if (file) {
          auto text = file->text();
          auto offset = std::min(related.location->offset, text.size());
          auto start = text.take_front(offset).rfind('\n');
          start = start == StringRef::npos ? 0 : start + 1;
          rendered += file->filename().str() + ":" +
                      std::to_string(1 + text.take_front(offset).count('\n')) +
                      ":" + std::to_string(offset - start + 1) + ": ";
        }
      }
      rendered += "note: " + related.message;
    }
    auto detail = std::make_unique<SourceDiagnostic>(
        d.code, d.message, std::move(rendered), d.location);
    detail->related = value.related;
    detail->causes = value.causes;
    result = Error(std::move(detail));
  });
  return result;
}
Error diagnostic(const ProjectInput &project, source::Span span, StringRef code,
                 const Twine &message) {
  const auto *file = project.file(span.file);
  auto error = diagnostic(file ? file->text() : StringRef(),
                          file ? file->filename() : "<generated>", span.offset,
                          code, message);
  Error result = Error::success();
  handleAllErrors(std::move(error), [&](const SourceDiagnostic &d) {
    result = make_error<SourceDiagnostic>(d.code, d.message, d.rendered, span);
  });
  return result;
}
Error diagnostic(StringRef text, StringRef filename, size_t offset,
                 StringRef code, const Twine &message) {
  offset = std::min(offset, text.size());
  size_t start = text.take_front(offset).rfind('\n');
  start = start == StringRef::npos ? 0 : start + 1;
  size_t end = text.find('\n', offset);
  if (end == StringRef::npos)
    end = text.size();
  unsigned line = 1 + text.take_front(offset).count('\n');
  std::string result;
  raw_string_ostream out(result);
  out << filename << ':' << line << ':' << offset - start + 1
      << ": error: " << code << ": " << message << '\n';
  // Keep the error in a bounded window, shifting back near the line's end.
  // Mark omitted source and preserve tabs in the caret's displayed prefix.
  size_t excerptStart = offset - std::min(offset - start, size_t(80));
  size_t excerptEnd = std::min(end, excerptStart + 160);
  excerptStart = excerptEnd - std::min(excerptEnd - start, size_t(160));
  if (excerptStart > start)
    out << "...";
  out << text.slice(excerptStart, excerptEnd);
  if (excerptEnd < end)
    out << "...";
  out << '\n';
  if (excerptStart > start)
    out << "   ";
  for (size_t i = excerptStart; i < offset; ++i)
    out << (text[i] == '\t' ? '\t' : ' ');
  out << '^';
  return make_error<SourceDiagnostic>(
      code.str(), message.str(), std::move(result), source::Span{offset, 0});
}

} // namespace zkc::frontend
