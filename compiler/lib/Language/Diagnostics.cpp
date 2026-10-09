#include "zkc/Language/Diagnostics.h"
#include "zkc/Support/BoundedStream.h"
#include "llvm/ADT/StringExtras.h"
#include <algorithm>
#include <map>
#include <set>
#include <tuple>

using namespace llvm;
namespace zkc::language {
namespace {
std::string escaped(StringRef text, size_t limit) {
  std::string result;
  raw_string_ostream out(result);
  printEscapedString(text.take_front(limit), out);
  if (text.size() > limit)
    out << "...";
  return result;
}
class Renderer {
  const CapturedProject &capture;
  raw_ostream &out;
  std::map<unsigned, std::vector<unsigned>> lines;

public:
  Renderer(const CapturedProject &capture, raw_ostream &out)
      : capture(capture), out(out) {}
  void location(Span span) {
    if (span.module.index >= capture.sources().size()) {
      out << " (invalid source span)\n";
      return;
    }
    const auto &source = capture.sources()[span.module.index];
    if (span.begin > span.end || span.end > source.text.size()) {
      out << " (invalid source span)\n";
      return;
    }
    auto [it, inserted] = lines.try_emplace(span.module.index);
    auto &starts = it->second;
    if (inserted) {
      starts.push_back(0);
      for (unsigned i = 0; i < source.text.size(); ++i)
        if (source.text[i] == '\n')
          starts.push_back(i + 1);
    }
    size_t line = std::upper_bound(starts.begin(), starts.end(), span.begin) -
                  starts.begin() - 1;
    auto start = starts[line];
    auto end =
        line + 1 < starts.size() ? starts[line + 1] - 1 : source.text.size();
    auto path =
        source.diagnosticPath.empty() ? source.module : source.diagnosticPath;
    out << " at " << escaped(path, 512) << ':' << line + 1 << ':'
        << span.begin - start + 1 << " [" << escaped(source.module, 256)
        << "]\n";
    auto first = std::max(start, span.begin > 40 ? span.begin - 40 : 0);
    auto last = std::min(end, size_t(first) + 120);
    StringRef text(source.text);
    out << "  | " << (first > start ? "..." : "")
        << escaped(text.slice(first, last), 120) << (last < end ? "..." : "")
        << '\n';
    auto column = escaped(text.slice(first, span.begin), 120).size();
    out << "  | " << std::string(column + (first > start ? 3 : 0), ' ')
        << "^\n";
  }
  void diagnostic(const Diagnostic &value) {
    out << escaped(value.code, 128) << ": " << escaped(value.message, 2048);
    if (value.primary)
      location(*value.primary);
    else
      out << '\n';
    std::set<std::tuple<unsigned, unsigned, unsigned>> seen;
    if (value.primary)
      seen.emplace(value.primary->module.index, value.primary->begin,
                   value.primary->end);
    unsigned shown = 0;
    for (auto span : value.related) {
      if (!seen.emplace(span.module.index, span.begin, span.end).second)
        continue;
      if (shown++ == 4) {
        out << "note: further related locations omitted\n";
        break;
      }
      out << "note: related source";
      location(span);
    }
  }
};
} // namespace
std::string formatDiagnostics(const CapturedProject &capture,
                              ArrayRef<Diagnostic> diagnostics) {
  std::string result;
  BoundedStream out(result, 64 * 1024 - 64);
  Renderer renderer(capture, out);
  size_t shown = 0;
  for (const auto &diagnostic : diagnostics.take_front(20)) {
    renderer.diagnostic(diagnostic);
    ++shown;
    if (out.overflow())
      break;
  }
  if (out.overflow())
    result += "\ndiagnostic output truncated\n";
  else if (shown < diagnostics.size())
    out << diagnostics.size() - shown << " further diagnostics omitted\n";
  return result;
}
} // namespace zkc::language
