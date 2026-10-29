#include "Server.h"

using namespace llvm;
namespace zkc::editor {
namespace {
unsigned symbolKind(language::Declaration::Kind kind) {
  using K = language::Declaration::Kind;
  switch (kind) {
  case K::Module:
    return 2;
  case K::Interface:
    return 11;
  case K::Record:
    return 23;
  case K::Variant:
    return 10;
  case K::Protocol:
  case K::Math:
  case K::Local:
  case K::EntryFunction:
    return 12;
  default:
    return 13;
  }
}
const Document *document(const Snapshot &snapshot, StringRef uri) {
  for (const auto &doc : snapshot.documents)
    if (doc.uri == uri)
      return &doc;
  return nullptr;
}
json::Value location(ArrayRef<source::SourceBuffer> sources, source::Span span,
                     source::PositionEncoding encoding) {
  if (span.source.index >= sources.size())
    return nullptr;
  const auto &source = sources[span.source.index];
  if (source.origin != source::SourceOrigin::Captured)
    return nullptr;
  return json::Object{
      {"uri", source.diagnosticPath},
      {"range", range(source::Revision(source), span, encoding)}};
}
json::Array recoveredSymbols(const source::Revision &revision,
                             source::PositionEncoding encoding,
                             source::Cancellation cancellation) {
  auto tree = syntax::parseHeaders(revision, {0}, {}, cancellation);
  json::Array result;
  for (unsigned i = 0; i < tree.nodes().size() && result.size() < 10000; ++i) {
    syntax::NodeId id{i};
    auto kind = tree.node(id).kind;
    if (syntax::category(kind) != syntax::Category::Declaration ||
        kind == syntax::Kind::Use || kind == syntax::Kind::Attribute)
      continue;
    for (auto child : tree.children(id))
      if (tree.node(child).kind == syntax::Kind::Name) {
        result.push_back(json::Object{
            {"name", tree.text(child)},
            {"kind", 13},
            {"detail", "syntax only; project is not checked"},
            {"range", range(revision, tree.span(id), encoding)},
            {"selectionRange", range(revision, tree.span(child), encoding)}});
        break;
      }
  }
  return result;
}
} // namespace
Error Server::analyze(Job &job) {
  if (job.cancellation.cancelled())
    return error("request cancelled", lsp::ErrorCode::RequestCancelled);
  if (job.snapshot->analysis)
    return Error::success();
  std::vector<source::SourceBuffer> sources;
  for (const auto &doc : job.snapshot->documents) {
    if (!doc.synchronized)
      return error("project contains an unsynchronized document",
                   lsp::ErrorCode::ContentModified);
    sources.push_back(doc.revision.buffer());
  }
  if (sources.empty())
    return error("project has no captured documents");
  language::CaptureOptions options;
  options.format = "zkc-layout";
  auto capture = language::capture(std::move(sources), options);
  if (!capture)
    return capture.takeError();
  auto analysis = language::analyze(*capture, {}, job.cancellation);
  if (job.cancellation.cancelled())
    return error("request cancelled", lsp::ErrorCode::RequestCancelled);
  job.snapshot->capture = std::move(*capture);
  job.snapshot->analysis = std::move(analysis);
  return Error::success();
}
Expected<json::Value> Server::query(Job &job) {
  const auto *doc = document(*job.snapshot, job.uri);
  if (!doc || !doc->synchronized)
    return error("document is not synchronized",
                 lsp::ErrorCode::ContentModified);
  if (auto failure = analyze(job))
    return std::move(failure);
  const auto &analysis = *job.snapshot->analysis;
  auto checked = analysis.checkedProject();
  if (job.method == "status") {
    bool valid = bool(checked);
    bool requested = valid && !checked->pendingSpecifications().empty();
    if (!checked)
      consumeError(checked.takeError());
    return json::Value(
        json::Object{{"generation", job.snapshot->generation},
                     {"capture", job.snapshot->capture->identity()},
                     {"native", valid ? "checked" : "invalid"},
                     {"assurance", requested ? "unavailable"
                                   : valid   ? "not-requested"
                                             : "unknown"}});
  }
  if (!checked) {
    consumeError(checked.takeError());
    if (job.method == "symbols")
      return json::Value(
          recoveredSymbols(doc->revision, encoding, job.cancellation));
    return error(
        "semantic information is unavailable; repair project diagnostics",
        lsp::ErrorCode::RequestFailed);
  }
  source::SourceId source{UINT32_MAX};
  for (unsigned i = 0; i < checked->sources().size(); ++i)
    if (checked->sources()[i].diagnosticPath == job.uri)
      source.index = i;
  if (source.index == UINT32_MAX)
    return error("document is outside this capture");
  language::Authoring authoring(*checked);
  if (job.method == "symbols") {
    json::Array result;
    for (const auto &symbol : authoring.symbols(source))
      result.push_back(
          json::Object{{"name", symbol.name},
                       {"kind", symbolKind(symbol.kind)},
                       {"detail", symbol.detail},
                       {"range", range(doc->revision, symbol.span, encoding)},
                       {"selectionRange",
                        range(doc->revision, symbol.selection, encoding)}});
    return json::Value(std::move(result));
  }
  if (job.method == "formatting") {
    auto formatted = authoring.format(source, job.cancellation);
    if (!formatted.complete)
      return error("formatting requires complete resolved syntax",
                   lsp::ErrorCode::RequestFailed);
    json::Array edits;
    if (formatted.text != doc->revision.text())
      edits.push_back(json::Object{
          {"range",
           range(doc->revision,
                 {source, 0, uint32_t(doc->revision.text().size())}, encoding)},
          {"newText", formatted.text}});
    return json::Value(std::move(edits));
  }
  auto *parameters = job.parameters.value.getAsObject();
  auto at = position(parameters ? parameters->get("position") : nullptr);
  auto offset = at ? doc->revision.offset(*at, encoding) : std::nullopt;
  if (!offset)
    return error("invalid source position");
  if (job.method == "definition") {
    auto target = authoring.definition(source, *offset);
    return target ? location(checked->sources(), *target, encoding)
                  : json::Value(nullptr);
  }
  if (job.method == "hover") {
    auto hover = authoring.hover(source, *offset);
    if (!hover)
      return json::Value(nullptr);
    return json::Value(
        json::Object{{"range", range(doc->revision, hover->span, encoding)},
                     {"contents", json::Object{{"kind", "plaintext"},
                                               {"value", hover->text}}}});
  }
  if (job.method == "completion") {
    json::Array items;
    for (const auto &candidate : authoring.completion(source, *offset))
      items.push_back(json::Object{{"label", candidate.name},
                                   {"detail", candidate.detail}});
    return json::Value(json::Object{{"isIncomplete", items.size() == 256},
                                    {"items", std::move(items)}});
  }
  return error("unknown source query", lsp::ErrorCode::MethodNotFound);
}
void Server::diagnostics(Job &job) {
  auto failure = analyze(job);
  if (job.cancellation.cancelled()) {
    if (failure)
      consumeError(std::move(failure));
    return;
  }
  std::map<std::string, json::Array> diagnostics;
  for (const auto &doc : job.snapshot->documents)
    if (doc.open)
      diagnostics.emplace(doc.uri, json::Array{});
  if (failure) {
    auto message = toString(std::move(failure));
    for (const auto &doc : job.snapshot->documents)
      if (doc.open)
        diagnostics[doc.uri].push_back(json::Object{
            {"range", range(doc.revision, {{0}, 0, 0}, encoding)},
            {"severity", 1},
            {"code", doc.synchronized ? "source.project" : "source.sync"},
            {"source", "zkc"},
            {"message", message}});
  } else {
    const auto &analysis = *job.snapshot->analysis;
    for (const auto &diagnostic : analysis.diagnostics()) {
      if (diagnostic.primary &&
          diagnostic.primary->source.index < analysis.sources().size()) {
        const auto &source =
            analysis.sources()[diagnostic.primary->source.index];
        auto found = diagnostics.find(source.diagnosticPath);
        if (found != diagnostics.end())
          found->second.push_back(
              json::Object{{"range", range(source::Revision(source),
                                           *diagnostic.primary, encoding)},
                           {"severity", 1},
                           {"code", diagnostic.code},
                           {"source", "zkc"},
                           {"message", diagnostic.message}});
        else
          for (const auto &doc : job.snapshot->documents)
            if (doc.open)
              diagnostics[doc.uri].push_back(json::Object{
                  {"range", range(doc.revision, {{0}, 0, 0}, encoding)},
                  {"severity", 1},
                  {"code", diagnostic.code},
                  {"source", "zkc"},
                  {"message", source.module + ": " + diagnostic.message}});
      } else
        for (const auto &doc : job.snapshot->documents)
          if (doc.open)
            diagnostics[doc.uri].push_back(json::Object{
                {"range", range(doc.revision, {{0}, 0, 0}, encoding)},
                {"severity", 1},
                {"code", diagnostic.code},
                {"source", "zkc"},
                {"message", diagnostic.message}});
    }
  }
  std::lock_guard lock(mutex);
  if (job.snapshot != current || job.cancellation.cancelled() || shuttingDown ||
      stopping)
    return;
  for (auto &[uri, items] : diagnostics) {
    auto *doc = document(*job.snapshot, uri);
    json::Object message{{"uri", uri}, {"diagnostics", std::move(items)}};
    if (doc && doc->version)
      message["version"] = *doc->version;
    publish(std::move(message));
  }
}
} // namespace zkc::editor
