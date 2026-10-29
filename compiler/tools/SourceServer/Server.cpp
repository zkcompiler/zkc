#include "Server.h"
#include "llvm/Support/Path.h"
#include <algorithm>
#include <set>

using namespace llvm;
namespace zkc::editor {
namespace {
const json::Object *document(const Parameters &parameters) {
  auto *object = parameters.value.getAsObject();
  return object ? object->getObject("textDocument") : nullptr;
}
Expected<std::string> uri(const Parameters &parameters) {
  auto *value = document(parameters);
  auto name = value ? value->getString("uri") : std::nullopt;
  return name ? canonicalURI(*name)
              : Expected<std::string>(error("missing textDocument.uri"));
}
std::string standaloneModule(StringRef uri, StringRef text) {
  auto tree =
      syntax::parseHeaders(source::Revision({"main", text.str(), uri.str()}));
  for (auto id : tree.children(tree.root()))
    if (tree.node(id).kind == syntax::Kind::Module) {
      bool body = false;
      std::string name;
      for (auto child : tree.children(id)) {
        body |= tree.node(child).kind == syntax::Kind::Suite;
        if (tree.node(child).kind == syntax::Kind::Name)
          name = tree.text(child).str();
      }
      if (!body && !name.empty())
        return name;
    }
  auto decoded = lsp::URIForFile::fromURI(uri);
  if (!decoded) {
    consumeError(decoded.takeError());
    return "main";
  }
  return sys::path::stem(decoded->file()).str();
}
bool bounded(const std::map<std::string, Document> &documents) {
  size_t bytes = 0, diskBytes = 0;
  for (const auto &[_, document] : documents) {
    bytes += document.revision.text().size();
    if (document.disk)
      diskBytes += document.disk->text.size();
  }
  return documents.size() <= 256 && bytes <= 8388608 && diskBytes <= 8388608;
}
} // namespace
Server::Server(Input &input, lsp::MessageHandler &handlers) : input(input) {
  publish = handlers.outgoingNotification<json::Value>(
      "textDocument/publishDiagnostics");
  log = handlers.outgoingNotification<json::Value>("window/logMessage");
  handlers.method("initialize", this, &Server::initialize);
  handlers.method("shutdown", this, &Server::shutdown);
  handlers.notification("textDocument/didOpen", this, &Server::open);
  handlers.notification("textDocument/didChange", this, &Server::change);
  handlers.notification("textDocument/didClose", this, &Server::close);
  handlers.notification("workspace/didChangeWatchedFiles", this,
                        &Server::watched);
  handlers.notification("$/cancelRequest", this, &Server::cancel);
  handlers.method("textDocument/documentSymbol", this, &Server::symbols);
  handlers.method("textDocument/definition", this, &Server::definition);
  handlers.method("textDocument/hover", this, &Server::hover);
  handlers.method("textDocument/completion", this, &Server::completion);
  handlers.method("textDocument/formatting", this, &Server::formatting);
  handlers.method("zkc/status", this, &Server::status);
  worker = std::thread([this] { loop(); });
}
Server::~Server() {
  {
    std::lock_guard lock(mutex);
    stopping = true;
    if (running)
      running->cancellation.cancel();
    for (auto &[_, job] : active)
      job->cancellation.cancel();
    ready.notify_one();
  }
  worker.join();
}
void Server::initialize(const Parameters &parameters, Reply reply) {
  std::lock_guard lock(mutex);
  if (initialized || shuttingDown)
    return reply(error("server already initialized"));
  auto *object = parameters.value.getAsObject();
  if (!object)
    return reply(error("initialize requires an object"));
  std::map<std::string, Document> configured;
  std::set<std::string> modules;
  auto *optionsValue = object->get("initializationOptions");
  if (optionsValue && optionsValue->kind() != json::Value::Null &&
      !optionsValue->getAsObject())
    return reply(error("initializationOptions requires an object or null"));
  if (auto *options = object->getObject("initializationOptions")) {
    for (const auto &option : *options)
      if (option.first != "modules")
        return reply(error("unknown source initialization option"));
    if (options->get("modules") && !options->getArray("modules"))
      return reply(error("modules requires an array"));
    if (auto *files = options->getArray("modules")) {
      if (files->size() > 256)
        return reply(error("module limit exceeded"));
      for (const auto &item : *files) {
        auto *file = item.getAsObject();
        auto module = file ? file->getString("module") : std::nullopt;
        auto path = file ? file->getString("uri") : std::nullopt;
        if (!module || !path || file->size() != 2 || module->empty() ||
            module->size() > 2048 || !modules.insert(module->str()).second)
          return reply(
              error("configured modules require unique names and URIs"));
        auto name = canonicalURI(*path);
        if (!name)
          return reply(name.takeError());
        auto source = readDocument(*name, *module);
        if (!source)
          return reply(source.takeError());
        if (!configured
                 .emplace(*name, Document{*name,
                                          source::Revision(*source),
                                          false,
                                          true,
                                          {},
                                          *source,
                                          true})
                 .second ||
            !bounded(configured))
          return reply(error("duplicate URI or project limit exceeded"));
      }
    }
  }
  if (auto *capabilities = object->getObject("capabilities"))
    if (auto *general = capabilities->getObject("general"))
      if (auto *encodings = general->getArray("positionEncodings"))
        for (const auto &candidate : *encodings)
          if (candidate.getAsString() == "utf-8") {
            encoding = source::PositionEncoding::UTF8;
            break;
          }
  documents = std::move(configured);
  initialized = true;
  reply(json::Object{
      {"capabilities",
       json::Object{
           {"positionEncoding",
            encoding == source::PositionEncoding::UTF8 ? "utf-8" : "utf-16"},
           {"textDocumentSync",
            json::Object{{"openClose", true}, {"change", 2}}},
           {"documentSymbolProvider", true},
           {"definitionProvider", true},
           {"hoverProvider", true},
           {"completionProvider", json::Object{}},
           {"documentFormattingProvider", true}}},
      {"serverInfo",
       json::Object{{"name", "zkc-source-lsp"}, {"version", "0"}}}});
  changed();
}
void Server::finish(const std::shared_ptr<Job> &job,
                    Expected<json::Value> result) {
  if (job->finished) {
    if (!result)
      consumeError(result.takeError());
    return;
  }
  if (result && debugString(*result).size() > 8388608)
    result = error("source response byte limit exceeded",
                   lsp::ErrorCode::RequestFailed);
  job->finished = true;
  if (job->reply)
    job->reply(std::move(result));
  else if (!result)
    consumeError(result.takeError());
  if (!job->key.empty()) {
    auto found = active.find(job->key);
    if (found != active.end() && found->second == job)
      active.erase(found);
  }
}
void Server::changed() {
  if (running)
    running->cancellation.cancel();
  auto old = active;
  for (auto &[_, job] : old) {
    job->cancellation.cancel();
    finish(job, error("project changed", lsp::ErrorCode::ContentModified));
  }
  queue.clear();
  current = std::make_shared<Snapshot>(Snapshot{++generation, {}, {}, {}});
  for (const auto &[_, document] : documents)
    current->documents.push_back(document);
  auto job = std::make_shared<Job>();
  job->method = "diagnostics";
  job->snapshot = current;
  queue.push_back(job);
  ready.notify_one();
}
void Server::shutdown(const Parameters &, Reply reply) {
  std::lock_guard lock(mutex);
  if (active.count(input.requestKey))
    return reply(error("duplicate outstanding request ID",
                       lsp::ErrorCode::InvalidRequest));
  if (!initialized || shuttingDown)
    return reply(error("server is not running"));
  shuttingDown = true;
  if (running)
    running->cancellation.cancel();
  auto old = active;
  for (auto &[_, job] : old) {
    job->cancellation.cancel();
    finish(job,
           error("server shutting down", lsp::ErrorCode::RequestCancelled));
  }
  queue.clear();
  reply(json::Value(nullptr));
}
void Server::synchronizeError(Document &document, StringRef message) {
  document.synchronized = false;
  log(json::Object{
      {"type", 1},
      {"message",
       (message + "; send a full-text change or reopen " + document.uri)
           .str()}});
}
void Server::open(const Parameters &parameters) {
  std::lock_guard lock(mutex);
  if (!initialized || shuttingDown)
    return;
  auto name = uri(parameters);
  if (!name) {
    consumeError(name.takeError());
    return;
  }
  auto *item = document(parameters);
  auto text = item->getString("text");
  auto version = item->getInteger("version");
  auto found = documents.find(*name);
  if (!text || !version || *version < INT32_MIN || *version > INT32_MAX ||
      text->size() > 1048576) {
    if (found != documents.end()) {
      synchronizeError(found->second, "invalid document open");
      changed();
    } else
      log(json::Object{
          {"type", 1},
          {"message", "invalid document open or source byte limit"}});
    return;
  }
  if (found != documents.end() && found->second.open && found->second.version &&
      *version <= *found->second.version)
    return;
  auto module = found == documents.end() || !found->second.configured
                    ? standaloneModule(*name, *text)
                    : found->second.revision.buffer().module;
  auto next = documents;
  auto disk = found == documents.end() ? std::optional<source::SourceBuffer>{}
                                       : found->second.disk;
  next.insert_or_assign(
      *name, Document{*name, source::Revision({module, text->str(), *name}, 1),
                      true, true, *version, std::move(disk),
                      found != documents.end() && found->second.configured});
  if (!bounded(next)) {
    if (found != documents.end()) {
      synchronizeError(found->second, "project source limit exceeded");
      changed();
    } else
      log(json::Object{{"type", 1},
                       {"message", "project source limit exceeded"}});
    return;
  }
  documents = std::move(next);
  changed();
}
void Server::change(const Parameters &parameters) {
  std::lock_guard lock(mutex);
  if (!initialized || shuttingDown)
    return;
  auto name = uri(parameters);
  if (!name) {
    consumeError(name.takeError());
    return;
  }
  auto found = documents.find(*name);
  if (found == documents.end() || !found->second.open)
    return;
  auto &document = found->second;
  auto version = editor::document(parameters)->getInteger("version");
  auto *object = parameters.value.getAsObject();
  auto *changes = object ? object->getArray("contentChanges") : nullptr;
  if (!version || *version < INT32_MIN || *version > INT32_MAX || !changes ||
      changes->empty() || changes->size() > 1024) {
    synchronizeError(document, "invalid document change");
    changed();
    return;
  }
  if (document.version && *version <= *document.version)
    return;
  auto candidate = document.revision;
  bool synchronized = document.synchronized;
  for (const auto &value : *changes) {
    auto *edit = value.getAsObject();
    auto text = edit ? edit->getString("text") : std::nullopt;
    if (!text || text->size() > 1048576) {
      synchronized = false;
      break;
    }
    auto *span = edit->getObject("range");
    if (!span && !edit->get("range")) {
      candidate = source::Revision(
          {document.revision.buffer().module, text->str(), document.uri},
          candidate.version() + 1);
      synchronized = true;
      continue;
    }
    if (!span || !synchronized) {
      synchronized = false;
      break;
    }
    auto begin = position(span->get("start")), end = position(span->get("end"));
    if (!begin || !end) {
      synchronized = false;
      break;
    }
    // Revision::edit requires an increasing internal version; a notification
    // may contain several edits but has only one external LSP version.
    auto updated = candidate.edit(*begin, *end, encoding, *text,
                                  candidate.version() + 1, 1048576);
    if (!updated) {
      synchronized = false;
      break;
    }
    candidate = std::move(*updated);
  }
  auto next = documents;
  next.at(*name).revision = candidate;
  if (!synchronized || !bounded(next)) {
    synchronizeError(document,
                     "document edits could not be applied atomically");
    document.version = *version;
    changed();
    return;
  }
  if (!document.configured) {
    auto buffer = candidate.buffer();
    buffer.module = standaloneModule(document.uri, candidate.text());
    candidate = source::Revision(std::move(buffer), candidate.version());
  }
  document.revision = std::move(candidate);
  document.version = *version;
  document.synchronized = true;
  changed();
}
void Server::close(const Parameters &parameters) {
  std::lock_guard lock(mutex);
  if (!initialized || shuttingDown)
    return;
  auto name = uri(parameters);
  if (!name) {
    consumeError(name.takeError());
    return;
  }
  auto found = documents.find(*name);
  if (found == documents.end())
    return;
  if (found->second.configured) {
    if (found->second.disk)
      found->second.revision = source::Revision(*found->second.disk);
    found->second.open = false;
    found->second.synchronized = found->second.disk.has_value();
    found->second.version.reset();
  } else
    documents.erase(found);
  publish(json::Object{{"uri", *name}, {"diagnostics", json::Array{}}});
  changed();
}
void Server::watched(const Parameters &parameters) {
  std::lock_guard lock(mutex);
  if (!initialized || shuttingDown)
    return;
  auto *object = parameters.value.getAsObject();
  auto *changes = object ? object->getArray("changes") : nullptr;
  if (!changes || changes->size() > 256)
    return;
  bool modified = false;
  for (const auto &value : *changes) {
    auto *change = value.getAsObject();
    auto path = change ? change->getString("uri") : std::nullopt;
    if (!path)
      continue;
    auto name = canonicalURI(*path);
    if (!name) {
      consumeError(name.takeError());
      continue;
    }
    auto found = documents.find(*name);
    if (found == documents.end() || !found->second.configured)
      continue;
    auto fresh = readDocument(*name, found->second.revision.buffer().module);
    modified = true;
    if (!fresh) {
      consumeError(fresh.takeError());
      found->second.disk.reset();
      if (!found->second.open)
        synchronizeError(found->second, "configured module is unavailable");
      continue;
    }
    auto next = documents;
    auto &candidate = next.at(*name);
    candidate.disk = *fresh;
    if (!candidate.open) {
      candidate.revision = source::Revision(*fresh);
      candidate.synchronized = true;
    }
    if (!bounded(next)) {
      found->second.disk.reset();
      if (!found->second.open)
        synchronizeError(found->second, "project source limit exceeded");
      else
        log(json::Object{
            {"type", 1},
            {"message", "project source limit exceeded on disk reload"}});
    } else
      documents = std::move(next);
  }
  if (modified)
    changed();
}
void Server::cancel(const Parameters &parameters) {
  std::lock_guard lock(mutex);
  auto *object = parameters.value.getAsObject();
  auto *id = object ? object->get("id") : nullptr;
  if (!id)
    return;
  std::string key;
  if (auto string = id->getAsString())
    key = "s:" + string->str();
  else if (auto integer = id->getAsInteger())
    key = "i:" + std::to_string(*integer);
  auto found = active.find(key);
  if (found == active.end())
    return;
  auto job = found->second;
  job->cancellation.cancel();
  auto queued = std::find(queue.begin(), queue.end(), job);
  if (queued != queue.end())
    queue.erase(queued);
  finish(job, error("request cancelled", lsp::ErrorCode::RequestCancelled));
}
void Server::enqueue(StringRef method, const Parameters &parameters,
                     Reply reply) {
  std::lock_guard lock(mutex);
  if (!initialized)
    return reply(
        error("initialize first", lsp::ErrorCode::ServerNotInitialized));
  if (shuttingDown)
    return reply(
        error("server is shutting down", lsp::ErrorCode::InvalidRequest));
  if (active.count(input.requestKey))
    return reply(error("duplicate outstanding request ID",
                       lsp::ErrorCode::InvalidRequest));
  if (queue.size() >= 32 || active.size() >= 32)
    return reply(
        error("source request queue is full", lsp::ErrorCode::RequestFailed));
  if (debugString(parameters.value).size() > 65536)
    return reply(error("source query parameter limit exceeded",
                       lsp::ErrorCode::InvalidParams));
  auto name = uri(parameters);
  if (!name)
    return reply(name.takeError());
  if (!documents.count(*name))
    return reply(error("document is not captured"));
  auto job = std::make_shared<Job>();
  job->key = input.requestKey;
  job->method = method.str();
  job->uri = *name;
  job->parameters = parameters;
  job->reply = std::move(reply);
  job->snapshot = current;
  active.emplace(job->key, job);
  queue.push_back(job);
  ready.notify_one();
}
void Server::loop() {
  for (;;) {
    std::shared_ptr<Job> job;
    {
      std::unique_lock lock(mutex);
      ready.wait(lock, [&] { return stopping || !queue.empty(); });
      if (stopping) {
        auto old = active;
        for (auto &[_, pending] : old)
          finish(pending,
                 error("connection closed", lsp::ErrorCode::RequestCancelled));
        return;
      }
      job = queue.front();
      queue.pop_front();
      if (job->finished)
        continue;
      running = job;
    }
    if (job->method == "diagnostics")
      diagnostics(*job);
    else {
      auto answer = query(*job);
      std::lock_guard lock(mutex);
      if (job->snapshot != current || job->cancellation.cancelled()) {
        if (!answer)
          consumeError(answer.takeError());
        finish(job, error("request cancelled or superseded",
                          lsp::ErrorCode::RequestCancelled));
      } else
        finish(job, std::move(answer));
    }
    std::lock_guard lock(mutex);
    running.reset();
  }
}
#define QUERY(Name, Method)                                                    \
  void Server::Name(const Parameters &p, Reply r) {                            \
    enqueue(Method, p, std::move(r));                                          \
  }
QUERY(symbols, "symbols")
QUERY(definition, "definition")
QUERY(hover, "hover")
QUERY(completion, "completion")
QUERY(formatting, "formatting")
QUERY(status, "status")
#undef QUERY
} // namespace zkc::editor
