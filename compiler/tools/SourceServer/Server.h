#ifndef ZKC_SOURCE_SERVER_H
#define ZKC_SOURCE_SERVER_H

#include "RequestQueue.h"
#include "zkc/Language/Authoring.h"
#include "llvm/Support/LSP/Transport.h"
#include <condition_variable>
#include <deque>
#include <mutex>
#include <thread>

namespace zkc::editor {
struct Parameters {
  llvm::json::Value value = nullptr;
};
inline bool fromJSON(const llvm::json::Value &value, Parameters &out,
                     llvm::json::Path) {
  out.value = value;
  return true;
}
using Reply = llvm::lsp::Callback<llvm::json::Value>;

/// Captures an envelope only until synchronous method dispatch. Workers copy
/// its identity into a Job. No worker reads this mutable input object.
class Input final : public llvm::lsp::JSONTransportInput {
public:
  bool hasError() const override { return invalid; }
  bool isEndOfInput() const override { return ended; }
  llvm::LogicalResult readDelimitedMessage(std::string &) override;
  llvm::LogicalResult readStandardMessage(std::string &) override;
  std::string requestKey;
  bool exitSeen = false;

private:
  bool invalid = false, ended = false;
  llvm::LogicalResult stop();
};

struct Document {
  std::string uri;
  source::Revision revision;
  bool open = false, synchronized = true;
  std::optional<int64_t> version;
  std::optional<source::SourceBuffer> disk;
  bool configured = false;
};
struct Snapshot {
  uint64_t generation;
  std::vector<Document> documents;
  // Only the single compute worker reads or writes the completed result.
  std::optional<language::Analysis> analysis;
  std::optional<language::CapturedProject> capture;
};
struct Job {
  std::string key, method, uri;
  Parameters parameters;
  Reply reply;
  std::shared_ptr<Snapshot> snapshot;
  source::Cancellation cancellation;
  bool finished = false;
};
class Server {
public:
  Server(Input &, llvm::lsp::MessageHandler &);
  ~Server();
  void initialize(const Parameters &, Reply);
  void shutdown(const Parameters &, Reply);
  void open(const Parameters &);
  void change(const Parameters &);
  void close(const Parameters &);
  void watched(const Parameters &);
  void cancel(const Parameters &);
  void symbols(const Parameters &, Reply);
  void definition(const Parameters &, Reply);
  void hover(const Parameters &, Reply);
  void completion(const Parameters &, Reply);
  void formatting(const Parameters &, Reply);
  void status(const Parameters &, Reply);
  bool shutdownRequested() const { return shuttingDown; }

private:
  Input &input;
  llvm::lsp::OutgoingNotification<llvm::json::Value> publish, log;
  std::map<std::string, Document> documents;
  std::shared_ptr<Snapshot> current;
  RequestQueue<Job> requests;
  std::mutex mutex;
  std::condition_variable ready;
  std::thread worker;
  uint64_t generation = 0;
  bool initialized = false, shuttingDown = false, stopping = false;
  source::PositionEncoding encoding = source::PositionEncoding::UTF16;

  void enqueue(llvm::StringRef, const Parameters &, Reply);
  void changed(); // mutex held: invalidate, cancel and enqueue diagnostics
  void finish(const std::shared_ptr<Job> &, llvm::Expected<llvm::json::Value>);
  void loop();
  void synchronizeError(Document &, llvm::StringRef);
  llvm::Expected<llvm::json::Value> query(Job &);
  void diagnostics(Job &);
  llvm::Error analyze(Job &);
};
llvm::Error error(llvm::StringRef,
                  llvm::lsp::ErrorCode = llvm::lsp::ErrorCode::InvalidParams);
llvm::Expected<std::string> canonicalURI(llvm::StringRef);
llvm::Expected<source::SourceBuffer> readDocument(llvm::StringRef uri,
                                                  llvm::StringRef module);
std::optional<source::Position> position(const llvm::json::Value *);
llvm::json::Value range(const source::Revision &, source::Span,
                        source::PositionEncoding);
} // namespace zkc::editor
#endif
