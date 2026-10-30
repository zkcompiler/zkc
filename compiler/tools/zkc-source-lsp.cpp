#include "SourceServer/Server.h"
#include "llvm/Support/raw_ostream.h"

int main() {
  auto input = std::make_unique<zkc::editor::Input>();
  auto &envelope = *input;
  llvm::lsp::JSONTransport transport(std::move(input), llvm::outs());
  llvm::lsp::MessageHandler handlers(transport);
  zkc::editor::Server server(envelope, handlers);
  if (auto error = transport.run(handlers)) {
    llvm::errs() << llvm::toString(std::move(error)) << '\n';
    return 1;
  }
  return envelope.exitSeen && server.shutdownRequested() ? 0 : 1;
}
