#include "zkc/Frontend/Protocol.h"
#include "zkc/Source/Execution.h"
#include "llvm/Support/raw_ostream.h"

// An unused family parameter still executes its selector. Static trace views
// must refuse instead of dropping this provenance-bearing entry execution.
int main() {
  auto document = zkc::frontend::parseProtocolDocument(R"pir(module {
    fn Select(n: index) -> index { return n; }
    protocol Family {
      roles (P, V);
      parameters (unused);
      inputs (P pn: index, V vn: index);
      outputs (P index, V index);
      return (pn, vn);
    }
    instance Main: Family {
      parameters (unused = ingress(10, P = Select(pn), V = Select(vn)));
      roles (P = P, V = V);
    }
    entry main = Main;
  })pir");
  if (!document) {
    llvm::errs() << llvm::toString(document.takeError()) << '\n';
    return 1;
  }
  auto execution = zkc::source::inspectExecution(*document->module(), "main");
  if (execution) {
    llvm::errs() << "unresolved family selector omitted from static trace\n";
    return 1;
  }
  auto code = llvm::toString(execution.takeError());
  if (code != "source-execution-family-input-required") {
    llvm::errs() << code << '\n';
    return 1;
  }
}
