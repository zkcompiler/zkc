#include "zkc/Dialect/IR.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Transforms/Protocol.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace mlir;

// Public native export must reject malformed operations even when a C++ pass
// supplies them without running the textual parser's verifier first.
int main() {
  DialectRegistry registry;
  zkc::registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto document = zkc::frontend::parseProtocolDocument(R"pir(module {
    protocol Transfer {
      roles (Alice, Bob);
      inputs (Alice x: bool);
      message [send] bool: Alice(x) -> Bob(y);
      return ();
    }
    instance transfer: Transfer { roles (Alice = Alice, Bob = Bob); }
    entry main = transfer;
  })pir");
  if (!document) {
    errs() << toString(document.takeError());
    return 1;
  }
  auto common = zkc::protocol::importModule(document->root(), context);
  if (!common) {
    errs() << toString(common.takeError());
    return 2;
  }
  auto projected = zkc::protocol::project(**common);
  if (!projected) {
    errs() << toString(projected.takeError());
    return 3;
  }
  auto snapshot = [](ModuleOp module) {
    std::string text;
    raw_string_ostream out(text);
    module.print(out);
    return text;
  };
  auto before = snapshot(**projected);
  if (succeeded(zkc::protocol::lowerPhysical(**projected,
                                             {{"missing", "unknown"}})) ||
      snapshot(**projected) != before)
    return 8;
  for (bool send : {true, false}) {
    OwningOpRef<ModuleOp> copy(cast<ModuleOp>((*projected)->clone()));
    Operation *target = nullptr;
    copy->walk([&](Operation *op) {
      if (send ? isa<zkc::EmitOp>(op) : isa<zkc::AwaitOp>(op))
        target = op;
    });
    if (!target)
      return 4;
    if (send) {
      target->setOperands(ValueRange{});
    } else {
      // The received value is deliberately unused, so replacing it is safe.
      if (!target->use_empty())
        return 5;
      OperationState state(target->getLoc(), target->getName());
      state.addAttributes(target->getAttrs());
      auto *replacement = Operation::create(state);
      target->getBlock()->getOperations().insert(target->getIterator(),
                                                 replacement);
      target->erase();
    }
    auto result = zkc::protocol::exportSource(copy.get());
    if (result)
      return 6;
    if (toString(result.takeError()) != "interactive-malformed-ir")
      return 7;
  }
  outs() << "native export rejects missing emit operands and await results\n";
  return 0;
}
