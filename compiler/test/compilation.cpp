#include "zkc/Compiler/Compilation.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Compiler/Source.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/TableLibrary.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Source/Codec.h"
#include "zkc/Source/Snapshot.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Protocol.h"
#include "zkc/Translation/Table.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace zkc;
namespace {
void require(bool value, StringRef message) {
  if (!value) {
    errs() << message << '\n';
    std::exit(1);
  }
}
template <typename T> T take(Expected<T> result) {
  if (!result) {
    errs() << toString(result.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*result);
}
constexpr StringLiteral program = R"(module {
  fn Identity(x: bool) -> bool { return x; }
  protocol Send {
    roles(P, V);
    inputs(P x: bool);
    outputs(V bool);
    local P: let a = Identity(x);
    message value: P(a) -> V(y);
    return y;
  }
  instance run: Send { roles(P = prover, V = verifier); }
  entry main = run;
})";
Compilation compile(ProtocolAction action) {
  // Both the caller's registry and analysis die before using the returned IR.
  mlir::DialectRegistry registry;
  // Built-ins are initialized by the invocation, even with an empty registry.
  auto analysis = frontend::analyzeProtocol(program, "owned.pir");
  auto document = take(lowerSource(analysis));
  return take(compileProtocol(std::move(document), {action, {}}, registry));
}
void ownership() {
  auto first = compile(ProtocolAction::Import);
  auto second = compile(ProtocolAction::Plan);
  require(first.module().getContext() != second.module().getContext(),
          "invocations share mutable contexts");
  require(first.source()->text() == program, "source spelling was not owned");
  auto expected = take(protocol::exportModule(second.module()));
  first = std::move(second); // destroys old IR before its old context
  require(succeeded(mlir::verify(first.module())), "moved IR lost its context");
  require(take(protocol::exportModule(first.module())) == expected,
          "move assignment changed the artifact");
  auto expansion = compile(ProtocolAction::Expand);
  require(expansion.source()->filename() == "owned.pir", "source name lost");
  auto projected = compile(ProtocolAction::Project);
  auto content = take(protocol::exportSource(projected.module()));
  require(std::get<source::Participants>(content).stage ==
              source::Participants::Stage::Logical,
          "projection did not stop");
}
void selectionAndFailure() {
  mlir::DialectRegistry registry;
  registerDialects(registry);
  auto document = take(frontend::parseProtocolDocument(program, "refusal.pir"));
  ProtocolOptions options;
  options.physical.implementations.sourceSnapshot.assign(64, '0');
  options.physical.implementations.choices = {{"missing", "missing"}};
  auto stale = compileProtocol(document, options, registry);
  require(!stale, "stale selection accepted");
  bool structured = false;
  handleAllErrors(stale.takeError(), [&](const Refusal &e) {
    structured = e.code == "binding-stale-selection";
  });
  require(structured, "source selection did not preserve its code");
  auto projected = compile(ProtocolAction::Project);
  auto logical = take(protocol::exportSource(projected.module()));
  auto rejected = compileProtocol(source::Document(logical), {}, registry);
  require(!rejected, "projection of participant input accepted");
  structured = false;
  handleAllErrors(rejected.takeError(), [&](const CompilationError &e) {
    for (const auto &refusal : e.refusals)
      structured |= refusal.code == "interactive-projection-stage";
  });
  require(structured, "pass refusal metadata lost at invocation teardown");
  auto malformed = *document.module();
  malformed.entries[0].instance = "missing";
  auto bad = compileProtocol(source::Document(malformed), {}, registry);
  require(!bad, "malformed typed source accepted");
  structured = false;
  handleAllErrors(bad.takeError(), [&](const CompilationError &e) {
    structured = !e.refusals.empty() && !e.message.empty();
  });
  require(structured, "located source refusal lost its structured identity");
}
} // namespace
int main() {
  ownership();
  selectionAndFailure();
}
