#include "zkc/Dialect/Diagnostics.h"
#include "mlir/IR/Builders.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Support/Refusal.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace mlir;
using namespace llvm;

namespace {
class ExtendedRefusal : public ErrorInfo<ExtendedRefusal, zkc::Refusal> {
public:
  static char ID;
  ExtendedRefusal() : ErrorInfo("extension", "detail") {}
  void log(raw_ostream &out) const override {
    out << "extension-specific text";
  }
};
char ExtendedRefusal::ID;

class TrackedRefusal : public ErrorInfo<TrackedRefusal, zkc::Refusal> {
  bool &destroyed;

public:
  static char ID;
  explicit TrackedRefusal(bool &destroyed)
      : ErrorInfo("disabled", ""), destroyed(destroyed) {}
  ~TrackedRefusal() override { destroyed = true; }
};
char TrackedRefusal::ID;

void require(bool ok, StringRef message) {
  if (!ok) {
    errs() << message << '\n';
    std::exit(1);
  }
}
Error mixedErrors() {
  return joinErrors(zkc::error("first", "details: with punctuation"),
                    joinErrors(createStringError(inconvertibleErrorCode(),
                                                 "foreign: not a code"),
                               zkc::error("last")));
}
} // namespace

int main() {
  DialectRegistry registry;
  zkc::registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Builder builder(&context);
  auto location = FileLineColLoc::get(&context, "test.mlir", 7, 3);
  std::vector<zkc::diagnostics::RefusalInfo> codes;
  std::string text;
  unsigned notes = 0;
  std::vector<std::string> noteText;
  std::vector<Location> noteLocations;
  ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
    codes = zkc::diagnostics::refusals(diagnostic);
    text = diagnostic.str();
    notes = std::distance(diagnostic.getNotes().begin(),
                          diagnostic.getNotes().end());
    noteText.clear();
    noteLocations.clear();
    for (auto &note : diagnostic.getNotes()) {
      noteText.push_back(note.str());
      noteLocations.push_back(note.getLocation());
    }
    require(diagnostic.getLocation() == location, "diagnostic location lost");
    return success();
  });
  {
    auto diagnostic =
        zkc::diagnostics::emit(emitError(location), mixedErrors());
    diagnostic.attachNote(FileLineColLoc::get(&context, "related.mlir", 2, 9))
        << "source context";
  }
  require(text == toString(mixedErrors()), "LLVM error rendering changed");
  require(codes.size() == 2 && codes[0].code == "first" &&
              codes[0].detail == "details: with punctuation" &&
              codes[1].code == "last" && codes[1].detail.empty() &&
              notes == 1 && noteText[0] == "source context" &&
              noteLocations[0] ==
                  FileLineColLoc::get(&context, "related.mlir", 2, 9),
          "native refusals must retain fields and order across foreign errors");
  // The metadata's strings must survive temporary Error/source data teardown.
  {
    auto diagnostic = emitError(location);
    {
      std::string code = "temporary", detail = "owned detail";
      auto annotated =
          zkc::diagnostics::emit(std::move(diagnostic), code, detail);
      auto captured =
          zkc::diagnostics::refusals(*annotated.getUnderlyingDiagnostic());
      code.assign(4096, 'x');
      detail.clear();
      require(captured.size() == 1 && captured[0].code == "temporary" &&
                  captured[0].detail == "owned detail",
              "borrowed refusal fields");
    }
  }
  require(codes.size() == 1 && codes[0].code == "temporary" &&
              text == "temporary: owned detail",
          "metadata lifetime");
  emitError(location) << "first: identical-looking unclassified prose";
  require(codes.empty(), "must not infer identifiers from prose");
  zkc::diagnostics::emit(
      emitError(location),
      createStringError(inconvertibleErrorCode(), "foreign"));
  require(codes.empty() && text == "foreign",
          "foreign LLVM errors remain opaque");
  zkc::diagnostics::emit(emitError(location), make_error<ExtendedRefusal>());
  require(codes.size() == 1 && codes[0].code == "extension" &&
              codes[0].detail == "detail" && text == "extension-specific text",
          "native refusal extensions retain their own rendering");
  // Check payload lifetime even when LLVM unchecked-error assertions are off.
  bool destroyed = false;
  zkc::diagnostics::emit(InFlightDiagnostic(),
                         make_error<TrackedRefusal>(destroyed));
  require(destroyed, "inactive diagnostic retained its error payload");

  auto type = zkc::poly::TableType::getChecked(
      [&] { return emitError(location); }, &context, StringRef("f7"),
      StringRef("00"));
  require(!type && codes.size() == 1 &&
              codes[0].code == "invalid-original-rank",
          "type verifier exposes a structured refusal");

  OperationState state(location, zkc::local::StopOp::getOperationName());
  auto *operation = Operation::create(state);
  zkc::diagnostics::emit(operation->emitOpError(), "local", "detail context");
  operation->destroy();
  require(codes.size() == 1 && codes[0].code == "local" &&
              codes[0].detail == "detail context" &&
              text == "'local.stop' op local: detail context",
          "operation prefix and complete detail preserved");

  // Native entry symbol verification preserves the missing target in detail.
  OwningOpRef<ModuleOp> module(ModuleOp::create(location));
  OpBuilder operations(&context);
  operations.setInsertionPointToEnd(module->getBody());
  OperationState rootState(location, "protocol.module");
  rootState.addAttribute("profile",
                         zkc::protocol_ir::ProfileAttr::get(
                             &context, zkc::protocol_ir::Profile::Exec));
  rootState.addRegion();
  auto *root = operations.create(rootState);
  operations.createBlock(&root->getRegion(0));
  OperationState entryState(location, "protocol.entry");
  entryState.addAttribute("sym_name", builder.getStringAttr("main"));
  entryState.addAttribute("targets",
                          builder.getArrayAttr({builder.getArrayAttr(
                              {builder.getStringAttr("P"),
                               FlatSymbolRefAttr::get(&context, "absent")})}));
  auto entry =
      cast<zkc::protocol_ir::ProtocolEntryOp>(operations.create(entryState));
  SymbolTableCollection tables;
  require(failed(entry.verifySymbolUses(tables)) && codes.size() == 1 &&
              codes[0].code == "interactive-symbol-kind" &&
              StringRef(codes[0].detail).contains("absent"),
          "native verifier lost missing symbol detail");

  // Extracted payloads remain valid after their MLIR context and temporary
  // rendering operands are gone.
  auto owned = [] {
    MLIRContext temporary;
    std::vector<zkc::diagnostics::RefusalInfo> result;
    ScopedDiagnosticHandler collect(&temporary, [&](Diagnostic &diagnostic) {
      result = zkc::diagnostics::refusals(diagnostic);
      return success();
    });
    std::string detail;
    raw_string_ostream(detail) << StringAttr::get(&temporary, "owned") << " / "
                               << IntegerType::get(&temporary, 17);
    zkc::diagnostics::emit(emitError(UnknownLoc::get(&temporary)), "owned",
                           detail);
    return result;
  }();
  require(owned.size() == 1 && owned[0].code == "owned" &&
              owned[0].detail == "\"owned\" / i17",
          "rendered attribute/type detail borrowed its context");
  outs() << "structured MLIR diagnostics preserve identifiers, prose and "
            "ownership\n";
}
