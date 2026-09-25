#include "zkc/Dialect/Diagnostics.h"
#include "mlir/IR/Builders.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Support/Json.h"
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
  auto location = FileLineColLoc::get(&context, "test.pir", 7, 3);
  std::vector<zkc::diagnostics::RefusalInfo> codes;
  std::string text;
  unsigned notes = 0;
  ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
    codes = zkc::diagnostics::refusals(diagnostic);
    text = diagnostic.str();
    notes = std::distance(diagnostic.getNotes().begin(),
                          diagnostic.getNotes().end());
    require(diagnostic.getLocation() == location, "diagnostic location lost");
    return success();
  });
  {
    auto diagnostic =
        zkc::diagnostics::emit(emitError(location), mixedErrors());
    diagnostic.attachNote() << "source context";
  }
  require(text == toString(mixedErrors()), "LLVM error rendering changed");
  require(codes.size() == 2 && codes[0].code == "first" &&
              codes[0].detail == "details: with punctuation" &&
              codes[1].code == "last" && codes[1].detail.empty() && notes == 1,
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
  // An inactive MLIR diagnostic must still consume a native Error.
  zkc::diagnostics::emit(InFlightDiagnostic(), zkc::error("disabled"));

  auto type =
      zkc::TableType::getChecked([&] { return emitError(location); }, &context,
                                 StringRef("f7"), StringRef("00"));
  require(!type && codes.size() == 1 &&
              codes[0].code == "invalid-original-rank",
          "type verifier exposes a structured refusal");

  OperationState state(location, zkc::PIRStopOp::getOperationName());
  auto *operation = Operation::create(state);
  zkc::diagnostics::emit(operation->emitOpError(), "local", "detail")
      << " context";
  operation->destroy();
  require(codes.size() == 1 && codes[0].code == "local" &&
              codes[0].detail == "detail" &&
              text == "'pir.stop' op local: detail context",
          "operation prefix and streamed context preserved");
  outs() << "structured MLIR diagnostics preserve identifiers, prose and "
            "ownership\n";
}
