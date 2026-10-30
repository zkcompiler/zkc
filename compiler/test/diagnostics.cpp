#include "zkc/Dialect/Diagnostics.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Interfaces/CatalogType.h"
#include "zkc/Support/Refusal.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <future>
#include <thread>

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

// All emissions intentionally share one location. Promises order registration,
// emission and removal outside diagnostic callbacks (which MLIR serializes).
void checkOverlappingHandlers(bool forwarding) {
  MLIRContext context;
  auto location = UnknownLoc::get(&context);
  unsigned firstCalls = 0, secondCalls = 0, forwarded = 0;
  bool foreignLimit = false;
  ScopedDiagnosticHandler observer(&context, [&](Diagnostic &) {
    ++forwarded;
    return success();
  });
  std::promise<void> firstReady, secondReady, firstEmitted, secondEmitted,
      firstRemoved;
  auto secondStarted = secondReady.get_future();
  auto secondDone = secondEmitted.get_future();
  std::thread first([&] {
    {
      zkc::diagnostics::ScopedThreadDiagnosticHandler capture(
          &context, [&](Diagnostic &diagnostic) {
            ++firstCalls;
            auto codes = zkc::diagnostics::refusals(diagnostic);
            require(codes.size() == 1 &&
                        codes[0].code == "mathematical-expansion-limit",
                    "capture received another invocation's diagnostic");
            return success();
          });
      firstReady.set_value();
      secondStarted.wait();
      zkc::diagnostics::emit(emitError(location),
                             "mathematical-expansion-limit");
      firstEmitted.set_value();
      secondDone.wait();
    }
    firstRemoved.set_value();
  });
  firstReady.get_future().wait();
  {
    zkc::diagnostics::ScopedThreadDiagnosticHandler second(
        &context, [&](Diagnostic &diagnostic) {
          ++secondCalls;
          for (auto &code : zkc::diagnostics::refusals(diagnostic))
            foreignLimit |= code.code == "mathematical-expansion-limit";
          return forwarding ? failure() : success();
        });
    secondReady.set_value();
    firstEmitted.get_future().wait();
    zkc::diagnostics::emit(emitError(location), "second-invocation");
    secondEmitted.set_value();
    firstRemoved.get_future().wait();
    // The older scope has gone away while the newer scope is still alive.
    zkc::diagnostics::emit(emitError(location), "second-invocation-again");
  }
  first.join();
  require(firstCalls == 1 && secondCalls == 2 && !foreignLimit &&
              forwarded == (forwarding ? 2u : 0u),
          "overlapping capture, suppression or observation crossed threads");
  zkc::diagnostics::emit(emitError(location), "after-both-scopes");
  require(forwarded == (forwarding ? 3u : 1u),
          "scoped handler was not removed");
}

struct TypeGate {
  std::promise<void> entered, resume;
  bool used = false;
  unsigned skip = 0;
};
thread_local TypeGate *activeTypeGate = nullptr;
thread_local unsigned typeObservations = 0;
// A test-owned interface pauses a real binding read while its internal capture
// is installed. No production hooks or diagnostic-engine locks are involved.
struct PausingCatalogType
    : zkc::CatalogTypeInterface::ExternalModel<PausingCatalogType, NoneType> {
  std::optional<zkc::CatalogTypeApplication> getCatalogApplication(Type) const {
    ++typeObservations;
    // The closure reader first verifies its declarations. Count that exact
    // synchronous preflight below, then pause only inside its later capture.
    if (activeTypeGate && activeTypeGate->skip) {
      --activeTypeGate->skip;
      return zkc::CatalogTypeApplication{"bool", {}};
    }
    if (auto *gate = std::exchange(activeTypeGate, nullptr)) {
      gate->used = true;
      gate->entered.set_value();
      gate->resume.get_future().wait();
      return std::nullopt;
    }
    return zkc::CatalogTypeApplication{"bool", {}};
  }
};

void checkOverlappingBindingRead(bool closure) {
  DialectRegistry registry;
  zkc::registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  NoneType::attachInterface<PausingCatalogType>(context);
  context.printOpOnDiagnostic(false);
  OpBuilder builder(&context);
  auto location = builder.getUnknownLoc();
  OwningOpRef<ModuleOp> module(ModuleOp::create(location));
  builder.setInsertionPointToEnd(module->getBody());
  auto signature = builder.getFunctionType(
      {zkc::runtime::ScopeType::get(&context)},
      {zkc::exec::OutcomeType::get(
          &context,
          {zkc::data::SequenceType::get(&context, NoneType::get(&context))})});
  auto binding = zkc::runtime::BindingOp::create(
      builder, location, "invalid", "sequence.empty",
      builder.getArrayAttr({TypeAttr::get(NoneType::get(&context))}), "",
      signature, ArrayAttr{}, ArrayAttr{});
  std::vector<zkc::diagnostics::RefusalInfo> observed;
  ScopedDiagnosticHandler observer(&context, [&](Diagnostic &diagnostic) {
    auto codes = zkc::diagnostics::refusals(diagnostic);
    observed.insert(observed.end(), codes.begin(), codes.end());
    return success();
  });
  TypeGate gate;
  typeObservations = 0;
  require(succeeded(verify(binding)), "binding overlap preflight failed");
  gate.skip = closure ? typeObservations : 0;
  std::string result;
  std::thread reader([&] {
    activeTypeGate = &gate;
    if (closure) {
      auto read = zkc::protocol::readExecutionClosure(*module, false);
      require(!read, "invalid native closure accepted");
      result = toString(read.takeError());
    } else {
      auto read = zkc::protocol::readBinding(binding);
      require(!read, "invalid binding accepted");
      result = toString(read.takeError());
    }
    // Avoid hanging on a failed prerequisite: report a missing pause below.
    if (activeTypeGate) {
      activeTypeGate = nullptr;
      gate.entered.set_value();
    }
  });
  gate.entered.get_future().wait();
  zkc::diagnostics::emit(emitError(location), "foreign-required-refusal");
  gate.resume.set_value();
  reader.join();
  bool isolated = gate.used && observed.size() == 1 &&
                  observed[0].code == "foreign-required-refusal" &&
                  StringRef(result).contains("logical-type-formation") &&
                  !StringRef(result).contains("foreign-required-refusal");
  if (!isolated) {
    errs() << (closure ? "closure" : "binding")
           << " overlap: paused=" << gate.used << ", result=" << result
           << ", observed=";
    for (const auto &refusal : observed)
      errs() << refusal.code << ' ';
    errs() << '\n';
  }
  require(isolated, "internal binding capture consumed or misclassified a "
                    "foreign error");
}
} // namespace

int main() {
  checkOverlappingHandlers(false);
  checkOverlappingHandlers(true);
  checkOverlappingBindingRead(false);
  checkOverlappingBindingRead(true);
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

  OperationState state(location, zkc::exec::StopOp::getOperationName());
  auto *operation = Operation::create(state);
  zkc::diagnostics::emit(operation->emitOpError(), "local", "detail context");
  operation->destroy();
  require(codes.size() == 1 && codes[0].code == "local" &&
              codes[0].detail == "detail context" &&
              text == "'exec.stop' op local: detail context",
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
