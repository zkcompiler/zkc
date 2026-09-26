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
  auto location = FileLineColLoc::get(&context, "test.pir", 7, 3);
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
    diagnostic.attachNote(FileLineColLoc::get(&context, "related.pir", 2, 9))
        << "source context";
  }
  require(text == toString(mixedErrors()), "LLVM error rendering changed");
  require(codes.size() == 2 && codes[0].code == "first" &&
              codes[0].detail == "details: with punctuation" &&
              codes[1].code == "last" && codes[1].detail.empty() &&
              notes == 1 && noteText[0] == "source context" &&
              noteLocations[0] ==
                  FileLineColLoc::get(&context, "related.pir", 2, 9),
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

  auto type =
      zkc::TableType::getChecked([&] { return emitError(location); }, &context,
                                 StringRef("f7"), StringRef("00"));
  require(!type && codes.size() == 1 &&
              codes[0].code == "invalid-original-rank",
          "type verifier exposes a structured refusal");

  OperationState state(location, zkc::PIRStopOp::getOperationName());
  auto *operation = Operation::create(state);
  zkc::diagnostics::emit(operation->emitOpError(), "local", "detail context");
  operation->destroy();
  require(codes.size() == 1 && codes[0].code == "local" &&
              codes[0].detail == "detail context" &&
              text == "'pir.stop' op local: detail context",
          "operation prefix and complete detail preserved");

  // Exercise the verifier callers that previously streamed detail after
  // attaching metadata. Invoke symbol verification directly so the checks do
  // not depend on MLIR's order of structural and region verification.
  OwningOpRef<ModuleOp> module(ModuleOp::create(location));
  OpBuilder operations(&context);
  operations.setInsertionPointToEnd(module->getBody());
  auto make = [&](StringRef name, ArrayRef<NamedAttribute> attributes,
                  bool region = false) {
    OperationState state(location, name);
    state.addAttributes(attributes);
    if (region)
      state.addRegion();
    return operations.create(state);
  };
  auto attr = [&](StringRef name, Attribute value) {
    return builder.getNamedAttr(name, value);
  };
  auto empty = builder.getArrayAttr({});
  auto role = builder.getStringAttr("P");
  auto roles = builder.getArrayAttr({role});
  auto mapping = builder.getArrayAttr({role, role});
  auto roleBindings = builder.getArrayAttr({mapping});
  auto dependency = [&](StringRef alias) {
    return builder.getArrayAttr({builder.getArrayAttr(
        {builder.getStringAttr(alias),
         FlatSymbolRefAttr::get(&context, "child"), empty})});
  };
  auto protocol = [&](StringRef name, ArrayAttr dependencies) {
    return cast<zkc::ProtocolOp>(make(
        "pir.protocol",
        {attr("sym_name", builder.getStringAttr(name)),
         attr("function_type", TypeAttr::get(builder.getFunctionType({}, {}))),
         attr("roles", roles), attr("parameters", empty),
         attr("dependencies", dependencies)},
        true));
  };
  auto child = protocol("child", empty);
  auto parent = protocol("parent", dependency("declared"));
  auto instance = cast<zkc::InstanceOp>(
      make("pir.instance",
           {attr("protocol", FlatSymbolRefAttr::get(&context, "child")),
            attr("dependencies", empty), attr("parameters", empty),
            attr("roles", builder.getArrayAttr({mapping, mapping}))}));
  SymbolTableCollection tables;
  auto expect = [&](StringRef code, StringRef detail, LogicalResult result) {
    require(failed(result) && codes.size() == 1 && codes[0].code == code &&
                codes[0].detail == detail &&
                StringRef(text).ends_with((code + ": " + detail).str()),
            "verifier detail missing from metadata or rendering");
  };
  expect("interactive-binding-attribute", "duplicate binding P",
         instance.verifySymbolUses(tables));
  instance->setAttr("roles", roleBindings);
  instance->setAttr("protocol", FlatSymbolRefAttr::get(&context, "absent"));
  expect("interactive-symbol-kind", "expected pir.protocol for @absent",
         instance.verifySymbolUses(tables));
  instance->setAttr("protocol", FlatSymbolRefAttr::get(&context, "parent"));
  instance->setAttr("dependencies",
                    builder.getArrayAttr({builder.getArrayAttr(
                        {builder.getStringAttr("other"),
                         FlatSymbolRefAttr::get(&context, "i")})}));
  expect("interactive-dependency-binding", "missing alias declared",
         instance.verifySymbolUses(tables));
  auto *body = new Block;
  parent->getRegion(0).push_back(body);
  operations.setInsertionPointToEnd(body);
  auto call = cast<zkc::ProtocolCallOp>(
      make("pir.protocol_call",
           {attr("dependency", builder.getStringAttr("absent"))}));
  expect("interactive-dependency", "undeclared alias absent",
         call.verifySymbolUses(tables));
  call->setAttr("dependency", builder.getStringAttr("declared"));
  child->setAttr("roles", builder.getArrayAttr({builder.getStringAttr("V")}));
  expect("interactive-dependency-role",
         "child formal role is absent in caller: V",
         call.verifySymbolUses(tables));
  child->setAttr("roles", roles);
  child->setAttr("function_type", TypeAttr::get(builder.getFunctionType(
                                      {builder.getI1Type()}, {})));
  expect("interactive-call-signature",
         "operands/results must match \"child\" function_type",
         call.verifySymbolUses(tables));

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
