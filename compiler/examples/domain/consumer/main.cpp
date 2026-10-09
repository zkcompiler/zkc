#include "mlir/AsmParser/AsmParser.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Contracts/Binding.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"
#include <cstdlib>
#if EXPECT_ENVELOPE
#include "envelope/Envelope.h"
#include "envelope/Specialization.h"
#endif
#include "llvm/Support/raw_ostream.h"
#if EXPECT_ENVELOPE
namespace {
void require(bool condition, llvm::StringRef message) {
  if (!condition) {
    llvm::errs() << message << '\n';
    std::exit(1);
  }
}
template <typename T> T take(llvm::Expected<T> value) {
  if (!value) {
    llvm::errs() << llvm::toString(value.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*value);
}
void domainControls(mlir::MLIRContext &context) {
  using namespace mlir;
  using namespace zkc::protocol;
  for (llvm::StringRef spelling :
       {"envelope<field:koala-bear,4>", "fixed_vector<envelope<bool,2>,3>"}) {
    auto logical = take(parseBoundType(spelling, false));
    auto native = decodeBoundType(&context, logical);
    require(bool(native), "contributed bound type did not decode");
    require(take(encodeBoundType(native, false)) == logical,
            "nested contributed descriptor changed");
    std::string printed;
    llvm::raw_string_ostream stream(printed);
    native.print(stream);
    require(parseType(printed, &context) == native,
            "contributed type assembly did not roundtrip");
    auto physical = defaultRepresentation(logical);
    require(!physical, "logical-only type acquired a physical implementation");
    llvm::consumeError(physical.takeError());
  }
  require(boundOperationName("envelope.keep") == "envelope.keep" &&
              boundOperationName("envelope.pair").empty(),
          "contributed operation mapping differs");
  auto module = parseSourceString<ModuleOp>(R"(
!T = !envelope.value<!algebra.field<"koala-bear">,4>
module { "protocol.module"() ({
 "local.binding"() {sym_name="keep",contract="envelope.keep",arguments=["field:koala-bear","4"],implementation=""} : ()->()
 local.func @Keep(%x:!T)->!T attributes {logical_origin=["Keep",[]]} {
   %y = "envelope.keep"(%x) {binding=@keep,site="keep",parameters=[]} : (!T)->!T
   local.return %y : !T
 }
 "protocol.func"() ({^entry(%x:!T):
   %y = "protocol.local_call"(%x) {callee=@Keep,role="P",site="use"} : (!T)->!T
   "protocol.return"(%y) : (!T)->()
 }) {sym_name="main",function_type=(!T)->!T,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })",
                                            ParserConfig(&context, false));
  require(bool(module), "contributed operation fixture refused");
  // The contributed carrier has logical adapters but no native port policy.
  // Check its registered operation invariant independently of module admission.
  unsigned operations = 0;
  module->walk([&](envelope::KeepOp operation) {
    ++operations;
    require(succeeded(operation->getName().verifyInvariants(operation)),
            "valid contributed signature refused");
    auto original = operation->getResult(0).getType();
    operation->getResult(0).setType(IntegerType::get(&context, 1));
    {
      ScopedDiagnosticHandler silence(&context,
                                      [](Diagnostic &) { return success(); });
      require(failed(operation->getName().verifyInvariants(operation)),
              "wrong contributed result type admitted");
    }
    operation->getResult(0).setType(original);
    require(succeeded(operation->getName().verifyInvariants(operation)),
            "contributed operation restoration failed");
  });
  require(operations == 1, "contributed operation missing");
  {
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(verify(*module)),
            "logical-only carrier acquired native endpoint support");
  }
  bool unknownProperty = false;
  {
    ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
      std::string message;
      llvm::raw_string_ostream stream(message);
      diagnostic.print(stream);
      unknownProperty |=
          llvm::StringRef(message).contains("mlir-unknown-property");
      return success();
    });
    auto malformed = parseSourceString<ModuleOp>(
        R"(module { "envelope.keep"() <{surprise="must-not-disappear"}> : ()->() })",
        &context);
    require(!malformed, "unknown contributed property disappeared");
  }
  require(unknownProperty, "contributed parser bypassed strict properties");
}
} // namespace
#endif
int main() {
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
#if !EXPECT_ENVELOPE
  return registry.getDialectAllocator("envelope") ? 1 : 0;
#else
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  domainControls(context);
  auto type = mlir::parseType("!envelope.value<i1, 3>", &context);
  if (!mlir::isa_and_nonnull<envelope::EnvelopeType>(type))
    return 1;
  auto module = mlir::parseSourceString<mlir::ModuleOp>(R"(
!F = !algebra.field<"koala-bear">
module { "protocol.module"() ({
 "local.binding"() {sym_name="add",contract="field.add",arguments=["koala-bear"],implementation=""} : ()->()
 local.func @Sum(%x:!F,%y:!F,%z:!F)->!F attributes {logical_origin=["Sum",[]]} {
   %a = "algebra.exec.field_add"(%x,%y) {binding=@add,site="first",parameters=[]} : (!F,!F)->!F
   %b = "algebra.exec.field_add"(%a,%z) {binding=@add,site="second",parameters=[]} : (!F,!F)->!F
   local.return %b : !F
 }
 "protocol.func"() ({^entry(%x:!F,%y:!F,%z:!F):
   %out = "protocol.local_call"(%x,%y,%z) {callee=@Sum,role="P",site="work"} : (!F,!F,!F)->!F
   "protocol.return"(%out) : (!F)->()
 }) {sym_name="main",function_type=(!F,!F,!F)->!F,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })",
                                                        &context);
  if (!module)
    return 2;
  auto text = [&] {
    std::string result;
    llvm::raw_string_ostream stream(result);
    module->print(stream, mlir::OpPrintingFlags().enableDebugInfo());
    return result;
  };
  auto before = text();
  if (mlir::failed(envelope::specializeFieldSums(*module)))
    return 3;
  unsigned composites = 0;
  module->walk([&](envelope::FieldSumChainOp) { ++composites; });
  if (composites != 1)
    return 4;
  if (mlir::failed(envelope::decomposeFieldSums(*module)) ||
      mlir::failed(mlir::verify(*module)) || text() != before)
    return 5;
  // Restoration metadata is required; failure must leave the composite present.
  if (mlir::failed(envelope::specializeFieldSums(*module)))
    return 6;
  module->walk([&](envelope::FieldSumChainOp operation) {
    operation->setAttr("first_attributes", mlir::DictionaryAttr::get(&context));
  });
  {
    mlir::ScopedDiagnosticHandler silence(
        &context, [](mlir::Diagnostic &) { return mlir::success(); });
    if (mlir::succeeded(envelope::decomposeFieldSums(*module)))
      return 7;
  }
  composites = 0;
  module->walk([&](envelope::FieldSumChainOp) { ++composites; });
  return composites != 1;
#endif
}
