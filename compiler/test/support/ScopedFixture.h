#ifndef ZKC_TEST_SCOPED_FIXTURE_H
#define ZKC_TEST_SCOPED_FIXTURE_H
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Transforms/Passes.h"
#include <string>
namespace zkc::test {
inline std::string replaceText(std::string text, llvm::StringRef from,
                               llvm::StringRef to) {
  size_t position = 0;
  while ((position = text.find(from.str(), position)) != std::string::npos) {
    text.replace(position, from.size(), to.str());
    position += to.size();
  }
  return text;
}
// The caller authors the actual scoped CFG, including its success return.
// Projection supplies participant metadata through the production pass.
inline std::string scopedFixture(llvm::StringRef declarations,
                                 llvm::StringRef arguments,
                                 llvm::StringRef inputs, llvm::StringRef types,
                                 llvm::StringRef result, llvm::StringRef body,
                                 unsigned arity) {
  std::string roles;
  for (unsigned i = 0; i < arity; ++i)
    roles += (i ? "," : "") + std::string("[\"P\"]");
  auto outcome = "!exec.outcome<(" + result.str() + ")>";
  std::string failure;
  if (body.contains("^failed"))
    failure = "\n^failed(%reason:!exec.stop):\n"
              "%failure=\"exec.failed\"(%reason) : (!exec.stop)->" +
              outcome + "\nfunc.return %failure : " + outcome;
  return "module { \"protocol.module\"() ({\n" + declarations.str() +
         "\nfunc.func @Work(%scope:!runtime.scope" +
         (arguments.empty() ? "" : "," + arguments.str()) + ")->" + outcome +
         " attributes {no_inline,runtime.origin=[\"Work\",[]]} {\n" +
         body.str() + failure + "\n}\n" + "\"protocol.func\"() ({ ^entry(" +
         arguments.str() + "):\n" + "%out = \"protocol.local_call\"(" +
         inputs.str() + ") {callee=@Work,role=\"P\",site=\"work\"} : (" +
         types.str() + ")->" + result.str() +
         "\n\"protocol.return\"(%out) : (" + result.str() + ")->()\n" +
         "}) {sym_name=\"main\",function_type=(" + types.str() + ")->" +
         result.str() + ",roles=[\"P\"],input_roles=[" + roles +
         "],output_roles=[[\"P\"]]} : ()->()\n" +
         "}) {profile=#protocol.profile<protocol>} : ()->() }";
}
inline llvm::Expected<mlir::OwningOpRef<mlir::ModuleOp>>
executableFixture(llvm::StringRef text, mlir::MLIRContext &context) {
  auto module = mlir::parseSourceString<mlir::ModuleOp>(text, &context);
  if (!module)
    return zkc::error("fixture-parse");
  mlir::PassManager pipeline(&context);
  pipeline.addPass(protocol::createProjectProtocolPass(false));
  pipeline.addPass(protocol::createLowerMathPass());
  if (mlir::failed(pipeline.run(*module)))
    return zkc::error("fixture-lowering");
  return module;
}
} // namespace zkc::test
#endif
