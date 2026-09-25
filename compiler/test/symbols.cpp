#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Dialect/IR.h"
#include "llvm/Support/raw_ostream.h"

using namespace mlir;

// Exercise real MLIR symbol-use enumeration and renaming across local aliases.
// A dependency string is not a use of the unrelated global symbol with that
// name.
int main() {
  DialectRegistry registry;
  zkc::registerDialects(registry);
  MLIRContext context(registry);
  auto module = parseSourceString<ModuleOp>(R"mlir(
module {
  func.func private @alias()
  "pir.protocol"() <{sym_name = "child", dependencies = [], external = true,
    function_type = (i1) -> i1, input_roles = ["P"], output_roles = ["P"],
    roles = ["P"], parameters = []}> ({}) : () -> ()
  "pir.protocol"() <{sym_name = "parent", dependencies = [["alias", @child, []]],
    external = false, function_type = (i1) -> i1, input_roles = ["P"],
    output_roles = ["P"], roles = ["P"], parameters = []}> ({
  ^bb0(%arg: i1):
    %result = "pir.protocol_call"(%arg) <{dependency = "alias", site = "s"}>
      : (i1) -> i1
    "pir.finish"(%result) : (i1) -> ()
  }) : () -> ()
  "pir.instance"() <{sym_name = "i", protocol = @child, parameters = [],
    dependencies = [], roles = [["P", "P"]]}> : () -> ()
})mlir",
                                            &context);
  if (!module)
    return 1;
  auto *child = SymbolTable::lookupSymbolIn(*module, "child");
  auto *alias = SymbolTable::lookupSymbolIn(*module, "alias");
  auto uses = SymbolTable::getSymbolUses(child, *module);
  if (!uses || std::distance(uses->begin(), uses->end()) != 2 ||
      !SymbolTable::symbolKnownUseEmpty(alias, *module))
    return 2;
  for (auto use : *uses)
    if (!isa<SymbolUserOpInterface>(use.getUser()))
      return 3;
  zkc::ProtocolCallOp call;
  module->walk([&](zkc::ProtocolCallOp op) { call = op; });
  if (!call || !isa<SymbolUserOpInterface>(call.getOperation()))
    return 4;
  auto renamed = StringAttr::get(&context, "renamed");
  if (failed(SymbolTable::replaceAllSymbolUses(child, renamed, *module)))
    return 5;
  SymbolTable::setSymbolName(child, renamed);
  if (call.getDependency() != "alias" || failed(verify(*module)))
    return 6;
  llvm::outs() << "symbol uses and alias-preserving rename passed\n";
  return 0;
}
