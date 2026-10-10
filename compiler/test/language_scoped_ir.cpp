#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Translation/Language.h"
#include <fstream>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
std::string read(const std::string &path) {
  std::ifstream input(path);
  require(bool(input), "cannot read fixture " + path);
  return std::string(std::istreambuf_iterator<char>(input), {});
}
ClosedEntry example() {
  std::string root = ZKC_SCOPED_ROOT;
  auto captured = take(
      capture({{"example",
                read(root + "/examples/projects/scoped-computations/main.zkc"),
                "main.zkc"},
               {"zkc::computation",
                read(root + "/libraries/zkc/computation.zkc"), "scoped.zkc"},
               {"zkc::vector", read(root + "/libraries/zkc/vector.zkc"),
                "vector.zkc"}}));
  return take(
      closeEntry(take(analyze(captured).checkedProject()), "example::Demo"));
}
} // namespace
int main() {
  Cases cases;
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  cases.run("component example emits closure-free ordinary helpers", [&] {
    auto entry = example();
    auto original = take(prepareOriginal(entry));
    require(original.bytes().contains("protocol.local_call") &&
                original.bytes().contains("local.apply"),
            "ordinary call boundaries missing");
    require(!original.bytes().contains("scoped.invoke") &&
                !original.bytes().contains("closure"),
            "runtime closure emitted");
    take(compileEntry(original));
    take(compileEntry(original, {false, false}));
    auto bytes = take(emitOriginal(entry, context));
    auto parsed = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
    require(bool(parsed), "original did not parse");
    take(compareOriginal(entry, *parsed));
  });
  cases.run("native same-typed capture swap refuses source comparison", [&] {
    auto entry = example();
    auto bytes = take(emitOriginal(entry, context));
    auto module = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
    require(bool(module), "original did not parse");
    bool changed = false;
    module->walk([&](mlir::Operation *op) {
      if (changed || op->getName().getStringRef() != "local.apply")
        return;
      for (unsigned i = 0; i < op->getNumOperands(); ++i)
        for (unsigned j = i + 1; j < op->getNumOperands(); ++j)
          if (op->getOperand(i).getType() == op->getOperand(j).getType()) {
            auto value = op->getOperand(i);
            op->setOperand(i, op->getOperand(j));
            op->setOperand(j, value);
            changed = true;
            return;
          }
    });
    require(changed, "no comparable captures");
    refuses(compareOriginal(entry, *module), "source.correspondence");
  });
  return cases.result();
}
