#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Algebra/IR/AlgebraDialect.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Diagnostics.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
int main() {
  DialectRegistry registry;
  registry
      .insert<data::DataDialect, algebra::AlgebraDialect, func::FuncDialect>();
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  std::vector<diagnostics::RefusalInfo> refusals;
  ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
    auto codes = diagnostics::refusals(diagnostic);
    refusals.insert(refusals.end(), codes.begin(), codes.end());
    return success();
  });
  auto parse = [&](llvm::StringRef name, llvm::StringRef source, bool valid) {
    cases.run(name, [&] {
      refusals.clear();
      auto module = parseSourceString<ModuleOp>(source, &context);
      require(bool(module) == valid, "unexpected collection formation result");
      if (!valid)
        require(llvm::any_of(refusals,
                             [](const auto &refusal) {
                               return refusal.code == "mathematical-formation";
                             }),
                "collection refusal lost its semantic diagnostic");
    });
  };
  constexpr llvm::StringLiteral field = "!algebra.field<\"bls12-381.fr\">";
  constexpr llvm::StringLiteral other = "!algebra.field<\"bn254.fr\">";
  for (auto length : {0, 2}) {
    std::string array =
        "!data.field_array<\"bls12-381.fr\", " + std::to_string(length) + ">";
    std::string source =
        "module { func.func @extract(%a: " + array + ") -> " + field.str() +
        " { %v = \"data.array_at\"(%a) {index=0:i64} : (" + array + ") -> " +
        field.str() + " func.return %v : " + field.str() + " } }";
    parse("field array index bounds", source, length == 2);
  }
  auto pack = [&](llvm::StringRef name, llvm::StringRef inputs,
                  llvm::StringRef operands, llvm::StringRef types,
                  llvm::StringRef domain, unsigned length, bool valid) {
    std::string array = "!data.field_array<\"" + domain.str() + "\", " +
                        std::to_string(length) + ">";
    std::string source = "module { func.func @pack(" + inputs.str() + ") -> " +
                         array + " { %v = \"data.array_from_elements\"(" +
                         operands.str() + ") : (" + types.str() + ") -> " +
                         array + " func.return %v : " + array + " } }";
    parse(name, source, valid);
  };
  pack("empty field array", "", "", "", "bls12-381.fr", 0, true);
  std::string inputs = "%a: " + field.str() + ", %b: " + field.str();
  std::string types = field.str() + ", " + field.str();
  pack("ordered field elements", inputs, "%a, %b", types, "bls12-381.fr", 2,
       true);
  pack("wrong operand count", inputs, "%a, %b", types, "bls12-381.fr", 1,
       false);
  pack("wrong result field", inputs, "%a, %b", types, "bn254.fr", 2, false);
  pack("mixed operand fields", "%a: " + field.str() + ", %b: " + other.str(),
       "%a, %b", field.str() + ", " + other.str(), "bls12-381.fr", 2, false);
  cases.run("standalone collection formation", [&] {
    require(!context.getLoadedDialect("poly") &&
                !context.getLoadedDialect("protocol"),
            "collection formation loaded a higher semantic layer");
  });
  return cases.result();
}
