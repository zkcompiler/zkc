#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Diagnostics.h"
#include "llvm/Support/raw_ostream.h"

int main() {
  mlir::DialectRegistry registry;
  registry.insert<zkc::algebra::AlgebraDialect, mlir::func::FuncDialect>();
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  unsigned failures = 0;
  std::vector<zkc::diagnostics::RefusalInfo> refusals;
  mlir::ScopedDiagnosticHandler handler(&context, [&](mlir::Diagnostic &d) {
    auto codes = zkc::diagnostics::refusals(d);
    refusals.insert(refusals.end(), codes.begin(), codes.end());
    return mlir::success();
  });
  auto parse = [&](llvm::StringRef name, llvm::StringRef source, bool valid) {
    refusals.clear();
    auto module = mlir::parseSourceString<mlir::ModuleOp>(source, &context);
    if (bool(module) != valid ||
        (!valid && !llvm::any_of(refusals, [](const auto &r) {
          return r.code == "mathematical-formation";
        }))) {
      llvm::errs() << "algebra formation case failed: " << name << '\n';
      ++failures;
    }
  };
  auto check = [&](llvm::StringRef name, llvm::StringRef op,
                   llvm::StringRef lhs, llvm::StringRef rhs,
                   llvm::StringRef output, bool valid) {
    std::string source = "module { func.func @standalone(%a: " + lhs.str() +
                         ", %b: " + rhs.str() + ") -> " + output.str() +
                         " { %v = algebra." + op.str() + " %a, %b : (" +
                         lhs.str() + ", " + rhs.str() + ") -> " + output.str() +
                         " func.return %v : " + output.str() + " } }";
    parse(name, source, valid);
  };
  constexpr llvm::StringLiteral field = "!algebra.field<\"bls12-381.fr\">";
  constexpr llvm::StringLiteral other = "!algebra.field<\"bn254.fr\">";
  constexpr llvm::StringLiteral group = "!algebra.group<\"bls12-381.g1\">";
  constexpr llvm::StringLiteral otherGroup = "!algebra.group<\"bn254.g1\">";
  for (auto op : {"field_add", "field_multiply", "field_subtract"}) {
    check(op, op, field, field, field, true);
    check("different field input", op, field, other, field, false);
    check("different field result", op, field, field, other, false);
  }
  check("field equality", "field_equal", field, field, "i1", true);
  check("different equality fields", "field_equal", field, other, "i1", false);
  check("group addition", "group_add", group, group, group, true);
  check("different groups", "group_add", group, otherGroup, group, false);
  check("different group result", "group_add", group, group, otherGroup, false);
  check("group equality", "group_equal", group, group, "i1", true);
  check("different equality groups", "group_equal", group, otherGroup, "i1",
        false);
  check("scalar action", "group_scale", group, field, group, true);
  check("wrong scalar field", "group_scale", group, other, group, false);
  check("unknown nominal group", "group_equal", "!algebra.group<\"missing\">",
        "!algebra.group<\"missing\">", "i1", false);
  constexpr llvm::StringLiteral g2 = "!algebra.group<\"bn254.g2\">";
  constexpr llvm::StringLiteral gt = "!algebra.group<\"bn254.gt\">";
  check("pairing target", "pairing", otherGroup, g2, gt, true);
  check("swapped pairing", "pairing", g2, otherGroup, gt, false);
  check("wrong pairing output", "pairing", otherGroup, g2, otherGroup, false);
  check("mixed pairing domain", "pairing", group, g2, gt, false);
  check("target scalar action", "group_scale", gt, other, gt, true);
  check("wrong target scalar", "group_scale", gt, field, gt, false);
  for (auto value : {"0", "00", "-1"}) {
    std::string source = "module { func.func @constant() -> " + field.str() +
                         " { %v = \"algebra.constant\"() {value=\"" + value +
                         "\"} : () -> " + field.str() +
                         " func.return %v : " + field.str() + " } }";
    parse("canonical field literal", source, llvm::StringRef(value) == "0");
  }
  for (auto shape : {"2", "0", "?", "2x2", "1048577"}) {
    std::string array =
        "tensor<" + std::string(shape) + "x" + field.str() + ">";
    std::string source =
        "module { func.func @extract(%a: " + array + ") -> " + field.str() +
        " { %v = \"algebra.array_at\"(%a) {index=0:i64} : (" + array + ") -> " +
        field.str() + " func.return %v : " + field.str() + " } }";
    parse("static field array", source, llvm::StringRef(shape) == "2");
  }
  if (context.getLoadedDialect("poly")) {
    llvm::errs() << "standalone algebra unexpectedly loaded Polynomial\n";
    ++failures;
  }
  if (context.getLoadedDialect("protocol")) {
    llvm::errs() << "standalone algebra unexpectedly loaded Protocol\n";
    ++failures;
  }
  return failures != 0;
}
