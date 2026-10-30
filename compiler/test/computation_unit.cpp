#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Dialect/IR.h"
#include <string>
#include <tuple>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;

namespace {
constexpr llvm::StringLiteral aliases = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!A = !algebra.field_array<"bls12-381.fr", 2>
!P = !poly.polynomial<"bls12-381.fr", 1>
)mlir";
std::string standalone(StringRef declarations) {
  return aliases.str() + "module {" + declarations.str() + "}";
}
OwningOpRef<mlir::ModuleOp> parse(StringRef text, MLIRContext &context) {
  auto result =
      parseSourceString<mlir::ModuleOp>(text, ParserConfig(&context, false));
  require(bool(result), "test input did not parse");
  return result;
}
LogicalResult admit(mlir::ModuleOp module) {
  if (failed(verify(module)))
    return failure();
  auto result = module.walk([](mlir::ModuleOp unit) {
    if (mathematical::isComputationUnit(unit) &&
        failed(mathematical::verifyComputationUnit(unit)))
      return WalkResult::interrupt();
    return WalkResult::advance();
  });
  return failure(result.wasInterrupted());
}
void accepts(StringRef text, MLIRContext &context) {
  auto module = parse(text, context);
  require(succeeded(admit(*module)), "valid computation unit was refused");
}
void rejects(StringRef text, StringRef code, MLIRContext &context) {
  auto module = parse(text, context);
  std::string diagnostic;
  ScopedDiagnosticHandler handler(&context, [&](Diagnostic &value) {
    diagnostic += value.str();
    return success();
  });
  require(failed(admit(*module)), "malformed computation unit was admitted");
  require(namesIdentifier(diagnostic, code),
          "unexpected refusal: " + diagnostic);
}
std::string replace(StringRef original, StringRef from, StringRef to) {
  std::string result = original.str();
  auto offset = result.find(from.str());
  require(offset != std::string::npos, "missing test substitution");
  result.replace(offset, from.size(), to.str());
  return result;
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler silence(&context,
                                  [](Diagnostic &) { return success(); });
  Cases cases;
  cases.run("computation marker has an exact type", [&] {
    rejects(standalone("module @unit attributes {exec.computation=true} {"
                       "func.func @entry() {func.return}}"),
            "computation-profile", context);
  });
  cases.run("computation marker cannot decorate a function", [&] {
    rejects(
        standalone(
            "func.func @entry() attributes {exec.computation} {func.return}"),
        "computation-profile", context);
  });
  cases.run("computation entry retains explicit mathematical premises", [&] {
    accepts(standalone(R"mlir(
      module @unit attributes {exec.computation} {
        func.func @a(%x:!A,%i:ui64) attributes
          {data.preconditions=[#data.index_bound<1,0,0>]} {func.return}
      }
    )mlir"),
            context);
  });
  for (const auto &test : {
           std::tuple<StringRef, StringRef, StringRef>{
               "missing entry", "module @unit attributes {exec.computation} {}",
               "computation-entry"},
           {"two entries",
            "module @unit attributes {exec.computation} { func.func @a() "
            "{func.return} func.func @b() "
            "{func.return} }",
            "computation-entry"},
           {"no public entry",
            "module @unit attributes {exec.computation} {func.func private "
            "@a() {func.return}}",
            "computation-entry"},
           {"external entry",
            "module @unit attributes {exec.computation} {func.func @a()}",
            "func.func"},
           {"external dormant helper",
            "module @unit attributes {exec.computation} {func.func @a() "
            "{func.return} func.func "
            "private @unused()}",
            "mathematical-formation"},
           {"unsupported declaration",
            "module @unit attributes {exec.computation} {func.func @a() "
            "{func.return} module @unsupported {}}",
            "computation-formation"},
           {"unit attribute",
            "module @unit attributes {exec.computation, test.assume=true} "
            "{func.func @a() "
            "{func.return}}",
            "computation-formation"},
           {"entry attribute",
            "module @unit attributes {exec.computation} {func.func @a() "
            "attributes {assume=true} "
            "{func.return}}",
            "mathematical-formation"},
           {"polynomial port",
            "module @unit attributes {exec.computation} {func.func @a(%p:!P) "
            "-> !P {func.return "
            "%p:!P}}",
            "computation-entry"},
           {"affine port",
            "module @unit attributes {exec.computation} {func.func "
            "@a(%r:!runtime.capability<rng, \"bls12-381.fr\">) {func.return}}",
            "computation-entry"},
           {"dormant resource helper",
            "module @unit attributes {exec.computation} {func.func @a() "
            "{func.return} func.func "
            "private @r(%r:!runtime.capability<rng, \"bls12-381.fr\">) "
            "{func.return}}",
            "mathematical-formation"},
           {"dormant recursive helper",
            "module @unit attributes {exec.computation} {func.func @a() "
            "{func.return} func.func "
            "private @r() {func.call @r():()->() func.return}}",
            "mathematical-formation"},
           {"dormant unsupported body",
            "module @unit attributes {exec.computation} {func.func @a() "
            "{func.return} func.func "
            "private @r() {%v=arith.constant 1:i32 func.return}}",
            "mathematical-dependencies"},
           {"discardable mathematical attribute",
            "module @unit attributes {exec.computation} {func.func "
            "@a(%x:!F)->!F "
            "{%v=algebra.field_add %x,%x {assume=true}:(!F,!F)->!F func.return "
            "%v:!F}}",
            "mathematical-formation"},
       })
    cases.run(std::get<0>(test), [&] {
      rejects(standalone(std::get<1>(test)), std::get<2>(test), context);
    });
  cases.run("dormant helper cannot escape its owning symbol table", [&] {
    rejects(standalone(R"mlir(
      func.func private @outside(%x:!F) -> !F {func.return %x:!F}
      module @unit attributes {exec.computation} {
        func.func @entry() {func.return}
        func.func private @unused(%x:!F) -> !F {
          %v = func.call @outside(%x) : (!F)->!F
          func.return %v : !F
        }
      }
    )mlir"),
            "func.call", context);
  });
  for (bool valid : {true, false})
    cases.run(valid ? "helper premise discharged by actual index"
                    : "helper premise refused at actual call",
              [&] {
                std::string text = standalone(R"mlir(
        module @bounded attributes {exec.computation} {
          func.func private @at(%xs:!A,%i:ui64) -> !F
              attributes {data.preconditions=[#data.index_bound<1,0,0>]} {
            %v = "data.bounded_at"(%xs,%i) : (!A,ui64)->!F
            func.return %v : !F
          }
          func.func @entry(%xs:!A) -> !F {
            %i = "data.index"() {value="INDEX"} : ()->ui64
            %v = func.call @at(%xs,%i) : (!A,ui64)->!F
            func.return %v : !F
          }
        }
      )mlir");
                text = replace(text, "INDEX", valid ? "0" : "2");
                if (valid)
                  accepts(text, context);
                else
                  rejects(text, "finite-bound", context);
              });
  for (bool valid : {true, false})
    cases.run(valid ? "generic polynomial observation has known actual bound"
                    : "generic summary cannot hide an overflowing observation",
              [&] {
                std::string text = standalone(R"mlir(
        module @polynomial attributes {exec.computation} {
          func.func private @observe(%p:!P) -> !A {
            %v = "poly.coefficients"(%p) : (!P)->!A
            func.return %v : !A
          }
          func.func @entry(%a:!A) -> !A {
            %p = "poly.from_coefficients"(%a) : (!A)->!P
            %square = "poly.multiply"(%p,%p) : (!P,!P)->!P
            %v = func.call @observe(%ACTUAL) : (!P)->!A
            func.return %v : !A
          }
        }
      )mlir");
                text = replace(text, "ACTUAL", valid ? "p" : "square");
                if (valid)
                  accepts(text, context);
                else
                  rejects(text, "polynomial-formation", context);
              });
  cases.run("closed finite mathematics retains its owned domain and premises",
            [&] {
              accepts(standalone(R"mlir(
      module @sum attributes {exec.computation} {
        "data.domain"() ({
        ^entry(%xs:!A):
          %d = "data.domain_indices"(%xs) {axis=0:i64} : (!A)->!data.domain<ui64>
          "data.domain_yield"(%d) : (!data.domain<ui64>)->()
        }) {sym_name="items",sym_visibility="private",function_type=(!A)->!data.domain<ui64>} : ()->()
        func.func private @step(%state:!F,%i:ui64,%xs:!A) -> !F
            attributes {data.preconditions=[#data.index_bound<1,2,0>]} {
          %x = "data.bounded_at"(%xs,%i) : (!A,ui64)->!F
          %v = algebra.field_add %state,%x : (!F,!F)->!F
          func.return %v : !F
        }
        func.func @entry(%xs:!A,%initial:!F) -> !F {
          %v = "algebra.finite_fold"(%xs,%initial) {domain=@items,step=@step} : (!A,!F)->!F
          func.return %v : !F
        }
      }
    )mlir"),
                      context);
            });
  cases.run("unused domain dependencies still verify their constructors", [&] {
    rejects(standalone(R"mlir(
      module @unit attributes {exec.computation} {
        func.func @entry() {func.return}
        "data.domain"() ({
        ^entry(%xs:!A):
          %d = "data.domain_indices"(%xs) {axis=1:i64} : (!A)->!data.domain<ui64>
          "data.domain_yield"(%d) : (!data.domain<ui64>)->()
        }) {sym_name="unused",sym_visibility="private",function_type=(!A)->!data.domain<ui64>} : ()->()
      }
    )mlir"),
            "finite-domain", context);
  });
  return cases.result();
}
