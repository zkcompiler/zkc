#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Transforms/Passes.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/ResidueArithmetic.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Residue/IR/ResidueOps.h"
#include "zkc/Transforms/Residue.h"
#include "llvm/ADT/DenseMap.h"
#include <array>
#include <limits>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
// Interpret the actual word program. This oracle does not invoke the residue
// folder or the lowering's helper functions; comparisons use u128 arithmetic.
SmallVector<llvm::APInt> execute(func::FuncOp function, uint64_t a,
                                 uint64_t b) {
  llvm::DenseMap<Value, llvm::APInt> values;
  for (auto [arg, input] : llvm::zip(function.getArguments(), std::array{a, b}))
    values.try_emplace(arg, cast<IntegerType>(arg.getType()).getWidth(), input);
  for (auto &op : function.front()) {
    if (auto returned = dyn_cast<func::ReturnOp>(op)) {
      SmallVector<llvm::APInt> result;
      for (Value operand : returned.getOperands())
        result.push_back(values.at(operand));
      return result;
    }
    require(op.getNumResults() == 1,
            "unexpected word instruction result count");
    unsigned width = cast<IntegerType>(op.getResult(0).getType()).getWidth();
    auto input = [&](unsigned i) { return values.at(op.getOperand(i)); };
    llvm::APInt result(width, 0);
    if (auto constant = dyn_cast<arith::ConstantOp>(op))
      result = cast<IntegerAttr>(constant.getValue()).getValue();
    else if (isa<arith::ExtUIOp>(op))
      result = input(0).zext(width);
    else if (isa<arith::TruncIOp>(op))
      result = input(0).trunc(width);
    else if (auto add = dyn_cast<arith::AddIOp>(op)) {
      require(add.getOverflowFlags() == arith::IntegerOverflowFlags::none,
              "modular lowering introduced an unproved overflow flag");
      result = input(0) + input(1);
    } else if (auto sub = dyn_cast<arith::SubIOp>(op)) {
      require(sub.getOverflowFlags() == arith::IntegerOverflowFlags::none,
              "modular lowering introduced an unproved overflow flag");
      result = input(0) - input(1);
    } else if (auto mul = dyn_cast<arith::MulIOp>(op)) {
      require(mul.getOverflowFlags() == arith::IntegerOverflowFlags::none,
              "modular lowering introduced an unproved overflow flag");
      result = input(0) * input(1);
    } else if (isa<arith::RemUIOp>(op)) {
      require(!input(1).isZero(), "division by zero reached the word program");
      result = input(0).urem(input(1));
    } else if (auto comparison = dyn_cast<arith::CmpIOp>(op)) {
      require(comparison.getPredicate() == arith::CmpIPredicate::uge,
              "unexpected comparison predicate");
      result = llvm::APInt(1, input(0).uge(input(1)));
    } else if (isa<arith::SelectOp>(op))
      result = input(0).isZero() ? input(2) : input(1);
    else
      require(false,
              "unexpected word instruction: " + op.getName().getStringRef());
    values.try_emplace(op.getResult(0), result);
  }
  throw std::runtime_error("word program has no return");
}
std::string program(uint64_t q, unsigned width) {
  std::string type = "!residue.value<" + std::to_string(q) + " : ui" +
                     std::to_string(width) + ">";
  return "!R = " + type + R"mlir(
module {
 func.func @arithmetic(%a: !R, %b: !R) -> (!R, !R, !R, i64, i64) {
  %sum = residue.add %a, %b : !R
  %difference = residue.subtract %a, %b : !R
  %product = residue.multiply %a, %b : !R
  %lift = residue.lift %a : !R to i64
  %centered = residue.centered_lift %a : !R to i64
  return %sum, %difference, %product, %lift, %centered : !R, !R, !R, i64, i64
 }
}
)mlir";
}
} // namespace
int main() {
  DialectRegistry registry;
  registry.insert<residue::ResidueDialect, arith::ArithDialect,
                  func::FuncDialect>();
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  auto arithmetic = [&](uint64_t q, unsigned width, bool exhaustive) {
    auto source = parseSourceString<ModuleOp>(program(q, width), &context);
    require(bool(source), "valid residue module refused");
    auto candidate = residue::lowerArithmetic(*source);
    require(bool(candidate), "word lowering failed");
    require(succeeded(residue::verifyArithmetic(*source, *candidate)),
            "independent word reader refused valid arithmetic");
    auto function = *candidate->getOps<func::FuncOp>().begin();
    require(
        isa<residue::ValueType>(
            (*source->getOps<func::FuncOp>().begin()).getArgument(0).getType()),
        "word producer mutated its retained source");
    SmallVector<uint64_t> inputs{0, 1, q / 2, q / 2 + q % 2, q - 1};
    if (exhaustive) {
      inputs.clear();
      for (uint64_t i = 0; i < q; ++i)
        inputs.push_back(i);
    }
    for (uint64_t a : inputs)
      for (uint64_t b : inputs) {
        auto actual = execute(function, a, b);
        unsigned __int128 x = a, y = b, modulus = q;
        std::array<uint64_t, 5> expected{
            uint64_t((x + y) % modulus), uint64_t((x + modulus - y) % modulus),
            uint64_t((x * y) % modulus), a, a >= q / 2 + q % 2 ? a - q : a};
        require(actual.size() == expected.size(), "word output count changed");
        for (auto [got, wanted] : llvm::zip(actual, expected))
          require(got.getZExtValue() == wanted,
                  "word result differs at q=" + Twine(q) + ", a=" + Twine(a) +
                      ", b=" + Twine(b));
      }
  };
  for (uint64_t q = 2; q <= 19; ++q)
    cases.run("exhaustive canonical modulus " + Twine(q),
              [&] { arithmetic(q, 8, true); });
  for (auto [q, width] : std::array<std::pair<uint64_t, unsigned>, 5>{
           {{42, 8},
            {12289, 16},
            {2130706433, 32},
            {18446744069414584321ULL, 64},
            {std::numeric_limits<uint64_t>::max(), 64}}})
    cases.run(
        "word boundary modulus " + Twine(q),
        [&, modulus = q, bits = width] { arithmetic(modulus, bits, false); });
  for (StringRef type : {"!residue.value<0 : ui8>", "!residue.value<1 : ui8>",
                         "!residue.value<17 : i8>", "!residue.value<17 : si8>",
                         "!residue.value<17 : ui4097>"})
    cases.run("refused residue type " + type, [&] {
      std::vector<diagnostics::RefusalInfo> failures;
      ScopedDiagnosticHandler quiet(&context, [&](Diagnostic &diagnostic) {
        auto codes = diagnostics::refusals(diagnostic);
        failures.insert(failures.end(), codes.begin(), codes.end());
        return success();
      });
      auto module = parseSourceString<ModuleOp>(
          ("module { func.func private @bad(" + type + ") }").str(), &context);
      require(!module, "invalid residue type accepted");
      require(llvm::any_of(
                  failures,
                  [](const auto &r) { return r.code == "residue-formation"; }),
              "type refusal lost residue-formation");
    });
  auto mutation = [&](StringRef name,
                      llvm::function_ref<void(func::FuncOp)> change) {
    cases.run(name, [&] {
      auto source = parseSourceString<ModuleOp>(program(17, 8), &context);
      auto candidate = residue::lowerArithmetic(*source);
      require(bool(candidate), "mutation control failed to lower");
      change(*candidate->getOps<func::FuncOp>().begin());
      require(succeeded(verify(*candidate)),
              "mutation is not well-formed MLIR");
      std::vector<diagnostics::RefusalInfo> failures;
      ScopedDiagnosticHandler quiet(&context, [&](Diagnostic &diagnostic) {
        auto codes = diagnostics::refusals(diagnostic);
        failures.insert(failures.end(), codes.begin(), codes.end());
        return success();
      });
      require(failed(residue::verifyArithmetic(*source, *candidate)),
              "independent word reader accepted changed semantics");
      require(llvm::any_of(failures,
                           [](const auto &r) {
                             return r.code == "represented-arithmetic";
                           }),
              "candidate refusal lost represented-arithmetic");
    });
  };
  mutation("changed reduction modulus", [](func::FuncOp function) {
    auto rem = *function.getOps<arith::RemUIOp>().begin();
    OpBuilder builder(rem);
    auto value = arith::ConstantIntOp::create(
        builder, rem.getLoc(), 19, cast<IntegerType>(rem.getType()).getWidth());
    rem->setOperand(1, value);
  });
  mutation("unproved overflow flag", [](func::FuncOp function) {
    auto add = *function.getOps<arith::AddIOp>().begin();
    add.setOverflowFlags(arith::IntegerOverflowFlags::nuw);
  });
  mutation("unproved truncation flag", [](func::FuncOp function) {
    auto truncate = *function.getOps<arith::TruncIOp>().begin();
    truncate.setOverflowFlags(arith::IntegerOverflowFlags::nsw);
  });
  mutation("unproved extension sign", [](func::FuncOp function) {
    auto extend = *function.getOps<arith::ExtUIOp>().begin();
    extend.setNonNeg(true);
  });
  mutation("unknown arithmetic attribute", [](func::FuncOp function) {
    auto add = *function.getOps<arith::AddIOp>().begin();
    add->setAttr("approval", UnitAttr::get(function.getContext()));
  });
  mutation("wrong centered tie", [](func::FuncOp function) {
    auto compare = *function.getOps<arith::CmpIOp>().begin();
    OpBuilder builder(compare);
    auto value = arith::ConstantIntOp::create(builder, compare.getLoc(), 8, 64);
    compare->setOperand(1, value);
  });
  mutation("unselected undefined instruction", [](func::FuncOp function) {
    OpBuilder builder(function.front().getTerminator());
    auto zero = arith::ConstantIntOp::create(builder, function.getLoc(), 0, 8);
    arith::DivUIOp::create(builder, function.getLoc(), function.getArgument(0),
                           zero);
  });
  mutation("returned value changed", [](func::FuncOp function) {
    function.front().getTerminator()->setOperand(0, function.getArgument(0));
  });
  mutation("removed canonical reduction", [](func::FuncOp function) {
    auto truncate = *function.getOps<arith::TruncIOp>().begin();
    auto remainder = truncate.getIn().getDefiningOp<arith::RemUIOp>();
    truncate->setOperand(0, remainder.getLhs());
  });
  mutation("multiplication wraps before reduction", [](func::FuncOp function) {
    auto multiply = *function.getOps<arith::MulIOp>().begin();
    OpBuilder builder(multiply);
    auto narrow =
        arith::MulIOp::create(builder, multiply.getLoc(),
                              function.getArgument(0), function.getArgument(1));
    auto widened = arith::ExtUIOp::create(builder, multiply.getLoc(),
                                          multiply.getType(), narrow);
    multiply.getResult().replaceAllUsesWith(widened);
    multiply.erase();
  });
  cases.run("candidate sharing is independent of producer order", [&] {
    auto source = parseSourceString<ModuleOp>(program(17, 8), &context);
    auto candidate = residue::lowerArithmetic(*source);
    auto function = *candidate->getOps<func::FuncOp>().begin();
    auto add = *function.getOps<arith::AddIOp>().begin();
    auto left = add.getLhs();
    add->setOperand(0, add.getRhs());
    add->setOperand(1, left);
    require(succeeded(residue::verifyArithmetic(*source, *candidate)),
            "equivalent word addition order was refused");
  });
  cases.run("actual word expression is consumed", [&] {
    auto source = parseSourceString<ModuleOp>(R"mlir(
!R = !residue.value<17 : ui8>
module {
 func.func @constant_identity(%a: !R) -> !R {
  %zero = "residue.constant"() <{value = #residue.literal<!R, 0 : ui8>}> : () -> !R
  %result = residue.add %a, %zero : !R
  return %result : !R
 }
})mlir",
                                              &context);
    require(bool(source), "constant identity source failed to parse");
    auto candidate = residue::lowerArithmetic(*source);
    auto decoded = residue::consumeArithmetic(*source, *candidate);
    require(bool(decoded), "actual word consumption failed");
    auto function = *decoded->getOps<func::FuncOp>().begin();
    require(
        llvm::hasSingleElement(function.front()) &&
            function.front().back().getOperand(0) == function.getArgument(0),
        "consumer copied the source instead of reading the word expression");
  });
  cases.run("standard CSE preserves checked word semantics", [&] {
    auto source = parseSourceString<ModuleOp>(program(17, 8), &context);
    auto candidate = residue::lowerArithmetic(*source);
    PassManager passes(&context);
    passes.addPass(createCSEPass());
    require(succeeded(passes.run(*candidate)), "standard CSE failed");
    require(succeeded(residue::verifyArithmetic(*source, *candidate)),
            "word reader refused standard CSE");
    auto function = *candidate->getOps<func::FuncOp>().begin();
    for (uint64_t x = 0; x != 17; ++x)
      require(execute(function, x, 0)[0].getZExtValue() == x,
              "CSE changed the actual interpreted result");
  });
  for (unsigned inputWidth : {4, 8, 16, 64})
    cases.run("unsigned projection width " + Twine(inputWidth), [&] {
      auto word = "i" + std::to_string(inputWidth);
      auto source = parseSourceString<ModuleOp>(
          "!R = !residue.value<17 : ui8>\nmodule { func.func @projection(%x: " +
              word + ") -> !R { %r = residue.project %x : " + word +
              " to !R return %r : !R } }",
          &context);
      require(bool(source), "projection source failed to parse");
      auto candidate = residue::lowerArithmetic(*source);
      require(bool(candidate) &&
                  succeeded(residue::verifyArithmetic(*source, *candidate)),
              "projection correspondence failed");
      auto function = *candidate->getOps<func::FuncOp>().begin();
      for (uint64_t x : {uint64_t(0), uint64_t(1), uint64_t(16), uint64_t(17),
                         std::numeric_limits<uint64_t>::max()}) {
        auto input = llvm::APInt(inputWidth, x).getZExtValue();
        require(execute(function, input, 0).front().getZExtValue() ==
                    input % 17,
                "projection did not use the full unsigned input");
      }
    });
  for (StringRef body : {"%r = residue.lift %x : !R to i4 return %r : i4",
                         "%r = residue.project %x : !R to i8 return %r : i8"})
    cases.run("refused ill-typed residue conversion " + body, [&] {
      std::vector<diagnostics::RefusalInfo> failures;
      ScopedDiagnosticHandler quiet(&context, [&](Diagnostic &diagnostic) {
        auto codes = diagnostics::refusals(diagnostic);
        failures.insert(failures.end(), codes.begin(), codes.end());
        return success();
      });
      auto source = parseSourceString<ModuleOp>(
          std::string("!R = !residue.value<17 : ui8>\nmodule { func.func "
                      "@bad(%x: !R) -> ") +
              (body.contains("i4") ? "i4" : "i8") + " { " + body.str() + " } }",
          &context);
      require(!source, "ill-typed conversion accepted");
      require(llvm::any_of(
                  failures,
                  [](const auto &r) { return r.code == "residue-formation"; }),
              "conversion refusal lost residue-formation");
    });
  for (StringRef literal : {"17 : ui8", "255 : ui8", "0 : ui16"})
    cases.run("refused noncanonical literal " + literal, [&] {
      std::vector<diagnostics::RefusalInfo> failures;
      ScopedDiagnosticHandler quiet(&context, [&](Diagnostic &diagnostic) {
        auto codes = diagnostics::refusals(diagnostic);
        failures.insert(failures.end(), codes.begin(), codes.end());
        return success();
      });
      auto source = parseSourceString<ModuleOp>(
          std::string("!R = !residue.value<17 : ui8>\nmodule { func.func "
                      "@bad() -> !R { ") +
              "%r = \"residue.constant\"() <{value = #residue.literal<!R, " +
              literal.str() + ">}> : () -> !R return %r : !R } }",
          &context);
      require(!source, "noncanonical literal accepted");
      require(llvm::any_of(
                  failures,
                  [](const auto &r) { return r.code == "residue-formation"; }),
              "literal refusal lost residue-formation");
    });
  return cases.result();
}
