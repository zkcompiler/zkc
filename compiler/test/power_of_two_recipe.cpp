#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/KernelRecipes.h"
#include "llvm/ADT/DenseMap.h"
#include <variant>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
using Datum = std::variant<uint64_t, bool>;
// Evaluate the actual emitted straight-line recipe through its existing
// executable contracts. This is bounded native evidence, not a Runner proof.
bool evaluate(local::FuncOp function, SymbolTable &symbols, uint64_t n,
              uint64_t r) {
  llvm::DenseMap<Value, Datum> values;
  auto &block = function.getBody().front();
  values[block.getArgument(0)] = n;
  values[block.getArgument(1)] = r;
  for (auto &op : block) {
    if (isa<local::ReturnOp>(op))
      return std::get<bool>(values.lookup(op.getOperand(0)));
    auto ref = op.getAttrOfType<FlatSymbolRefAttr>("binding");
    auto *binding = ref ? symbols.lookup(ref.getValue()) : nullptr;
    require(binding && op.getNumResults() == 1 && op.getNumRegions() == 0,
            "recipe is not a straight-line executable circuit");
    auto contract = binding->getAttrOfType<StringAttr>("contract").getValue();
    auto arg = [&](unsigned i) { return values.lookup(op.getOperand(i)); };
    Datum result;
    if (contract == "index.constant") {
      auto parameters = op.getAttrOfType<ArrayAttr>("parameters");
      uint64_t value;
      require(parameters && parameters.size() == 1 &&
                  !cast<StringAttr>(parameters[0])
                       .getValue()
                       .getAsInteger(10, value),
              "invalid executable constant");
      result = value;
    } else if (contract == "index.equal")
      result = std::get<uint64_t>(arg(0)) == std::get<uint64_t>(arg(1));
    else if (contract == "bool.and")
      result = std::get<bool>(arg(0)) && std::get<bool>(arg(1));
    else if (contract == "bool.or")
      result = std::get<bool>(arg(0)) || std::get<bool>(arg(1));
    else
      throw std::runtime_error("unexpected execution contract " +
                               contract.str());
    values[op.getResult(0)] = result;
  }
  throw std::runtime_error("recipe did not return");
}
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto source = parseSourceString<ModuleOp>(R"(
    module { "protocol.module"() ({
      func.func private @power(%n:ui64,%r:ui64)->i1 {
        %ok = "data.index_power_of_two"(%n,%r) : (ui64,ui64)->i1
        return %ok : i1
      }
    }) {profile=#protocol.profile<protocol>} : ()->() }
  )",
                                            &context);
  require(bool(source), "power fixture failed native formation");
  auto numerical =
      kernelRecipeSource(&source->getBody()->front(), "power", "entry");
  mathematical::RealizationWork work;
  auto candidate = realizeKernelEntry(*numerical, "power", {}, work);
  require(bool(candidate), "power recipe failed");
  require(succeeded(verify(*candidate)), "executable circuit failed formation");
  auto owner = kernelRecipeOutput(*candidate);
  SymbolTable symbols(owner);
  local::FuncOp function;
  for (auto entry : owner.getBody().front().getOps<local::FuncOp>())
    function = entry;
  cases.run("all representable powers, zero and adjacent nonpowers", [&] {
    // Multiplication, independent of the producer's constant shifts.
    uint64_t value = 1;
    for (unsigned r = 0; r < 64; ++r) {
      require(evaluate(function, symbols, value, r),
              "representable power refused");
      require(!evaluate(function, symbols, 0, r), "zero accepted");
      require(!evaluate(function, symbols, value - 1, r),
              "predecessor accepted");
      require(!evaluate(function, symbols, value + 1, r), "successor accepted");
      if (r < 63)
        value *= 2;
    }
  });
  cases.run("unrepresentable exponents stay false", [&] {
    for (uint64_t r : {uint64_t(64), uint64_t(65), UINT64_MAX})
      for (uint64_t n : {uint64_t(0), uint64_t(1), UINT64_MAX})
        require(!evaluate(function, symbols, n, r),
                "oversized exponent accepted");
  });
  cases.run("independent recipe reader rejects a changed constant", [&] {
    require(
        succeeded(kernel::verifyEntryRecipes(*numerical, *candidate, "power")),
        "independent recipe reader refused the produced circuit");
    auto &constant = function.getBody().front().front();
    auto parameters = constant.getAttr("parameters");
    OpBuilder builder(&context);
    constant.setAttr("parameters",
                     builder.getArrayAttr({builder.getStringAttr("1")}));
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(kernel::verifyEntryRecipes(*numerical, *candidate, "power")),
            "independent recipe reader accepted a changed exponent");
    constant.setAttr("parameters", parameters);
  });
  return cases.result();
}
