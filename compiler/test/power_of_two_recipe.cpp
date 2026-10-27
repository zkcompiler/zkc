#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/ComputationRecipes.h"
#include "support/ScopedFinite.h"
#include "llvm/ADT/DenseMap.h"
#include <variant>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
using Datum = std::variant<uint64_t, bool>;
// Evaluate the actual emitted straight-line recipe through its existing
// executable contracts. This is bounded native evidence, not a Runner proof.
bool evaluate(func::FuncOp function,
              llvm::ArrayRef<protocol::SourceExecutionStep> body,
              SymbolTable &symbols, uint64_t n, uint64_t r) {
  llvm::DenseMap<Value, Datum> values;
  values[function.getArgument(1)] = n;
  values[function.getArgument(2)] = r;
  for (const auto &step : body) {
    auto *op = step.operation;
    if (isa<exec::ReturnOp>(op)) {
      require(step.inputs.size() == 1 && values.count(step.inputs.front()),
              "recipe returned an unavailable value");
      return std::get<bool>(values.lookup(step.inputs.front()));
    }
    auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    auto *binding = ref ? symbols.lookup(ref.getValue()) : nullptr;
    require(binding && isa<exec::ApplyOp>(op) && step.outputs.size() == 1 &&
                step.regions.empty(),
            "recipe is not a straight-line scoped circuit");
    auto contract = binding->getAttrOfType<StringAttr>("contract").getValue();
    auto arg = [&](unsigned i) {
      require(i < step.inputs.size() && values.count(step.inputs[i]),
              "recipe consumed an unavailable value");
      return values.lookup(step.inputs[i]);
    };
    Datum result;
    if (contract == "index.constant") {
      auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
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
    values[step.outputs.front()] = result;
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
      computationRecipeSource(&source->getBody()->front(), "power", "entry");
  mathematical::RealizationWork work;
  auto candidate = realizeComputationEntry(*numerical, "power", {}, work);
  require(bool(candidate), "power recipe failed");
  require(succeeded(verify(*candidate)), "executable circuit failed formation");
  auto owner = computationRecipeOutput(*candidate);
  SymbolTable symbols(owner);
  auto function = symbols.lookup<func::FuncOp>("entry");
  require(bool(function), "power recipe lost its scoped entry");
  auto closure = take(protocol::readSourceExecutionClosure(owner));
  const auto &body = closure.bodies.at(function.getSymName().str());
  cases.run("all representable powers, zero and adjacent nonpowers", [&] {
    // Multiplication, independent of the producer's constant shifts.
    uint64_t value = 1;
    for (unsigned r = 0; r < 64; ++r) {
      require(evaluate(function, body, symbols, value, r),
              "representable power refused");
      require(!evaluate(function, body, symbols, 0, r), "zero accepted");
      require(!evaluate(function, body, symbols, value - 1, r),
              "predecessor accepted");
      require(!evaluate(function, body, symbols, value + 1, r),
              "successor accepted");
      if (r < 63)
        value *= 2;
    }
  });
  cases.run("unrepresentable exponents stay false", [&] {
    for (uint64_t r : {uint64_t(64), uint64_t(65), UINT64_MAX})
      for (uint64_t n : {uint64_t(0), uint64_t(1), UINT64_MAX})
        require(!evaluate(function, body, symbols, n, r),
                "oversized exponent accepted");
  });
  cases.run("independent recipe reader rejects a changed constant", [&] {
    require(succeeded(computation::verifyEntryRecipes(*numerical, *candidate,
                                                      "power")),
            "independent recipe reader refused the produced circuit");
    auto constant = scopedFinite::application(function, "index.constant");
    auto parameters = constant.getParametersAttr();
    OpBuilder builder(&context);
    auto changed = builder.getStrArrayAttr({"1"});
    require(parameters != changed, "constant mutation would change nothing");
    constant.setParametersAttr(changed);
    require(succeeded(verify(*candidate)), "changed constant lost formation");
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(computation::verifyEntryRecipes(*numerical, *candidate,
                                                   "power")),
            "independent recipe reader accepted a changed exponent");
    constant.setParametersAttr(parameters);
  });
  return cases.result();
}
