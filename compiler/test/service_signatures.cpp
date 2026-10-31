#include "mlir/AsmParser/AsmParser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Protocol/Services.h"
#include "zkc/Dialect/Registry.h"
using namespace mlir;
using namespace llvm;
using namespace zkc::test;
using namespace zkc::protocol_ir;
int main() {
  Cases cases;
  DialectRegistry registry;
  zkc::registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  cases.run("service signatures inspect nominal native types", [&] {
    for (const auto &service : zkc::protocol::randomServices)
      for (StringRef name : {"draw", "index", "indices"}) {
        auto method = zkc::protocol::serviceMethod(service.contract, name);
        if (!method)
          continue;
        SmallVector<Type> inputs;
        for (const auto &type : method->inputs)
          inputs.push_back(zkc::protocol::decodeBoundType(&context, type));
        auto output = zkc::protocol::decodeBoundType(&context, method->output);
        require(output && matchesServiceSignature(inputs, {output}, *method),
                "native service signature differs from shared declaration");
        require(
            !matchesServiceSignature(inputs, {}, *method) &&
                !matchesServiceSignature(inputs, {output, output}, *method) &&
                !matchesServiceSignature(
                    inputs, {IntegerType::get(&context, 64)}, *method),
            "service accepted a wrong width, signedness or result arity");
        auto physical =
            take(zkc::protocol::defaultRepresentation(method->output));
        auto represented = zkc::protocol::decodeBoundType(&context, physical);
        require(represented &&
                    !matchesServiceSignature(inputs, {represented}, *method),
                "service logical signature admitted a selected representation");
        if (name == "draw") {
          auto other = parseType(service.field == "bls12-381.fr"
                                     ? "!algebra.field<\"bn254.fr\">"
                                     : "!algebra.field<\"bls12-381.fr\">",
                                 &context);
          require(other && !matchesServiceSignature(inputs, {other}, *method),
                  "service signature lost nominal field identity");
        }
      }
  });
  return cases.result();
}
