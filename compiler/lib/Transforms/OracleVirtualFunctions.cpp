#include "OracleVirtualFunctions.h"
#include "OracleEmissionAccounting.h"
#include "OracleVirtualRecipe.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Support/Refusal.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
Expected<OracleVirtualFunctions>
emitOracleVirtualFunctions(ModuleOp candidate,
                           protocol_ir::OracleDefinitionOp source,
                           OracleVirtualFunctionWork &work) {
  return oracleExpectedWithWork(
      work.getWork(), [&]() -> Expected<OracleVirtualFunctions> {
        auto sourceUnit =
            source
                ? dyn_cast<protocol_ir::ProtocolModuleOp>(source->getParentOp())
                : protocol_ir::ProtocolModuleOp{};
        if (!candidate || !sourceUnit ||
            source.getContext() != candidate.getContext() ||
            sourceUnit.getProfile() != protocol_ir::Profile::Protocol ||
            failed(work.checkSubject(sourceUnit)) ||
            failed(work.checkSubject(candidate)) ||
            !hasSingleElement(candidate.getBody()->getOperations()))
          return error("oracle-virtual-functions");
        auto unit = dyn_cast<protocol_ir::ProtocolModuleOp>(
            candidate.getBody()->front());
        if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol ||
            unit == sourceUnit)
          return error("oracle-virtual-functions");
        auto session = startOracleEmissionSession(work.getWork(), unit);
        if (auto found = work.getWork().emission->findVirtualFunctions(source))
          return std::move(*found);
        auto recipe = planOracleVirtualFunctions(source, work);
        if (!recipe)
          return recipe.takeError();
        auto emit =
            [&](StringRef suffix,
                const OracleVirtualBody &body) -> Expected<func::FuncOp> {
          OracleEmissionListener emission(work.getWork());
          OpBuilder builder(candidate.getContext(), &emission);
          std::string prefix = "_oracle_virtual_" + source.getSymName().str() +
                               "_" + suffix.str();
          std::string name = prefix;
          for (unsigned n = 0;
               lookupOracleEmissionSymbol(unit, name, work.getWork()); ++n)
            name = prefix + "_" + std::to_string(n);
          builder.setInsertionPointToEnd(&unit.getBody().front());
          auto helper = func::FuncOp::create(
              builder, source.getLoc(), name,
              builder.getFunctionType(body.block.types, body.resultType));
          helper.setPrivate();
          llvm::DenseMap<unsigned, Value> values;
          auto copy = [&](auto &&copy, const OracleVirtualBlock &plan,
                          Block &block, llvm::DenseMap<unsigned, Value> values)
              -> Expected<llvm::DenseMap<unsigned, Value>> {
            if (!work.reserveCapacity(1,
                                      plan.arguments.size() + values.size()) ||
                !work.getWork().charge(1 + plan.arguments.size() +
                                       values.size()))
              return error("oracle-virtual-function-limit");
            for (auto [id, type] : zip(plan.arguments, plan.types))
              values[id] = block.addArgument(type, source.getLoc());
            for (const auto &item : plan.instructions) {
              uint64_t cost = item.inputs.size() + item.outputs.size();
              if (!work.reserveCapacity(1, cost) ||
                  !work.getWork().charge(cost))
                return error("oracle-virtual-function-limit");
              builder.setInsertionPointToEnd(&block);
              OperationState state(item.source->getLoc(),
                                   item.source->getName());
              state.addAttributes(item.source->getAttrs());
              state.addTypes(item.source->getResultTypes());
              for (unsigned id : item.inputs)
                state.addOperands(values.lookup(id));
              for (const auto &region : item.regions) {
                reserveOracleEmission(work.getWork(), 1);
                auto *nested = new Block;
                state.addRegion()->push_back(nested);
                auto copied = copy(copy, *region, *nested, values);
                if (!copied)
                  return copied.takeError();
              }
              builder.setInsertionPointToEnd(&block);
              auto *op = builder.create(state);
              for (auto [id, value] : zip(item.outputs, op->getResults()))
                values[id] = value;
            }
            return values;
          };
          reserveOracleEmission(work.getWork(), 1);
          auto *block = new Block;
          helper.getBody().push_back(block);
          auto copied = copy(copy, body.block, *block, values);
          if (!copied)
            return copied.takeError();
          builder.setInsertionPointToEnd(block);
          func::ReturnOp::create(builder, source.getLoc(),
                                 copied->lookup(body.result));
          return helper;
        };
        OracleVirtualFunctions result;
        for (auto [i, query] : enumerate(recipe->queries)) {
          auto function = emit("position_" + std::to_string(i), query.position);
          if (!function)
            return function.takeError();
          result.queries.push_back(
              {query.source, query.site, query.kind, *function});
        }
        auto answer = emit("answer", recipe->answer);
        if (!answer)
          return answer.takeError();
        result.answer = *answer;
        if (failed(work.checkSubject(candidate)))
          return error("oracle-virtual-functions");
        work.getWork().emission->rememberVirtualFunctions(source, result);
        commitOracleEmissionSession(session);
        return result;
      });
}
} // namespace zkc::protocol
