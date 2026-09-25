#include "AIR.h"
#include "../Support/Input.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Relation/AIRPolynomial.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/MLIRInput.h"
#include "zkc/Translation/Relations.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
namespace zkc::relation {
namespace {
Expected<json::Value> readJSON(StringRef path) {
  auto text = readInput(path, AIRLimits::bytes);
  if (!text)
    return text.takeError();
  return readAIRJson(*text);
}
Expected<AIR> read(StringRef path, mlir::MLIRContext &context, bool ir) {
  auto text = readInput(path, AIRLimits::bytes);
  if (!text)
    return text.takeError();
  if (!ir)
    return readAIRText(*text);
  if (!mlirNestingWithinLimit(*text))
    return zkc::error("air-ir-depth-limit");
  auto module = mlir::parseSourceString<mlir::ModuleOp>(*text, &context);
  if (!module || failed(mlir::verify(*module)))
    return zkc::error("air-ir");
  auto &ops = module->getBody()->getOperations();
  if (!hasSingleElement(ops) || !isa<AIRRelationOp>(ops.front()))
    return zkc::error("air-ir-module");
  return readAIROperation(&ops.front());
}
} // namespace

int runAIRCommand(int argc, char **argv,
                  const mlir::DialectRegistry &registry) {
  auto fail = [](Error error) {
    errs() << toString(std::move(error)) << '\n';
    return 1;
  };
  StringRef mode(argv[1]);
  bool import = mode == "relation-air-import",
       exportIR = mode == "relation-air-export",
       inspect = mode == "relation-air-inspect",
       plan = mode == "relation-air-plan",
       polynomial = mode == "relation-air-polynomial",
       evaluate = mode == "relation-air-evaluate",
       normalize = mode == "relation-air-read";
  if ((!import && !exportIR && !inspect && !plan && !polynomial && !evaluate &&
       !normalize) ||
      (evaluate     ? argc != 5
       : polynomial ? argc != 6
       : plan       ? argc != 4
       : import     ? argc != 3 && argc != 4
                    : argc != 3))
    return fail(zkc::error("air-command"));
  mlir::MLIRContext context(registry);
  auto relation = read(argv[2], context, exportIR);
  if (!relation)
    return fail(relation.takeError());
  if (import) {
    auto module = importAIR(*relation, argc == 4 ? argv[3] : "Trace", context);
    if (!module)
      return fail(module.takeError());
    (*module)->print(outs());
    outs() << '\n';
  } else if (inspect) {
    outs() << relation->analysis() << '\n';
  } else if (polynomial) {
    AIRPolynomialParameters parameters;
    uint32_t *destinations[] = {&parameters.height, &parameters.domainSize,
                                &parameters.traceDegree};
    for (unsigned i = 0; i < 3; ++i) {
      StringRef text(argv[3 + i]);
      if (text.empty() || (text.size() > 1 && text.front() == '0') ||
          !all_of(text, [](char c) { return c >= '0' && c <= '9'; }) ||
          text.getAsInteger(10, *destinations[i]))
        return fail(zkc::error("air-polynomial-parameter"));
    }
    auto analysis = analyzeAIRPolynomials(*relation, parameters);
    if (!analysis)
      return fail(analysis.takeError());
    outs() << analysis->encode() << '\n';
  } else if (plan) {
    StringRef text(argv[3]);
    uint32_t height = 0;
    if (text.empty() || (text.size() > 1 && text.front() == '0') ||
        !all_of(text, [](char c) { return c >= '0' && c <= '9'; }) ||
        text.getAsInteger(10, height))
      return fail(zkc::error("air-height"));
    auto schedule = relation->compile(height);
    if (!schedule)
      return fail(schedule.takeError());
    outs() << schedule->encode() << '\n';
  } else if (evaluate) {
    auto traceJSON = readJSON(argv[3]);
    if (!traceJSON)
      return fail(traceJSON.takeError());
    auto trace = readAIRTrace(*traceJSON);
    if (!trace)
      return fail(trace.takeError());
    auto statementJSON = readJSON(argv[4]);
    if (!statementJSON)
      return fail(statementJSON.takeError());
    auto *array = statementJSON->getAsArray();
    if (!array || array->size() != relation->publicInputs())
      return fail(zkc::error("air-public-shape"));
    std::vector<std::string> statement;
    for (const auto &item : *array) {
      auto value = item.getAsString();
      if (!value)
        return fail(zkc::error("relation-coefficient"));
      statement.push_back(value->str());
    }
    auto result = relation->evaluate(*trace, statement);
    if (!result)
      return fail(result.takeError());
    outs() << result->encode() << '\n';
  } else {
    outs() << relation->encode() << '\n';
  }
  return 0;
}
} // namespace zkc::relation
