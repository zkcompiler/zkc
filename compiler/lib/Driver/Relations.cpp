#include "Relations.h"
#include "../Support/Input.h"
#include "AIR.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Relation/Matrices.h"
#include "zkc/Source/RelationLowering.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/MLIRInput.h"
#include "zkc/Translation/Relations.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
namespace zkc::relation {
namespace {
Expected<R1CS> read(StringRef filename) {
  auto bytes = readInput(filename, Limits::bytes);
  if (!bytes)
    return bytes.takeError();
  if (StringRef(*bytes).starts_with("r1cs"))
    return readR1CS(*bytes);
  auto data = parseR1CSText(*bytes);
  if (!data)
    return data.takeError();
  return decodeR1CS(*data);
}
Expected<std::vector<std::string>> values(StringRef filename) {
  auto text = readInput(filename, Limits::bytes);
  if (!text)
    return text.takeError();
  auto parsed = parseR1CSText(*text);
  if (!parsed)
    return parsed.takeError();
  auto *array = parsed->getAsArray();
  if (!array || array->size() > Limits::columns)
    return zkc::error("relation-assignment-shape");
  std::vector<std::string> result;
  for (const auto &item : *array) {
    auto text = item.getAsString();
    if (!text)
      return zkc::error("relation-coefficient");
    result.push_back(text->str());
  }
  return result;
}
} // namespace

int runCommand(int argc, char **argv, const mlir::DialectRegistry &registry) {
  auto fail = [](Error error) {
    errs() << toString(std::move(error)) << '\n';
    return 1;
  };
  const StringRef mode(argv[1]);
  if (mode.starts_with("relation-air-"))
    return runAIRCommand(argc, argv, registry);
  bool publicMatrices =
      mode == "relation-compile-data" || mode == "relation-lower-data";
  bool compile = mode == "relation-compile" || mode == "relation-compile-data";
  bool import = mode == "relation-import";
  bool lower = mode == "relation-lower" || mode == "relation-lower-data";
  bool exportIR = mode == "relation-export";
  bool evaluateMode = mode == "relation-evaluate";
  bool inspect = mode == "relation-inspect";
  bool normalize = mode == "relation-read";
  bool matrices = mode == "relation-matrices";
  if ((!compile && !import && !lower && !exportIR && !evaluateMode &&
       !inspect && !normalize && !matrices) ||
      (evaluateMode          ? argc != 5
       : (compile || import) ? argc != 3 && argc != 4
                             : argc != 3))
    return fail(zkc::error("relation-command"));
  mlir::MLIRContext context(registry);
  std::string symbol = argc == 4 ? argv[3] : "Imported";
  auto relation = [&]() -> Expected<R1CS> {
    if (!lower && !exportIR)
      return read(argv[2]);
    auto text = readInput(argv[2], Limits::bytes);
    if (!text)
      return text.takeError();
    if (!mlirNestingWithinLimit(*text))
      return zkc::error("relation-depth-limit");
    auto module = mlir::parseSourceString<mlir::ModuleOp>(*text, &context);
    if (!module || failed(mlir::verify(*module)))
      return zkc::error("relation-ir");
    auto &operations = module->getBody()->getOperations();
    if (!llvm::hasSingleElement(operations) ||
        !isa<R1CSRelationOp>(operations.front()))
      return zkc::error("relation-module");
    auto op = cast<R1CSRelationOp>(operations.front());
    symbol = op.getSymName().str();
    return readR1CSOperation(op);
  }();
  if (!relation)
    return fail(relation.takeError());
  if (compile || lower) {
    auto source = lowerMultilinearR1CS(*relation, symbol,
                                       publicMatrices ? Staging::PublicMatrices
                                                      : Staging::Specialized);
    if (!source)
      return fail(source.takeError());
    auto text = frontend::printProtocol(source::Content{std::move(*source)});
    if (!text)
      return fail(text.takeError());
    outs() << *text;
  } else if (import) {
    auto module = importR1CS(*relation, symbol, context);
    if (!module)
      return fail(module.takeError());
    (*module)->print(outs());
    outs() << '\n';
  } else if (evaluateMode) {
    auto statement = values(argv[3]);
    if (!statement)
      return fail(statement.takeError());
    auto assignment = values(argv[4]);
    if (!assignment)
      return fail(assignment.takeError());
    auto result = evaluate(*relation, *statement, *assignment);
    if (!result)
      return fail(result.takeError());
    json::Array products;
    for (const auto &product : result->products) {
      json::Array values;
      for (const auto &value : product)
        values.push_back(value);
      products.push_back(std::move(values));
    }
    outs() << json::Value(json::Object{{"subject", relation->identity()},
                                       {"bound", result->bound},
                                       {"satisfied", result->satisfied},
                                       {"products", std::move(products)}})
           << '\n';
  } else if (matrices) {
    outs() << printJson(matrixValues(*relation)) << '\n';
  } else if (inspect) {
    outs() << json::Value(
                  json::Object{{"subject", relation->identity()},
                               {"field", relation->field()},
                               {"columns", relation->columns()},
                               {"constraints", relation->constraints().size()},
                               {"nonzeros", relation->nonzeros()},
                               {"public_outputs", relation->publicOutputs()},
                               {"public_inputs", relation->publicInputs()},
                               {"private_witness", relation->witnessCount()},
                               {"unique_constraints",
                                relation->deduplicate().constraints().size()}})
           << '\n';
  } else {
    outs() << printJson(relation->encode()) << '\n';
  }
  return 0;
}
} // namespace zkc::relation
