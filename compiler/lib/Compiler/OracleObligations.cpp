#include "zkc/Compiler/OracleObligations.h"
#include "SourceView.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/TypeSwitch.h"
#include <optional>
using namespace llvm;
namespace zkc::protocol {
namespace {
using J = json::Value;
using A = json::Array;
using Path = SmallVector<unsigned>;
A address(ArrayRef<unsigned> path) {
  A result;
  for (unsigned index : path)
    result.push_back(index);
  return result;
}
struct Deriver {
  A conditions, footprints;
  unsigned remaining = 100000;
  Error charge(uint64_t amount) {
    if (amount > remaining)
      return error("oracle-obligations-limit");
    remaining -= amount;
    return Error::success();
  }
  Error block(const SourceBlock &body, Path path, unsigned depth,
              unsigned sources = 0, unsigned inputs = 0, A *queries = nullptr) {
    if (!depth)
      return error("oracle-obligations-limit");
    std::vector<std::optional<unsigned>> parameters;
    for (unsigned i = 0; i < inputs; ++i)
      parameters.push_back(i);
    for (unsigned i = 0; i < body.instructions.size(); ++i) {
      const auto &instruction = body.instructions[i];
      auto *op = instruction.operation;
      Path row = path;
      row.append({1, i});
      if (auto e = charge(1 + instruction.operands.size() +
                          instruction.results.size() + row.size()))
        return e;
      auto purpose = llvm::TypeSwitch<mlir::Operation *, StringRef>(op)
                         .Case<protocol_ir::OracleInputOp>(
                             [](auto) { return "input_pair"; })
                         .Case<protocol_ir::OracleSendOp>(
                             [](auto) { return "send_shape"; })
                         .Case<protocol_ir::OracleVirtualOp>(
                             [](auto) { return "virtual_admissibility"; })
                         .Case<protocol_ir::OracleQueryOp>(
                             [](auto) { return "query_domain"; })
                         .Default(StringRef());
      if (!purpose.empty())
        conditions.push_back(A{purpose, address(row)});
      if (queries && mlir::isa<protocol_ir::OracleQueryOp>(op)) {
        if (op->hasAttr("owner") || instruction.operands.size() != 2)
          return error("oracle-obligations-source");
        unsigned handle = instruction.operands[0];
        unsigned position = instruction.operands[1];
        if (handle >= parameters.size() || position >= parameters.size() ||
            !parameters[handle] || *parameters[handle] >= sources)
          return error("oracle-obligations-source");
        queries->push_back(A{address(row), *parameters[handle], position});
      }
      if (queries && !instruction.regions.empty())
        return error("oracle-obligations-source");
      for (unsigned r = 0; r < instruction.regions.size(); ++r) {
        Path nested = row;
        nested.append({3, r, 2});
        if (auto e =
                block(instruction.regions[r], std::move(nested), depth - 1))
          return e;
      }
      if (queries)
        parameters.insert(parameters.begin(), instruction.results.size(),
                          std::nullopt);
    }
    return Error::success();
  }
  Expected<J> run(const SourceView &source) {
    for (unsigned i = 0; i < source.definitions.size(); ++i) {
      const auto &definition = source.definitions[i];
      if (!definition.hasBody)
        continue;
      if (definition.kind != "oracle") {
        if (auto e = block(definition.body, {7, i, 9}, 64))
          return std::move(e);
      } else {
        unsigned sources = 0;
        for (mlir::Type type : definition.body.inputs) {
          if (!mlir::isa<protocol_ir::OracleHandleType>(type))
            break;
          ++sources;
        }
        A queries;
        if (auto e = block(definition.body, {7, i, 7}, 64, sources,
                           definition.body.inputs.size(), &queries))
          return std::move(e);
        footprints.push_back(A{i, sources, std::move(queries)});
      }
    }
    J result = A{"zkc.oracle-obligations/0", source.identity, source.entry,
                 std::move(conditions), std::move(footprints)};
    if (!jsonWithinByteLimit(result, 1024 * 1024 - 1))
      return error("oracle-obligations-limit");
    return result;
  }
};
} // namespace
Expected<std::string> exportOracleObligations(StringRef original,
                                              StringRef symbol,
                                              mlir::MLIRContext &context) {
  auto source = readSourceView(original, symbol, context);
  if (!source)
    return source.takeError();
  auto report = Deriver().run(*source);
  if (!report)
    return report.takeError();
  return printJson(*report) + '\n';
}
Error checkOracleObligations(StringRef original, StringRef symbol,
                             StringRef proposal, mlir::MLIRContext &context) {
  auto source = readSourceView(original, symbol, context);
  if (!source)
    return source.takeError();
  auto expected = Deriver().run(*source);
  if (!expected)
    return expected.takeError();
  auto actual =
      parseNaturalJson(proposal, 1024 * 1024, 16, "oracle-obligations-shape",
                       "oracle-obligations-limit");
  if (!actual)
    return actual.takeError();
  if (!zkc::equalNaturalJson(*actual, *expected))
    return error("oracle-obligations-mismatch");
  return Error::success();
}
} // namespace zkc::protocol
