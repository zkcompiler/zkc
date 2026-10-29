#include "zkc/Compiler/OracleObligations.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringSwitch.h"
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
  Error block(const J &value, Path path, unsigned depth, unsigned sources = 0,
              unsigned inputs = 0, A *queries = nullptr) {
    if (!depth)
      return error("oracle-obligations-limit");
    auto body = value.getAsArray();
    if (!body || body->size() != 3 || (*body)[0] != J("block") ||
        !(*body)[1].getAsArray())
      return error("oracle-obligations-source");
    std::vector<std::optional<unsigned>> parameters;
    for (unsigned i = 0; i < inputs; ++i)
      parameters.push_back(i);
    auto &instructions = *(*body)[1].getAsArray();
    for (unsigned i = 0; i < instructions.size(); ++i) {
      auto instruction = instructions[i].getAsArray();
      if (!instruction || instruction->size() != 5)
        return error("oracle-obligations-source");
      auto descriptor = (*instruction)[0].getAsArray();
      auto operands = (*instruction)[1].getAsArray();
      auto results = (*instruction)[2].getAsArray();
      auto regions = (*instruction)[3].getAsArray();
      if (!descriptor || descriptor->empty() ||
          !(*descriptor)[0].getAsString() || !operands || !results || !regions)
        return error("oracle-obligations-source");
      Path row = path;
      row.append({1, i});
      if (auto e = charge(1 + operands->size() + results->size() + row.size()))
        return e;
      auto tag = *(*descriptor)[0].getAsString();
      auto purpose = StringSwitch<StringRef>(tag)
                         .Case("oracle_input", "input_pair")
                         .Case("oracle_send", "send_shape")
                         .Case("oracle_virtual", "virtual_admissibility")
                         .Case("oracle_query", "query_domain")
                         .Default("");
      if (!purpose.empty())
        conditions.push_back(A{purpose, address(row)});
      if (queries && tag == "oracle_query") {
        if (descriptor->size() != 3 || (*descriptor)[1] != J(nullptr) ||
            operands->size() != 2 || !(*operands)[0].getAsUINT64() ||
            !(*operands)[1].getAsUINT64())
          return error("oracle-obligations-source");
        uint64_t handle = *(*operands)[0].getAsUINT64();
        uint64_t position = *(*operands)[1].getAsUINT64();
        if (handle >= parameters.size() || position >= parameters.size() ||
            !parameters[handle] || *parameters[handle] >= sources)
          return error("oracle-obligations-source");
        queries->push_back(A{address(row), *parameters[handle], position});
      }
      if (queries && !regions->empty())
        return error("oracle-obligations-source");
      for (unsigned r = 0; r < regions->size(); ++r) {
        auto region = (*regions)[r].getAsArray();
        if (!region || region->size() != 3)
          return error("oracle-obligations-source");
        Path nested = row;
        nested.append({3, r, 2});
        if (auto e = block((*region)[2], std::move(nested), depth - 1))
          return e;
      }
      if (queries)
        parameters.insert(parameters.begin(), results->size(), std::nullopt);
    }
    return Error::success();
  }
  Expected<J> run(const J &value) {
    auto snapshot = value.getAsArray();
    if (!snapshot || snapshot->size() != 11 ||
        (*snapshot)[0] != J("zkc.structured-source/0") ||
        (*snapshot)[1] != J("original") || !(*snapshot)[2].getAsString() ||
        !(*snapshot)[3].getAsString() || !(*snapshot)[7].getAsArray())
      return error("oracle-obligations-source");
    auto &definitions = *(*snapshot)[7].getAsArray();
    for (unsigned i = 0; i < definitions.size(); ++i) {
      auto definition = definitions[i].getAsArray();
      if (!definition || definition->empty() || !(*definition)[0].getAsString())
        return error("oracle-obligations-source");
      auto tag = *(*definition)[0].getAsString();
      if (tag == "function") {
        if (definition->size() != 10)
          return error("oracle-obligations-source");
        if (auto e = block((*definition)[9], {7, i, 9}, 64))
          return std::move(e);
      } else if (tag == "oracle") {
        if (definition->size() != 8 || !(*definition)[2].getAsArray())
          return error("oracle-obligations-source");
        auto &inputs = *(*definition)[2].getAsArray();
        unsigned sources = 0;
        for (const auto &type : inputs) {
          auto fields = type.getAsArray();
          if (!fields || fields->size() != 2 || (*fields)[0] != J("oracle"))
            break;
          ++sources;
        }
        A queries;
        if (auto e = block((*definition)[7], {7, i, 7}, 64, sources,
                           inputs.size(), &queries))
          return std::move(e);
        footprints.push_back(A{i, sources, std::move(queries)});
      }
    }
    return J(A{"zkc.oracle-obligations/0", (*snapshot)[2], (*snapshot)[3],
               std::move(conditions), std::move(footprints)});
  }
};
} // namespace
Expected<std::string> exportOracleObligations(StringRef original,
                                              StringRef symbol,
                                              mlir::MLIRContext &context) {
  auto source = exportStructuredSource(original, symbol, context);
  if (!source)
    return source.takeError();
  auto snapshot = json::parse(source->bytes);
  if (!snapshot)
    return snapshot.takeError();
  auto report = Deriver().run(*snapshot);
  if (!report)
    return report.takeError();
  auto bytes = printJson(*report) + '\n';
  if (bytes.size() > 1024 * 1024)
    return error("oracle-obligations-limit");
  return bytes;
}
Error checkOracleObligations(StringRef original, StringRef symbol,
                             StringRef proposal, mlir::MLIRContext &context) {
  auto expected = exportOracleObligations(original, symbol, context);
  if (!expected)
    return expected.takeError();
  auto actual =
      parseNaturalJson(proposal, 1024 * 1024, 16, "oracle-obligations-shape",
                       "oracle-obligations-limit");
  if (!actual)
    return actual.takeError();
  auto canonical = json::parse(*expected);
  if (!canonical)
    return canonical.takeError();
  if (!zkc::equalNaturalJson(*actual, *canonical))
    return error("oracle-obligations-mismatch");
  return Error::success();
}
} // namespace zkc::protocol
