#include "zkc/Relation/Lowering.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Relation/Authoring.h"
#include "zkc/Target/Json.h"
#include "llvm/ADT/StringExtras.h"
#include <map>

using namespace llvm;
namespace zkc::relation {
bool isValidSymbol(StringRef name) {
  return !name.empty() && name.size() <= 64 &&
         (isAlpha(name.front()) || name.front() == '_') &&
         all_of(name, [](char c) { return isAlnum(c) || c == '_'; });
}
namespace {
uint32_t cube(uint32_t size) {
  uint32_t result = 2;
  while (result < size)
    result *= 2;
  return result;
}

class Builder {
public:
  source::Module module;
  Builder(StringRef field, StringRef prefix, StringRef subject)
      : field(field.str()), prefix(prefix.str()), subject(subject.str()) {}

  std::string type(StringRef kind) const { return (kind + ":" + field).str(); }

  void function(StringRef name, std::vector<source::Parameter> inputs,
                source::Names outputs) {
    source::Function fn;
    fn.name = prefix + "_" + name.str();
    fn.arguments = std::move(inputs);
    fn.results = std::move(outputs);
    fn.origin = source::LogicalOrigin{"Relation_" + subject, {}};
    fn.body.emplace();
    module.functions.push_back(std::move(fn));
    constants.clear();
    next = 0;
  }

  source::Names operation(StringRef contract, source::Names inputs = {},
                          source::Names attributes = {}, unsigned count = 1) {
    auto found = bindings.find(contract.str());
    if (found == bindings.end()) {
      source::OperationBinding binding;
      binding.name = prefix + "_op_" + std::to_string(bindings.size());
      binding.contract = contract.str();
      if (contract != "control.require")
        binding.arguments = {field};
      found = bindings.emplace(contract.str(), binding.name).first;
      module.bindings.push_back(std::move(binding));
    }
    source::Instruction instruction;
    instruction.site = "step_" + std::to_string(next++);
    source::Operation op;
    op.callee = found->second;
    op.inputs = std::move(inputs);
    op.attributes = std::move(attributes);
    for (unsigned i = 0; i < count; ++i)
      op.outputs.push_back("value_" + std::to_string(next++));
    auto outputs = op.outputs;
    instruction.value = std::move(op);
    module.functions.back().body->push_back(std::move(instruction));
    return outputs;
  }

  std::string op(StringRef contract, source::Names inputs = {},
                 source::Names attrs = {}) {
    return operation(contract, std::move(inputs), std::move(attrs))[0];
  }
  void require(const std::string &condition) {
    operation("control.require", {condition}, {}, 0);
  }
  void length(const std::string &value, uint32_t count) {
    require(op("vector.length_check", {value}, {std::to_string(count)}));
  }
  std::string constant(StringRef value) {
    auto found = constants.find(value.str());
    if (found == constants.end())
      found = constants
                  .emplace(value.str(), op("field.constant", {}, {value.str()}))
                  .first;
    return found->second;
  }
  void returns(source::Names outputs) {
    source::Instruction ret;
    ret.value = source::Return{std::move(outputs)};
    module.functions.back().body->push_back(std::move(ret));
  }
  std::string weights(const std::string &point, uint32_t width) {
    unsigned arity = 0;
    for (uint32_t n = width; n > 1; n /= 2)
      ++arity;
    length(op("vector.from_point", {point}), arity);
    return op("poly.equality_weights", {point});
  }

private:
  std::string field, prefix, subject;
  std::map<std::string, std::string> bindings, constants;
  size_t next = 0;
};

struct Sparse {
  source::Names rows, columns, coefficients;
};

std::array<Sparse, 3> matrices(const R1CS &relation) {
  std::array<Sparse, 3> result;
  for (auto [i, constraint] : enumerate(relation.constraints()))
    for (unsigned k = 0; k < 3; ++k)
      for (const auto &term : constraint[k]) {
        result[k].rows.push_back(std::to_string(i));
        result[k].columns.push_back(std::to_string(term.column));
        result[k].coefficients.push_back(term.coefficient);
      }
  return result;
}

std::string product(Builder &b, const Sparse &matrix, const std::string &input,
                    uint32_t length, bool transpose) {
  auto values =
      b.op("vector.gather", {input}, transpose ? matrix.rows : matrix.columns);
  auto coefficients = b.op("vector.constant", {}, matrix.coefficients);
  auto terms = b.op("vector.mul", {values, coefficients});
  auto destination = transpose ? matrix.columns : matrix.rows;
  destination.insert(destination.begin(), std::to_string(length));
  return b.op("vector.scatter_sum", {terms}, std::move(destination));
}
} // namespace

json::Value matrixValues(const R1CS &relation, bool padded) {
  json::Array matrices;
  for (unsigned k = 0; k < 3; ++k) {
    json::Array entries;
    for (auto [row, constraint] : enumerate(relation.constraints()))
      for (const auto &term : constraint[k])
        entries.push_back(json::Array{std::to_string(row),
                                      std::to_string(term.column),
                                      term.coefficient});
    matrices.push_back(json::Array{
        std::to_string(padded ? cube(relation.constraints().size())
                              : relation.constraints().size()),
        std::to_string(padded ? cube(relation.columns()) : relation.columns()),
        std::move(entries)});
  }
  return matrices;
}

Expected<source::Module>
lowerMultilinearR1CS(const R1CS &relation, StringRef prefix, Staging staging) {
  if (!isValidSymbol(prefix))
    return zkc::error("relation-symbol");
  // This first consumer authenticates public coordinates individually. The
  // relation model itself does not impose this proof-cost policy.
  if (relation.publicCount() > 128)
    return zkc::error("relation-public-opening-limit");
  const uint32_t rows = cube(relation.constraints().size());
  const uint32_t columns = cube(relation.columns());
  const bool publicMatrices = staging == Staging::PublicMatrices;
  // Scatter carries one dimension attribute in addition to its destinations.
  // zkc_runtime::interactive::Limits::OPERATION_ATTRIBUTES is 16384 inclusive;
  // one slot is the dimension, leaving at most 16383 destinations.
  // Keep specialization within the native per-operation attribute ceiling;
  // coefficients beyond it belong in the immutable matrix input path.
  if (!publicMatrices) {
    std::array<size_t, 3> counts{};
    for (const auto &row : relation.constraints())
      for (unsigned k = 0; k < 3; ++k) {
        counts[k] += row[k].size();
        if (counts[k] >= 16384)
          return zkc::error("relation-specialization-attributes");
      }
  }
  auto data = publicMatrices ? std::array<Sparse, 3>{} : matrices(relation);
  Builder b(relation.field(), prefix, relation.identity());
  auto vector = b.type("vector"), field = b.type("field"),
       point = b.type("point"), table = b.type("table");
  auto matrixArguments = [&](std::vector<source::Parameter> args) {
    if (publicMatrices)
      args.insert(args.begin(), {{"a", b.type("matrix")},
                                 {"b", b.type("matrix")},
                                 {"c", b.type("matrix")}});
    return args;
  };
  const std::array<std::string, 3> matrixNames{"a", "b", "c"};
  auto checkShapes = [&]() {
    if (publicMatrices)
      for (auto [k, name] : enumerate(matrixNames)) {
        b.require(b.op("matrix.identity_check", {name},
                       {matrixIdentity(relation, k)}));
        b.require(b.op("matrix.shape_check", {name},
                       {std::to_string(rows), std::to_string(columns)}));
      }
  };

  b.function("Assemble", {{"statement", vector}, {"witness", vector}},
             {vector});
  b.length("statement", relation.publicCount());
  b.length("witness", relation.witnessCount());
  auto one = b.op("vector.constant", {}, {"1"});
  auto publicPrefix = b.op("vector.concat", {one, "statement"});
  b.returns({b.op("vector.concat", {publicPrefix, "witness"})});

  b.function("Products", matrixArguments({{"assignment", vector}}),
             {vector, vector, vector, table});
  checkShapes();
  b.length("assignment", relation.columns());
  std::string padded = "assignment";
  if (columns > relation.columns()) {
    auto zeros = b.op("vector.splat", {b.constant("0")},
                      {std::to_string(columns - relation.columns())});
    padded = b.op("vector.concat", {padded, zeros});
  }
  source::Names products;
  for (unsigned k = 0; k < 3; ++k)
    products.push_back(publicMatrices
                           ? b.op("matrix.mul_vector", {matrixNames[k], padded})
                           : product(b, data[k], "assignment", rows, false));
  products.push_back(b.op("vector.to_table", {padded}));
  b.returns(std::move(products));

  b.function(
      "Contract",
      matrixArguments(
          {{"r", point}, {"alpha", field}, {"beta", field}, {"gamma", field}}),
      {table});
  checkShapes();
  auto rowWeights = b.weights("r", rows);
  source::Names pieces;
  for (unsigned k = 0; k < 3; ++k) {
    auto columnsVector =
        publicMatrices
            ? b.op("matrix.transpose_mul_vector", {matrixNames[k], rowWeights})
            : product(b, data[k], rowWeights, columns, true);
    pieces.push_back(b.op("vector.scale",
                          {columnsVector, std::array<std::string, 3>{
                                              "alpha", "beta", "gamma"}[k]}));
  }
  auto sum = b.op("vector.add", {pieces[0], pieces[1]});
  sum = b.op("vector.add", {sum, pieces[2]});
  b.returns({b.op("vector.to_table", {sum})});

  b.function("Evaluate", matrixArguments({{"r", point}, {"s", point}}),
             {field, field, field});
  checkShapes();
  rowWeights = b.weights("r", rows);
  auto columnWeights = b.weights("s", columns);
  source::Names evaluations;
  for (unsigned k = 0; k < 3; ++k) {
    if (publicMatrices) {
      evaluations.push_back(
          b.op("matrix.bilinear", {matrixNames[k], rowWeights, columnWeights}));
      continue;
    }
    auto rowEntries = b.op("vector.gather", {rowWeights}, data[k].rows);
    auto columnEntries =
        b.op("vector.gather", {columnWeights}, data[k].columns);
    auto coefficients = b.op("vector.constant", {}, data[k].coefficients);
    auto terms = b.op("vector.mul", {rowEntries, coefficients});
    evaluations.push_back(b.op("vector.dot", {terms, columnEntries}));
  }
  b.returns(std::move(evaluations));

  for (uint32_t coordinate = 0; coordinate <= relation.publicCount();
       ++coordinate) {
    b.function("BindingPoint" + std::to_string(coordinate), {}, {point});
    source::Names bits;
    for (uint32_t bit = columns / 2; bit; bit /= 2)
      bits.push_back(coordinate & bit ? "1" : "0");
    auto coordinates = b.op("vector.constant", {}, std::move(bits));
    b.returns({b.op("vector.to_point", {coordinates})});
    std::vector<source::Parameter> args{{"value", field}};
    if (coordinate)
      args.push_back({"statement", vector});
    b.function("CheckBinding" + std::to_string(coordinate), std::move(args),
               {});
    std::string expected;
    if (coordinate) {
      b.length("statement", relation.publicCount());
      expected =
          b.op("vector.at", {"statement"}, {std::to_string(coordinate - 1)});
    } else {
      expected = b.constant("1");
    }
    b.require(b.op("field.equal", {"value", expected}));
    b.returns({});
  }
  if (auto failure = protocol::admit(source::Content{b.module}, false))
    return std::move(failure);
  return std::move(b.module);
}
Expected<source::Module> lowerRankOneR1CS(const R1CS &relation,
                                          StringRef prefix, Staging staging) {
  if (!isValidSymbol(prefix))
    return zkc::error("relation-symbol");
  bool dataStaging = staging == Staging::PublicMatrices;
  auto data = dataStaging ? std::array<Sparse, 3>{} : matrices(relation);
  if (!dataStaging)
    for (const auto &m : data)
      if (m.rows.size() >= 16384)
        return zkc::error("relation-specialization-attributes");
  Builder b(relation.field(), prefix, relation.identity());
  auto vector = b.type("vector");
  b.function("Assemble", {{"statement", vector}, {"witness", vector}},
             {vector});
  b.length("statement", relation.publicCount());
  b.length("witness", relation.witnessCount());
  auto one = b.op("vector.constant", {}, {"1"});
  auto head = b.op("vector.concat", {one, "statement"});
  b.returns({b.op("vector.concat", {head, "witness"})});
  std::vector<source::Parameter> args;
  if (dataStaging)
    args = {{"a", b.type("matrix")},
            {"b", b.type("matrix")},
            {"c", b.type("matrix")}};
  args.push_back({"assignment", vector});
  b.function("Products", std::move(args), {vector, vector, vector});
  b.length("assignment", relation.columns());
  source::Names products;
  const std::array<std::string, 3> names{"a", "b", "c"};
  for (unsigned k = 0; k < 3; ++k) {
    if (dataStaging) {
      b.require(b.op("matrix.identity_check", {names[k]},
                     {matrixIdentity(relation, k, false)}));
      b.require(b.op("matrix.shape_check", {names[k]},
                     {std::to_string(relation.constraints().size()),
                      std::to_string(relation.columns())}));
    }
    products.push_back(dataStaging
                           ? b.op("matrix.mul_vector", {names[k], "assignment"})
                           : product(b, data[k], "assignment",
                                     relation.constraints().size(), false));
  }
  b.returns(std::move(products));
  b.function("Residuals", {{"az", vector}, {"bz", vector}, {"cz", vector}},
             {vector});
  for (const auto &name : {"az", "bz", "cz"})
    b.length(name, relation.constraints().size());
  auto multiplied = b.op("vector.mul", {"az", "bz"});
  b.returns({b.op("vector.sub", {multiplied, "cz"})});
  if (auto e = protocol::admit(b.module, false))
    return std::move(e);
  return std::move(b.module);
}

Expected<source::Module> lowerAIRArithmetic(const AIR &relation,
                                            StringRef prefix, uint32_t height) {
  if (!isValidSymbol(prefix))
    return zkc::error("relation-symbol");
  auto plan = relation.compile(height);
  if (!plan)
    return plan.takeError();
  // This view consumes a dense vector; the sparse schedule's read-cell bound
  // does not bound its complete row-major input. Widen before multiplication.
  const uint64_t cells = uint64_t(height) * relation.columns();
  if (cells > AIRLimits::cells)
    return zkc::error("air-cell-limit");
  uint64_t work = 0;
  for (const auto &invocation : plan->invocations()) {
    work += relation.constraints()[invocation.constraint].expression.size() + 1;
    if (work > 8192)
      return zkc::error("relation-generation-limit");
  }
  source::RelationDeclaration declaration;
  declaration.value = std::make_shared<const AIR>(relation);
  Builder b(relation.field(), prefix, identity(declaration));
  auto vector = b.type("vector");
  b.function("Evaluate", {{"statement", vector}, {"trace", vector}}, {vector});
  b.length("statement", relation.publicInputs());
  b.length("trace", static_cast<uint32_t>(cells));
  auto residuals = b.op("vector.empty");
  for (const auto &invocation : plan->invocations()) {
    source::Names values;
    for (const auto &node :
         relation.constraints()[invocation.constraint].expression) {
      switch (node.kind) {
      case AIRKind::Constant:
        values.push_back(b.constant(node.value));
        break;
      case AIRKind::Public:
        values.push_back(
            b.op("vector.at", {"statement"}, {std::to_string(node.index)}));
        break;
      case AIRKind::Read:
        values.push_back(b.op("vector.at", {"trace"},
                              {std::to_string((invocation.row + node.offset) *
                                                  relation.columns() +
                                              node.column)}));
        break;
      case AIRKind::Add:
        values.push_back(
            b.op("field.add", {values[node.lhs], values[node.rhs]}));
        break;
      case AIRKind::Mul:
        values.push_back(
            b.op("field.mul", {values[node.lhs], values[node.rhs]}));
        break;
      case AIRKind::Neg:
        values.push_back(b.op("field.neg", {values[node.lhs]}));
        break;
      }
    }
    residuals = b.op("vector.append", {residuals, values.back()});
  }
  b.returns({residuals});
  if (auto e = protocol::admit(b.module, false))
    return std::move(e);
  return std::move(b.module);
}
} // namespace zkc::relation
