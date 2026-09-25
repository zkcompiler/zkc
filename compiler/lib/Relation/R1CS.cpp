#include "zkc/Relation/R1CS.h"
#include "Field.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <map>
#include <set>

using namespace llvm;
namespace zkc::relation {
namespace {
json::Value encodeRow(const Constraint &row) {
  json::Array forms;
  for (const auto &form : row) {
    json::Array entries;
    for (const auto &term : form)
      entries.push_back(
          json::Array{std::to_string(term.column), term.coefficient});
    forms.push_back(std::move(entries));
  }
  return forms;
}

Expected<uint32_t> count(const json::Value &value, uint32_t maximum) {
  auto text = value.getAsString();
  uint32_t result = 0;
  if (!text || text->empty() || (text->size() > 1 && text->front() == '0') ||
      !all_of(*text, [](char c) { return c >= '0' && c <= '9'; }) ||
      text->getAsInteger(10, result) || result > maximum)
    return zkc::error("relation-dimension");
  return result;
}
} // namespace

R1CS::R1CS(std::string field, uint32_t columns, uint32_t publicOutputs,
           uint32_t publicInputs, std::vector<Constraint> constraints)
    : fieldName(std::move(field)), columnCount(columns),
      outputCount(publicOutputs), inputCount(publicInputs),
      rows(std::move(constraints)) {}

Expected<R1CS> R1CS::create(std::string field, uint32_t columns,
                            uint32_t publicOutputs, uint32_t publicInputs,
                            std::vector<Constraint> constraints) {
  StringRef modulus = Field::primeModulus(field);
  if (modulus.empty())
    return zkc::error("relation-field");
  if (!columns || columns > Limits::columns ||
      uint64_t(publicOutputs) + publicInputs >= columns ||
      constraints.size() > Limits::rows)
    return zkc::error("relation-dimension");
  Field arithmetic(modulus);
  size_t terms = 0;
  for (auto &row : constraints)
    for (auto &form : row) {
      if (form.size() > Limits::terms - terms)
        return zkc::error("relation-term-limit");
      terms += form.size();
      std::map<uint32_t, APInt> normalized;
      for (const auto &term : form) {
        if (term.column >= columns)
          return zkc::error("relation-column");
        auto coefficient = arithmetic.parse(term.coefficient);
        if (!coefficient)
          return coefficient.takeError();
        auto result = normalized.emplace(term.column, *coefficient);
        if (!result.second)
          result.first->second =
              arithmetic.add(result.first->second, *coefficient);
      }
      form.clear();
      for (const auto &entry : normalized)
        if (!entry.second.isZero())
          form.push_back({entry.first, Field::print(entry.second)});
    }
  return R1CS(std::move(field), columns, publicOutputs, publicInputs,
              std::move(constraints));
}

size_t R1CS::nonzeros() const {
  size_t result = 0;
  for (const auto &row : rows)
    for (const auto &form : row)
      result += form.size();
  return result;
}

json::Value R1CS::encode() const {
  json::Array constraints;
  for (const auto &row : rows)
    constraints.push_back(encodeRow(row));
  return json::Array{"zkc.relation.r1cs/1",       fieldName,
                     std::to_string(columnCount), std::to_string(outputCount),
                     std::to_string(inputCount),  std::move(constraints)};
}

std::string R1CS::identity() const {
  SHA256 hash;
  hash.update("zkc.relation-subject/1\n");
  hash.update(printJson(encode()));
  return toHex(hash.final(), true);
}

R1CS R1CS::deduplicate() const {
  std::set<std::string> seen;
  std::vector<Constraint> unique;
  for (const auto &row : rows)
    if (seen.insert(printJson(encodeRow(row))).second)
      unique.push_back(row);
  return R1CS(fieldName, columnCount, outputCount, inputCount,
              std::move(unique));
}

Expected<R1CS> decodeR1CS(const json::Value &value) {
  const auto *record = value.getAsArray();
  if (!record || record->size() != 6 ||
      (*record)[0].getAsString() != "zkc.relation.r1cs/1" ||
      !(*record)[1].getAsString())
    return zkc::error("relation-format");
  auto columns = count((*record)[2], Limits::columns);
  if (!columns)
    return columns.takeError();
  auto outputs = count((*record)[3], Limits::columns);
  if (!outputs)
    return outputs.takeError();
  auto inputs = count((*record)[4], Limits::columns);
  if (!inputs)
    return inputs.takeError();
  const auto *rows = (*record)[5].getAsArray();
  if (!rows || rows->size() > Limits::rows)
    return zkc::error("relation-dimension");
  std::vector<Constraint> constraints;
  size_t terms = 0;
  for (const auto &row : *rows) {
    const auto *forms = row.getAsArray();
    if (!forms || forms->size() != 3)
      return zkc::error("relation-row");
    Constraint constraint;
    for (unsigned k = 0; k < 3; ++k) {
      const auto *entries = (*forms)[k].getAsArray();
      if (!entries || entries->size() > Limits::terms - terms)
        return zkc::error("relation-term-limit");
      terms += entries->size();
      for (const auto &entry : *entries) {
        const auto *pair = entry.getAsArray();
        if (!pair || pair->size() != 2 || !(*pair)[1].getAsString())
          return zkc::error("relation-term");
        auto column = count((*pair)[0], Limits::columns);
        if (!column)
          return column.takeError();
        constraint[k].push_back({*column, (*pair)[1].getAsString()->str()});
      }
    }
    constraints.push_back(std::move(constraint));
  }
  auto result = R1CS::create((*record)[1].getAsString()->str(), *columns,
                             *outputs, *inputs, std::move(constraints));
  if (!result)
    return result.takeError();
  if (result->encode() != value)
    return zkc::error("relation-noncanonical");
  return result;
}

Expected<Evaluation> evaluate(const R1CS &relation,
                              ArrayRef<std::string> statement,
                              ArrayRef<std::string> assignment) {
  if (statement.size() != relation.publicCount() ||
      assignment.size() != relation.columns())
    return zkc::error("relation-assignment-shape");
  Field field(Field::primeModulus(relation.field()));
  std::vector<APInt> values;
  for (const auto &text : assignment) {
    auto value = field.parse(text);
    if (!value)
      return value.takeError();
    values.push_back(std::move(*value));
  }
  Evaluation result;
  result.bound = values[0] == field.one();
  for (size_t i = 0; i < statement.size(); ++i) {
    auto value = field.parse(statement[i]);
    if (!value)
      return value.takeError();
    result.bound &= *value == values[i + 1];
  }
  result.satisfied = result.bound;
  for (const auto &row : relation.constraints()) {
    std::array<APInt, 3> products{field.zero(), field.zero(), field.zero()};
    for (unsigned k = 0; k < 3; ++k) {
      for (const auto &term : row[k]) {
        auto coefficient = field.parse(term.coefficient);
        if (!coefficient)
          return coefficient.takeError();
        products[k] = field.add(products[k],
                                field.mul(*coefficient, values[term.column]));
      }
      result.products[k].push_back(Field::print(products[k]));
    }
    result.satisfied &= field.mul(products[0], products[1]) == products[2];
  }
  return result;
}
} // namespace zkc::relation
