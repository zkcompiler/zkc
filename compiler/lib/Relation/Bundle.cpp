#include "BundleInternal.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <algorithm>
#include <numeric>
#include <set>

using namespace llvm;
namespace zkc::relation {
namespace bundle {

bool validName(StringRef name) {
  return !name.empty() && name.size() <= BundleLimits::name &&
         llvm::all_of(name, [](char c) {
           return static_cast<unsigned char>(c) >= 0x20 && c != 0x7f;
         });
}
bool installedField(StringRef field) {
  return protocol::installedDomains().hasFact("Field", {field.str()});
}
bool primeField(StringRef field) {
  return protocol::installedDomains().hasFact("PrimeField", {field.str()});
}
const json::Array *row(const json::Value &value, size_t arity, StringRef tag) {
  auto *array = value.getAsArray();
  if (!array || array->size() != arity)
    return nullptr;
  if (!tag.empty() && (*array)[0].getAsString() != tag)
    return nullptr;
  return array;
}
std::optional<uint64_t> natural(const json::Value &value, uint64_t limit) {
  auto number = value.getAsUINT64();
  if (!number || *number > limit)
    return std::nullopt;
  return number;
}
std::optional<int32_t> signedOffset(const json::Value &value) {
  auto text = value.getAsString();
  if (!text || text->empty() || text->size() > 7)
    return std::nullopt;
  StringRef digits = *text;
  bool negative = digits.consume_front("-");
  if (digits.empty() ||
      (digits.front() == '0' && (digits.size() > 1 || negative)) ||
      !llvm::all_of(digits, isDigit))
    return std::nullopt;
  uint32_t magnitude = 0;
  if (digits.getAsInteger(10, magnitude) || magnitude > BundleLimits::offset)
    return std::nullopt;
  return negative ? -int32_t(magnitude) : int32_t(magnitude);
}
std::string printOffset(int32_t offset) { return std::to_string(offset); }
std::optional<std::string> string(const json::Value &value) {
  auto text = value.getAsString();
  if (!text)
    return std::nullopt;
  return text->str();
}

Error checkScope(const BundleScope &scope) {
  switch (scope.kind) {
  case BundleScopeKind::All:
  case BundleScopeKind::First:
  case BundleScopeKind::Last:
    if (scope.first || scope.second)
      return zkc::error("bundle-scope");
    return Error::success();
  case BundleScopeKind::Interior:
  case BundleScopeKind::Interval:
    if (scope.first > BundleLimits::height ||
        scope.second > BundleLimits::height ||
        (scope.kind == BundleScopeKind::Interval && scope.first > scope.second))
      return zkc::error("bundle-scope");
    return Error::success();
  }
  return zkc::error("bundle-scope");
}
json::Value encodeScope(const BundleScope &scope) {
  switch (scope.kind) {
  case BundleScopeKind::All:
    return json::Array{"all"};
  case BundleScopeKind::First:
    return json::Array{"first"};
  case BundleScopeKind::Last:
    return json::Array{"last"};
  case BundleScopeKind::Interior:
    return json::Array{"interior", scope.first, scope.second};
  case BundleScopeKind::Interval:
    return json::Array{"interval", scope.first, scope.second};
  }
  llvm_unreachable("admitted bundle scope");
}
Expected<BundleScope> readScope(const json::Value &value) {
  auto *array = value.getAsArray();
  auto tag =
      array && !array->empty() ? (*array)[0].getAsString() : std::nullopt;
  if (!tag)
    return zkc::error("bundle-scope");
  BundleScope scope;
  if (array->size() == 1 &&
      (*tag == "all" || *tag == "first" || *tag == "last")) {
    scope.kind = *tag == "all"     ? BundleScopeKind::All
                 : *tag == "first" ? BundleScopeKind::First
                                   : BundleScopeKind::Last;
    return scope;
  }
  if (array->size() != 3 || (*tag != "interior" && *tag != "interval"))
    return zkc::error("bundle-scope");
  auto first = natural((*array)[1], BundleLimits::height);
  auto second = natural((*array)[2], BundleLimits::height);
  if (!first || !second)
    return zkc::error("bundle-scope");
  scope.kind = *tag == "interior" ? BundleScopeKind::Interior
                                  : BundleScopeKind::Interval;
  scope.first = *first;
  scope.second = *second;
  if (auto error = checkScope(scope))
    return error;
  return scope;
}
std::pair<uint32_t, uint32_t> scopeRows(const BundleScope &scope,
                                        uint32_t height) {
  switch (scope.kind) {
  case BundleScopeKind::All:
    return {0, height};
  case BundleScopeKind::First:
    return {0, 1};
  case BundleScopeKind::Last:
    return {height - 1, height};
  case BundleScopeKind::Interior:
    if (uint64_t(scope.first) + scope.second >= height)
      return {0, 0};
    return {scope.first, height - scope.second};
  case BundleScopeKind::Interval:
    return {scope.first, scope.second};
  }
  llvm_unreachable("admitted bundle scope");
}
bool staticWindow(const BundleScope &scope, int32_t offset) {
  int64_t o = offset;
  switch (scope.kind) {
  case BundleScopeKind::All:
    return o == 0;
  case BundleScopeKind::First:
    return o >= 0;
  case BundleScopeKind::Last:
    return o <= 0;
  case BundleScopeKind::Interior:
    return int64_t(scope.first) + o >= 0 && o <= int64_t(scope.second);
  case BundleScopeKind::Interval:
    return scope.first >= scope.second || int64_t(scope.first) + o >= 0;
  }
  return false;
}
Error windowAt(const BundleScope &scope, BundleReadModel model, uint32_t height,
               ArrayRef<int32_t> offsets) {
  if (scope.kind == BundleScopeKind::Interval && scope.second > height)
    return zkc::error("bundle-scope-height");
  if (model == BundleReadModel::Cyclic)
    return Error::success();
  auto [lo, hi] = scopeRows(scope, height);
  if (lo >= hi)
    return Error::success();
  for (int32_t offset : offsets)
    if (int64_t(lo) + offset < 0 || int64_t(hi) + offset > int64_t(height))
      return zkc::error("bundle-window");
  return Error::success();
}
uint32_t readRow(BundleReadModel model, uint32_t height, uint32_t row,
                 int32_t offset) {
  int64_t index = int64_t(row) + offset;
  if (model == BundleReadModel::Cyclic) {
    index %= int64_t(height);
    if (index < 0)
      index += height;
  }
  return uint32_t(index);
}

Expected<Presentation> presentation(StringRef field) {
  if (primeField(field))
    return Presentation{field.str(), 1, ""};
  const auto &catalog = protocol::installedDomains();
  // Closed reference table; see docs/spec/domains/values.md.
  static const struct {
    StringRef field, base;
    unsigned degree;
    StringRef nonresidue;
  } extensions[] = {{"koala-bear.ext8-binomial3", "koala-bear", 8, "3"}};
  for (const auto &entry : extensions)
    if (entry.field == field &&
        catalog.hasFact("ExtensionField", {field.str()}) &&
        catalog.associatedIdentity(field, "BaseField") == entry.base &&
        primeField(entry.base))
      return Presentation{entry.base.str(), entry.degree,
                          entry.nonresidue.str()};
  return zkc::error("bundle-field-presentation", field);
}

Expected<Arithmetic> Arithmetic::create(StringRef field) {
  auto shape = presentation(field);
  if (!shape)
    return shape.takeError();
  StringRef modulus = protocol::fieldModulus(shape->prime);
  if (modulus.empty())
    return zkc::error("bundle-field-presentation", field);
  Arithmetic result;
  result.field_ = field.str();
  result.prime_ = shape->prime;
  result.degree_ = shape->degree;
  result.width_ = 2 * APInt::getBitsNeeded(modulus, 10) + 2;
  result.modulus_ = APInt(result.width_, modulus, 10);
  result.nonresidue_ = APInt(
      result.width_, shape->nonresidue.empty() ? "0" : shape->nonresidue, 10);
  return result;
}
Expected<APInt> Arithmetic::parseCoordinate(StringRef text) const {
  if (text.empty() || text.size() > 256 ||
      (text.size() != 1 && text.front() == '0') ||
      !llvm::all_of(text, isDigit) || APInt::getBitsNeeded(text, 10) >= width_)
    return zkc::error("bundle-value");
  APInt value(width_, text, 10);
  if (value.uge(modulus_))
    return zkc::error("bundle-value");
  return value;
}
Expected<Scalar> Arithmetic::parse(ArrayRef<std::string> coordinates) const {
  if (coordinates.size() != degree_)
    return zkc::error("bundle-value");
  Scalar result;
  result.reserve(degree_);
  for (const auto &text : coordinates) {
    auto value = parseCoordinate(text);
    if (!value)
      return value.takeError();
    result.push_back(std::move(*value));
  }
  return result;
}
Scalar Arithmetic::zero() const { return Scalar(degree_, APInt(width_, 0)); }
Scalar Arithmetic::constant(const APInt &value) const {
  auto result = zero();
  result[0] = value.zextOrTrunc(width_).urem(modulus_);
  return result;
}
Scalar Arithmetic::add(const Scalar &a, const Scalar &b) const {
  Scalar result(degree_);
  for (unsigned i = 0; i < degree_; ++i)
    result[i] = (a[i] + b[i]).urem(modulus_);
  return result;
}
Scalar Arithmetic::neg(const Scalar &a) const {
  Scalar result(degree_);
  for (unsigned i = 0; i < degree_; ++i)
    result[i] = a[i].isZero() ? a[i] : modulus_ - a[i];
  return result;
}
Scalar Arithmetic::mul(const Scalar &a, const Scalar &b) const {
  // Coordinates of a*b in F_p[X]/(X^degree - nonresidue).
  auto result = zero();
  for (unsigned i = 0; i < degree_; ++i)
    for (unsigned j = 0; j < degree_; ++j) {
      APInt term = (a[i] * b[j]).urem(modulus_);
      unsigned k = i + j;
      if (k >= degree_) {
        k -= degree_;
        term = (term * nonresidue_).urem(modulus_);
      }
      result[k] = (result[k] + term).urem(modulus_);
    }
  return result;
}
bool Arithmetic::isZero(const Scalar &a) const {
  return llvm::all_of(a, [](const APInt &x) { return x.isZero(); });
}
BundleColumns Arithmetic::print(const Scalar &a) const {
  BundleColumns result;
  result.reserve(a.size());
  for (const auto &x : a) {
    SmallString<80> text;
    x.toString(text, 10, false);
    result.push_back(text.str().str());
  }
  return result;
}
std::optional<uint64_t> Arithmetic::natural(const Scalar &a) const {
  if (degree_ != 1 || a[0].getActiveBits() > 64)
    return std::nullopt;
  return a[0].getZExtValue();
}
Expected<const Arithmetic *> Fields::get(StringRef field) {
  for (const auto &entry : fields)
    if (entry->field() == field)
      return entry.get();
  auto created = Arithmetic::create(field);
  if (!created)
    return created.takeError();
  fields.push_back(std::make_unique<Arithmetic>(std::move(*created)));
  return fields.back().get();
}

Expected<Scalar> RowAlgebra::constant(StringRef field, StringRef literal) {
  auto key = std::make_pair(field.str(), literal.str());
  auto found = constants.find(key);
  if (found != constants.end())
    return found->second;
  auto arithmetic = fields.get(field);
  if (!arithmetic)
    return arithmetic.takeError();
  // Ring literals are canonical naturals of the prime subfield.
  auto prime = fields.get((*arithmetic)->prime());
  if (!prime)
    return prime.takeError();
  auto value = (*prime)->parseCoordinate(literal);
  if (!value)
    return value.takeError();
  auto result = (*arithmetic)->constant(*value);
  constants.emplace(std::move(key), result);
  return result;
}
Expected<Scalar> RowAlgebra::add(StringRef field, const Scalar &a,
                                 const Scalar &b) {
  auto arithmetic = fields.get(field);
  if (!arithmetic)
    return arithmetic.takeError();
  return (*arithmetic)->add(a, b);
}
Expected<Scalar> RowAlgebra::mul(StringRef field, const Scalar &a,
                                 const Scalar &b) {
  auto arithmetic = fields.get(field);
  if (!arithmetic)
    return arithmetic.takeError();
  return (*arithmetic)->mul(a, b);
}
Expected<Scalar> RowAlgebra::neg(StringRef field, const Scalar &a) {
  auto arithmetic = fields.get(field);
  if (!arithmetic)
    return arithmetic.takeError();
  return (*arithmetic)->neg(a);
}
Expected<Scalar> RowAlgebra::embed(StringRef source, StringRef target,
                                   const Scalar &a) {
  auto from = fields.get(source);
  if (!from)
    return from.takeError();
  auto to = fields.get(target);
  if (!to)
    return to.takeError();
  if ((*from)->degree() != 1 || (*to)->prime() != source)
    return zkc::error("bundle-field-presentation", target);
  return (*to)->constant(a[0]);
}

json::Value encodeValue(const BundleColumns &value) {
  if (value.size() == 1)
    return value.front();
  json::Array result;
  for (const auto &coordinate : value)
    result.push_back(coordinate);
  return result;
}
Error readValue(const json::Value &value, unsigned degree, BundleColumns &out) {
  if (degree == 1) {
    auto text = value.getAsString();
    if (!text)
      return zkc::error("bundle-value");
    out.push_back(text->str());
    return Error::success();
  }
  auto *array = value.getAsArray();
  if (!array || array->size() != degree)
    return zkc::error("bundle-value");
  for (const auto &coordinate : *array) {
    auto text = coordinate.getAsString();
    if (!text)
      return zkc::error("bundle-value");
    out.push_back(text->str());
  }
  return Error::success();
}
Expected<std::vector<BundleColumns>> readValues(const json::Value &value,
                                                ArrayRef<std::string> fields) {
  auto *array = value.getAsArray();
  if (!array || array->size() != fields.size())
    return zkc::error("bundle-public-shape");
  std::vector<BundleColumns> result(fields.size());
  for (size_t i = 0; i < fields.size(); ++i) {
    auto degree = bundleFieldDegree(fields[i]);
    if (!degree)
      return degree.takeError();
    if (auto error = readValue((*array)[i], *degree, result[i]))
      return error;
  }
  return result;
}
Expected<BundleColumns> readGroupValues(const json::Value &value,
                                        unsigned degree, uint64_t &budget) {
  auto *array = value.getAsArray();
  if (!array)
    return zkc::error("bundle-data-shape");
  if (uint64_t(array->size()) * degree > budget)
    return zkc::error("bundle-data-limit");
  budget -= uint64_t(array->size()) * degree;
  BundleColumns result;
  result.reserve(array->size() * degree);
  for (const auto &element : *array)
    if (auto error = readValue(element, degree, result))
      return error;
  return result;
}
json::Value encodeGroupValues(const BundleColumns &coordinates,
                              unsigned degree) {
  json::Array result;
  for (size_t i = 0; i + degree <= coordinates.size(); i += degree)
    result.push_back(encodeValue(BundleColumns(
        coordinates.begin() + i, coordinates.begin() + i + degree)));
  return result;
}
Scalar element(const std::vector<APInt> &coordinates, unsigned degree,
               uint32_t width, uint32_t row, uint32_t column) {
  size_t base = (size_t(row) * width + column) * degree;
  return Scalar(coordinates.begin() + base,
                coordinates.begin() + base + degree);
}
Error checkColumns(const BundleColumns &columns, uint64_t elements,
                   const Arithmetic &arithmetic, std::vector<APInt> &out) {
  if (columns.size() != elements * arithmetic.degree())
    return zkc::error("bundle-group-shape");
  out.clear();
  out.reserve(columns.size());
  for (const auto &text : columns) {
    auto value = arithmetic.parseCoordinate(text);
    if (!value)
      return value.takeError();
    out.push_back(std::move(*value));
  }
  return Error::success();
}

Error withDetail(Error error, StringRef detail) {
  return handleErrors(std::move(error), [&](const zkc::Refusal &r) -> Error {
    return zkc::error(r.code, r.detail.empty()
                                  ? detail.str()
                                  : detail.str() + ": " + r.detail);
  });
}
Error AnalysisBudget::account(const ring::Expression &arena,
                              uint64_t traversals, uint64_t retainedOutputs) {
  uint64_t inputCount = arena.inputs().size();
  uint64_t scan = arena.nodes().size() + inputCount + 1;
  if (traversals > (BundleLimits::analysisWork - work) / scan ||
      (inputCount &&
       retainedOutputs > (BundleLimits::analysisInputs - inputs) / inputCount))
    return zkc::error("bundle-analysis-limit");
  work += traversals * scan;
  inputs += retainedOutputs * inputCount;
  return Error::success();
}

Error checkOutputsUsed(const ring::Expression &arena,
                       ArrayRef<uint32_t> referenced) {
  std::vector<bool> used(arena.outputs().size(), false);
  for (uint32_t position : referenced) {
    if (position >= used.size())
      return zkc::error("bundle-output");
    used[position] = true;
  }
  if (!llvm::all_of(used, [](bool x) { return x; }))
    return zkc::error("bundle-unused-output");
  std::vector<uint32_t> all(arena.outputs().size());
  std::iota(all.begin(), all.end(), 0);
  auto inputs = arena.usedInputs(all);
  if (!inputs)
    return inputs.takeError();
  if (inputs->size() != arena.inputs().size())
    return zkc::error("bundle-unused-input");
  return Error::success();
}
} // namespace bundle

using namespace bundle;

BundleInput BundleInput::publicSlot(uint32_t index) {
  BundleInput input;
  input.index = index;
  return input;
}
BundleInput BundleInput::read(uint32_t group, int32_t offset, uint32_t column) {
  BundleInput input;
  input.kind = Kind::Read;
  input.index = group;
  input.offset = offset;
  input.column = column;
  return input;
}

Expected<unsigned> bundleFieldDegree(StringRef field) {
  auto shape = presentation(field);
  if (!shape)
    return shape.takeError();
  return shape->degree;
}

namespace {
Error uniqueNames(ArrayRef<std::string> names) {
  std::set<StringRef> seen;
  for (const auto &name : names) {
    if (!validName(name))
      return zkc::error("bundle-name", name);
    if (!seen.insert(name).second)
      return zkc::error("bundle-duplicate-name", name);
  }
  return Error::success();
}
bool hasPowerOfTwo(uint32_t min, uint32_t max) {
  for (uint64_t value = 1; value <= max; value <<= 1)
    if (value >= min)
      return true;
  return false;
}
Error checkHeight(const BundleHeight &height) {
  if (height.min < 1 || height.min > height.max ||
      height.max > BundleLimits::height)
    return zkc::error("bundle-height");
  if (height.authority == BundleHeightAuthority::Fixed &&
      (height.min != height.max || height.powerOfTwo))
    return zkc::error("bundle-height");
  if (height.powerOfTwo && !hasPowerOfTwo(height.min, height.max))
    return zkc::error("bundle-height");
  return Error::success();
}
} // namespace

Bundle::Bundle(std::vector<BundleSlot> publics,
               std::vector<BundleChannel> channels,
               std::vector<BundleTable> tables,
               std::vector<std::vector<BundleOutputFact>> facts)
    : publics_(std::move(publics)), channels_(std::move(channels)),
      tables_(std::move(tables)), facts_(std::move(facts)) {}

Expected<Bundle> Bundle::create(std::vector<BundleSlot> publics,
                                std::vector<BundleChannel> channels,
                                std::vector<BundleTable> tables) {
  if (publics.size() > BundleLimits::publics ||
      channels.size() > BundleLimits::channels ||
      tables.size() > BundleLimits::tables)
    return zkc::error("bundle-limit");
  if (tables.empty())
    return zkc::error("bundle-tables");
  std::vector<std::string> names;
  for (const auto &slot : publics) {
    names.push_back(slot.name);
    if (!installedField(slot.field))
      return zkc::error("bundle-field", slot.field);
    if (auto degree = bundleFieldDegree(slot.field); !degree)
      return degree.takeError();
  }
  if (auto error = uniqueNames(names))
    return error;
  names.clear();
  for (const auto &channel : channels) {
    names.push_back(channel.name);
    if (channel.tuple.size() > BundleLimits::arity)
      return zkc::error("bundle-limit", channel.name);
    for (const auto &field : channel.tuple)
      if (!installedField(field))
        return zkc::error("bundle-field", field);
    if (!installedField(channel.count))
      return zkc::error("bundle-field", channel.count);
    if (channel.kind == BundleChannelKind::Multiset &&
        !primeField(channel.count))
      return zkc::error("bundle-multiset-field", channel.name);
  }
  if (auto error = uniqueNames(names))
    return error;
  names.clear();
  for (const auto &table : tables)
    names.push_back(table.name);
  if (auto error = uniqueNames(names))
    return error;

  std::vector<std::vector<BundleOutputFact>> facts;
  AnalysisBudget analysisBudget;
  for (const auto &table : tables) {
    auto context = [&](StringRef code) { return zkc::error(code, table.name); };
    if (auto error = checkHeight(table.height))
      return error;
    if (table.groups.size() > BundleLimits::groups)
      return context("bundle-limit");
    names.clear();
    for (const auto &group : table.groups) {
      names.push_back(group.name);
      if (!installedField(group.field))
        return zkc::error("bundle-field", group.field);
      if (auto degree = bundleFieldDegree(group.field); !degree)
        return degree.takeError();
      if (group.width < 1 || group.width > BundleLimits::width)
        return context("bundle-width");
      if (group.authority == BundleAuthority::Config &&
          table.height.authority == BundleHeightAuthority::Instance)
        return context("bundle-config-height");
    }
    if (auto error = uniqueNames(names))
      return error;
    const auto &arena = table.arena;
    if (table.inputs.size() != arena.inputs().size())
      return context("bundle-input-count");
    std::set<std::tuple<int, uint32_t, int32_t, uint32_t>> bindings;
    std::vector<uint32_t> weights;
    for (size_t i = 0; i < table.inputs.size(); ++i) {
      const auto &input = table.inputs[i];
      StringRef field;
      if (input.kind == BundleInput::Kind::Public) {
        if (input.offset || input.column || input.index >= publics.size())
          return context("bundle-input");
        field = publics[input.index].field;
        weights.push_back(0);
      } else {
        if (input.index >= table.groups.size() ||
            input.column >= table.groups[input.index].width ||
            input.offset > int32_t(BundleLimits::offset) ||
            input.offset < -int32_t(BundleLimits::offset))
          return context("bundle-input");
        field = table.groups[input.index].field;
        weights.push_back(1);
      }
      if (arena.inputs()[i].field != field)
        return context("bundle-input-field");
      if (!bindings
               .insert(
                   {int(input.kind), input.index, input.offset, input.column})
               .second)
        return context("bundle-duplicate-input");
    }
    if (table.assertions.size() + table.interactions.size() >
        BundleLimits::checks)
      return context("bundle-limit");
    std::vector<uint32_t> referenced;
    for (const auto &assertion : table.assertions) {
      if (auto error = checkScope(assertion.scope))
        return error;
      referenced.push_back(assertion.output);
    }
    for (const auto &interaction : table.interactions) {
      if (auto error = checkScope(interaction.scope))
        return error;
      llvm::append_range(referenced, interactionOutputs(interaction));
    }
    if (auto error = analysisBudget.account(
            arena, arena.outputs().size() + referenced.size() + 1,
            arena.outputs().size()))
      return withDetail(std::move(error), table.name);
    if (auto error = checkOutputsUsed(arena, referenced))
      return withDetail(std::move(error), table.name);
    auto degrees = arena.degrees(weights);
    if (!degrees)
      return degrees.takeError();
    std::vector<BundleOutputFact> outputFacts;
    for (uint32_t position = 0; position < arena.outputs().size(); ++position) {
      uint32_t node = arena.outputs()[position];
      BundleOutputFact fact{
          arena.facts()[node].field, (*degrees)[node], {}, {}};
      auto used = arena.usedInputs({position});
      if (!used)
        return used.takeError();
      for (uint32_t input : *used) {
        const auto &binding = table.inputs[input];
        if (binding.kind == BundleInput::Kind::Public)
          fact.publics.push_back(binding.index);
        else
          fact.reads.push_back({binding.index, binding.offset, binding.column});
      }
      llvm::sort(fact.publics);
      llvm::sort(fact.reads);
      outputFacts.push_back(std::move(fact));
    }
    auto fieldOf = [&](uint32_t position) -> StringRef {
      return outputFacts[position].field;
    };
    // Finite windows that are undefined at every height refuse here; the
    // height-dependent remainder is checked when an instance is admitted.
    auto staticCheck = [&](const BundleScope &scope,
                           ArrayRef<uint32_t> positions) -> Error {
      if (table.readModel == BundleReadModel::Cyclic)
        return Error::success();
      for (uint32_t position : positions)
        for (const auto &read : outputFacts[position].reads)
          if (!staticWindow(scope, read.offset))
            return context("bundle-window");
      return Error::success();
    };
    for (const auto &assertion : table.assertions)
      if (auto error = staticCheck(assertion.scope, {assertion.output}))
        return error;
    for (const auto &interaction : table.interactions) {
      if (interaction.channel >= channels.size())
        return context("bundle-channel");
      const auto &channel = channels[interaction.channel];
      if (interaction.kind != channel.kind)
        return context("bundle-interaction-kind");
      if (interaction.tuple.size() != channel.tuple.size())
        return context("bundle-tuple-arity");
      for (size_t i = 0; i < interaction.tuple.size(); ++i)
        if (fieldOf(interaction.tuple[i]) != channel.tuple[i])
          return context("bundle-tuple-field");
      if (fieldOf(interaction.count) != channel.count)
        return context("bundle-count-field");
      if (interaction.locality.key > BundleLimits::checks ||
          (!interaction.locality.local && interaction.locality.key))
        return context("bundle-locality");
      if (interaction.kind == BundleChannelKind::Multiset) {
        if (!interaction.bound || *interaction.bound < 1 ||
            *interaction.bound > BundleLimits::multiplicity)
          return context("bundle-multiset-bound");
        StringRef text = protocol::fieldModulus(channel.count);
        unsigned bits = std::max(APInt::getBitsNeeded(text, 10) + 1, 66u);
        if (APInt(bits, text, 10).ule(APInt(bits, *interaction.bound)))
          return context("bundle-multiset-bound");
      } else if (interaction.side != BundleSide::Push) {
        return context("bundle-interaction-kind");
      }
      if (auto error =
              staticCheck(interaction.scope, interactionOutputs(interaction)))
        return error;
    }
    facts.push_back(std::move(outputFacts));
  }
  Bundle result(std::move(publics), std::move(channels), std::move(tables),
                std::move(facts));
  auto bytes = zkc::printJson(result.encode());
  if (bytes.size() > BundleLimits::bytes)
    return zkc::error("bundle-limit");
  result.identity_ = toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
  return result;
}

namespace bundle {
StringRef authorityName(BundleAuthority authority) {
  switch (authority) {
  case BundleAuthority::Witness:
    return "witness";
  case BundleAuthority::Config:
    return "config";
  case BundleAuthority::Public:
    return "public";
  }
  llvm_unreachable("admitted authority");
}
json::Value encodeHeight(const BundleHeight &height) {
  switch (height.authority) {
  case BundleHeightAuthority::Fixed:
    return json::Array{"fixed", height.min};
  case BundleHeightAuthority::Config:
  case BundleHeightAuthority::Instance:
    return json::Array{height.authority == BundleHeightAuthority::Config
                           ? "config"
                           : "instance",
                       height.min, height.max, height.powerOfTwo};
  }
  llvm_unreachable("admitted height");
}
} // namespace bundle

namespace {
json::Value encodeLocality(const BundleLocality &locality) {
  if (!locality.local)
    return json::Array{"global"};
  return json::Array{"local", locality.key};
}
json::Value positions(ArrayRef<uint32_t> values) {
  json::Array result;
  for (auto value : values)
    result.push_back(value);
  return result;
}
} // namespace

json::Value Bundle::encode() const {
  json::Array publics, channels, tables;
  for (const auto &slot : publics_)
    publics.push_back(json::Array{slot.name, slot.field});
  for (const auto &channel : channels_) {
    json::Array tuple;
    for (const auto &field : channel.tuple)
      tuple.push_back(field);
    channels.push_back(json::Array{channel.name,
                                   channel.kind == BundleChannelKind::Multiset
                                       ? "multiset"
                                       : "field-balance",
                                   std::move(tuple), channel.count});
  }
  for (const auto &table : tables_) {
    json::Array groups, inputs, assertions, interactions;
    for (const auto &group : table.groups)
      groups.push_back(json::Array{group.name, authorityName(group.authority),
                                   group.field, group.width});
    for (const auto &input : table.inputs)
      inputs.push_back(input.kind == BundleInput::Kind::Public
                           ? json::Array{"public", input.index}
                           : json::Array{"read", input.index,
                                         printOffset(input.offset),
                                         input.column});
    for (const auto &assertion : table.assertions)
      assertions.push_back(
          json::Array{assertion.output, encodeScope(assertion.scope)});
    for (const auto &interaction : table.interactions) {
      if (interaction.kind == BundleChannelKind::FieldBalance)
        interactions.push_back(
            json::Array{"field-balance", interaction.channel,
                        encodeLocality(interaction.locality),
                        encodeScope(interaction.scope),
                        positions(interaction.tuple), interaction.count,
                        interaction.bound ? json::Value(*interaction.bound)
                                          : json::Value(nullptr)});
      else
        interactions.push_back(
            json::Array{"multiset", interaction.channel,
                        encodeLocality(interaction.locality),
                        encodeScope(interaction.scope),
                        interaction.side == BundleSide::Push ? "push" : "pull",
                        positions(interaction.tuple), interaction.count,
                        *interaction.bound});
    }
    tables.push_back(json::Array{
        table.name, table.optional ? "optional" : "required",
        encodeHeight(table.height),
        table.readModel == BundleReadModel::Cyclic ? "cyclic" : "finite",
        std::move(groups), table.arena.encode(), std::move(inputs),
        std::move(assertions), std::move(interactions)});
  }
  return json::Array{"zkc.relation-bundle/0", std::move(publics),
                     std::move(channels), std::move(tables)};
}

json::Value Bundle::analysis() const {
  json::Array tables;
  for (size_t t = 0; t < tables_.size(); ++t) {
    json::Array outputs;
    uint32_t maxOffset = 0, maxDegree = 0;
    for (const auto &fact : facts_[t]) {
      json::Array reads, publics;
      for (const auto &read : fact.reads) {
        reads.push_back(
            json::Array{read.group, printOffset(read.offset), read.column});
        maxOffset = std::max<uint32_t>(maxOffset, std::abs(read.offset));
      }
      for (auto slot : fact.publics)
        publics.push_back(slot);
      maxDegree = std::max(maxDegree, fact.degree);
      outputs.push_back(json::Array{fact.field, fact.degree, std::move(reads),
                                    std::move(publics)});
    }
    tables.push_back(json::Object{{"table", tables_[t].name},
                                  {"max_offset", maxOffset},
                                  {"max_degree", maxDegree},
                                  {"degree_variables", "reads"},
                                  {"outputs", std::move(outputs)}});
  }
  return json::Object{{"schema", "zkc.relation-bundle-analysis/0"},
                      {"relation", identity()},
                      {"tables", std::move(tables)}};
}

namespace {
Expected<BundleHeight> readHeight(const json::Value &value) {
  auto *array = value.getAsArray();
  auto tag =
      array && !array->empty() ? (*array)[0].getAsString() : std::nullopt;
  if (!tag)
    return zkc::error("bundle-height");
  BundleHeight height;
  if (*tag == "fixed" && array->size() == 2) {
    auto h = natural((*array)[1], BundleLimits::height);
    if (!h)
      return zkc::error("bundle-height");
    height.min = height.max = *h;
  } else if ((*tag == "config" || *tag == "instance") && array->size() == 4) {
    auto min = natural((*array)[1], BundleLimits::height);
    auto max = natural((*array)[2], BundleLimits::height);
    auto pow2 = (*array)[3].getAsBoolean();
    if (!min || !max || !pow2)
      return zkc::error("bundle-height");
    height.authority = *tag == "config" ? BundleHeightAuthority::Config
                                        : BundleHeightAuthority::Instance;
    height.min = *min;
    height.max = *max;
    height.powerOfTwo = *pow2;
  } else {
    return zkc::error("bundle-height");
  }
  return height;
}
Expected<BundleLocality> readLocality(const json::Value &value) {
  if (row(value, 1, "global"))
    return BundleLocality{};
  if (auto *array = row(value, 2, "local"))
    if (auto key = natural((*array)[1], BundleLimits::checks))
      return BundleLocality{true, uint32_t(*key)};
  return zkc::error("bundle-locality");
}
Expected<std::vector<uint32_t>> readPositions(const json::Value &value,
                                              size_t limit) {
  auto *array = value.getAsArray();
  if (!array || array->size() > limit)
    return zkc::error("bundle-schema");
  std::vector<uint32_t> result;
  for (const auto &item : *array) {
    auto position = natural(item, UINT32_MAX);
    if (!position)
      return zkc::error("bundle-schema");
    result.push_back(*position);
  }
  return result;
}
Expected<BundleInteraction> readInteraction(const json::Value &value) {
  auto *array = value.getAsArray();
  auto tag =
      array && !array->empty() ? (*array)[0].getAsString() : std::nullopt;
  if (!tag)
    return zkc::error("bundle-schema");
  BundleInteraction interaction;
  if (*tag == "field-balance" && array->size() == 7) {
    interaction.kind = BundleChannelKind::FieldBalance;
  } else if (*tag == "multiset" && array->size() == 8) {
    interaction.kind = BundleChannelKind::Multiset;
  } else {
    return zkc::error("bundle-interaction-kind");
  }
  const auto &a = *array;
  auto channel = natural(a[1], BundleLimits::channels);
  if (!channel)
    return zkc::error("bundle-channel");
  interaction.channel = *channel;
  auto locality = readLocality(a[2]);
  if (!locality)
    return locality.takeError();
  interaction.locality = *locality;
  auto scope = readScope(a[3]);
  if (!scope)
    return scope.takeError();
  interaction.scope = *scope;
  size_t next = 4;
  if (interaction.kind == BundleChannelKind::Multiset) {
    auto side = a[4].getAsString();
    if (!side || (*side != "push" && *side != "pull"))
      return zkc::error("bundle-side");
    interaction.side = *side == "push" ? BundleSide::Push : BundleSide::Pull;
    next = 5;
  }
  auto tuple = readPositions(a[next], BundleLimits::arity);
  if (!tuple)
    return tuple.takeError();
  interaction.tuple = std::move(*tuple);
  auto count = natural(a[next + 1], UINT32_MAX);
  if (!count)
    return zkc::error("bundle-schema");
  interaction.count = *count;
  const auto &bound = a[next + 2];
  if (interaction.kind == BundleChannelKind::FieldBalance &&
      bound.kind() == json::Value::Null)
    return interaction;
  auto value64 = bound.getAsUINT64();
  if (!value64)
    return zkc::error(interaction.kind == BundleChannelKind::Multiset
                          ? "bundle-multiset-bound"
                          : "bundle-schema");
  interaction.bound = *value64;
  return interaction;
}
Expected<BundleTable> readTable(const json::Value &value) {
  auto *array = row(value, 9);
  if (!array)
    return zkc::error("bundle-schema");
  const auto &a = *array;
  auto name = string(a[0]);
  auto presence = a[1].getAsString();
  auto model = a[3].getAsString();
  auto *groups = a[4].getAsArray();
  auto *inputs = a[6].getAsArray();
  auto *assertions = a[7].getAsArray();
  auto *interactions = a[8].getAsArray();
  if (!name || !presence ||
      (*presence != "required" && *presence != "optional") || !model ||
      (*model != "finite" && *model != "cyclic") || !groups || !inputs ||
      !assertions || !interactions)
    return zkc::error("bundle-schema");
  if (groups->size() > BundleLimits::groups ||
      inputs->size() > ring::Limits::inputs ||
      assertions->size() + interactions->size() > BundleLimits::checks)
    return zkc::error("bundle-limit");
  auto height = readHeight(a[2]);
  if (!height)
    return height.takeError();
  auto arena = ring::readExpression(a[5]);
  if (!arena)
    return arena.takeError();
  BundleTable table{
      *name,
      *presence == "optional",
      *height,
      *model == "cyclic" ? BundleReadModel::Cyclic : BundleReadModel::Finite,
      {},
      std::move(*arena),
      {},
      {},
      {}};
  for (const auto &item : *groups) {
    auto *group = row(item, 4);
    if (!group)
      return zkc::error("bundle-schema");
    auto groupName = string((*group)[0]);
    auto authority = (*group)[1].getAsString();
    auto field = string((*group)[2]);
    auto width = natural((*group)[3], BundleLimits::width);
    if (!groupName || !authority || !field || !width ||
        (*authority != "witness" && *authority != "config" &&
         *authority != "public"))
      return zkc::error("bundle-schema");
    table.groups.push_back({*groupName,
                            *authority == "witness"  ? BundleAuthority::Witness
                            : *authority == "config" ? BundleAuthority::Config
                                                     : BundleAuthority::Public,
                            *field, uint32_t(*width)});
  }
  for (const auto &item : *inputs) {
    if (auto *input = row(item, 2, "public")) {
      auto index = natural((*input)[1], BundleLimits::publics);
      if (!index)
        return zkc::error("bundle-input");
      table.inputs.push_back(BundleInput::publicSlot(*index));
    } else if (auto *input = row(item, 4, "read")) {
      auto group = natural((*input)[1], BundleLimits::groups);
      auto offset = signedOffset((*input)[2]);
      auto column = natural((*input)[3], BundleLimits::width);
      if (!group || !offset || !column)
        return zkc::error("bundle-input");
      table.inputs.push_back(BundleInput::read(*group, *offset, *column));
    } else {
      return zkc::error("bundle-input-kind");
    }
  }
  for (const auto &item : *assertions) {
    auto *assertion = row(item, 2);
    auto output =
        assertion ? natural((*assertion)[0], UINT32_MAX) : std::nullopt;
    if (!output)
      return zkc::error("bundle-schema");
    auto scope = readScope((*assertion)[1]);
    if (!scope)
      return scope.takeError();
    table.assertions.push_back({uint32_t(*output), *scope});
  }
  for (const auto &item : *interactions) {
    auto interaction = readInteraction(item);
    if (!interaction)
      return interaction.takeError();
    table.interactions.push_back(std::move(*interaction));
  }
  return table;
}
} // namespace

Expected<Bundle> readBundle(const json::Value &value) {
  auto *root = row(value, 4, "zkc.relation-bundle/0");
  if (!root)
    return zkc::error("bundle-schema");
  auto *publics = (*root)[1].getAsArray();
  auto *channels = (*root)[2].getAsArray();
  auto *tables = (*root)[3].getAsArray();
  if (!publics || !channels || !tables)
    return zkc::error("bundle-schema");
  if (publics->size() > BundleLimits::publics ||
      channels->size() > BundleLimits::channels ||
      tables->size() > BundleLimits::tables)
    return zkc::error("bundle-limit");
  std::vector<BundleSlot> slots;
  for (const auto &item : *publics) {
    auto *slot = row(item, 2);
    auto name = slot ? string((*slot)[0]) : std::nullopt;
    auto field = slot ? string((*slot)[1]) : std::nullopt;
    if (!name || !field)
      return zkc::error("bundle-schema");
    slots.push_back({*name, *field});
  }
  std::vector<BundleChannel> channelList;
  for (const auto &item : *channels) {
    auto *channel = row(item, 4);
    auto name = channel ? string((*channel)[0]) : std::nullopt;
    auto kind = channel ? (*channel)[1].getAsString() : std::nullopt;
    auto *tuple = channel ? (*channel)[2].getAsArray() : nullptr;
    auto count = channel ? string((*channel)[3]) : std::nullopt;
    if (!name || !kind || !tuple || !count ||
        (*kind != "field-balance" && *kind != "multiset"))
      return zkc::error("bundle-schema");
    if (tuple->size() > BundleLimits::arity)
      return zkc::error("bundle-limit");
    BundleChannel result{*name,
                         *kind == "multiset" ? BundleChannelKind::Multiset
                                             : BundleChannelKind::FieldBalance,
                         {},
                         *count};
    for (const auto &field : *tuple) {
      auto text = string(field);
      if (!text)
        return zkc::error("bundle-schema");
      result.tuple.push_back(*text);
    }
    channelList.push_back(std::move(result));
  }
  std::vector<BundleTable> tableList;
  for (const auto &item : *tables) {
    auto table = readTable(item);
    if (!table)
      return table.takeError();
    tableList.push_back(std::move(*table));
  }
  return Bundle::create(std::move(slots), std::move(channelList),
                        std::move(tableList));
}

Expected<Bundle> readBundleText(StringRef text) {
  auto json = zkc::parseNaturalJson(text, BundleLimits::bytes, 16,
                                    "bundle-schema", "bundle-limit");
  if (!json)
    return json.takeError();
  return readBundle(*json);
}

Expected<Bundle> embedAIR(const AIR &air) {
  std::string field = air.field().str();
  std::vector<BundleSlot> publics;
  for (uint32_t i = 0; i < air.publicInputs(); ++i)
    publics.push_back({"public_" + std::to_string(i), field});
  std::vector<BundleGroup> groups;
  if (air.columns())
    groups.push_back(
        {"columns", BundleAuthority::Witness, field, air.columns()});
  auto view = air.expressionView();
  if (!view)
    return view.takeError();
  std::vector<BundleInput> bindings;
  for (const auto &input : view->inputs)
    bindings.push_back(
        input.kind == AIRExpressionInput::Kind::Public
            ? BundleInput::publicSlot(input.publicIndex)
            : BundleInput::read(0, int32_t(input.cell.row), input.cell.column));
  std::vector<BundleAssertion> assertions;
  for (const auto &constraint : air.constraints()) {
    BundleScope scope;
    switch (constraint.scope.kind) {
    case AIRScopeKind::Every:
      scope.kind = BundleScopeKind::All;
      break;
    case AIRScopeKind::First:
      scope.kind = BundleScopeKind::First;
      break;
    case AIRScopeKind::Last:
      scope.kind = BundleScopeKind::Last;
      break;
    case AIRScopeKind::Transition:
      scope = {BundleScopeKind::Interior, 0, constraint.scope.lookahead};
      break;
    }
    assertions.push_back({uint32_t(assertions.size()), scope});
  }
  std::vector<BundleTable> tables;
  tables.push_back(
      {"trace",
       false,
       {BundleHeightAuthority::Instance, 1, AIRLimits::height, false},
       BundleReadModel::Finite,
       std::move(groups),
       std::move(view->expression),
       std::move(bindings),
       std::move(assertions),
       {}});
  return Bundle::create(std::move(publics), {}, std::move(tables));
}

BundleData embedAIRData(const Bundle &bundle, const AIRTrace &trace,
                        ArrayRef<std::string> statement) {
  std::string identity = bundle.identity().str();
  BundleData data;
  data.configuration = {identity, {{std::nullopt, {}}}};
  data.instance.relation = identity;
  for (const auto &value : statement)
    data.instance.publics.push_back({value});
  data.instance.tables.push_back({true, trace.layout.height, {}});
  std::vector<BundleColumns> groups;
  if (trace.layout.columns)
    groups.push_back(trace.cells);
  data.witness = {identity, {std::move(groups)}};
  return data;
}

} // namespace zkc::relation
