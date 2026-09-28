#include "zkc/Mathematical/Types.h"
#include "zkc/Support/Refusal.h"
#include <algorithm>
#include <limits>

using namespace llvm;
namespace zkc::mathematical {
namespace {
void append(std::string &key, StringRef value) {
  key += std::to_string(value.size()) + ':' + value.str();
}
Expected<std::string> staticKey(ArrayRef<NormalStatic> values,
                                AdmissionBudget &budget) {
  std::string result;
  if (auto failure = budget.consume(values.size()))
    return failure;
  for (const auto &value : values) {
    auto key = value.key(budget);
    if (!key)
      return key.takeError();
    append(result, *key);
  }
  return result;
}
Expected<std::vector<NormalStatic>>
substitute(ArrayRef<Static> values, ArrayRef<NormalStatic> parameters,
           AdmissionBudget &budget) {
  if (auto failure = budget.consume(values.size()))
    return failure;
  std::vector<NormalStatic> result;
  for (const auto &value : values) {
    auto normalized = normalize(value, parameters, budget);
    if (!normalized)
      return normalized.takeError();
    result.push_back(std::move(*normalized));
  }
  return result;
}
} // namespace

struct TypeOwnership {};
TypeTable::TypeTable() : ownership(std::make_shared<const TypeOwnership>()) {}

const TypeShape *TypeTable::get(TypeId type) const {
  return type.owner == ownership.get() && type.index < types.size()
             ? &types[type.index]
             : nullptr;
}
const TypeSize *TypeTable::size(TypeId type) const {
  return get(type) ? &sizes[type.index] : nullptr;
}
bool TypeTable::isCondition(TypeId type) const {
  const auto *shape = get(type);
  if (!shape || shape->kind != TypeShape::Kind::Fin ||
      shape->statics.size() != 1)
    return false;
  auto count = shape->statics[0].closed();
  if (!count) {
    consumeError(count.takeError());
    return false;
  }
  return *count == 2;
}
Expected<TypeId> TypeTable::intern(TypeShape shape, AdmissionBudget &budget) {
  if (auto failure =
          budget.consume(1 + shape.elements.size() + shape.constructor.size()))
    return failure;
  TypeSize measured;
  for (auto element : shape.elements) {
    const auto *child = size(element);
    if (!child)
      return error("math-type-owner");
    if (child->nodes > typeNodeLimit - measured.nodes)
      return error("math-type-size");
    if (child->height > typeDepthLimit)
      return error("math-type-depth");
    measured.nodes += child->nodes;
    measured.height = std::max(measured.height, 1 + child->height);
  }
  auto statics = staticKey(shape.statics, budget);
  if (!statics)
    return statics.takeError();
  std::string key = std::to_string(static_cast<unsigned>(shape.kind)) + ';';
  append(key, shape.domain ? std::to_string(*shape.domain) : "");
  append(key, shape.constructor);
  append(key, *statics);
  key += std::to_string(static_cast<unsigned>(shape.degree)) + ';';
  for (auto element : shape.elements) {
    key += std::to_string(element.ordinal()) + ';';
  }
  auto found = interned.find(key);
  if (found != interned.end())
    return found->second;
  if (types.size() >= std::numeric_limits<uint32_t>::max())
    return error("math-admission-limit");
  TypeId result(ownership.get(), static_cast<uint32_t>(types.size()));
  types.push_back(std::move(shape));
  sizes.push_back(measured);
  interned.emplace(std::move(key), result);
  return result;
}
Expected<TypeId> TypeTable::product(ArrayRef<TypeId> elements,
                                    AdmissionBudget &budget) {
  if (auto failure = budget.consume(elements.size()))
    return failure;
  return intern({TypeShape::Kind::Product,
                 {},
                 {},
                 {},
                 elements.vec(),
                 raw::PolynomialType::Degree::Individual},
                budget);
}
Expected<TypeId> TypeTable::fin(NormalStatic count, AdmissionBudget &budget) {
  return intern({TypeShape::Kind::Fin,
                 {},
                 {},
                 {std::move(count)},
                 {},
                 raw::PolynomialType::Degree::Individual},
                budget);
}
Expected<TypeId> TypeTable::vector(TypeId element, NormalStatic count,
                                   AdmissionBudget &budget) {
  return intern({TypeShape::Kind::Vector,
                 {},
                 {},
                 {std::move(count)},
                 {element},
                 raw::PolynomialType::Degree::Individual},
                budget);
}

Expected<TypeId>
TypeTable::instantiate(const raw::TypeUse &use, uint64_t earlier,
                       ArrayRef<NormalStatic> parameters,
                       const raw::Subject &subject, DomainTypeResolver resolver,
                       AdmissionBudget &budget, unsigned depth) {
  if (auto failure = budget.consume())
    return failure;
  if (depth > typeDepthLimit)
    return error("math-type-template-depth");
  if (use.type.index >= earlier ||
      use.type.index >= subject.module.types.size())
    return error("math-type-reference");
  const auto &declaration = subject.module.types[use.type.index];
  if (use.statics.size() != declaration.statics)
    return error("math-static-arity");
  auto arguments = substitute(use.statics, parameters, budget);
  if (!arguments)
    return arguments.takeError();
  auto key = staticKey(*arguments, budget);
  if (!key)
    return key.takeError();
  *key = std::to_string(use.type.index) + ';' + *key;
  auto found = instances.find(*key);
  if (found != instances.end())
    return found->second;
  // A reference selects the constructor at this depth. Its product/vector
  // children advance once in expand. Counting the lookup again would reject
  // structurally legal chains depending on which instances were cached.
  auto result = expand(declaration.body, use.type.index, *arguments, subject,
                       resolver, budget, depth);
  if (!result)
    return result.takeError();
  instances.emplace(std::move(*key), *result);
  return result;
}
Expected<TypeId> TypeTable::formTemplate(uint64_t index,
                                         const raw::Subject &subject,
                                         DomainTypeResolver resolver,
                                         AdmissionBudget &budget) {
  if (index >= subject.module.types.size())
    return error("math-type-reference");
  const auto &declaration = subject.module.types[index];
  if (auto failure = budget.consume(declaration.statics))
    return failure;
  std::vector<NormalStatic> parameters;
  for (uint64_t i = 0; i < declaration.statics; ++i)
    parameters.push_back(NormalStatic::parameter(i));
  return expand(declaration.body, index, parameters, subject, resolver, budget,
                0);
}
Expected<TypeId> TypeTable::expand(const raw::Type &type, uint64_t earlier,
                                   ArrayRef<NormalStatic> parameters,
                                   const raw::Subject &subject,
                                   DomainTypeResolver resolver,
                                   AdmissionBudget &budget, unsigned depth) {
  if (auto failure = budget.consume())
    return failure;
  if (depth > typeDepthLimit)
    return error("math-type-template-depth");
  if (const auto *productType = std::get_if<raw::ProductType>(&type)) {
    std::vector<TypeId> elements;
    if (auto failure = budget.consume(productType->elements.size()))
      return failure;
    for (const auto &element : productType->elements) {
      auto result = instantiate(element, earlier, parameters, subject, resolver,
                                budget, depth + 1);
      if (!result)
        return result.takeError();
      elements.push_back(*result);
    }
    return product(elements, budget);
  }
  if (const auto *finType = std::get_if<raw::FinType>(&type)) {
    auto count = normalize(finType->count, parameters, budget);
    if (!count)
      return count.takeError();
    return fin(std::move(*count), budget);
  }
  if (const auto *vectorType = std::get_if<raw::VectorType>(&type)) {
    auto count = normalize(vectorType->count, parameters, budget);
    if (!count)
      return count.takeError();
    auto element = instantiate(vectorType->element, earlier, parameters,
                               subject, resolver, budget, depth + 1);
    if (!element)
      return element.takeError();
    return vector(*element, std::move(*count), budget);
  }
  TypeShape shape{TypeShape::Kind::Nominal,
                  {},
                  {},
                  {},
                  {},
                  raw::PolynomialType::Degree::Individual};
  uint64_t domain = 0;
  ArrayRef<Static> arguments;
  std::vector<Static> polynomialArguments;
  if (const auto *nominal = std::get_if<raw::NominalType>(&type)) {
    domain = nominal->domain.index;
    shape.constructor = nominal->name;
    arguments = nominal->arguments;
  } else if (const auto *polynomial = std::get_if<raw::PolynomialType>(&type)) {
    domain = polynomial->domain.index;
    shape.kind = TypeShape::Kind::Polynomial;
    shape.degree = polynomial->convention;
    polynomialArguments = {polynomial->arity, polynomial->degree};
    arguments = polynomialArguments;
  } else if (const auto *residual = std::get_if<raw::ResidualType>(&type)) {
    domain = residual->domain.index;
    shape.kind = TypeShape::Kind::Residual;
    polynomialArguments = {residual->arity, residual->degree};
    arguments = polynomialArguments;
  } else
    return error("math-type-kind");
  if (domain >= subject.manifest.domains.size() ||
      domain > std::numeric_limits<uint32_t>::max())
    return error("math-domain-reference");
  shape.domain = static_cast<uint32_t>(domain);
  auto statics = substitute(arguments, parameters, budget);
  if (!statics)
    return statics.takeError();
  shape.statics = std::move(*statics);
  if (auto failure = resolver(subject.manifest.domains[domain], shape))
    return failure;
  return intern(std::move(shape), budget);
}
} // namespace zkc::mathematical
