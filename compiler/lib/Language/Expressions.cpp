#include "BodyCheck.h"
#include "ManagedServices.h"
#include "RecordIntrinsics.h"
#include "ScopedWitness.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Language/Builtins.h"
#include "llvm/Support/SaveAndRestore.h"
#include <algorithm>
#include <cassert>
using namespace llvm;
namespace zkc::language::detail {
std::optional<ValueId>
BodyChecker::expression(uint32_t id, std::optional<Type> expected,
                        unsigned depth, bool allowUntypedStop,
                        std::optional<ValuePlacement> placed,
                        const ValuePlacement *schema) {
  SaveAndRestore referenceSite(checker.referenceSite,
                               syntax.expressions[id].referenceSite);
  assert((!protocol() || placement) &&
         "protocol expression requires a statement inference scope");
  SaveAndRestore completionScope(completionAllowed,
                                 completionAllowed && completionLoop == id);
  SaveAndRestore<const ValuePlacement *> placementContext(
      contextualPlacement, placed ? &*placed : nullptr);
  SaveAndRestore<const ValuePlacement *> schemaContext(
      contextualPlacementSchema, schema);
  const bool expectedDataContract =
      expected.has_value() && !placed &&
      !(schema && std::holds_alternative<ProductPlacement>(schema->value));
  TypeScope types(*this, id, expected);
  if (!types)
    return {};
  if (!expected)
    expected = inferredType(id);
  auto result = evaluate(id, expected, depth, allowUntypedStop);
  if (result && expectedDataContract && expected &&
      !isLogicalValue(*expected) && product(*result)) {
    fail("source.placement",
         "distributed product requires an expected placed contract",
         syntax.expressions[id].span);
    return {};
  }
  if (result && placed &&
      !matchPlacement(*result, *placed, syntax.expressions[id].span))
    return {};
  if (result && retainExpressionValues) {
    if (!checker.types.charge(1, syntax.expressions[id].span))
      return {};
    body.expressionValues.insert_or_assign(id, *result);
  }
  const auto &expr = syntax.expressions[id];
  if (!result && body.stopped && !checker.types.diagnostic &&
      expr.kind != Expression::Kind::Block &&
      expr.kind != Expression::Kind::If && expr.kind != Expression::Kind::Match)
    fail("source.unreachable", "operation follows an operand that always stops",
         expr.span);
  return result;
}
std::optional<ValueId> BodyChecker::evaluate(uint32_t id,
                                             std::optional<Type> expected,
                                             unsigned depth,
                                             bool allowUntypedStop) {
  const auto &expr = syntax.expressions[id];
  if (depth > checker.work.limits.expressionDepth ||
      !checker.types.charge(1, expr.span)) {
    if (!checker.types.diagnostic)
      fail("source.limit", "expression depth limit exceeded", expr.span);
    return {};
  }
  SaveAndRestore<std::optional<uint32_t>> origin(
      originatingExpression, expr.synthesized ? originatingExpression : id);
  using K = Expression::Kind;
  using T = Type::Kind;
  if (this->oracleMode() && !oracleExpression(expr))
    return {};
  const auto oracleMode = oracleEvaluation(expr.kind);
  if (syntax.layoutSyntax || this->oracleMode() || orderedRoot) {
    bool ordered =
        (expr.kind == K::MethodCall && !inference->callees.count(id)) ||
        oracleMode == Statement::Evaluation::Ordered;
    if (expr.kind == K::Record) {
      auto type = inferredType(id);
      const auto *nominal =
          type ? checker.types.typeDeclaration(*type) : nullptr;
      ordered |= nominal && nominal->resource.has_value();
    }
    if (auto found = inference->callees.find(id);
        found != inference->callees.end()) {
      const auto &callee =
          checker.output.declarations[found->second.declaration.index];
      if (callee.kind == Declaration::Kind::Oracle &&
          (!protocol() || orderedRoot != id)) {
        fail("source.oracle-construction",
             "oracle construction requires an outer '<-' in Protocol mode",
             expr.span);
        return {};
      }
      const auto *association =
          checker.output.declarationIndex->association(callee.id);
      if (isRecordIntrinsic(association)) {
        ordered |=
            association->rule != protocol::FrontendSignature::RecordUnpack;
        if (!expr.children.empty()) {
          auto source = inferredType(expr.children.front());
          const auto *nominal =
              source ? checker.types.typeDeclaration(*source) : nullptr;
          ordered |=
              nominal && (nominal->resource.has_value() ||
                          (protocol() && source->kind == T::LogicalRecord &&
                           !nominal->roles.empty()));
        }
      } else {
        ordered |=
            callee.kind == Declaration::Kind::Oracle ||
            callee.kind == Declaration::Kind::Protocol ||
            callee.kind == Declaration::Kind::Local ||
            callee.kind == Declaration::Kind::EntryFunction ||
            (callee.generated && callee.generated->operation.has_value());
      }
    }
    if (bindingPattern && bindingPatternRoot == id) {
      auto source = inferredType(id);
      if (source)
        ordered |= retiresCustody(*bindingPattern, *source);
    }
    if ((ordered && orderedRoot != id) || (!ordered && orderedRoot == id)) {
      fail("source.action",
           ordered
               ? "ordered action requires the outer '<-' position"
               : "'<-' requires an ordered action; use '=' for a pure value",
           expr.span);
      return {};
    }
  }
  std::optional<ValueId> result;
  if (expr.kind == K::FinishIf) {
    fail("source.mode", "protocol action requires a complete let statement",
         expr.span);
    return {};
  }
  if (expr.kind == K::RoleAssembly)
    result = assembleRoles(expr, depth);
  else if (oracleMode)
    result = oracle(expr, depth);
  else if (expr.kind == K::And || expr.kind == K::Or) {
    result = boolean(expr, depth);
  } else if (expr.kind == K::Kernel) {
    result = kernel(expr, depth);
  } else if (expr.kind == K::Intrinsic) {
    result = intrinsic(expr, depth);

  } else if (expr.kind == K::Map) {
    result = bulk(expr, depth);
  } else if (auto selected = inference->callees.find(id);
             selected != inference->callees.end() &&
             selected->second.reference.category ==
                 ResolutionCategory::ServiceMethod) {
    const auto &target = selected->second;
    const auto *method = checker.index().serviceAssociation(target.declaration);
    if (!protocol() || !method || expr.children.size() != 1) {
      fail("source.service", "managed query requires Protocol mode", expr.span);
      return {};
    }
    auto root = service(syntax.expressions[expr.children.front()]);
    if (!root)
      return {};
    const auto &port = body.services[root->index];
    if (!active({port.owner}, expr.span))
      return {};
    const auto &arguments = inference->arguments.at(id);
    unsigned count = serviceStaticCount(method->signature);
    if (arguments.size() != count + 1 || arguments.front() != port.field) {
      fail("source.service", "managed request arguments differ", expr.span);
      return {};
    }
    CallBinding binding{target, arguments, {}, {}, {}, {}, {}};
    binding.roles = {port.owner};
    binding.services = {*root};
    binding.scopedSource = witnesses.calls.size();
    witnesses.calls.push_back(std::make_shared<
                              ScopedCallSource>(ScopedCallSource{
        {decl.id, target.declaration, id, {}, {}, arguments, target.reference},
        {},
        {},
        {}}));
    result = emit(
        ServiceQuery{
            *root,
            count >= 1 ? std::optional(arguments[1].dimension) : std::nullopt,
            count == 2 ? std::optional(arguments[2].dimension) : std::nullopt},
        serviceResult(method->signature, port.field), {port.owner}, expr.span);
    if (result)
      body.operations.back().binding = std::move(binding);
  } else if (expr.kind == K::Name) {
    auto p = place(id, depth);
    if (!p)
      return {};
    result = p->first;
  } else if (expr.kind == K::Projection ||
             (expr.kind == K::Subscript && !inference->callees.count(id))) {
    auto p = place(id, depth);
    if (!p)
      return {};
    auto type =
        projected(body.values[p->first.index].type, p->second, expr.span);
    if (!type || !use(p->first, expr.span, p->second))
      return {};
    result = emit(Projection{p->first, p->second}, *type, components(p->first),
                  expr.span);
  } else if (expr.kind == K::Boolean || expr.kind == K::Decimal) {
    Type type;
    if (expr.kind == K::Decimal) {
      if (!expected ||
          (expected->kind != T::Field && expected->kind != T::Index)) {
        fail("source.inference",
             "numeric literal needs a unique field or index context",
             expr.span);
        return {};
      }
      type = *expected;
      if (type.kind == T::Index) {
        uint64_t number;
        if (StringRef(expr.text).getAsInteger(10, number)) {
          fail("source.literal", "index literal overflows uint64", expr.span);
          return {};
        }
        if (local())
          result = emit(
              LocalPrimitive{"index.constant", {}, {std::to_string(number)}},
              type, {}, expr.span);
        else
          result = emit(MathValue{MathematicalIdentity::IndexConstant,
                                  {},
                                  std::to_string(number)},
                        type, math() ? std::vector<unsigned>{} : allRoles(),
                        expr.span);
      } else {
        if (type.symbolic) {
          if (auto error = protocol::checkGenericParameters("field.constant",
                                                            {expr.text})) {
            fail("source.literal", toString(std::move(error)), expr.span);
            return {};
          }
        } else if (auto error = protocol::checkParameters(
                       "field.constant", {expr.text}, type.domain)) {
          fail("source.literal", toString(std::move(error)), expr.span);
          return {};
        }
      }
    }
    if (!result) {
      if (local())
        result = emit(LocalPrimitive{expr.kind == K::Boolean ? "bool.constant"
                                                             : "field.constant",
                                     {},
                                     {expr.text}},
                      type, {}, expr.span);
      else
        result = emit(MathValue{expr.kind == K::Boolean
                                    ? MathematicalIdentity::BooleanConstant
                                    : MathematicalIdentity::FieldConstant,
                                {},
                                expr.text},
                      type, math() ? std::vector<unsigned>{} : allRoles(),
                      expr.span);
    }
  } else if (expr.kind == K::Call)
    result = call(expr, depth);
  else if (expr.kind == K::Tuple || expr.kind == K::Array ||
           expr.kind == K::Record)
    result = construct(expr, expected, depth);
  else if (expr.kind == K::Block)
    result = block(expr, expected, allowUntypedStop);
  else if (expr.kind == K::For && protocol()) {
    if (repeat(expr))
      result = pack({}, expr.span);
  } else if (expr.kind == K::If || expr.kind == K::Match || expr.kind == K::For)
    result = control(expr, expected, depth, allowUntypedStop);
  else
    result = call(expr, depth);
  if (result && expected && body.values[result->index].type != *expected) {
    fail("source.type", "expression type does not match context", expr.span);
    return {};
  }
  return result;
}
std::optional<ValueId> BodyChecker::construct(const Expression &expr,
                                              std::optional<Type> expected,
                                              unsigned depth) {
  using E = Expression::Kind;
  using T = Type::Kind;
  Type type;
  std::vector<TypeField> fields;
  if (expr.kind == E::Tuple) {
    type = Type(expr.children.empty() ? T::Unit : T::Tuple);
    if (expected) {
      if (expected->kind != type.kind) {
        fail("source.type", "tuple does not match expected type", expr.span);
        return {};
      }
      type = *expected;
    }
    if (!expected)
      type.arguments.resize(expr.children.size());
    if (type.arguments.size() != expr.children.size()) {
      fail("source.type", "tuple arity differs", expr.span);
      return {};
    }
    for (unsigned i = 0; i < type.arguments.size(); ++i)
      fields.push_back({std::to_string(i), type.arguments[i], true, expr.span});
  } else if (expr.kind == E::Array) {
    type = Type(T::Array);
    type.dimension = Natural::constant(expr.children.size());
    std::optional<Type> element;
    if (expected && expected->kind == T::Array) {
      type = *expected;
      element = type.arguments.front();
    } else
      for (auto child : expr.children) {
        element = inferredType(child);
        if (element || checker.types.diagnostic)
          break;
      }
    if (!element) {
      if (!checker.types.diagnostic)
        fail("source.inference", "array literal needs an element type",
             expr.span);
      return {};
    }
    if (type.dimension != Natural::constant(expr.children.size())) {
      fail("source.type", "array literal length differs", expr.span);
      return {};
    }
    type.arguments = {*element};
    for (unsigned i = 0; i < expr.children.size(); ++i)
      fields.push_back({std::to_string(i), *element, true, expr.span});
  } else {
    type =
        inference->expressions.at(uint32_t(&expr - syntax.expressions.data()));
    if (type.kind != T::Record && type.kind != T::LogicalRecord) {
      fail("source.type", "named field constructor requires a record",
           expr.span);
      return {};
    }
    auto fs = checker.types.fields(type, expr.span);
    if (!fs)
      return {};
    fields = std::move(*fs);
    const auto *definition = checker.types.typeDeclaration(type);
    if (definition && definition->generated &&
        !definition->generated->constructible) {
      fail("source.host-result", "native result records are projection-only",
           expr.span);
      return {};
    }
    if ((restricted(type) ||
         llvm::any_of(fields, [](auto &f) { return !f.isPublic; })) &&
        !checker.types.constructorAllowed(decl, type)) {
      fail("source.private",
           "record constructor is private to its defining module", expr.span);
      return {};
    }
  }
  if (fields.size() != expr.children.size()) {
    fail("source.field", "constructor field count differs", expr.span);
    return {};
  }
  std::optional<ValuePlacement> productPlacement;
  if ((type.kind == T::Tuple || type.kind == T::Array) && contextualPlacement &&
      std::holds_alternative<ProductPlacement>(contextualPlacement->value))
    productPlacement = *contextualPlacement;
  const auto *definition = checker.types.typeDeclaration(type);
  const auto *structuralSchema =
      contextualPlacementSchema
          ? std::get_if<ProductPlacement>(&contextualPlacementSchema->value)
          : nullptr;
  if (type.kind == T::LogicalRecord && definition &&
      !definition->roles.empty()) {
    if (contextualPlacement)
      productPlacement = *contextualPlacement;
    if (expr.roles) {
      SyntaxType target;
      target.name = expr.text;
      target.arguments = expr.arguments;
      target.labels = expr.staticLabels;
      target.roles = expr.roles;
      target.span = expr.span;
      auto explicitType = checker.placedType(decl, target);
      if (!explicitType || !explicitType->placement)
        return {};
      if (productPlacement && *productPlacement != *explicitType->placement) {
        fail("source.placement",
             "constructor role application differs from context", expr.span);
        return {};
      }
      productPlacement = explicitType->placement;
    }
  }
  if (expr.roles && !productPlacement && type.kind != T::LogicalRecord) {
    fail("source.roles", "role application requires a distributed constructor",
         expr.span);
    return {};
  }
  std::vector<ValueId> values(fields.size());
  std::map<std::string, unsigned> fieldIndices;
  if (expr.kind == E::Record)
    for (unsigned i = 0; i < fields.size(); ++i)
      fieldIndices.emplace(fields[i].name, i);
  std::set<unsigned> assigned;
  for (unsigned i = 0; i < expr.children.size(); ++i) {
    unsigned index = i;
    if (expr.kind == E::Record) {
      auto found = fieldIndices.find(expr.labels[i]);
      if (found == fieldIndices.end()) {
        fail("source.field", "unknown constructor field", expr.span);
        return {};
      }
      index = found->second;
    }
    if (!assigned.insert(index).second) {
      fail("source.duplicate", "duplicate constructor field", expr.span);
      return {};
    }
    // Evaluate each field exactly once, in source order.
    const bool inferred = expr.kind == E::Tuple && !expected;
    const ValuePlacement *schema = nullptr;
    if (!productPlacement) {
      if (expr.kind == E::Record && fields[index].placement)
        schema = &*fields[index].placement;
      else if (structuralSchema)
        schema = &structuralSchema->fields[type.kind == T::Array ? 0 : index];
    }
    auto v = expression(
        expr.children[i],
        inferred ? std::nullopt : std::optional<Type>(fields[index].type),
        depth + 1, false,
        productPlacement
            ? std::optional(std::get<ProductPlacement>(productPlacement->value)
                                .fields[type.kind == T::Array ? 0 : index])
            : std::nullopt,
        schema);
    if (!v || !use(*v, expr.span))
      return {};
    if (inferred)
      type.arguments[index] = body.values[v->index].type;
    values[index] = *v;
  }
  auto selectFields = [&] {
    const auto &product = std::get<ProductPlacement>(productPlacement->value);
    for (unsigned i = 0; i < values.size(); ++i) {
      const auto &field = product.fields[type.kind == T::Array ? 0 : i];
      if (!matchPlacement(values[i], field, expr.span))
        return false;
      const auto *data = std::get_if<DataPlacement>(&field.value);
      auto available = components(values[i]);
      if (!data || !available.owners.empty() || available.roles == data->roles)
        continue;
      // The authored field has already transferred above. Retain its selected
      // components explicitly without evaluating or moving that operand twice.
      auto selected =
          emit(Restriction{values[i], data->roles},
               body.values[values[i].index].type, data->roles, expr.span);
      if (!selected || !use(*selected, expr.span))
        return false;
      values[i] = *selected;
    }
    return true;
  };
  if ((isLogicalValue(type) || productPlacement || structuralSchema) &&
      (type.kind == T::Tuple || type.kind == T::Array)) {
    if (!productPlacement) {
      ProductPlacement schema{typeIdentity(type), {}, {}};
      std::set<unsigned> roles;
      for (auto id : values) {
        const auto &value = body.values[id.index];
        const auto *legacy = checker.types.typeDeclaration(value.type);
        if (value.type.kind == T::LogicalRecord && legacy &&
            legacy->roles.empty()) {
          fail("source.oracle-boundary",
               "legacy logical families require separate ports", expr.span);
          return {};
        }
        if (!value.placement) {
          fail("source.placement-inference",
               "product child has no concrete placement", expr.span);
          return {};
        }
        auto participation = placementRoles(*value.placement);
        roles.insert(participation.begin(), participation.end());
        if (type.kind == T::Array && !schema.fields.empty()) {
          if (schema.fields[0] != *value.placement) {
            fail("source.placement",
                 "array elements have different placed identities", expr.span);
            return {};
          }
        } else
          schema.fields.push_back(*value.placement);
      }
      schema.arguments.assign(roles.begin(), roles.end());
      productPlacement =
          checker.types.placement(type, schema, decl.roles.size(), expr.span);
      if (!productPlacement)
        return {};
    }
    if (!selectFields())
      return {};
    return emit(Construct{std::move(values), {}}, type,
                placementRoles(*productPlacement), expr.span, productPlacement);
  }
  const auto *nominal = checker.types.typeDeclaration(type);
  if (!local() && nominal && nominal->resource &&
      !(protocol() && type.kind == T::LogicalRecord && orderedRoot &&
        *orderedRoot == uint32_t(&expr - syntax.expressions.data()))) {
    fail("source.mode", "resource construction requires local mode", expr.span);
    return {};
  }
  if (type.kind == T::LogicalRecord && nominal && !nominal->roles.empty()) {
    if (!protocol()) {
      fail("source.oracle-boundary",
           "distributed construction requires protocol mode", expr.span);
      return {};
    }
    if (!productPlacement)
      productPlacement = inferRecordPlacement(type, fields, values, expr.span);
    if (!productPlacement)
      return {};
    if (!selectFields())
      return {};
    auto roles = placementRoles(*productPlacement);
    return emit(Construct{std::move(values), {}}, type, roles, expr.span,
                productPlacement);
  }
  if (type.kind == T::LogicalRecord) {
    if (!protocol() || !checker.types.logicalRecord(type, expr.span)) {
      if (!checker.types.diagnostic)
        fail("source.oracle-boundary",
             "logical record construction requires protocol mode", expr.span);
      return {};
    }
    // Only direct logical fields determine the family. Ordinary operands must
    // cover that entire family, even if their representation has no leaves.
    std::optional<unsigned> holder;
    std::vector<unsigned> family;
    for (unsigned i = 0; i < fields.size(); ++i) {
      if (!isOracleHandle(fields[i].type))
        continue;
      const auto &value = body.values[values[i].index];
      auto available = components(values[i]);
      if (!value.oracleHolder || !available.owners.empty()) {
        fail("source.oracle-role",
             "logical field has no concrete custody family", expr.span);
        return {};
      }
      if (!holder) {
        holder = value.oracleHolder;
        family = std::move(available.roles);
      } else if (holder != value.oracleHolder || family != available.roles) {
        fail("source.oracle-role",
             "logical fields must have identical holder and receiver families",
             expr.span);
        return {};
      }
    }
    if (!holder) {
      fail("source.oracle-aggregate",
           "logical record has no direct oracle field", expr.span);
      return {};
    }
    for (unsigned i = 0; i < fields.size(); ++i)
      if (!isOracleHandle(fields[i].type) &&
          !demand(values[i], family, expr.span))
        return {};
    return emit(Construct{std::move(values), {}}, type, family, expr.span);
  }
  // Unit has no operands from which to derive placement. Retain its expected
  // scope, including an empty distributed record's exact repacking payload.
  if (protocol() && type.kind == T::Unit && contextualPlacement &&
      std::holds_alternative<DataPlacement>(contextualPlacement->value))
    return emit(Construct{std::move(values), {}}, type,
                placementRoles(*contextualPlacement), expr.span,
                *contextualPlacement);
  auto components = combine(values, expr.span);
  if (!components)
    return {};
  return emit(Construct{std::move(values), {}}, type, *components, expr.span);
}
} // namespace zkc::language::detail
