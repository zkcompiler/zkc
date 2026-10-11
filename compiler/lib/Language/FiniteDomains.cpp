#include "FiniteDomains.h"
#include "Arguments.h"
#include "CallableConstraints.h"
#include "Checker.h"
#include "llvm/ADT/STLExtras.h"
#include <numeric>
using namespace llvm;
namespace zkc::language::detail {
namespace {
using Kind = DomainBinding::Kind;
struct Constructor {
  Kind kind;
  unsigned axis;
};
std::optional<Constructor> constructor(StringRef name) {
  if (name == "elements")
    return Constructor{Kind::Elements, 0};
  if (name == "indices" || name == "indices.rows")
    return Constructor{Kind::Indices, 0};
  if (name == "indices.columns")
    return Constructor{Kind::Indices, 1};
  if (name == "range")
    return Constructor{Kind::Range, 0};
  if (name == "zip")
    return Constructor{Kind::Zip, 0};
  if (name == "product")
    return Constructor{Kind::Product, 0};
  if (name == "matrix.row")
    return Constructor{Kind::MatrixRow, 0};
  if (name == "matrix.column")
    return Constructor{Kind::MatrixColumn, 1};
  if (name == "matrix.coordinates.row_major")
    return Constructor{Kind::MatrixCoordinates, 0};
  if (name == "matrix.coordinates.column_major")
    return Constructor{Kind::MatrixCoordinates, 1};
  if (name == "source_array")
    return Constructor{Kind::SourceArray, 0};
  return {};
}
std::optional<Type> element(const Type &container) {
  if (container.kind != Type::Kind::Builtin)
    return {};
  if (container.domain == "indices" && container.arguments.empty())
    return Type(Type::Kind::Index);
  if ((container.domain == "vector" || container.domain == "groups" ||
       container.domain == "sequence") &&
      container.arguments.size() == 1)
    return container.arguments.front();
  if (container.domain == "field_array" && container.arguments.size() == 2)
    return container.arguments.front();
  return {};
}
bool matrix(const Type &type) {
  return type.kind == Type::Kind::Builtin && type.domain == "matrix" &&
         type.arguments.size() == 1;
}
bool matches(const Declaration &decl, Constructor ctor) {
  if (!decl.domainResult)
    return false;
  const Type index(Type::Kind::Index);
  const auto &result = *decl.domainResult;
  auto data = [&](unsigned count) {
    return decl.inputs.size() == count && decl.domainInputs.empty();
  };
  switch (ctor.kind) {
  case Kind::Elements:
    return data(1) && element(decl.inputs[0].type) == result;
  case Kind::Indices:
    return data(1) && result == index &&
           (matrix(decl.inputs[0].type) ||
            (ctor.axis == 0 &&
             (element(decl.inputs[0].type) ||
              decl.inputs[0].type.kind == Type::Kind::Array)));
  case Kind::Range:
    return data(2) && result == index && decl.inputs[0].type == index &&
           decl.inputs[1].type == index;
  case Kind::Zip:
  case Kind::Product: {
    if (!decl.inputs.empty() || decl.domainInputs.size() != 2)
      return false;
    Type pair(Type::Kind::Tuple);
    for (const auto &domain : decl.domainInputs)
      pair.arguments.push_back(domain.item);
    return result == pair;
  }
  case Kind::MatrixRow:
  case Kind::MatrixColumn:
    return data(2) && matrix(decl.inputs[0].type) &&
           decl.inputs[1].type == index &&
           decl.inputs[0].type.arguments.front() == result;
  case Kind::MatrixCoordinates: {
    Type pair(Type::Kind::Tuple);
    pair.arguments = {index, index};
    return data(1) && matrix(decl.inputs[0].type) && result == pair;
  }
  case Kind::SourceArray:
    return data(1) && decl.inputs[0].type.kind == Type::Kind::Array &&
           decl.inputs[0].type.arguments.front() == result;
  case Kind::Parameter:
  case Kind::Application:
    return false;
  }
  llvm_unreachable("domain constructor kind");
}

class Composition {
  Checker &checker;
  Declaration &decl;
  const SyntaxDeclaration &syntax;
  DomainDefinition &definition;
  std::map<BindingId, ValueId> data;
  std::map<BindingId, unsigned> domains;
  unsigned callDepth;
  bool refuse(Span span, StringRef message) {
    return checker.types.fail("source.finite-domain", message, span);
  }
  std::optional<unsigned> expression(uint32_t id, unsigned depth) {
    const auto &expr = syntax.expressions[id];
    if (depth > checker.work.limits.expressionDepth ||
        !checker.types.charge(1, expr.span)) {
      checker.types.fail("source.limit", "domain composition depth exceeded",
                         expr.span);
      return {};
    }
    if (expr.kind == Expression::Kind::Name && expr.binding) {
      auto found = domains.find(*expr.binding);
      if (found != domains.end())
        return found->second;
      refuse(expr.span, "expected a finite domain binding");
      return {};
    }
    if (expr.kind != Expression::Kind::Call || expr.binding || expr.roles) {
      refuse(expr.span, "domain factories compose typed constructors");
      return {};
    }
    auto target = checker.callable(decl, expr.text, expr.span);
    if (!target)
      return {};
    auto &callee = checker.output.declarations[target->declaration.index];
    if (callee.kind != Declaration::Kind::DomainFunction ||
        !callee.domainResult) {
      refuse(expr.span, "domain composition requires a defined domain factory");
      return {};
    }
    if (!callee.abstract && !checker.body(callee.id, callDepth + 1))
      return {};
    checker.bodyHeights[decl.id.index] =
        std::max(checker.bodyHeights[decl.id.index],
                 checker.bodyHeights[callee.id.index] + 1);
    TypeInference types(checker.types);
    auto constraints =
        instantiateCallable(types, checker.types, callee, *target, expr.span);
    unsigned inherited = target->component && callee.parent
                             ? checker.output.declarations[callee.parent->index]
                                   .parameters.size()
                             : 0;
    auto statics =
        bindArguments(checker.types,
                      argumentNames<Parameter>(
                          ArrayRef(callee.parameters).drop_front(inherited)),
                      expr.arguments.size(), expr.staticLabels, false,
                      expr.span, "source.generic");
    auto order =
        bindArguments(checker.types, inputNames(callee), expr.children.size(),
                      expr.callLabels, true, expr.span, "source.call");
    if (!statics || !order)
      return {};
    for (unsigned i = 0; i < expr.arguments.size(); ++i) {
      if (expr.arguments[i].kind == SyntaxType::Kind::Hole)
        continue;
      auto argument = checker.type(decl, expr.arguments[i]);
      if (!argument ||
          !types.equal(constraints.parameters.at(
                           callee.parameters[inherited + (*statics)[i]].atom),
                       types.known(*argument, expr.span), expr.span))
        return {};
    }
    std::vector<ValueId> operands(callee.inputs.size());
    std::vector<unsigned> domainArguments(callee.domainInputs.size());
    for (unsigned i = 0; i < expr.children.size(); ++i) {
      auto slot = callee.inputOrder[(*order)[i]];
      const auto &argument = syntax.expressions[expr.children[i]];
      if (slot.kind == Declaration::InputSlot::Kind::Domain) {
        auto value = expression(expr.children[i], depth + 1);
        if (!value ||
            !types.equal(
                types.instantiate(callee.domainInputs[slot.index].item,
                                  constraints.parameters, argument.span),
                types.known(definition.bindings[*value].item, argument.span),
                argument.span))
          return {};
        domainArguments[slot.index] = *value;
      } else if (slot.kind == Declaration::InputSlot::Kind::Data) {
        auto found =
            argument.binding ? data.find(*argument.binding) : data.end();
        if (argument.kind != Expression::Kind::Name || found == data.end()) {
          refuse(
              argument.span,
              "factory data operands name inputs; evaluate other expressions "
              "at the factory call");
          return {};
        }
        operands[slot.index] = found->second;
        if (!types.equal(constraints.inputs[slot.index],
                         types.known(decl.inputs[found->second.index].type,
                                     argument.span),
                         argument.span))
          return {};
      } else {
        refuse(argument.span, "invalid domain factory input category");
        return {};
      }
    }
    if (!types.solve(expr.span))
      return {};
    auto arguments =
        callableArguments(types, checker.types, callee, constraints, expr.span);
    if (!arguments) {
      if (!checker.types.diagnostic)
        checker.types.fail("source.inference",
                           "cannot infer domain factory static arguments",
                           expr.span);
      return {};
    }
    Substitution substitution;
    for (const auto &[name, variable] : constraints.parameters) {
      auto value = types.get(variable, expr.span);
      if (!value)
        return {};
      substitution.emplace(name, *value);
    }
    if (!checker.types.checkArguments(callee, *arguments, expr.span, &decl,
                                      substitution))
      return {};
    for (const auto &bound : callee.bounds)
      if (!checker.types.assumptions(decl, bound, substitution, expr.span))
        return {};
    return instantiateDomain(
        checker.types, callee, *target, *arguments, operands, domainArguments,
        *order, definition.bindings, definition.applications, expr.span);
  }

public:
  Composition(Checker &checker, Declaration &decl, DomainDefinition &definition,
              unsigned depth)
      : checker(checker), decl(decl), syntax(*checker.sources[decl.id.index]),
        definition(definition), callDepth(depth) {
    for (unsigned i = 0; i < decl.inputs.size(); ++i)
      data.emplace(syntax.inputBindings[i], ValueId{i});
    for (unsigned i = 0; i < decl.domainInputs.size(); ++i)
      domains.emplace(syntax.domainBindings[i], i);
  }
  bool run() {
    const auto &body = syntax.bodies.front();
    if (!body.operators.empty() || body.stopped || body.results.size() != 1)
      return refuse(body.span, "domain factory returns one constructor recipe");
    for (const auto &statement : body.statements) {
      if (statement.kind != Statement::Kind::Let || statement.mutableBinding ||
          statement.type || statement.roles || statement.owner ||
          statement.exchange || statement.pattern.kind != Pattern::Kind::Name ||
          !statement.pattern.binding)
        return refuse(statement.span,
                      "domain factory bindings are immutable domain names");
      auto value = expression(statement.expression, 1);
      if (!value)
        return false;
      domains.emplace(*statement.pattern.binding, *value);
    }
    auto result = expression(body.results.front().second, 1);
    if (!result)
      return false;
    if (definition.bindings[*result].item != *decl.domainResult)
      return refuse(body.span, "domain factory result item differs");
    definition.result = *result;
    return true;
  }
};
} // namespace
std::optional<unsigned>
instantiateDomain(Semantics &types, const Declaration &callee,
                  const CallableReference &target, ArrayRef<Type> arguments,
                  ArrayRef<ValueId> operands, ArrayRef<unsigned> domains,
                  ArrayRef<unsigned> order,
                  std::vector<DomainBinding> &bindings,
                  std::vector<DomainApplication> &applications, Span span) {
  if (!types.charge(operands.size() + domains.size() + order.size() + 1, span))
    return {};
  auto substitution = types.substitution(callee, arguments);
  if (target.component && callee.parent) {
    auto inherited =
        types.boundMemberSubstitution(callee, *target.component, span);
    if (!inherited)
      return {};
    for (const auto &[name, value] : *inherited)
      substitution.insert_or_assign(name, value);
  }
  auto item = types.substitute(*callee.domainResult, substitution, span);
  if (!item)
    return {};
  // Keep the lexical factory boundary through checking. Specialization selects
  // abstract members and closes the complete recipe, including unused nodes
  // that belong to this factory's admission. Caller-local unused domains remain
  // separate. Eager data arguments have already executed at their call sites.
  unsigned result = bindings.size();
  bindings.push_back({Kind::Application,
                      *item,
                      operands.vec(),
                      domains.vec(),
                      0,
                      {},
                      span,
                      target,
                      arguments.vec(),
                      order.vec()});
  applications.push_back({target, arguments.vec(), operands.vec(),
                          domains.vec(), order.vec(), result, span});
  return result;
}
bool Checker::domainBody(Declaration &decl, unsigned depth) {
  const auto &syntax = *sources[decl.id.index];
  for (const auto &input : decl.inputs) {
    auto permissions = types.permissions(input.type, input.span, &decl);
    if (!permissions)
      return false;
    if (!permissions->copy || !permissions->drop)
      return types.fail("source.finite-domain",
                        "domain operands require Copy and Drop", input.span);
  }
  auto definition = std::make_shared<DomainDefinition>();
  for (unsigned i = 0; i < decl.domainInputs.size(); ++i)
    definition->bindings.push_back({Kind::Parameter,
                                    decl.domainInputs[i].item,
                                    {},
                                    {},
                                    0,
                                    i,
                                    decl.domainInputs[i].span});
  if (!syntax.domainConstructor) {
    if (!Composition(*this, decl, *definition, depth).run())
      return false;
    decl.domainDefinition = std::move(definition);
    return true;
  }
  auto selected = constructor(*syntax.domainConstructor);
  if (!selected || !matches(decl, *selected))
    return types.fail("source.finite-domain",
                      "written signature differs from the domain constructor",
                      decl.span);
  definition->constructor = selected->kind;
  definition->axis = selected->axis;
  DomainBinding result{
      selected->kind, *decl.domainResult, {}, {}, selected->axis, {},
      decl.span};
  for (unsigned i = 0; i < decl.inputs.size(); ++i)
    result.operands.push_back({i});
  for (unsigned i = 0; i < decl.domainInputs.size(); ++i)
    result.children.push_back(i);
  definition->result = definition->bindings.size();
  definition->bindings.push_back(std::move(result));
  decl.domainDefinition = std::move(definition);
  return true;
}
} // namespace zkc::language::detail
