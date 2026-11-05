#include "DescriptorFactories.h"
#include "Arguments.h"
#include "CallableConstraints.h"
#include "Checker.h"
#include "DataRequirements.h"
#include "zkc/Contracts/Instances.h"
#include "llvm/ADT/STLExtras.h"
#include <numeric>
using namespace llvm;
namespace zkc::language::detail {
std::optional<Type> finiteDomainElement(const Type &type) {
  return type.kind == Type::Kind::Array && type.arguments.size() == 1
             ? std::optional(type.arguments.front())
             : collectionElement(type);
}
std::optional<unsigned>
collectionDomain(Semantics &types, const Type &type, ValueId value,
                 std::vector<DescriptorBinding> &bindings, uint32_t expression,
                 Span span) {
  auto item = finiteDomainElement(type);
  if (!item) {
    types.fail("source.finite-domain",
               "expected a finite domain or a collection with an element "
               "traversal; matrices require an explicit view",
               span);
    return {};
  }
  if (!types.chargeType(*item, span) || !types.charge(1, span))
    return {};
  DescriptorBinding binding{type.kind == Type::Kind::Array
                                ? DescriptorBinding::Kind::SourceArray
                                : DescriptorBinding::Kind::Elements,
                            {DescriptorFamily::Finite, {*item}},
                            {value},
                            {},
                            0,
                            {},
                            span};
  binding.expression = expression;
  auto index = bindings.size();
  bindings.push_back(std::move(binding));
  return index;
}
namespace {
using Kind = DescriptorBinding::Kind;
struct Constructor {
  Kind kind;
  unsigned axis;
};
// The identity names a catalog domain constructor, which owns its kind and
// axis.
std::optional<Constructor> constructor(StringRef name) {
  using Declared = protocol::instances::DomainConstructorKind;
  for (const auto &row : protocol::instances::domainConstructors()) {
    if (row.identity != name)
      continue;
    switch (row.kind) {
    case Declared::Elements:
      return Constructor{Kind::Elements, row.axis};
    case Declared::Indices:
      return Constructor{Kind::Indices, row.axis};
    case Declared::Range:
      return Constructor{Kind::Range, row.axis};
    case Declared::Zip:
      return Constructor{Kind::Zip, row.axis};
    case Declared::Product:
      return Constructor{Kind::Product, row.axis};
    case Declared::MatrixRow:
      return Constructor{Kind::MatrixRow, row.axis};
    case Declared::MatrixColumn:
      return Constructor{Kind::MatrixColumn, row.axis};
    case Declared::MatrixCoordinates:
      return Constructor{Kind::MatrixCoordinates, row.axis};
    case Declared::SourceArray:
      return Constructor{Kind::SourceArray, row.axis};
    }
    llvm_unreachable("domain constructor kind");
  }
  return {};
}
// A rank-two collection, traversed through its explicit matrix view.
bool matrix(const Type &type) {
  return collectionElement(type, /*matrix=*/true).has_value();
}
bool matches(const Declaration &decl, Constructor ctor) {
  auto *item = decl.descriptorResult
                   ? finiteDescriptorItem(*decl.descriptorResult)
                   : nullptr;
  if (!item)
    return false;
  const Type index(Type::Kind::Index);
  const auto &result = *item;
  auto data = [&](unsigned count) {
    return decl.inputs.size() == count && decl.descriptorInputs.empty();
  };
  switch (ctor.kind) {
  case Kind::Elements:
    return data(1) && collectionElement(decl.inputs[0].type) == result;
  case Kind::Indices:
    return data(1) && result == index &&
           (matrix(decl.inputs[0].type) ||
            (ctor.axis == 0 &&
             (collectionElement(decl.inputs[0].type) ||
              decl.inputs[0].type.kind == Type::Kind::Array)));
  case Kind::Range:
    return data(2) && result == index && decl.inputs[0].type == index &&
           decl.inputs[1].type == index;
  case Kind::Zip:
  case Kind::Product: {
    if (!decl.inputs.empty() || decl.descriptorInputs.size() != 2)
      return false;
    Type pair(Type::Kind::Tuple);
    for (const auto &domain : decl.descriptorInputs) {
      auto *child = finiteDescriptorItem(domain.contract);
      if (!child)
        return false;
      pair.arguments.push_back(*child);
    }
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
  DescriptorDefinition &definition;
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
      auto input = data.find(*expr.binding);
      if (input != data.end())
        return collectionDomain(
            checker.types, decl.inputs[input->second.index].type, input->second,
            definition.bindings, id, expr.span);
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
    if (callee.kind != Declaration::Kind::View || !callee.descriptorResult) {
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
    unsigned inherited = target->module && callee.parent
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
    std::vector<unsigned> descriptorArguments(callee.descriptorInputs.size());
    for (unsigned i = 0; i < expr.children.size(); ++i) {
      auto slot = callee.inputOrder[(*order)[i]];
      const auto &argument = syntax.expressions[expr.children[i]];
      if (slot.kind == Declaration::InputSlot::Kind::Domain) {
        auto value = expression(expr.children[i], depth + 1);
        if (!value ||
            !types.equal(types.instantiate(
                             descriptorType(
                                 callee.descriptorInputs[slot.index].contract),
                             constraints.parameters, argument.span),
                         types.known(descriptorType(
                                         definition.bindings[*value].contract),
                                     argument.span),
                         argument.span))
          return {};
        descriptorArguments[slot.index] = *value;
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
    return instantiateDescriptor(checker.types, callee, *target, *arguments,
                                 operands, descriptorArguments, *order,
                                 definition.bindings, id, expr.span);
  }

public:
  Composition(Checker &checker, Declaration &decl,
              DescriptorDefinition &definition, unsigned depth)
      : checker(checker), decl(decl), syntax(*checker.sources[decl.id.index]),
        definition(definition), callDepth(depth) {
    for (unsigned i = 0; i < decl.inputs.size(); ++i)
      data.emplace(syntax.inputBindings[i], ValueId{i});
    for (unsigned i = 0; i < decl.descriptorInputs.size(); ++i)
      domains.emplace(syntax.descriptorBindings[i], i);
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
    if (definition.bindings[*result].contract != *decl.descriptorResult)
      return refuse(body.span, "descriptor factory result contract differs");
    definition.result = *result;
    return true;
  }
};
} // namespace
std::optional<unsigned>
instantiateDescriptor(Semantics &types, const Declaration &callee,
                      const CallableReference &target, ArrayRef<Type> arguments,
                      ArrayRef<ValueId> operands, ArrayRef<unsigned> domains,
                      ArrayRef<unsigned> order,
                      std::vector<DescriptorBinding> &bindings,
                      uint32_t expression, Span span) {
  if (!callee.descriptorResult || operands.size() != callee.inputs.size() ||
      domains.size() != callee.descriptorInputs.size() ||
      order.size() != callee.inputOrder.size()) {
    types.fail("source.descriptor",
               "factory argument or result contract differs", span);
    return {};
  }
  if (!types.charge(operands.size() + domains.size() + order.size() + 1, span))
    return {};
  auto substitution = types.substitution(callee, arguments);
  if (target.module && callee.parent) {
    auto inherited =
        types.boundMemberSubstitution(callee, *target.module, span);
    if (!inherited)
      return {};
    for (const auto &[name, value] : *inherited)
      substitution.insert_or_assign(name, value);
  }
  auto contract =
      types.substitute(*callee.descriptorResult, substitution, span);
  if (!contract)
    return {};
  std::vector<DescriptorEdge> children;
  for (unsigned i = 0; i < domains.size(); ++i) {
    auto expected = types.substitute(callee.descriptorInputs[i].contract,
                                     substitution, span);
    if (!expected || domains[i] >= bindings.size() ||
        *expected != bindings[domains[i]].contract) {
      if (!types.diagnostic)
        types.fail("source.descriptor", "factory child contract differs", span);
      return {};
    }
    children.push_back({domains[i], std::move(*expected)});
  }
  // Keep the lexical factory boundary through checking. Specialization selects
  // abstract members and closes the complete recipe, including unused nodes
  // that belong to this factory's admission. Caller-local unused domains remain
  // separate. Eager data arguments have already executed at their call sites.
  unsigned result = bindings.size();
  bindings.push_back({Kind::Application,
                      *contract,
                      operands.vec(),
                      std::move(children),
                      0,
                      {},
                      span,
                      target,
                      arguments.vec(),
                      order.vec(),
                      expression});
  return result;
}
bool checkViewStructure(Checker &checker, const Declaration &decl,
                        const SyntaxDeclaration &syntax) {
  auto refuse = [&](Span span) {
    return checker.types.fail(
        "source.view", "View requires structural formation or exact forwarding",
        span);
  };
  if (!decl.services.empty() || syntax.primitive || syntax.finiteDefinition ||
      (decl.effectAllowance && *decl.effectAllowance != EffectSummary{}))
    return refuse(decl.span);
  for (const auto &region : syntax.bodies) {
    if (!checker.types.charge(region.statements.size() +
                                  region.operators.size() + 1,
                              region.span))
      return false;
    if (region.stopped || !region.operators.empty())
      return refuse(region.span);
    for (const auto &statement : region.statements)
      if (statement.kind != Statement::Kind::Let || statement.mutableBinding ||
          statement.evaluation == Statement::Evaluation::Ordered)
        return refuse(statement.span);
  }
  for (const auto &expr : syntax.expressions) {
    if (!checker.types.charge(expr.children.size() + 1, expr.span))
      return false;
    switch (expr.kind) {
    case Expression::Kind::Name:
    case Expression::Kind::Projection:
    case Expression::Kind::Boolean:
    case Expression::Kind::Decimal:
      break;
    case Expression::Kind::Tuple:
      if (!expr.children.empty())
        return refuse(expr.span);
      break;
    case Expression::Kind::Call: {
      if (expr.binding || expr.roles)
        return refuse(expr.span);
      auto target = checker.callable(decl, expr.text, expr.span);
      if (!target)
        return false;
      const auto &callee =
          checker.output.declarations[target->declaration.index];
      if (callee.kind != Declaration::Kind::View || callee.descriptorResult)
        return refuse(expr.span);
      break;
    }
    default:
      return refuse(expr.span);
    }
  }
  return true;
}
bool Checker::domainBody(Declaration &decl, unsigned depth) {
  const auto &syntax = *sources[decl.id.index];
  auto definition = std::make_shared<DescriptorDefinition>();
  for (unsigned i = 0; i < decl.descriptorInputs.size(); ++i)
    definition->bindings.push_back({Kind::Parameter,
                                    decl.descriptorInputs[i].contract,
                                    {},
                                    {},
                                    0,
                                    i,
                                    decl.descriptorInputs[i].span});
  if (!syntax.domainConstructor) {
    if (!Composition(*this, decl, *definition, depth).run())
      return false;
    decl.descriptorDefinition = std::move(definition);
    return true;
  }
  auto selected = constructor(*syntax.domainConstructor);
  if (!selected || !matches(decl, *selected))
    return types.fail("source.finite-domain",
                      "written signature differs from the domain constructor",
                      decl.span);
  definition->constructor = selected->kind;
  definition->axis = selected->axis;
  DescriptorBinding result{
      selected->kind, *decl.descriptorResult, {}, {}, selected->axis, {},
      decl.span};
  for (unsigned i = 0; i < decl.inputs.size(); ++i)
    result.operands.push_back({i});
  for (unsigned i = 0; i < decl.descriptorInputs.size(); ++i)
    result.children.push_back({i, decl.descriptorInputs[i].contract});
  definition->result = definition->bindings.size();
  definition->bindings.push_back(std::move(result));
  decl.descriptorDefinition = std::move(definition);
  return true;
}
void Checker::beginViewReconstruction() {
  installContractInference(/*signaturesOnly=*/false);
  installAdmissionCollection(/*signaturesOnly=*/false);
  bodyState.assign(output.declarations.size(), 2);
  bodyHeights.assign(output.declarations.size(), 1);
}
void Checker::prepareViewReconstruction(DeclarationId id,
                                        const SyntaxDeclaration &source) {
  reconstructedSources[id.index] = source;
  sources[id.index] = &reconstructedSources[id.index];
  output.declarations[id.index].descriptorDefinition.reset();
  output.declarations[id.index].body.reset();
  bodyState[id.index] = 0;
}
} // namespace zkc::language::detail
