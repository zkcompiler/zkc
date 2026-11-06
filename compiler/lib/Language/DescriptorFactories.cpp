#include "DescriptorFactories.h"
#include "Arguments.h"
#include "CallableConstraints.h"
#include "Checker.h"
#include "DataRequirements.h"
#include "DescriptorFrames.h"
#include "DescriptorPatterns.h"
#include "zkc/Contracts/Instances.h"
#include "llvm/ADT/STLExtras.h"
#include <numeric>
using namespace llvm;
namespace zkc::language::detail {
std::optional<Type> descriptorSelector(Checker &checker,
                                       const Declaration &decl,
                                       const SyntaxDeclaration &syntax,
                                       uint32_t id) {
  std::function<std::optional<SyntaxType>(uint32_t, unsigned)> convert =
      [&](uint32_t index, unsigned depth) -> std::optional<SyntaxType> {
    if (index >= syntax.expressions.size())
      return {};
    const auto &expr = syntax.expressions[index];
    if (depth > checker.work.limits.expressionDepth ||
        !checker.types.charge(sizeof(SyntaxType) + 2 * expr.text.size() +
                                  2 * expr.children.size() * sizeof(SyntaxType),
                              expr.span))
      return {};
    SyntaxType result;
    result.span = expr.span;
    result.referenceSite = expr.referenceSite;
    if (expr.kind == Expression::Kind::Decimal) {
      result.kind = SyntaxType::Kind::Natural;
      result.name = expr.text;
    } else if (expr.kind == Expression::Kind::Name && !expr.binding) {
      result.kind = SyntaxType::Kind::Name;
      result.name = expr.text;
    } else if (expr.kind == Expression::Kind::Projection &&
               expr.children.size() == 1) {
      auto base = convert(expr.children.front(), depth + 1);
      if (!base || base->kind != SyntaxType::Kind::Name)
        return {};
      if (!checker.types.charge(base->name.size() + expr.text.size() + 2,
                                expr.span))
        return {};
      result.kind = SyntaxType::Kind::Name;
      result.name = base->name + "::" + expr.text;
    } else if (expr.kind == Expression::Kind::Call && expr.text == "pow2" &&
               !expr.binding && !expr.roles && expr.arguments.empty() &&
               expr.children.size() == 1 && expr.labels.empty()) {
      auto exponent = convert(expr.children.front(), depth + 1);
      if (!exponent)
        return {};
      result.kind = SyntaxType::Kind::PowerOfTwo;
      result.arguments.push_back(std::move(*exponent));
    } else {
      auto symbol = operatorSymbol(expr);
      if (expr.children.size() != 2 || (symbol != "+" && symbol != "*"))
        return {};
      result.kind =
          symbol == "+" ? SyntaxType::Kind::Add : SyntaxType::Kind::Multiply;
      for (auto child : expr.children) {
        auto value = convert(child, depth + 1);
        if (!value)
          return {};
        result.arguments.push_back(std::move(*value));
      }
    }
    return result;
  };
  auto term = convert(id, 1);
  auto result = term ? checker.type(decl, *term) : std::nullopt;
  if (!result || result->kind != Type::Kind::Natural) {
    if (!checker.types.diagnostic)
      checker.types.fail("source.descriptor-projection",
                         "sequence selector requires a static Natural",
                         syntax.expressions[id].span);
    return {};
  }
  return result;
}
std::optional<Type> descriptorCallContract(
    Checker &checker, const Declaration &owner, const SyntaxDeclaration &syntax,
    uint32_t id, llvm::function_ref<std::optional<Type>(uint32_t)> rigid) {
  const auto &expr = syntax.expressions[id];
  if (expr.text == "index")
    return {};
  auto target = checker.callable(owner, expr.text, expr.span, false, true);
  if (!target || checker.index().schemeAssociation(target->declaration))
    return {};
  const auto &callee = checker.declarations[target->declaration.index];
  if (!callee.descriptorResult && callee.outputs.size() != 1)
    return {};
  TypeInference types(checker.types);
  auto constraints =
      instantiateCallable(types, checker.types, callee, *target, expr.span);
  unsigned inherited =
      target->module && callee.parent
          ? checker.declarations[callee.parent->index].parameters.size()
          : 0;
  auto statics =
      bindArguments(checker.types,
                    argumentNames<Parameter>(
                        ArrayRef(callee.parameters).drop_front(inherited)),
                    expr.arguments.size(), expr.staticLabels, false, expr.span,
                    "source.generic");
  auto order =
      bindArguments(checker.types, inputNames(callee), expr.children.size(),
                    expr.callLabels, true, expr.span, "source.call");
  if (!statics || !order)
    return {};
  for (unsigned i = 0; i < expr.arguments.size(); ++i) {
    if (expr.arguments[i].kind == SyntaxType::Kind::Hole)
      continue;
    auto argument = checker.type(owner, expr.arguments[i]);
    if (!argument ||
        !types.equal(constraints.parameters.at(
                         callee.parameters[inherited + (*statics)[i]].atom),
                     types.known(*argument, expr.span), expr.span))
      return {};
  }
  for (unsigned i = 0; i < expr.children.size(); ++i) {
    const auto &argument = syntax.expressions[expr.children[i]];
    // Fresh aggregates are checked against the eventual signature demand;
    // their default extents/units are not rigid call evidence.
    if (argument.kind == Expression::Kind::Tuple ||
        argument.kind == Expression::Kind::Array)
      continue;
    auto known = rigid(expr.children[i]);
    if (!known)
      continue;
    const auto &slot = callee.inputOrder[(*order)[i]];
    if (slot.kind == Declaration::InputSlot::Kind::Scoped)
      continue;
    if (slot.kind == Declaration::InputSlot::Kind::Domain &&
        !isDescriptor(*known))
      if (auto item = finiteDomainElement(*known))
        known = descriptorType({DescriptorFamily::Finite, {*item}});
    auto formal =
        slot.kind == Declaration::InputSlot::Kind::Domain
            ? types.instantiate(
                  descriptorType(callee.descriptorInputs[slot.index].contract),
                  constraints.parameters, expr.span)
            : constraints.inputs[slot.index];
    if (!types.equal(formal, types.known(*known, expr.span), expr.span))
      return {};
  }
  if (!types.solve(expr.span))
    return {};
  return types.get(
      callee.descriptorResult
          ? types.instantiate(descriptorType(*callee.descriptorResult),
                              constraints.parameters, expr.span)
          : constraints.outputs.front(),
      expr.span);
}
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
std::optional<SelectedViewMember>
selectDescriptorView(Checker &checker, const Declaration &decl,
                     const SyntaxDeclaration &syntax, uint32_t id,
                     const Type &count, unsigned callDepth, bool authorBody) {
  const auto &expr = syntax.expressions[id];
  auto reject = [&]() -> std::optional<SelectedViewMember> {
    checker.types.fail("source.view-selection",
                       "expected a bare View with two descriptor ports and one "
                       "unwritten Natural binder",
                       expr.span);
    return {};
  };
  if (expr.kind != Expression::Kind::Name || expr.binding || expr.roles)
    return reject();
  auto target = checker.callable(decl, expr.text, expr.span);
  if (!target)
    return {};
  auto &member = checker.declarations[target->declaration.index];
  unsigned owner =
      member.parent
          ? checker.declarations[member.parent->index].parameters.size()
          : 0;
  if (member.kind != Declaration::Kind::View || !member.descriptorResult ||
      member.parameters.size() != owner + 1 ||
      member.parameters.back().sort != Parameter::Sort::Natural ||
      member.descriptorInputs.size() != 2 || member.inputOrder.size() != 2 ||
      !member.inputs.empty() || !member.scopedInputs.empty() ||
      !member.services.empty() || !member.roles.empty() ||
      !member.outputs.empty() ||
      (member.effectAllowance && *member.effectAllowance != EffectSummary{}))
    return reject();
  if (authorBody && !member.abstract && !checker.body(member.id, callDepth + 1))
    return {};
  unsigned inherited = target->module ? owner : 0;
  auto order = bindArguments(
      checker.types,
      argumentNames<Parameter>(
          ArrayRef(member.parameters).slice(inherited, owner - inherited)),
      expr.arguments.size(), expr.staticLabels, false, expr.span,
      "source.view-selection");
  if (!order)
    return {};
  if (!checker.types.charge(member.parameters.size() * sizeof(Type) +
                                owner * sizeof(bool),
                            expr.span))
    return {};
  std::vector<Type> arguments(member.parameters.size());
  std::vector<bool> assigned(owner);
  if (target->module) {
    auto bindings = checker.types.boundMemberSubstitution(
        member, *target->module, expr.span);
    if (!bindings)
      return {};
    for (unsigned i = 0; i < owner; ++i) {
      auto found = bindings->find(member.parameters[i].atom);
      if (found == bindings->end())
        return reject();
      if (!checker.types.chargeType(found->second, expr.span))
        return {};
      arguments[i] = found->second;
      assigned[i] = true;
    }
  }
  for (unsigned i = 0; i < expr.arguments.size(); ++i) {
    auto value = checker.type(decl, expr.arguments[i]);
    if (!value)
      return {};
    auto slot = inherited + (*order)[i];
    arguments[slot] = std::move(*value);
    assigned[slot] = true;
  }
  auto enclosing = checker.enclosingParameters(decl, member, expr.span);
  if (!enclosing)
    return {};
  for (unsigned i = 0; i < owner; ++i) {
    if (assigned[i])
      continue;
    if (!(*enclosing)[i])
      return reject();
    const auto &parameter = member.parameters[i];
    if (!checker.types.charge(
            2 * (parameter.atom.size() + parameter.domainSort.size()) +
                parameter.arguments.size() * sizeof(Type),
            expr.span))
      return {};
    for (const auto &argument : parameter.arguments)
      if (!checker.types.chargeType(argument, expr.span))
        return {};
    arguments[i] = parameterType(parameter);
  }
  if (!checker.types.charge(2 * member.parameters[owner].atom.size(),
                            expr.span))
    return {};
  arguments[owner] = parameterType(member.parameters[owner]);
  auto substitution =
      descriptorSubstitution(checker.types, member, arguments, expr.span);
  if (!substitution)
    return {};
  if (!checker.types.checkArguments(member, arguments, expr.span, &decl))
    return {};
  auto k = checker.types.substitute(member.descriptorInputs[0].contract,
                                    *substitution, expr.span);
  auto a = checker.types.substitute(member.descriptorInputs[1].contract,
                                    *substitution, expr.span);
  auto output = checker.types.substitute(*member.descriptorResult,
                                         *substitution, expr.span);
  if (!k || !a || !output || *output != *a)
    return reject();
  auto depends = [&](const Type &type) {
    if (!checker.types.charge(2 * sizeof(const Type *), expr.span))
      return true;
    std::vector<const Type *> pending{&type};
    while (!pending.empty()) {
      const auto *node = pending.back();
      pending.pop_back();
      if (!checker.types.charge(
              2 * node->arguments.size() * sizeof(const Type *) + 1, expr.span))
        return true;
      if (node->domain == member.parameters[owner].atom)
        return true;
      for (const auto &[factors, coefficient] : node->dimension.terms())
        for (const auto &factor : factors)
          if (factor.name == member.parameters[owner].atom)
            return true;
      for (const auto &child : node->arguments)
        pending.push_back(&child);
    }
    return false;
  };
  if (depends(descriptorType(*k)) || depends(descriptorType(*a)))
    return reject();
  for (const auto &bound : member.bounds) {
    auto left = descriptorNaturalTerm(checker.types, bound.lhs, expr.span),
         right = descriptorNaturalTerm(checker.types, bound.rhs, expr.span);
    if (!left || !right)
      return {};
    auto l = checker.types.substitute(*left, *substitution, expr.span);
    auto r = checker.types.substitute(*right, *substitution, expr.span);
    if (!l || !r)
      return {};
    auto canceled =
        checker.types.naturals.cancelCommonTerms(l->dimension, r->dimension);
    if (!canceled) {
      checker.types.accept(canceled.takeError(), expr.span);
      return {};
    }
    left->dimension = std::move(canceled->first);
    right->dimension = std::move(canceled->second);
    bool dependent = depends(*left) || depends(*right);
    if (!checker.types.charge(sizeof(Declaration) + (decl.bounds.size() + 1) *
                                                        sizeof(NaturalBound),
                              expr.span))
      return {};
    Declaration available;
    available.bounds.reserve(decl.bounds.size() + 1);
    for (const auto &premise : decl.bounds) {
      auto a = descriptorNaturalTerm(checker.types, premise.lhs, expr.span),
           b = descriptorNaturalTerm(checker.types, premise.rhs, expr.span);
      if (!a || !b)
        return {};
      available.bounds.push_back(
          {std::move(a->dimension), std::move(b->dimension), premise.span});
    }
    if (dependent) {
      auto next = checker.types.naturals.add(arguments[owner].dimension,
                                             Natural::constant(1));
      if (!next) {
        checker.types.accept(next.takeError(), expr.span);
        return {};
      }
      auto maximum =
          descriptorNaturalTerm(checker.types, count.dimension, expr.span);
      if (!maximum)
        return {};
      available.bounds.push_back(
          {std::move(*next), std::move(maximum->dimension), expr.span});
    }
    if (!checker.types.structuralAssumptions(
            available,
            {std::move(l->dimension), std::move(r->dimension), bound.span}, {},
            expr.span, dependent ? "source.view-step-bound" : "source.bound"))
      return {};
  }
  return SelectedViewMember{std::move(*target), std::move(arguments), owner,
                            std::move(*k), std::move(*a)};
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
bool matches(const DescriptorContract &contract, Constructor ctor,
             unsigned dataCount, function_ref<const Type &(unsigned)> input,
             unsigned childCount,
             function_ref<const DescriptorContract &(unsigned)> child) {
  auto *item = finiteDescriptorItem(contract);
  if (!item)
    return false;
  const Type index(Type::Kind::Index);
  const auto &result = *item;
  auto data = [&](unsigned count) {
    return dataCount == count && childCount == 0;
  };
  auto pair = [&] {
    // Match the complete Tuple identity head without copying either child.
    // Family and permission assumptions do not enter ordinary Type equality.
    return result.kind == Type::Kind::Tuple && result.arguments.size() == 2 &&
           result.domain.empty() && result.sort.empty() &&
           result.dimension == Natural() && !result.symbolic;
  };
  switch (ctor.kind) {
  case Kind::Elements:
    return data(1) && collectionElement(input(0)) == result;
  case Kind::Indices:
    return data(1) && result == index &&
           (matrix(input(0)) ||
            (ctor.axis == 0 && (collectionElement(input(0)) ||
                                input(0).kind == Type::Kind::Array)));
  case Kind::Range:
    return data(2) && result == index && input(0) == index && input(1) == index;
  case Kind::Zip:
  case Kind::Product: {
    if (dataCount || childCount != 2 || !pair())
      return false;
    for (unsigned i = 0; i < 2; ++i) {
      auto *element = finiteDescriptorItem(child(i));
      if (!element || *element != result.arguments[i])
        return false;
    }
    return true;
  }
  case Kind::MatrixRow:
  case Kind::MatrixColumn:
    return data(2) && matrix(input(0)) && input(1) == index &&
           input(0).arguments.front() == result;
  case Kind::MatrixCoordinates:
    return data(1) && pair() && matrix(input(0)) &&
           result.arguments[0] == index && result.arguments[1] == index;
  case Kind::SourceArray:
    return data(1) && input(0).kind == Type::Kind::Array &&
           !input(0).arguments.empty() && input(0).arguments.front() == result;
  case Kind::Parameter:
  case Kind::Application:
  case Kind::StructuralProduct:
  case Kind::Sequence:
  case Kind::ProductProjection:
  case Kind::SequenceProjection:
  case Kind::Append:
  case Kind::Concat:
  case Kind::Replace:
  case Kind::ForgetExtent:
  case Kind::CheckExtent:
  case Kind::Fold:
    return false;
  }
  llvm_unreachable("domain constructor kind");
}
bool matches(const Declaration &decl, Constructor ctor) {
  return decl.descriptorResult &&
         matches(
             *decl.descriptorResult, ctor, decl.inputs.size(),
             [&](unsigned i) -> const Type & { return decl.inputs[i].type; },
             decl.descriptorInputs.size(),
             [&](unsigned i) -> const DescriptorContract & {
               return decl.descriptorInputs[i].contract;
             });
}

class Composition {
  Checker &checker;
  Declaration &decl;
  const SyntaxDeclaration &syntax;
  DescriptorDefinition &definition;
  std::vector<DescriptorBinding> &bindings;
  std::map<BindingId, ValueId> data;
  std::map<BindingId, unsigned> domains;
  unsigned callDepth;
  std::function<const Type *(ValueId)> dataType;
  std::function<std::optional<ValueId>(uint32_t, const std::optional<Type> &)>
      evaluate;
  bool refuse(Span span, StringRef message) {
    return checker.types.fail("source.finite-domain", message, span);
  }
  std::optional<Type> rigid(uint32_t id, unsigned depth = 1,
                            bool aggregates = false) {
    const auto &expr = syntax.expressions[id];
    if (depth > checker.work.limits.expressionDepth ||
        !checker.types.charge(1, expr.span))
      return {};
    if (expr.kind == Expression::Kind::Name && expr.binding) {
      auto found = domains.find(*expr.binding);
      if (found != domains.end()) {
        const auto &type = descriptorType(bindings[found->second].contract);
        return checker.types.chargeType(type, expr.span) ? std::optional(type)
                                                         : std::nullopt;
      }
      auto input = data.find(*expr.binding);
      if (input != data.end()) {
        const auto *type = dataType(input->second);
        return type && checker.types.chargeType(*type, expr.span)
                   ? std::optional(*type)
                   : std::nullopt;
      }
    }
    if (expr.kind == Expression::Kind::Call && !expr.binding)
      return descriptorCallContract(
          checker, decl, syntax, id,
          [&](uint32_t child) { return rigid(child, depth + 1); });
    if (aggregates && !expr.children.empty() &&
        (expr.kind == Expression::Kind::Tuple ||
         expr.kind == Expression::Kind::Array)) {
      bool product = expr.kind == Expression::Kind::Tuple;
      if (!checker.types.charge(expr.children.size() * sizeof(Type) +
                                    2 * sizeof(Type),
                                expr.span))
        return {};
      Type result(product ? Type::Kind::DescriptorProduct
                          : Type::Kind::DescriptorSequence);
      std::optional<Type> element;
      for (unsigned pass = 0; pass < 2; ++pass) {
        for (auto child : expr.children) {
          auto known = rigid(child, depth + 1, pass != 0);
          if (!known) {
            if (product && pass)
              return {};
            continue;
          }
          if (!isDescriptor(*known))
            return {};
          if (product) {
            if (pass)
              result.arguments.push_back(std::move(*known));
          } else if (!element)
            element = std::move(*known);
          else if (*element != *known)
            return {};
        }
        if (!product && element)
          break;
      }
      if (!product) {
        if (!element)
          return {};
        result.arguments.push_back(std::move(*element));
        Type extent(Type::Kind::Natural);
        extent.dimension = Natural::constant(expr.children.size());
        result.arguments.push_back(std::move(extent));
      }
      return result;
    }
    // Fresh aggregates contribute no rigid sibling evidence. Their defaults
    // are considered only after all names and declared results were inspected.
    return {};
  }
  std::optional<unsigned> aggregate(uint32_t id, unsigned depth,
                                    const std::optional<Type> &expected) {
    const auto &expr = syntax.expressions[id];
    const bool product = expr.kind == Expression::Kind::Tuple;
    const auto head = product ? Type::Kind::DescriptorProduct
                              : Type::Kind::DescriptorSequence;
    if (product && expr.children.empty() && !expected) {
      checker.types.fail("source.descriptor-category",
                         "fresh unit needs a descriptor product expectation",
                         expr.span);
      return {};
    }
    if (expected && expected->kind != head) {
      checker.types.fail("source.descriptor-category",
                         "aggregate category differs", expr.span);
      return {};
    }
    if (product && expected &&
        expected->arguments.size() != expr.children.size()) {
      checker.types.fail("source.descriptor-contract",
                         "ordered product arity differs", expr.span);
      return {};
    }
    std::optional<Type> element;
    if (!product && expected)
      element = expected->arguments.front();
    if (!product && !element) {
      for (auto child : expr.children) {
        auto known = rigid(child, depth + 1);
        if (!known)
          continue;
        if (!isDescriptor(*known)) {
          checker.types.fail("source.descriptor-category",
                             "descriptor list contains data", expr.span);
          return {};
        }
        if (element && *element != *known) {
          checker.types.fail("source.descriptor-contract",
                             "sequence element contracts differ", expr.span);
          return {};
        }
        element = std::move(*known);
      }
    }
    if (!product && !element)
      for (auto child : expr.children)
        if (auto known = rigid(child, depth + 1, true)) {
          if (element && *element != *known) {
            checker.types.fail("source.descriptor-contract",
                               "nested sequence evidence differs", expr.span);
            return {};
          }
          element = std::move(*known);
        }
    if (!checker.types.charge(
            expr.children.size() * (sizeof(DescriptorEdge) + 1) + 1, expr.span))
      return {};
    std::vector<DescriptorEdge> children;
    Type contract(head);
    for (unsigned i = 0; i < expr.children.size(); ++i) {
      auto demand = product ? expected ? std::optional(expected->arguments[i])
                                       : std::nullopt
                            : element;
      auto child = expression(expr.children[i], depth + 1, demand);
      if (!child)
        return {};
      const auto &actual = bindings[*child].contract;
      if (!product && element && *element != descriptorType(actual)) {
        checker.types.fail("source.descriptor-contract",
                           "sequence element contracts differ", expr.span);
        return {};
      }
      if (!product && !element)
        element = descriptorType(actual);
      children.push_back({*child, actual});
      if (product)
        contract.arguments.push_back(descriptorType(actual));
    }
    if (!product) {
      if (!element) {
        checker.types.fail(
            "source.descriptor-inference",
            "empty descriptor sequence needs an element contract", expr.span);
        return {};
      }
      contract.arguments.push_back(*element);
      if (expected)
        contract = *expected;
      else {
        Type length(Type::Kind::Natural);
        length.dimension = Natural::constant(expr.children.size());
        contract.arguments.push_back(std::move(length));
      }
      if (contract.arguments.size() == 2 &&
          contract.arguments[1].dimension !=
              Natural::constant(children.size())) {
        checker.types.fail("source.descriptor-contract",
                           "sequence literal extent differs", expr.span);
        return {};
      }
    }
    DescriptorBinding binding{product ? Kind::StructuralProduct
                                      : Kind::Sequence,
                              DescriptorContract(std::move(contract)),
                              {},
                              std::move(children),
                              0,
                              {},
                              expr.span};
    binding.expression = id;
    auto result = bindings.size();
    bindings.push_back(std::move(binding));
    return result;
  }
  std::optional<SelectedViewMember> selection(uint32_t id, const Type &count) {
    return selectDescriptorView(checker, decl, syntax, id, count, callDepth,
                                true);
  }
  std::optional<unsigned> scheme(uint32_t id, unsigned depth,
                                 const CallableReference &target,
                                 const std::optional<Type> &expected) {
    const auto &expr = syntax.expressions[id];
    const auto *signature =
        checker.index().schemeAssociation(target.declaration);
    const auto *form = checker.index().schemeDefinition(target.declaration);
    if (!signature || !form || !syntax.layoutSyntax)
      return {};
    auto staticOrder =
        bindArguments(checker.types,
                      argumentNames<protocol::SourceStatic>(signature->statics),
                      expr.arguments.size(), expr.staticLabels, true, expr.span,
                      "source.generic");
    auto order = bindArguments(
        checker.types,
        argumentNames<protocol::NamedSchemePort>(signature->inputs),
        expr.children.size(), expr.callLabels, true, expr.span, "source.call");
    if (!staticOrder || !order)
      return {};
    std::vector<Type> statics(signature->statics.size());
    for (unsigned i = 0; i < expr.arguments.size(); ++i) {
      auto value = checker.type(decl, expr.arguments[i]);
      if (!value || value->kind != Type::Kind::Natural) {
        if (!checker.types.diagnostic)
          checker.types.fail("source.generic",
                             "structural static must be an explicit Natural",
                             expr.span);
        return {};
      }
      statics[(*staticOrder)[i]] = std::move(*value);
    }
    DescriptorPatterns patterns(checker.types, statics, form->variables.size(),
                                expr.span);
    auto match = [&](const protocol::PatternRef &p, const Type &t) {
      return patterns.match(p, t);
    };
    auto instantiate = [&](const protocol::PatternRef &p) {
      return patterns.instantiate(p);
    };
    auto &extents = patterns.extents;
    if (expected && !match(signature->output, *expected))
      return {};
    std::vector<unsigned> expressions(expr.children.size());
    for (unsigned i = 0; i < expr.children.size(); ++i)
      expressions[(*order)[i]] = expr.children[i];
    std::optional<SelectedViewMember> selected;
    for (unsigned i = 0; i < signature->inputs.size(); ++i)
      if (auto *port = std::get_if<protocol::SelectedViewPort>(
              &signature->inputs[i].port)) {
        selected = selection(expressions[i], statics.front());
        if (!selected ||
            !match(port->context, descriptorType(selected->context)) ||
            !match(port->state, descriptorType(selected->state)))
          return {};
      }
    for (unsigned i = 0; i < signature->inputs.size(); ++i)
      if (auto *port = std::get_if<protocol::DescriptorPort>(
              &signature->inputs[i].port)) {
        auto known = rigid(expressions[i], depth + 1);
        if (known && !match(port->contract, *known))
          return {};
      }
    std::vector<DescriptorEdge> children(signature->inputs.size() -
                                         (selected ? 1 : 0));
    for (unsigned i = 0; i < expr.children.size(); ++i) {
      auto slot = (*order)[i];
      auto *port =
          std::get_if<protocol::DescriptorPort>(&signature->inputs[slot].port);
      if (!port)
        continue;
      auto demand = instantiate(port->contract);
      // OptionalExtent is solved by the literal's actual size, independently
      // of required source-written statics. An unsolved extent is not None.
      if (!demand)
        if (auto *sequence =
                std::get_if<protocol::SequencePattern>(&port->contract->value))
          if (auto *extent =
                  std::get_if<protocol::ExtentVariable>(&sequence->extent)) {
            const auto &literal = syntax.expressions[expressions[slot]];
            if (literal.kind == Expression::Kind::Array) {
              Type length(Type::Kind::Natural);
              length.dimension = Natural::constant(literal.children.size());
              extents[extent->variable].emplace(std::move(length));
              demand = instantiate(port->contract);
            }
          }
      auto value = expression(expressions[slot], depth + 1, demand);
      if (!value ||
          !match(port->contract, descriptorType(bindings[*value].contract)))
        return {};
      children[slot - (selected ? 1 : 0)] = {*value, bindings[*value].contract};
    }
    auto result = instantiate(signature->output);
    if (!result) {
      checker.types.fail(
          "source.descriptor-inference",
          "installed scheme has an unresolved descriptor contract", expr.span);
      return {};
    }
    using Form = protocol::DescriptorForm;
    Kind kind;
    switch (form->form) {
    case Form::Append:
      kind = Kind::Append;
      break;
    case Form::Concat:
      kind = Kind::Concat;
      break;
    case Form::Replace:
      kind = Kind::Replace;
      break;
    case Form::ForgetExtent:
      kind = Kind::ForgetExtent;
      break;
    case Form::CheckExtent:
      kind = Kind::CheckExtent;
      break;
    case Form::Fold:
      kind = Kind::Fold;
      break;
    }
    DescriptorBinding binding{kind,
                              DescriptorContract(*result),
                              {},
                              std::move(children),
                              0,
                              {},
                              expr.span,
                              target,
                              std::move(statics),
                              *order,
                              id};
    binding.selectedView = std::move(selected);
    auto index = bindings.size();
    bindings.push_back(std::move(binding));
    return index;
  }
  std::optional<unsigned> expression(uint32_t id, unsigned depth,
                                     std::optional<Type> expected = {}) {
    const auto &expr = syntax.expressions[id];
    if (depth > checker.work.limits.expressionDepth ||
        !checker.types.charge(1, expr.span)) {
      checker.types.fail("source.limit", "domain composition depth exceeded",
                         expr.span);
      return {};
    }
    if (expr.kind == Expression::Kind::Name && expr.binding) {
      auto found = domains.find(*expr.binding);
      if (found != domains.end()) {
        if (expected &&
            *expected != descriptorType(bindings[found->second].contract)) {
          checker.types.fail("source.descriptor-contract",
                             "bound descriptor contract differs", expr.span);
          return {};
        }
        return found->second;
      }
      auto input = data.find(*expr.binding);
      if (input != data.end() && expected &&
          finiteDescriptorItem(DescriptorContract(*expected)))
        return collectionDomain(checker.types, *dataType(input->second),
                                input->second, bindings, id, expr.span);
      checker.types.fail("source.descriptor-category",
                         "expected a descriptor binding", expr.span);
      return {};
    }
    if (syntax.layoutSyntax && (expr.kind == Expression::Kind::Tuple ||
                                expr.kind == Expression::Kind::Array))
      return aggregate(id, depth, expected);
    if (syntax.layoutSyntax && (expr.kind == Expression::Kind::Projection ||
                                expr.kind == Expression::Kind::Subscript)) {
      auto base = expression(expr.children.front(), depth + 1);
      if (!base)
        return {};
      const auto &contract = descriptorType(bindings[*base].contract);
      std::optional<Type> index;
      unsigned component = 0;
      Type result;
      Kind kind;
      if (contract.kind == Type::Kind::DescriptorProduct &&
          expr.kind == Expression::Kind::Projection &&
          !StringRef(expr.text).getAsInteger(10, component) &&
          component < contract.arguments.size()) {
        result = contract.arguments[component];
        kind = Kind::ProductProjection;
      } else if (contract.kind == Type::Kind::DescriptorSequence &&
                 expr.kind == Expression::Kind::Subscript &&
                 expr.children.size() == 2) {
        index = descriptorSelector(checker, decl, syntax, expr.children[1]);
        if (!index)
          return {};
        if (contract.arguments.size() == 2 && index->dimension.isClosed() &&
            contract.arguments[1].dimension.isClosed() &&
            index->dimension.closedValue() >=
                contract.arguments[1].dimension.closedValue()) {
          checker.types.fail("source.descriptor-projection",
                             "sequence index is outside its extent", expr.span);
          return {};
        }
        result = contract.arguments.front();
        kind = Kind::SequenceProjection;
      } else {
        checker.types.fail("source.descriptor-projection",
                           "wrong structural projection or product component",
                           expr.span);
        return {};
      }
      DescriptorBinding binding{
          kind,      DescriptorContract(std::move(result)),
          {},        {{*base, bindings[*base].contract}},
          component, {},
          expr.span};
      binding.expression = id;
      if (index)
        binding.arguments.push_back(std::move(*index));
      auto selected = bindings.size();
      bindings.push_back(std::move(binding));
      return selected;
    }
    if (expr.kind != Expression::Kind::Call || expr.binding || expr.roles) {
      refuse(expr.span, "domain factories compose typed constructors");
      return {};
    }
    auto target = checker.callable(decl, expr.text, expr.span, true, true);
    if (!target)
      return {};
    if (checker.index().schemeAssociation(target->declaration))
      return scheme(id, depth, *target, expected);
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
    if (expected &&
        !types.equal(types.instantiate(descriptorType(*callee.descriptorResult),
                                       constraints.parameters, expr.span),
                     types.known(*expected, expr.span), expr.span))
      return {};
    // Rigid siblings constrain every port before any fresh aggregate defaults.
    for (unsigned i = 0; i < expr.children.size(); ++i) {
      auto slot = callee.inputOrder[(*order)[i]];
      auto known = rigid(expr.children[i], depth + 1);
      if (!known)
        continue;
      if (slot.kind == Declaration::InputSlot::Kind::Domain &&
          !isDescriptor(*known))
        if (auto item = finiteDomainElement(*known))
          known = descriptorType({DescriptorFamily::Finite, {*item}});
      auto parameter =
          slot.kind == Declaration::InputSlot::Kind::Domain
              ? types.instantiate(
                    descriptorType(
                        callee.descriptorInputs[slot.index].contract),
                    constraints.parameters, expr.span)
              : constraints.inputs[slot.index];
      if (!types.equal(parameter, types.known(*known, expr.span), expr.span))
        return {};
    }
    std::vector<ValueId> operands(callee.inputs.size());
    std::vector<unsigned> descriptorArguments(callee.descriptorInputs.size());
    for (unsigned i = 0; i < expr.children.size(); ++i) {
      auto slot = callee.inputOrder[(*order)[i]];
      const auto &argument = syntax.expressions[expr.children[i]];
      if (slot.kind == Declaration::InputSlot::Kind::Domain) {
        auto demand = types.get(
            types.instantiate(
                descriptorType(callee.descriptorInputs[slot.index].contract),
                constraints.parameters, argument.span),
            argument.span);
        auto value = expression(expr.children[i], depth + 1, demand);
        if (!value ||
            !types.equal(types.instantiate(
                             descriptorType(
                                 callee.descriptorInputs[slot.index].contract),
                             constraints.parameters, argument.span),
                         types.known(descriptorType(bindings[*value].contract),
                                     argument.span),
                         argument.span))
          return {};
        descriptorArguments[slot.index] = *value;
      } else if (slot.kind == Declaration::InputSlot::Kind::Data) {
        auto found =
            argument.binding ? data.find(*argument.binding) : data.end();
        std::optional<ValueId> value;
        if (evaluate) {
          auto expected =
              types.get(constraints.inputs[slot.index], argument.span);
          if (!checker.types.diagnostic)
            value = evaluate(expr.children[i], expected);
        } else if (argument.kind == Expression::Kind::Name &&
                   found != data.end())
          value = found->second;
        if (!value) {
          if (!checker.types.diagnostic)
            refuse(argument.span,
                   "factory data operands require a checked data value");
          return {};
        }
        auto actual = dataType(*value);
        if (!actual ||
            !types.equal(constraints.inputs[slot.index],
                         types.known(*actual, argument.span), argument.span))
          return {};
        operands[slot.index] = *value;
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
      if (!checker.types.structuralAssumptions(decl, bound, substitution,
                                               expr.span))
        return {};
    return instantiateDescriptor(checker.types, callee, *target, *arguments,
                                 operands, descriptorArguments, *order,
                                 bindings, id, expr.span);
  }

public:
  Composition(Checker &checker, Declaration &decl,
              DescriptorDefinition &definition, unsigned depth)
      : checker(checker), decl(decl), syntax(*checker.sources[decl.id.index]),
        definition(definition), bindings(definition.bindings), callDepth(depth),
        dataType([&decl](ValueId value) -> const Type * {
          return &decl.inputs.at(value.index).type;
        }) {
    for (unsigned i = 0; i < decl.inputs.size(); ++i)
      data.emplace(syntax.inputBindings[i], ValueId{i});
    for (unsigned i = 0; i < decl.descriptorInputs.size(); ++i)
      domains.emplace(syntax.descriptorBindings[i], i);
  }
  Composition(Checker &checker, Declaration &decl,
              const SyntaxDeclaration &syntax, DescriptorDefinition &definition,
              unsigned depth, std::vector<DescriptorBinding> &bindings,
              const std::map<BindingId, unsigned> &domains,
              const std::map<BindingId, ValueId> &data,
              std::function<const Type *(ValueId)> dataType,
              std::function<std::optional<ValueId>(uint32_t,
                                                   const std::optional<Type> &)>
                  evaluate)
      : checker(checker), decl(decl), syntax(syntax), definition(definition),
        bindings(bindings), data(data), domains(domains), callDepth(depth),
        dataType(std::move(dataType)), evaluate(std::move(evaluate)) {}
  std::optional<unsigned> author(uint32_t id, std::optional<Type> expected) {
    return expression(id, 1, std::move(expected));
  }
  bool run() {
    const auto &body = syntax.bodies.front();
    if (!body.operators.empty() || body.stopped || body.results.size() != 1)
      return refuse(body.span, "domain factory returns one constructor recipe");
    for (const auto &statement : body.statements) {
      if (statement.kind != Statement::Kind::Let || statement.mutableBinding ||
          statement.roles || statement.owner || statement.exchange ||
          statement.pattern.kind != Pattern::Kind::Name ||
          !statement.pattern.binding)
        return refuse(statement.span,
                      "domain factory bindings are immutable domain names");
      auto expected =
          statement.type ? checker.type(decl, *statement.type) : std::nullopt;
      if (statement.type && !expected)
        return false;
      auto value = expression(statement.expression, 1, expected);
      if (!value)
        return false;
      domains.emplace(*statement.pattern.binding, *value);
      definition.statements.emplace_back(statement.expression, *value);
    }
    auto result = expression(body.results.front().second, 1,
                             descriptorType(*decl.descriptorResult));
    if (!result)
      return false;
    if (bindings[*result].contract != *decl.descriptorResult)
      return refuse(body.span, "descriptor factory result contract differs");
    definition.result = *result;
    return true;
  }
};
} // namespace
bool descriptorConstructorSignature(const Declaration &declaration,
                                    DescriptorBinding::Kind kind,
                                    unsigned axis) {
  return matches(declaration, Constructor{kind, axis});
}
bool finiteConstructorSignature(
    const DescriptorContract &contract, DescriptorBinding::Kind kind,
    unsigned axis, unsigned dataCount,
    function_ref<const Type &(unsigned)> data, unsigned childCount,
    function_ref<const DescriptorContract &(unsigned)> child) {
  for (const auto &row : protocol::instances::domainConstructors()) {
    auto installed = constructor(row.identity);
    if (installed && installed->kind == kind && installed->axis == axis)
      return matches(contract, *installed, dataCount, data, childCount, child);
  }
  return false;
}
std::optional<unsigned> authorDescriptorExpression(
    Checker &checker, Declaration &decl, const SyntaxDeclaration &syntax,
    std::vector<DescriptorBinding> &bindings,
    const std::map<BindingId, unsigned> &domains,
    const std::map<BindingId, ValueId> &data,
    std::function<const Type *(ValueId)> dataType,
    std::function<std::optional<ValueId>(uint32_t, const std::optional<Type> &)>
        evaluate,
    uint32_t id, unsigned callDepth, std::optional<Type> expected) {
  DescriptorDefinition definition;
  auto result =
      Composition(checker, decl, syntax, definition, callDepth, bindings,
                  domains, data, std::move(dataType), std::move(evaluate))
          .author(id, std::move(expected));
  return result;
}
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
