#ifndef ZKC_LANGUAGE_DESCRIPTORSOURCEWITNESS_H
#define ZKC_LANGUAGE_DESCRIPTORSOURCEWITNESS_H
#include "Arguments.h"
#include "CallableConstraints.h"
#include "Checker.h"
#include "DescriptorFactories.h"
#include "DescriptorPatterns.h"
#include "zkc/Contracts/Instances.h"
namespace zkc::language::detail {
/// A relation over an authored expression and the actual recipe. The source
/// traversal owns coverage and order. No authoring, closure or emission
/// producer is invoked to create an expected recipe or shape.
class DescriptorSourceWitness {
  Checker &reader;
  const Declaration &owner;
  const SyntaxDeclaration &source;
  llvm::ArrayRef<DescriptorBinding> nodes;
  std::map<BindingId, unsigned> domains;
  std::map<BindingId, ValueId> data;
  std::map<uint32_t, unsigned> expressions;
  unsigned next;
  const Body *body;
  bool slice;
  std::set<unsigned> checked;
  std::optional<ValueId> dataValue(uint32_t id) {
    const auto &expr = source.expressions[id];
    if (body) {
      auto found = body->expressionValues.find(id);
      if (found != body->expressionValues.end() &&
          found->second.index < body->values.size())
        return found->second;
    }
    if (expr.binding) {
      auto found = data.find(*expr.binding);
      if (found != data.end())
        return found->second;
    }
    return {};
  }
  const Type *dataType(ValueId id) {
    if (body)
      return id.index < body->values.size() ? &body->values[id.index].type
                                            : nullptr;
    return id.index < owner.inputs.size() ? &owner.inputs[id.index].type
                                          : nullptr;
  }
  bool same(Span a, Span b) {
    return a.source.index == b.source.index && a.begin == b.begin &&
           a.end == b.end;
  }
  bool refuse(Span span) {
    return reader.types.fail(
        "source.view-witness",
        "descriptor differs from immutable authored source", span);
  }
  bool enter(unsigned depth, Span span) {
    if (!reader.types.charge(1, span))
      return false;
    return depth <= reader.work.limits.expressionDepth ||
           reader.types.fail("source.limit",
                             "descriptor source expression depth exceeded",
                             span);
  }
  std::optional<Type> finiteItem(uint32_t id, unsigned depth) {
    auto type = rigid(id, depth);
    if (!type)
      return {};
    auto span = source.expressions[id].span;
    if (isDescriptor(*type)) {
      const auto *item = finiteDescriptorItem(*type);
      if (item && reader.types.chargeType(*item, span))
        return *item;
    } else if (reader.types.chargeType(*type, span))
      return finiteDomainElement(*type);
    if (!reader.types.diagnostic)
      refuse(span);
    return {};
  }
  std::optional<Type> rigid(uint32_t id, unsigned depth = 1,
                            bool aggregates = false) {
    if (id >= source.expressions.size())
      return {};
    const auto &expr = source.expressions[id];
    if (!enter(depth, expr.span))
      return {};
    if (expr.kind == Expression::Kind::Name && expr.binding) {
      auto found = domains.find(*expr.binding);
      if (found != domains.end()) {
        if (descriptorType(nodes[found->second].contract).kind ==
                Type::Kind::Descriptor &&
            !finiteDescriptorItem(nodes[found->second].contract)) {
          refuse(expr.span);
          return {};
        }
        const auto &type = descriptorType(nodes[found->second].contract);
        return reader.types.chargeType(type, expr.span) ? std::optional(type)
                                                        : std::nullopt;
      }
      auto value = dataValue(id);
      if (value) {
        const auto *type = dataType(*value);
        return type && reader.types.chargeType(*type, expr.span)
                   ? std::optional(*type)
                   : std::nullopt;
      }
    }
    if (expr.kind == Expression::Kind::Call && !expr.binding)
      return descriptorCallContract(
          reader, owner, source, id,
          [&](uint32_t child) { return rigid(child, depth + 1); });
    if (expr.kind == Expression::Kind::DomainProduct) {
      if (expr.children.size() != 2 ||
          !reader.types.charge(4 * sizeof(Type), expr.span))
        return {};
      Type item(Type::Kind::Tuple);
      item.arguments.reserve(2);
      for (auto child : expr.children) {
        auto element = finiteItem(child, depth + 1);
        if (!element)
          return {};
        item.arguments.push_back(std::move(*element));
      }
      Type result(Type::Kind::Descriptor);
      result.arguments.push_back(std::move(item));
      return result;
    }
    // Ordinary data, including inline arrays, has already been associated
    // with its original Body value by the independent data source reader.
    if (auto value = dataValue(id)) {
      const auto *type = dataType(*value);
      if (type && reader.types.chargeType(*type, expr.span))
        return *type;
      return {};
    }
    if (aggregates && !expr.children.empty() &&
        (expr.kind == Expression::Kind::Tuple ||
         expr.kind == Expression::Kind::Array)) {
      bool product = expr.kind == Expression::Kind::Tuple;
      if (!reader.types.charge(expr.children.size() * sizeof(Type) +
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
    return {};
  }
  const DescriptorBinding *claim(uint32_t id) {
    auto found = expressions.find(id);
    if (found == expressions.end()) {
      refuse(source.expressions[id].span);
      return nullptr;
    }
    return &nodes[found->second];
  }
  bool edge(const DescriptorEdge &edge, unsigned child) {
    return edge.node == child && child < nodes.size() &&
           edge.contract == nodes[child].contract;
  }
  std::optional<unsigned> consume(uint32_t id, DescriptorBinding::Kind kind,
                                  const Type &contract,
                                  llvm::ArrayRef<unsigned> children,
                                  bool routed = false) {
    const auto &expr = source.expressions[id];
    unsigned selected = next;
    if (slice) {
      auto found = expressions.find(id);
      if (found == expressions.end()) {
        refuse(expr.span);
        return {};
      }
      selected = found->second;
    }
    if (selected >= nodes.size()) {
      refuse(expr.span);
      return {};
    }
    const auto &actual = nodes[selected];
    if (descriptorType(actual.contract).kind == Type::Kind::Descriptor &&
        !finiteDescriptorItem(actual.contract)) {
      refuse(expr.span);
      return {};
    }
    if (!reader.types.chargeContract(actual.contract, expr.span) ||
        !reader.types.charge(children.size() + actual.arguments.size() +
                                 actual.operands.size() + 1,
                             expr.span))
      return {};
    if (actual.kind != kind || descriptorType(actual.contract) != contract ||
        actual.expression != id || !same(actual.span, expr.span) ||
        actual.parameter || actual.children.size() != children.size() ||
        (!routed && (actual.factory || actual.selectedView ||
                     !actual.argumentOrder.empty())) ||
        (!routed && kind != DescriptorBinding::Kind::SequenceProjection &&
         !actual.arguments.empty()) ||
        (!routed && !actual.operands.empty())) {
      refuse(expr.span);
      return {};
    }
    for (unsigned i = 0; i < children.size(); ++i)
      if (!edge(actual.children[i], children[i])) {
        refuse(expr.span);
        return {};
      }
    if (!slice)
      ++next;
    checked.insert(selected);
    for (auto child : children)
      if (child >= selected) {
        refuse(expr.span);
        return {};
      }
    return selected;
  }
  std::optional<unsigned> aggregate(uint32_t id, unsigned depth,
                                    const Type *expected) {
    const auto &expr = source.expressions[id];
    bool product = expr.kind == Expression::Kind::Tuple;
    if (!source.layoutSyntax)
      return {};
    if (expected &&
        (expected->kind != (product ? Type::Kind::DescriptorProduct
                                    : Type::Kind::DescriptorSequence) ||
         (product && expected->arguments.size() != expr.children.size()) ||
         (!product && expected->arguments.size() != 1 &&
          expected->arguments.size() != 2))) {
      refuse(expr.span);
      return {};
    }
    if (product && expr.children.empty() && !expected) {
      refuse(expr.span);
      return {};
    }
    std::optional<Type> inferredElement;
    const Type *element = nullptr;
    if (!product) {
      if (expected)
        element = &expected->arguments.front();
      for (unsigned pass = 0; !element && pass < 2; ++pass) {
        std::optional<Type> evidence;
        for (auto child : expr.children)
          if (auto known = rigid(child, 1, pass != 0)) {
            if (!isDescriptor(*known) || (evidence && *evidence != *known)) {
              refuse(expr.span);
              return {};
            }
            evidence = std::move(*known);
          }
        inferredElement = std::move(evidence);
        if (inferredElement)
          element = &*inferredElement;
      }
      if (!element) {
        refuse(expr.span);
        return {};
      }
    }
    if (!reader.types.charge(expr.children.size() *
                                     (sizeof(unsigned) + sizeof(Type)) +
                                 2 * sizeof(Type),
                             expr.span))
      return {};
    std::vector<unsigned> children;
    Type contract(product ? Type::Kind::DescriptorProduct
                          : Type::Kind::DescriptorSequence);
    for (unsigned i = 0; i < expr.children.size(); ++i) {
      const Type *demand =
          product ? (expected ? &expected->arguments[i] : nullptr) : element;
      auto child = expression(expr.children[i], depth + 1, demand);
      if (!child)
        return {};
      children.push_back(*child);
      if (product) {
        const auto &type = descriptorType(nodes[*child].contract);
        if (!reader.types.chargeType(type, expr.span))
          return {};
        contract.arguments.push_back(type);
      }
    }
    if (!product) {
      if (!reader.types.chargeType(*element, expr.span))
        return {};
      contract.arguments.push_back(*element);
      Type extent(Type::Kind::Natural);
      extent.dimension = Natural::constant(children.size());
      if (!expected || expected->arguments.size() == 2)
        contract.arguments.push_back(extent);
    }
    if (expected && contract != *expected) {
      refuse(expr.span);
      return {};
    }
    auto result = consume(id,
                          product ? DescriptorBinding::Kind::StructuralProduct
                                  : DescriptorBinding::Kind::Sequence,
                          contract, children);
    if (result && nodes[*result].axis) {
      refuse(expr.span);
      return {};
    }
    return result;
  }
  std::optional<unsigned> scheme(uint32_t id, unsigned depth,
                                 const CallableReference &target,
                                 const Type *expected) {
    const auto &expr = source.expressions[id];
    const auto *signature =
        reader.index().schemeAssociation(target.declaration);
    const auto *form = reader.index().schemeDefinition(target.declaration);
    if (!signature || !form || !source.layoutSyntax)
      return {};
    auto staticsOrder = bindArguments(
        reader.types, argumentNames<protocol::SourceStatic>(signature->statics),
        expr.arguments.size(), expr.staticLabels, true, expr.span,
        "source.generic");
    auto order = bindArguments(
        reader.types,
        argumentNames<protocol::NamedSchemePort>(signature->inputs),
        expr.children.size(), expr.callLabels, true, expr.span, "source.call");
    if (!staticsOrder || !order)
      return {};
    std::vector<Type> statics(signature->statics.size());
    for (unsigned i = 0; i < expr.arguments.size(); ++i) {
      auto term = reader.type(owner, expr.arguments[i]);
      if (!term || term->kind != Type::Kind::Natural)
        return {};
      statics[(*staticsOrder)[i]] = std::move(*term);
    }
    DescriptorPatterns patterns(reader.types, statics, form->variables.size(),
                                expr.span);
    if (expected && !patterns.match(signature->output, *expected))
      return {};
    std::vector<uint32_t> slots(expr.children.size());
    for (unsigned i = 0; i < expr.children.size(); ++i)
      slots[(*order)[i]] = expr.children[i];
    std::optional<SelectedViewMember> selected;
    for (unsigned i = 0; i < slots.size(); ++i)
      if (auto *port = std::get_if<protocol::SelectedViewPort>(
              &signature->inputs[i].port)) {
        selected = selectDescriptorView(reader, owner, source, slots[i],
                                        statics.front(), 1, false);
        if (!selected ||
            !patterns.match(port->context, descriptorType(selected->context)) ||
            !patterns.match(port->state, descriptorType(selected->state)))
          return {};
      }
    for (unsigned i = 0; i < slots.size(); ++i)
      if (auto *port =
              std::get_if<protocol::DescriptorPort>(&signature->inputs[i].port))
        if (auto evidence = rigid(slots[i]))
          if (!patterns.match(port->contract, *evidence))
            return {};
    std::vector<unsigned> children(slots.size() - (selected ? 1 : 0));
    for (unsigned i = 0; i < expr.children.size(); ++i) {
      auto slot = (*order)[i];
      auto *port =
          std::get_if<protocol::DescriptorPort>(&signature->inputs[slot].port);
      if (!port)
        continue;
      auto demand = patterns.instantiate(port->contract);
      if (!demand)
        if (auto *sequence =
                std::get_if<protocol::SequencePattern>(&port->contract->value))
          if (auto *extent =
                  std::get_if<protocol::ExtentVariable>(&sequence->extent))
            if (source.expressions[slots[slot]].kind ==
                Expression::Kind::Array) {
              Type length(Type::Kind::Natural);
              length.dimension = Natural::constant(
                  source.expressions[slots[slot]].children.size());
              patterns.extents[extent->variable].emplace(std::move(length));
              demand = patterns.instantiate(port->contract);
            }
      auto child =
          expression(slots[slot], depth + 1, demand ? &*demand : nullptr);
      if (!child || !patterns.match(port->contract,
                                    descriptorType(nodes[*child].contract)))
        return {};
      children[slot - (selected ? 1 : 0)] = *child;
    }
    auto contract = patterns.instantiate(signature->output);
    if (!contract)
      return {};
    using Form = protocol::DescriptorForm;
    DescriptorBinding::Kind kind;
    switch (form->form) {
    case Form::Append:
      kind = DescriptorBinding::Kind::Append;
      break;
    case Form::Concat:
      kind = DescriptorBinding::Kind::Concat;
      break;
    case Form::Replace:
      kind = DescriptorBinding::Kind::Replace;
      break;
    case Form::ForgetExtent:
      kind = DescriptorBinding::Kind::ForgetExtent;
      break;
    case Form::CheckExtent:
      kind = DescriptorBinding::Kind::CheckExtent;
      break;
    case Form::Fold:
      kind = DescriptorBinding::Kind::Fold;
      break;
    }
    auto result = consume(id, kind, *contract, children, true);
    if (!result)
      return {};
    const auto &actual = nodes[*result];
    if (!actual.factory ||
        actual.factory->declaration.index != target.declaration.index ||
        actual.factory->module != target.module ||
        actual.factory->reference != target.reference ||
        actual.factory->authoredReference != target.authoredReference ||
        actual.selectedView != selected || actual.arguments != statics ||
        actual.argumentOrder != *order || !actual.operands.empty() ||
        actual.axis) {
      refuse(expr.span);
      return {};
    }
    return result;
  }

public:
  const std::set<unsigned> &coverage() const { return checked; }
  DescriptorSourceWitness(Checker &reader, const Declaration &owner,
                          const SyntaxDeclaration &source,
                          llvm::ArrayRef<DescriptorBinding> nodes,
                          std::map<BindingId, unsigned> domains = {},
                          std::map<BindingId, ValueId> data = {},
                          unsigned first = 0, const Body *body = nullptr,
                          bool slice = false)
      : reader(reader), owner(owner), source(source), nodes(nodes),
        domains(std::move(domains)), data(std::move(data)), next(first),
        body(body), slice(slice) {
    if (!reader.types.charge(
            nodes.size() *
                (sizeof(uint32_t) + sizeof(unsigned) + 4 * sizeof(void *)),
            source.span))
      return;
    for (unsigned i = first; i < nodes.size(); ++i)
      if (nodes[i].expression &&
          !expressions.emplace(*nodes[i].expression, i).second)
        refuse(nodes[i].span);
  }
  std::optional<unsigned> expression(uint32_t id, unsigned depth = 1,
                                     const Type *expected = nullptr) {
    if (id >= source.expressions.size() || !enter(depth, source.span))
      return {};
    const auto &expr = source.expressions[id];
    if (expected && finiteDescriptorItem(*expected)) {
      auto value = dataValue(id);
      auto type = value ? dataType(*value) : nullptr;
      if (type && !reader.types.chargeType(*type, expr.span))
        return {};
      auto item = type ? finiteDomainElement(*type) : std::nullopt;
      if (item && *item == *finiteDescriptorItem(*expected)) {
        const auto *actual = claim(id);
        auto kind = type->kind == Type::Kind::Array
                        ? DescriptorBinding::Kind::SourceArray
                        : DescriptorBinding::Kind::Elements;
        if (!actual || actual->kind != kind ||
            descriptorType(actual->contract) != *expected ||
            actual->operands.size() != 1 ||
            actual->operands.front().index != value->index ||
            !actual->children.empty() || actual->parameter || actual->factory ||
            actual->selectedView || actual->axis ||
            !actual->arguments.empty() || !actual->argumentOrder.empty() ||
            !same(actual->span, expr.span)) {
          refuse(expr.span);
          return {};
        }
        auto selected = expressions.at(id);
        if (!slice && selected != next++) {
          refuse(expr.span);
          return {};
        }
        checked.insert(selected);
        return selected;
      }
    }
    if (expr.kind == Expression::Kind::Name && expr.binding) {
      auto found = domains.find(*expr.binding);
      if (found == domains.end() ||
          (expected &&
           descriptorType(nodes[found->second].contract) != *expected)) {
        refuse(expr.span);
        return {};
      }
      checked.insert(found->second);
      return found->second;
    }
    if (expr.kind == Expression::Kind::DomainProduct) {
      if (expr.children.size() != 2 ||
          !reader.types.charge(5 * sizeof(Type) + 2 * sizeof(unsigned),
                               expr.span)) {
        if (!reader.types.diagnostic)
          refuse(expr.span);
        return {};
      }
      Type item(Type::Kind::Tuple);
      item.arguments.reserve(2);
      std::vector<unsigned> children;
      children.reserve(2);
      for (auto child : expr.children) {
        auto element = finiteItem(child, depth + 1);
        if (!element) {
          if (!reader.types.diagnostic)
            refuse(expr.span);
          return {};
        }
        if (!reader.types.chargeType(*element, expr.span))
          return {};
        item.arguments.push_back(*element);
        Type contract(Type::Kind::Descriptor);
        contract.arguments.push_back(std::move(*element));
        auto selected = expression(child, depth + 1, &contract);
        if (!selected)
          return {};
        children.push_back(*selected);
      }
      Type contract(Type::Kind::Descriptor);
      contract.arguments.push_back(std::move(item));
      if (expected && *expected != contract) {
        refuse(expr.span);
        return {};
      }
      return consume(id, DescriptorBinding::Kind::Product, contract, children);
    }
    if (expr.kind == Expression::Kind::Tuple ||
        expr.kind == Expression::Kind::Array)
      return aggregate(id, depth, expected);
    if (expr.kind == Expression::Kind::Projection ||
        expr.kind == Expression::Kind::Subscript) {
      auto base = expression(expr.children.front(), depth + 1);
      if (!base)
        return {};
      const auto &contract = descriptorType(nodes[*base].contract);
      const Type *result = nullptr;
      unsigned axis = 0;
      DescriptorBinding::Kind kind;
      std::optional<Type> index;
      if (expr.kind == Expression::Kind::Projection &&
          contract.kind == Type::Kind::DescriptorProduct &&
          !llvm::StringRef(expr.text).getAsInteger(10, axis) &&
          axis < contract.arguments.size()) {
        result = &contract.arguments[axis];
        kind = DescriptorBinding::Kind::ProductProjection;
      } else if (expr.kind == Expression::Kind::Subscript &&
                 contract.kind == Type::Kind::DescriptorSequence &&
                 expr.children.size() == 2) {
        index = descriptorSelector(reader, owner, source, expr.children[1]);
        if (!index)
          return {};
        result = &contract.arguments.front();
        kind = DescriptorBinding::Kind::SequenceProjection;
      } else {
        refuse(expr.span);
        return {};
      }
      auto selected = consume(id, kind, *result, {*base});
      if (!selected || nodes[*selected].axis != axis ||
          (index ? (nodes[*selected].arguments.size() != 1 ||
                    nodes[*selected].arguments.front() != *index)
                 : !nodes[*selected].arguments.empty()) ||
          (expected && *expected != *result)) {
        refuse(expr.span);
        return {};
      }
      return selected;
    }
    if (expr.kind != Expression::Kind::Call || expr.binding || expr.roles) {
      refuse(expr.span);
      return {};
    }
    auto target = reader.callable(owner, expr.text, expr.span, true, true);
    if (!target)
      return {};
    if (reader.index().schemeAssociation(target->declaration))
      return scheme(id, depth, *target, expected);
    const auto &callee = reader.declarations[target->declaration.index];
    const auto *actual = claim(id);
    if (!actual || callee.kind != Declaration::Kind::View ||
        !callee.descriptorResult || !actual->factory ||
        actual->factory->declaration.index != target->declaration.index ||
        actual->factory->module != target->module ||
        actual->factory->reference != target->reference ||
        actual->factory->authoredReference != target->authoredReference ||
        actual->arguments.size() != callee.parameters.size()) {
      refuse(expr.span);
      return {};
    }
    TypeInference inference(reader.types);
    auto constraints = instantiateCallable(inference, reader.types, callee,
                                           *target, expr.span);
    unsigned inherited =
        target->module && callee.parent
            ? reader.declarations[callee.parent->index].parameters.size()
            : 0;
    auto statics = bindArguments(
        reader.types,
        argumentNames<Parameter>(
            llvm::ArrayRef(callee.parameters).drop_front(inherited)),
        expr.arguments.size(), expr.staticLabels, false, expr.span,
        "source.generic");
    auto order =
        bindArguments(reader.types, inputNames(callee), expr.children.size(),
                      expr.callLabels, true, expr.span, "source.call");
    if (!statics || !order)
      return {};
    for (unsigned i = 0; i < expr.arguments.size(); ++i) {
      if (expr.arguments[i].kind == SyntaxType::Kind::Hole)
        continue;
      auto value = reader.type(owner, expr.arguments[i]);
      if (!value || !inference.equal(
                        constraints.parameters.at(
                            callee.parameters[inherited + (*statics)[i]].atom),
                        inference.known(*value, expr.span), expr.span))
        return {};
    }
    auto output =
        inference.instantiate(descriptorType(*callee.descriptorResult),
                              constraints.parameters, expr.span);
    if (expected &&
        !inference.equal(output, inference.known(*expected, expr.span),
                         expr.span))
      return {};
    for (unsigned i = 0; i < expr.children.size(); ++i) {
      const auto &slot = callee.inputOrder[(*order)[i]];
      if (auto evidence = rigid(expr.children[i])) {
        if (slot.kind == Declaration::InputSlot::Kind::Domain &&
            !isDescriptor(*evidence))
          if (auto item = finiteDomainElement(*evidence))
            evidence = descriptorType({DescriptorFamily::Finite, {*item}});
        auto port = slot.kind == Declaration::InputSlot::Kind::Domain
                        ? inference.instantiate(
                              descriptorType(
                                  callee.descriptorInputs[slot.index].contract),
                              constraints.parameters, expr.span)
                        : constraints.inputs[slot.index];
        if (!inference.equal(port, inference.known(*evidence, expr.span),
                             expr.span))
          return {};
      }
    }
    std::vector<unsigned> children(callee.descriptorInputs.size());
    std::vector<ValueId> operands(callee.inputs.size());
    for (unsigned i = 0; i < expr.children.size(); ++i) {
      const auto &slot = callee.inputOrder[(*order)[i]];
      if (slot.kind == Declaration::InputSlot::Kind::Domain) {
        auto port = inference.get(
            inference.instantiate(
                descriptorType(callee.descriptorInputs[slot.index].contract),
                constraints.parameters, expr.span),
            expr.span);
        auto child =
            expression(expr.children[i], depth + 1, port ? &*port : nullptr);
        if (!child ||
            !inference.equal(
                inference.instantiate(
                    descriptorType(
                        callee.descriptorInputs[slot.index].contract),
                    constraints.parameters, expr.span),
                inference.known(descriptorType(nodes[*child].contract),
                                expr.span),
                expr.span))
          return {};
        children[slot.index] = *child;
      } else if (slot.kind == Declaration::InputSlot::Kind::Data) {
        auto value = dataValue(expr.children[i]);
        auto type = value ? dataType(*value) : nullptr;
        if (!type ||
            !inference.equal(constraints.inputs[slot.index],
                             inference.known(*type, expr.span), expr.span))
          return {};
        operands[slot.index] = *value;
      } else {
        refuse(expr.span);
        return {};
      }
    }
    if (!inference.solve(expr.span))
      return {};
    auto arguments = callableArguments(inference, reader.types, callee,
                                       constraints, expr.span);
    auto resultType = inference.get(output, expr.span);
    if (!arguments || !resultType || *arguments != actual->arguments ||
        actual->selectedView || actual->axis ||
        actual->argumentOrder != *order ||
        !llvm::equal(actual->operands, operands,
                     [](ValueId a, ValueId b) { return a.index == b.index; })) {
      refuse(expr.span);
      return {};
    }
    return consume(id, DescriptorBinding::Kind::Application, *resultType,
                   children, true);
  }
  /// Join source-derived local formations with descriptor operands already
  /// related by the ordinary invocation witness. Unconsumed source lets are
  /// checked here without activating their closure or native assertions.
  using NestedRegion = std::function<std::optional<bool>(
      uint32_t, uint32_t, const std::map<BindingId, unsigned> &)>;
  bool bodyDefinitions(const std::set<unsigned> &invocationCoverage,
                       uint32_t region = 0, bool declarationParameters = true,
                       NestedRegion nested = {},
                       std::optional<uint32_t> selectedExpression = {}) {
    if (!source.layoutSyntax || source.bodies.empty() || !body)
      return true;
    for (unsigned i = 0;
         declarationParameters && i < owner.descriptorInputs.size(); ++i) {
      if (i >= nodes.size())
        return refuse(source.span);
      const auto &node = nodes[i];
      if (node.kind != DescriptorBinding::Kind::Parameter ||
          node.parameter != i ||
          node.contract != owner.descriptorInputs[i].contract ||
          !same(node.span, owner.descriptorInputs[i].span) ||
          !node.operands.empty() || !node.children.empty() || node.factory ||
          node.expression || node.selectedView || !node.arguments.empty() ||
          !node.argumentOrder.empty() || node.axis)
        return refuse(source.span);
      domains.emplace(source.descriptorBindings[i], i);
      checked.insert(i);
    }
    if (!declarationParameters)
      for (const auto &[name, index] : domains)
        checked.insert(index); // Captures are related by the enclosing reader.
    std::function<bool(uint32_t, unsigned)> descriptor = [&](uint32_t id,
                                                             unsigned depth) {
      if (id >= source.expressions.size() || !enter(depth, source.span))
        return false;
      const auto &expr = source.expressions[id];
      if (expr.kind == Expression::Kind::Name && expr.binding)
        return domains.count(*expr.binding) != 0;
      if (expr.kind == Expression::Kind::Tuple ||
          expr.kind == Expression::Kind::Array) {
        bool selected = false;
        for (auto child : expr.children)
          selected |= descriptor(child, depth + 1);
        return selected;
      }
      if (expr.kind == Expression::Kind::Projection ||
          expr.kind == Expression::Kind::Subscript)
        return !expr.children.empty() &&
               descriptor(expr.children.front(), depth + 1);
      if (expr.kind != Expression::Kind::Call || expr.binding ||
          expr.text == "index")
        return false;
      auto target = reader.callable(owner, expr.text, expr.span, false, true);
      return target && (reader.index().schemeAssociation(target->declaration) ||
                        reader.declarations[target->declaration.index]
                            .descriptorResult.has_value());
    };
    std::function<bool(uint32_t, unsigned)> scanRegion;
    std::function<bool(uint32_t, unsigned)> scan = [&](uint32_t id,
                                                       unsigned depth) {
      if (id >= source.expressions.size() || !enter(depth, source.span))
        return false;
      // An implicit selected Math scope executes this expression in a distinct
      // Body. The authenticated lexical relation, not a candidate flag, routes
      // its descriptors to that Body before ordinary expression inspection.
      if (nested && selectedExpression != id)
        if (auto related = nested(id, UINT32_MAX, domains))
          return *related;
      if (descriptor(id, depth))
        return expression(id, depth).has_value();
      if (reader.types.diagnostic)
        return false;
      const auto &expr = source.expressions[id];
      for (unsigned i = 0; i < expr.children.size(); ++i) {
        if ((expr.kind == Expression::Kind::And ||
             expr.kind == Expression::Kind::Or) &&
            i == 1)
          continue; // The RHS belongs to its selected source region.
        if (!scan(expr.children[i], depth + 1))
          return false;
      }
      for (auto child : expr.regions) {
        auto related = nested ? nested(id, child, domains) : std::nullopt;
        if (related ? !*related : !scanRegion(child, depth + 1))
          return false;
      }
      return true;
    };
    scanRegion = [&](uint32_t region, unsigned depth) {
      if (region >= source.bodies.size() || !enter(depth, source.span))
        return false;
      for (const auto &statement : source.bodies[region].statements) {
        std::optional<Type> expected;
        if (statement.type) {
          auto annotation = reader.placedType(owner, *statement.type);
          if (!annotation)
            return false;
          if (isDescriptor(annotation->type))
            expected = std::move(annotation->type);
        }
        if (expected || descriptor(statement.expression, depth)) {
          auto value = expression(statement.expression, depth,
                                  expected ? &*expected : nullptr);
          if (!value)
            return reader.types.diagnostic ? false : refuse(statement.span);
          if (statement.kind == Statement::Kind::Let) {
            if (statement.mutableBinding || !statement.pattern.binding)
              return refuse(statement.span);
            domains.emplace(*statement.pattern.binding, *value);
          } else if (statement.kind != Statement::Kind::Expression)
            return refuse(statement.span);
        } else if (reader.types.diagnostic ||
                   !scan(statement.expression, depth))
          return false;
      }
      for (const auto &[name, result] : source.bodies[region].results)
        if (!scan(result, depth))
          return false;
      return true;
    };
    if (selectedExpression ? !scan(*selectedExpression, 1)
                           : !scanRegion(region, 1))
      return false;
    for (unsigned i = 0; i < nodes.size(); ++i)
      if (!checked.count(i) && !invocationCoverage.count(i))
        return refuse(nodes[i].span);
    return !reader.types.diagnostic;
  }
  bool definition(const DescriptorDefinition &actual) {
    for (unsigned i = 0; i < owner.descriptorInputs.size(); ++i) {
      if (next >= nodes.size())
        return refuse(source.span);
      const auto &node = nodes[next];
      if (node.kind != DescriptorBinding::Kind::Parameter ||
          node.parameter != i ||
          node.contract != owner.descriptorInputs[i].contract ||
          !node.operands.empty() || !node.children.empty() || node.axis ||
          !same(node.span, owner.descriptorInputs[i].span) || node.factory ||
          node.selectedView || node.expression || !node.arguments.empty() ||
          !node.argumentOrder.empty())
        return refuse(source.span);
      domains.emplace(source.descriptorBindings[i], next++);
    }
    for (unsigned i = 0; i < owner.inputs.size(); ++i)
      data.emplace(source.inputBindings[i], ValueId{i});
    if (source.domainConstructor) {
      using Native = protocol::instances::DomainConstructorKind;
      std::optional<DescriptorBinding::Kind> kind;
      unsigned axis = 0;
      for (const auto &row : protocol::instances::domainConstructors())
        if (row.identity == *source.domainConstructor) {
          axis = row.axis;
          switch (row.kind) {
          case Native::Elements:
            kind = DescriptorBinding::Kind::Elements;
            break;
          case Native::Indices:
            kind = DescriptorBinding::Kind::Indices;
            break;
          case Native::Range:
            kind = DescriptorBinding::Kind::Range;
            break;
          case Native::Zip:
            kind = DescriptorBinding::Kind::Zip;
            break;
          case Native::Product:
            kind = DescriptorBinding::Kind::Product;
            break;
          case Native::MatrixRow:
            kind = DescriptorBinding::Kind::MatrixRow;
            break;
          case Native::MatrixColumn:
            kind = DescriptorBinding::Kind::MatrixColumn;
            break;
          case Native::MatrixCoordinates:
            kind = DescriptorBinding::Kind::MatrixCoordinates;
            break;
          case Native::SourceArray:
            kind = DescriptorBinding::Kind::SourceArray;
            break;
          }
        }
      if (!kind || !descriptorConstructorSignature(owner, *kind, axis) ||
          actual.constructor != kind || actual.axis != axis ||
          next + 1 != nodes.size() || actual.result != next ||
          !actual.statements.empty())
        return refuse(source.span);
      const auto &node = nodes[next];
      if (!same(node.span, owner.span) || node.kind != *kind ||
          node.contract != *owner.descriptorResult || node.axis != axis ||
          node.operands.size() != owner.inputs.size() ||
          node.children.size() != owner.descriptorInputs.size() ||
          node.parameter || node.factory || node.selectedView ||
          node.expression || !node.arguments.empty() ||
          !node.argumentOrder.empty())
        return refuse(source.span);
      for (unsigned i = 0; i < node.operands.size(); ++i)
        if (node.operands[i].index != i)
          return refuse(source.span);
      for (unsigned i = 0; i < node.children.size(); ++i)
        if (!edge(node.children[i], i))
          return refuse(source.span);
      return true;
    }
    if (actual.constructor || actual.axis || source.bodies.empty())
      return refuse(source.span);
    const auto &body = source.bodies.front();
    if (body.results.size() != 1 || body.stopped || !body.operators.empty() ||
        actual.statements.size() != body.statements.size())
      return refuse(source.span);
    for (unsigned i = 0; i < body.statements.size(); ++i) {
      const auto &statement = body.statements[i];
      if (statement.kind != Statement::Kind::Let || statement.mutableBinding ||
          statement.roles || statement.owner || statement.exchange ||
          statement.pattern.kind != Pattern::Kind::Name ||
          !statement.pattern.binding)
        return refuse(statement.span);
      auto expected =
          statement.type ? reader.type(owner, *statement.type) : std::nullopt;
      auto value =
          expression(statement.expression, 1, expected ? &*expected : nullptr);
      if (!value ||
          actual.statements[i] != std::make_pair(statement.expression, *value))
        return refuse(statement.span);
      domains.emplace(*statement.pattern.binding, *value);
    }
    auto result = expression(body.results.front().second, 1,
                             &descriptorType(*owner.descriptorResult));
    return result && *result == actual.result && next == nodes.size();
  }
};
} // namespace zkc::language::detail
#endif
