#include "Checker.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/STLExtras.h"
#include <numeric>
using namespace llvm;
namespace zkc::language::detail {
namespace {
/// Match the installed scheme against written ports. This only decomposes
/// constructors. Associated domains are evaluated forward after their roots
/// are known, never inverted to guess a parent domain.
std::optional<std::vector<Type>>
nativeRoots(Semantics &types, const Declaration &decl, StringRef identity) {
  const auto operations = protocol::executableOperationContracts();
  auto found = llvm::find_if(operations, [&](const auto &operation) {
    return operation.name == identity;
  });
  auto refuse = [&] {
    return types.fail(
        "source.primitive",
        "written signature does not determine the installed primitive scheme",
        decl.span);
  };
  if (found == operations.end()) {
    refuse();
    return {};
  }
  const auto &signature = found->signature;
  const auto &scope = signature.scope;
  std::vector<std::optional<Type>> terms(scope.terms.size());
  std::function<bool(unsigned, const Type &, unsigned)> matchTerm;
  auto matchConstructor = [&](StringRef name, ArrayRef<unsigned> indices,
                              const Type &value, unsigned depth) {
    if ((name == "field" && value.kind == Type::Kind::Field) ||
        (name == "group" && value.kind == Type::Kind::Group))
      return indices.size() == 1 &&
             matchTerm(indices.front(), value, depth + 1);
    if (name == "bool" || name == "index")
      return indices.empty() &&
             value ==
                 Type(name == "bool" ? Type::Kind::Boolean : Type::Kind::Index);
    if (value.kind != Type::Kind::Builtin || value.domain != name ||
        indices.size() != value.arguments.size())
      return false;
    for (unsigned i = 0; i < indices.size(); ++i)
      if (!matchTerm(indices[i], value.arguments[i], depth + 1))
        return false;
    return true;
  };
  matchTerm = [&](unsigned id, const Type &value, unsigned depth) {
    if (depth > types.work.limits.typeDepth)
      return types.fail("source.limit", "primitive scheme depth exceeded",
                        decl.span);
    if (!types.chargeType(value, decl.span) || id >= terms.size() ||
        !matchesStaticSort(value, scope.sorts[id]))
      return false;
    if (terms[id] && *terms[id] != value)
      return false;
    terms[id] = value;
    const auto &term = scope.terms[id];
    return !term.arguments ||
           matchConstructor(term.name, *term.arguments, value, depth);
  };
  auto matchPorts = [&](ArrayRef<generic::Type> scheme, ArrayRef<Port> ports) {
    if (scheme.size() != ports.size())
      return false;
    for (unsigned i = 0; i < ports.size(); ++i) {
      const auto &port = scheme[i];
      if (!(port.term ? matchTerm(*port.term, ports[i].type, 1)
                      : matchConstructor(port.constructor, port.arguments,
                                         ports[i].type, 1)))
        return false;
    }
    return true;
  };
  // A single written tuple is the result of a multiple-output native operation.
  std::vector<Port> outputs;
  if (signature.outputs.size() != 1 &&
      decl.outputs.front().type.kind == Type::Kind::Tuple) {
    for (const auto &element : decl.outputs.front().type.arguments)
      outputs.push_back({"", element, {}, decl.span});
  } else if (!signature.outputs.empty() ||
             decl.outputs.front().type.kind != Type::Kind::Unit)
    outputs = decl.outputs;
  if (!matchPorts(signature.inputs, decl.inputs) ||
      !matchPorts(signature.outputs, outputs)) {
    refuse();
    return {};
  }
  std::vector<Type> roots;
  for (unsigned i = 0; i < terms.size(); ++i) {
    const auto &term = scope.terms[i];
    std::optional<Type> value;
    if (term.arguments) {
      std::vector<Type> arguments;
      for (auto position : *term.arguments) {
        if (!terms[position]) {
          refuse();
          return {};
        }
        arguments.push_back(*terms[position]);
      }
      auto formed = builtinType(term.name, arguments);
      if (!formed) {
        consumeError(formed.takeError());
        refuse();
        return {};
      }
      value = *formed;
    } else if (term.parent) {
      if (terms[*term.parent])
        value = types.associated(*terms[*term.parent], term.name, decl.span);
    } else if (auto fixed = scope.constants.find(i);
               fixed != scope.constants.end()) {
      if (isDomainSort(scope.sorts[i]))
        value = domainType(scope.sorts[i], fixed->second);
      else if (scope.sorts[i] == "Nat") {
        uint64_t n;
        if (!StringRef(fixed->second).getAsInteger(10, n)) {
          value = Type(Type::Kind::Natural);
          value->dimension = Natural::constant(n);
        }
      }
    } else if (terms[i]) {
      value = terms[i];
      roots.push_back(*value);
    }
    if (!value || (terms[i] && *value != *terms[i])) {
      refuse();
      return {};
    }
    terms[i] = *value;
  }
  return roots;
}

std::optional<std::vector<Type>>
mathematicalRoots(Semantics &types, const Declaration &decl,
                  const MathematicalIntrinsic &intrinsic) {
  using I = MathematicalIdentity;
  using K = Type::Kind;
  auto refuse = [&]() -> std::optional<std::vector<Type>> {
    types.fail("source.primitive",
               "primitive static roots are not determined by this signature; "
               "use an intrinsic body",
               decl.span);
    return {};
  };
  if (intrinsic.domain == MathematicalIntrinsic::Domain::Boolean)
    return std::vector<Type>{};
  if (decl.inputs.empty())
    return refuse();
  const auto &input = decl.inputs.front().type;
  const auto &output = decl.outputs.front().type;
  if (intrinsic.scalar)
    return std::vector<Type>{input};
  const Type *anchor = &input;
  switch (intrinsic.identity) {
  case I::PolynomialConstant:
  case I::PolynomialMLE:
  case I::PolynomialCoefficients:
  case I::PolynomialFix:
    anchor = &output;
    break;
  case I::PolynomialFromCoefficients:
  case I::PolynomialAdd:
  case I::PolynomialMultiply:
  case I::PolynomialEvaluate:
    break;
  case I::ArrayFromElements: {
    if (input.kind != K::Array || input.arguments.size() != 1)
      return refuse();
    Type n(K::Natural);
    n.dimension = input.dimension;
    n.symbolic = !n.dimension.isClosed();
    return std::vector<Type>{input.arguments.front(), n};
  }
  default:
    return refuse();
  }
  if ((anchor->kind != K::Formal && anchor->kind != K::Builtin) ||
      anchor->arguments.size() != 2)
    return refuse();
  auto roots = anchor->arguments;
  if (intrinsic.identity == I::PolynomialFix) {
    if (decl.inputs.size() != 2 || decl.inputs[1].type.kind != K::Array)
      return refuse();
    Type n(K::Natural);
    n.dimension = decl.inputs[1].type.dimension;
    n.symbolic = !n.dimension.isClosed();
    roots.push_back(std::move(n));
  }
  return roots;
}
} // namespace

bool primitiveCallIsInline(Body::Mode mode, StringRef identity) {
  const auto *math = mathematicalIntrinsic(identity);
  return math ? mode != Body::Mode::Local || math->scalar
              : mode == Body::Mode::Local;
}

bool Checker::primitiveBody(Declaration &decl, Body &body) {
  const auto &identity = *sources[decl.id.index]->primitive;
  const auto *mathematical = mathematicalIntrinsic(identity);
  if (decl.outputs.size() != 1 || !decl.services.empty() ||
      (decl.kind != Declaration::Kind::Math &&
       decl.kind != Declaration::Kind::Local))
    return types.fail("source.primitive",
                      "primitive requires an ordinary function signature",
                      decl.span);
  if ((decl.kind == Declaration::Kind::Math) != (mathematical != nullptr))
    return types.fail(
        "source.primitive",
        "primitive declaration mode differs from its installed identity",
        decl.span);
  auto arguments = mathematical ? mathematicalRoots(types, decl, *mathematical)
                                : nativeRoots(types, decl, identity);
  if (!arguments)
    return false;
  auto signature =
      mathematical
          ? types.intrinsicSignature(&decl, identity, *arguments, {}, decl.span)
          : types.kernelSignature(identity, *arguments, {}, decl.span, &decl);
  if (!signature)
    return false;
  if (signature->inputs.size() != decl.inputs.size() ||
      signature->resultType() != decl.outputs.front().type)
    return types.fail("source.primitive",
                      "primitive result or input count differs", decl.span);
  std::vector<ValueId> operands;
  std::vector<unsigned> dependencies;
  for (unsigned i = 0; i < decl.inputs.size(); ++i) {
    const auto &port = decl.inputs[i];
    if (port.type != signature->inputs[i])
      return types.fail("source.primitive", "primitive operand type differs",
                        port.span);
    if (!types.permissions(port.type, port.span, &decl) ||
        (mathematical ? !types.mathematicalData(port.type, port.span, &decl)
                      : !types.executableType(port.type, port.span)) ||
        !types.chargeType(port.type, port.span))
      return false;
    operands.push_back(ValueId{i});
    body.values.push_back(
        {port.type,
         mathematical ? std::vector<unsigned>{i} : std::vector<unsigned>{},
         port.span});
    if (mathematical)
      dependencies.push_back(i);
  }
  body.inputs = operands.size();
  if (!types.permissions(decl.outputs.front().type, decl.span, &decl) ||
      !types.chargeType(decl.outputs.front().type, decl.span) ||
      !types.accept(work.count(work.operations, work.limits.operations,
                               "operation count", decl.span)))
    return false;
  ValueId result{uint32_t(body.values.size())};
  body.values.push_back({decl.outputs.front().type, dependencies, decl.span});
  decltype(Operation::action) action =
      MathValue{MathematicalIdentity::BooleanEqual, {}, {}};
  if (mathematical) {
    // Scalar identities carry their domain in port types, matching authored
    // mathematics. Formal intrinsic roots remain explicit.
    action = MathValue{mathematical->identity,
                       operands,
                       {},
                       mathematical->scalar ? std::vector<Type>{} : *arguments};
    body.formationRequirements.push_back(dependencies);
  } else {
    LocalPrimitive primitive{identity, operands, {}};
    primitive.bindingArguments = *arguments;
    action = std::move(primitive);
    body.mayStop = identity != "index.equal";
  }
  if (decl.effectAllowance && body.mayStop && !decl.effectAllowance->mayStop)
    return types.fail("source.effect",
                      "primitive exceeds its written effect allowance",
                      decl.span);
  body.operations.push_back({std::move(action), {result}, decl.span, 0});
  body.results = {result};
  decl.primitive = PrimitiveDefinition{identity, std::move(*arguments)};
  return true;
}
} // namespace zkc::language::detail
