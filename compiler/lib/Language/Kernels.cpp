#include "zkc/Contracts/Kernels.h"
#include "BodyCheck.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
std::optional<Checker::CallSignature>
Checker::kernelSignature(StringRef contract, ArrayRef<Type> arguments,
                         ArrayRef<std::string> attributes, Span span,
                         const Declaration *context) {
  auto stage = protocol::authoringStage(contract);
  if (stage != protocol::AuthoringStage::Source &&
      stage != protocol::AuthoringStage::Construction) {
    fail("source.kernel", "operation is not source authorable", span);
    return {};
  }
  if (protocol::operationEffect(contract) != "local" ||
      protocol::isHistoryTransition(contract) ||
      protocol::samplingContract(contract)) {
    fail("source.kernel", "operation requires a managed effect interface",
         span);
    return {};
  }
  const auto operations = protocol::executableOperationContracts();
  auto found = llvm::find_if(operations, [&](const auto &operation) {
    return operation.name == contract;
  });
  if (found == operations.end()) {
    fail("source.kernel", "unknown installed operation", span);
    return {};
  }
  auto validate = [&](Error error) {
    return !error || fail("source.kernel", toString(std::move(error)), span);
  };
  const auto &signature = found->signature;
  const auto &scope = signature.scope;
  std::vector<Type> terms;
  unsigned root = 0;
  auto form = [&](StringRef constructor,
                  ArrayRef<unsigned> positions) -> std::optional<Type> {
    std::vector<Type> selected;
    for (auto position : positions) {
      if (position >= terms.size()) {
        fail("source.kernel", "invalid installed type scope", span);
        return {};
      }
      selected.push_back(terms[position]);
    }
    auto type = builtinType(constructor, selected);
    if (!type) {
      fail("source.kernel", toString(type.takeError()), span);
      return {};
    }
    return std::move(*type);
  };
  for (unsigned i = 0; i < scope.terms.size(); ++i) {
    if (!charge(1, span))
      return {};
    const auto &term = scope.terms[i];
    const auto &sort = scope.sorts[i];
    std::optional<Type> value;
    if (term.arguments)
      value = form(term.name, *term.arguments);
    else if (term.parent) {
      const auto &base = terms[*term.parent];
      value = associated(base, term.name, span);
    } else if (auto fixed = scope.constants.find(i);
               fixed != scope.constants.end()) {
      if (isDomainSort(sort))
        value = domainType(sort, fixed->second);
      else if (sort == "Nat") {
        uint64_t n;
        if (!StringRef(fixed->second).getAsInteger(10, n)) {
          value = Type(Type::Kind::Natural);
          value->dimension = Natural::constant(n);
        }
      }
    } else if (root < arguments.size())
      value = arguments[root++];
    if (!value) {
      if (!diagnostic)
        fail("source.kernel", "static argument or association is unavailable",
             span);
      return {};
    }
    bool formed = matchesStaticSort(*value, sort);
    if (!formed) {
      fail("source.kernel", "installed static argument sort differs", span);
      return {};
    }
    if (sort == "Type") {
      auto caps = permissions(*value, span);
      if (!caps || !caps->copy || !caps->drop) {
        if (!diagnostic)
          fail("source.kernel", "native Type roots require Copy and Drop",
               span);
        return {};
      }
    }
    if (!chargeType(*value, span))
      return {};
    terms.push_back(std::move(*value));
  }
  if (root != arguments.size()) {
    fail("source.kernel", "installed static argument count differs", span);
    return {};
  }
  for (const auto &requirement : signature.requirements) {
    if (requirement.kind == requirements::Predicate::Kind::Equal) {
      if (terms[requirement.arguments[0]] != terms[requirement.arguments[1]]) {
        fail("source.kernel",
             "installed equality requires identical source terms", span);
        return {};
      }
      continue;
    }
    CapabilityBound goal{requirement.relation, {}, span};
    for (auto index : requirement.arguments)
      goal.arguments.push_back(terms[index]);
    if (!entails(context, goal, "source.kernel"))
      return {};
  }
  const auto *parameterSchema = protocol::parameterContract(contract);
  const Type *literalField = parameterSchema && parameterSchema->fieldTerm
                                 ? &terms[*parameterSchema->fieldTerm]
                                 : nullptr;
  if (literalField && symbolic(*literalField)) {
    if (!validate(protocol::checkGenericParameters(contract, attributes)))
      return {};
  } else if (!validate(protocol::checkParameters(
                 contract, attributes,
                 literalField ? literalField->domain : "")))
    return {};
  std::optional<protocol::BoundOperation> closedSignature;
  if (llvm::none_of(arguments,
                    [&](const auto &type) { return symbolic(type); })) {
    auto args = kernelArguments(contract, arguments);
    if (!args) {
      fail("source.kernel", toString(args.takeError()), span);
      return {};
    }
    protocol::BindingApplication binding{contract.str(), *args, {}};
    auto selected = protocol::resolveBinding(binding, false);
    if (!selected) {
      fail("source.kernel", toString(selected.takeError()), span);
      return {};
    }
    closedSignature = std::move(*selected);
  }
  CallSignature result;
  auto ports = [&](ArrayRef<generic::Type> source, std::vector<Type> &dest) {
    for (const auto &port : source) {
      auto type = port.term ? std::optional<Type>(terms[*port.term])
                            : form(port.constructor, port.arguments);
      if (!type)
        return false;
      // A Type root cannot smuggle a source record or custody token into a
      // native one-value port, even when its representation has one leaf.
      if (port.term && !isNativeData(*type))
        return fail("source.kernel", "native Type root requires native data",
                    span);
      dest.push_back(std::move(*type));
    }
    return true;
  };
  if (!ports(signature.inputs, result.inputs) ||
      !ports(signature.outputs, result.outputs))
    return {};
  if (protocol::hasUnclassifiedProviderEffect(contract)) {
    // The generic registry cannot assume Copy for Type formals. Refine that
    // uncertainty only for signatures with those formals and admitted data
    // ports; provider and history operations remain outside this interface.
    bool typeRoot = false;
    for (unsigned i = 0; i < scope.terms.size(); ++i)
      typeRoot |= scope.sorts[i] == "Type" && !scope.terms[i].parent &&
                  !scope.terms[i].arguments && !scope.constants.count(i);
    if (!typeRoot) {
      fail("source.kernel", "operation has an unclassified provider effect",
           span);
      return {};
    }
    auto data = [&](ArrayRef<Type> ports) {
      return llvm::all_of(ports, [&](const Type &type) {
        auto caps = permissions(type, span);
        return caps && caps->copy && caps->drop;
      });
    };
    if (!data(result.inputs) || !data(result.outputs)) {
      if (!diagnostic)
        fail("source.kernel", "Type-root operations require Copy and Drop data",
             span);
      return {};
    }
  }
  if (closedSignature) {
    auto agree = [&](ArrayRef<Type> source,
                     ArrayRef<protocol::BoundType> installed) {
      if (source.size() != installed.size())
        return fail("source.kernel", "closed kernel port count differs", span);
      for (unsigned i = 0; i < source.size(); ++i) {
        auto native = builtinLayout(source[i]);
        if (!native) {
          fail("source.kernel", toString(native.takeError()), span);
          return false;
        }
        if (!(*native == installed[i]))
          return fail("source.kernel", "closed kernel port type differs", span);
      }
      return true;
    };
    if (!agree(result.inputs, closedSignature->inputs) ||
        !agree(result.outputs, closedSignature->outputs))
      return {};
  }
  return result;
}
Type Checker::CallSignature::resultType() const {
  if (outputs.size() == 1)
    return outputs.front();
  Type result(outputs.empty() ? Type::Kind::Unit : Type::Kind::Tuple);
  result.arguments = outputs;
  return result;
}
std::optional<Checker::CallSignature>
BodyChecker::kernelSignature(const Expression &expr,
                             std::vector<Type> &arguments) {
  for (const auto &syntax : expr.arguments) {
    auto type = checker.type(decl, syntax);
    if (!type)
      return {};
    arguments.push_back(std::move(*type));
  }
  return checker.kernelSignature(expr.text, arguments, expr.labels, expr.span,
                                 &decl);
}
std::optional<ValueId> BodyChecker::kernel(const Expression &expr,
                                           unsigned depth) {
  if (!local()) {
    fail("source.mode", "kernel bindings require an ordinary local function",
         expr.span);
    return {};
  }
  std::vector<Type> arguments;
  auto signature = kernelSignature(expr, arguments);
  if (!signature)
    return {};
  if (expr.children.size() != signature->inputs.size()) {
    fail("source.kernel", "installed input count differs", expr.span);
    return {};
  }
  std::vector<ValueId> operands;
  for (unsigned i = 0; i < expr.children.size(); ++i) {
    auto input = expression(expr.children[i], signature->inputs[i], depth + 1);
    if (!input || !use(*input, expr.span))
      return {};
    operands.push_back(*input);
  }
  Type result = signature->resultType();
  LocalPrimitive primitive{expr.text, std::move(operands), expr.labels};
  primitive.bindingArguments = std::move(arguments);
  // The installed local envelope does not certify totality.
  body.mayStop = true;
  return emit(std::move(primitive), result, {}, expr.span);
}
} // namespace zkc::language::detail
