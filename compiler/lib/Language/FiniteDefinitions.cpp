#include "Checker.h"
using namespace llvm;
namespace zkc::language::detail {
bool Checker::finiteBody(Declaration &decl, Body &body) {
  const auto &identity = *sources[decl.id.index]->finiteDefinition;
  StringRef name(identity);
  const bool mathematical = decl.kind == Declaration::Kind::Math;
  auto refuse = [&](StringRef message) {
    return types.fail("source.finite", message, decl.span);
  };
  if ((decl.kind != Declaration::Kind::Math &&
       decl.kind != Declaration::Kind::Local) ||
      !name.consume_front(mathematical ? "math." : "local.") ||
      decl.domainInputs.size() != 1 || decl.outputs.size() != 1 ||
      !decl.services.empty())
    return refuse("finite definition requires one domain and an ordinary "
                  "function signature of the selected mode");
  bool filtered = name.consume_back("_where");
  const bool fold = name == "fold";
  if (!fold && !name.consume_front("collect."))
    return refuse("unknown finite definition identity");
  if (decl.inputs.size() != unsigned(fold) ||
      decl.scopedInputs.size() != (filtered ? 2u : 1u))
    return refuse("finite data or scoped input count differs");
  const auto &item = decl.domainInputs.front().item;
  const auto &output = decl.outputs.front().type;
  Type element = output;
  if (fold) {
    if (decl.inputs.front().type != output)
      return refuse("fold initial and result state types differ");
  } else {
    if (output.kind != Type::Kind::Builtin || output.domain != name ||
        (name != "vector" && name != "groups" && name != "sequence" &&
         name != "indices" && name != "field_array"))
      return refuse("collect requires its selected native collection result");
    if (name == "indices") {
      if (!output.arguments.empty())
        return refuse("indices collection takes no element parameter");
      element = Type(Type::Kind::Index);
    } else {
      if (output.arguments.size() != (name == "field_array" ? 2u : 1u))
        return refuse("collection element parameters differ");
      element = output.arguments.front();
    }
    if (filtered && name == "field_array")
      return refuse("filtered collect cannot establish a fixed result size");
  }
  const auto mode =
      mathematical ? ScopedSignature::Mode::Math : ScopedSignature::Mode::Local;
  auto matches = [&](const ScopedSignature &signature, ArrayRef<Type> inputs,
                     const Type &result) {
    return signature.mode == mode && ArrayRef(signature.inputs) == inputs &&
           signature.result == result && signature.itemDomain == 0 &&
           !signature.allowance.opaque &&
           (!mathematical || !signature.allowance.mayStop);
  };
  std::vector<Type> inputs;
  if (fold)
    inputs.push_back(output);
  inputs.push_back(item);
  unsigned bodyIndex = filtered ? 1 : 0;
  if (!matches(decl.scopedInputs[bodyIndex].signature, inputs, element))
    return refuse(
        "finite body must accept the selected item and state on its domain");
  if (filtered && !matches(decl.scopedInputs[0].signature, {item}, Type{}))
    return refuse("finite predicate must return bool on its domain");
  if (decl.effectAllowance && !mathematical &&
      !decl.effectAllowance->fixed.mayStop)
    return types.fail("source.effect", "finite admission can stop", decl.span);
  for (const auto &type : {item, element, output}) {
    if (!types.permissions(type, decl.span, &decl) ||
        (mathematical ? !types.mathematicalData(type, decl.span, &decl)
                      : !types.executableType(type, decl.span)) ||
        !types.chargeType(type, decl.span))
      return false;
  }
  auto itemPermissions = types.permissions(item, decl.span, &decl);
  if (!itemPermissions || !itemPermissions->copy || !itemPermissions->drop)
    return refuse("domain items require Copy and Drop");
  std::vector<ValueId> operands;
  if (fold) {
    operands.push_back({0});
    body.values.push_back(
        {output,
         mathematical ? std::vector<unsigned>{0} : std::vector<unsigned>{},
         decl.span});
  }
  body.inputs = operands.size();
  body.domainBindings.push_back(
      {DomainBinding::Kind::Parameter, item, {}, {}, 0, 0, decl.span});
  for (unsigned i = 0; i < decl.scopedInputs.size(); ++i) {
    const auto &parameter = decl.scopedInputs[i];
    body.scopedBindings.push_back(
        {parameter.signature, i, {}, {}, {}, parameter.span, {}});
  }
  if (!types.accept(work.count(work.operations, work.limits.operations,
                               "operation count", decl.span)))
    return false;
  ValueId result{unsigned(body.values.size())};
  body.values.push_back({output, {}, decl.span});
  body.operations.push_back(
      {FiniteApplication{fold ? FiniteApplication::Kind::Fold
                              : FiniteApplication::Kind::Collect,
                         0, bodyIndex,
                         filtered ? std::optional<unsigned>(0) : std::nullopt,
                         std::move(operands)},
       {result},
       decl.span,
       0});
  body.results = {result};
  body.effects.fixed.mayStop = !mathematical;
  body.parameterizedSummary = true;
  decl.finiteDefinition = identity;
  return true;
}
} // namespace zkc::language::detail
