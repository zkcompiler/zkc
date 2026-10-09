#include "Checker.h"
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Relation/Bundle.h"
#include "llvm/ADT/STLExtras.h"
#include <algorithm>

using namespace llvm;
namespace zkc::language::detail {
std::optional<Type> Checker::assetProperty(const Declaration &context,
                                           const SyntaxType &syntax,
                                           unsigned depth) {
  auto refuse = [&](StringRef detail) -> std::optional<Type> {
    types.fail("source.asset-property", detail, syntax.span);
    return {};
  };
  if (!types.charge(output.assets.size() + syntax.assetName.size() + 1,
                    syntax.span))
    return {};
  auto found = llvm::find_if(output.assets, [&](const auto &asset) {
    return asset.name() == syntax.assetName;
  });
  if (found == output.assets.end())
    return refuse("captured asset is absent");
  std::vector<uint32_t> arguments;
  for (const auto &argument : syntax.arguments) {
    auto value = elaborateType(context, argument, depth + 1);
    if (!value)
      return {};
    if (value->kind != Type::Kind::Natural || !value->dimension.isClosed() ||
        value->dimension.closedValue() > ring::Limits::degree)
      return refuse("asset query arguments require bounded closed naturals");
    arguments.push_back(value->dimension.closedValue());
  }
  uint64_t result = 0;
  if (const auto *arena = found->ring()) {
    if (!types.charge(arena->nodes().size() + arena->inputs().size() +
                          arena->outputs().size() + 1,
                      syntax.span))
      return {};
    if (syntax.name == "input-field" || syntax.name == "output-field") {
      if (arguments.size() != 1)
        return refuse("field query requires one valid slot index");
      auto index = arguments.front();
      if (syntax.name == "input-field" && index < arena->inputs().size())
        return Type(Type::Kind::Field, arena->inputs()[index].field);
      if (syntax.name == "output-field" && index < arena->outputs().size())
        return Type(Type::Kind::Field,
                    arena->facts()[arena->outputs()[index]].field);
      return refuse("field query slot is out of range");
    }
    if (syntax.name == "inputs" && arguments.empty())
      result = arena->inputs().size();
    else if (syntax.name == "outputs" && arguments.empty())
      result = arena->outputs().size();
    else if (syntax.name == "degree") {
      if (arguments.empty())
        arguments.assign(arena->inputs().size(), 1);
      if (arguments.size() != arena->inputs().size())
        return refuse("degree query requires one weight per declared input");
      auto degrees = arena->degrees(arguments);
      if (!degrees) {
        types.accept(degrees.takeError(), syntax.span);
        return {};
      }
      for (auto output : arena->outputs())
        result = std::max<uint64_t>(result, (*degrees)[output]);
    } else
      return refuse("unknown ring property or incorrect query arguments");
  } else if (const auto *bundle = found->bundle()) {
    if (syntax.name == "tables" && arguments.empty())
      result = bundle->tables().size();
    else if (syntax.name == "publics" && arguments.empty())
      result = bundle->publics().size();
    else {
      if (arguments.size() != 1 || arguments.front() >= bundle->tables().size())
        return refuse("table query requires one valid table index");
      const auto &table = bundle->tables()[arguments.front()];
      if (syntax.name == "inputs")
        result = table.arena.inputs().size();
      else if (syntax.name == "outputs")
        result = table.arena.outputs().size();
      else if (syntax.name == "degree") {
        const auto &facts = bundle->facts()[arguments.front()];
        if (!types.charge(facts.size() + 1, syntax.span))
          return {};
        for (const auto &fact : facts)
          result = std::max<uint64_t>(result, fact.degree);
      } else
        return refuse("unknown relation bundle property");
    }
  } else
    return refuse("asset kind has no expression properties");
  Type value(Type::Kind::Natural);
  value.dimension = Natural::constant(result);
  return value;
}
} // namespace zkc::language::detail
