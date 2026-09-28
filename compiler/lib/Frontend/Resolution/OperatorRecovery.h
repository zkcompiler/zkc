#ifndef ZKC_FRONTEND_RESOLUTION_OPERATORRECOVERY_H
#define ZKC_FRONTEND_RESOLUTION_OPERATORRECOVERY_H

#include "../Static/Types.h"
#include "Project.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Frontend/Work.h"
#include "llvm/ADT/STLExtras.h"
#include <type_traits>

namespace zkc::frontend::resolution {
/// Recover only dependencies justified by known nominal operand heads. This
/// is not type checking: opaque, structural and unknown heads remain unknown,
/// never wildcards. In particular, a broken hook must not remove every user of
/// the same operator symbol. The ordinary checkers still own hook formation,
/// coherence, exact types, requirements and resource use. This runs only after
/// a recoverable resolution error and can never admit code. Work/depth
/// exhaustion discards its local edges and disables partial recovery, retaining
/// the original resolution diagnostics. It does not change valid-program
/// admission limits.
class OperatorRecovery {
  struct Head {
    enum class Kind { Record, Logical } kind;
    std::string name;
    bool operator<(const Head &other) const {
      return std::tie(kind, name) < std::tie(other.kind, other.name);
    }
  };
  using KnownHead = std::optional<Head>;
  using Sorts = std::map<std::string, std::string>;
  using Values = std::map<std::string, KnownHead>;
  using Key = std::pair<std::string, std::vector<Head>>;
  struct Target {
    std::string callee;
    bool installed;
    KnownHead result;
  };
  const syntax::Module &module;
  const Context &context;
  std::vector<Context::Reference> references;
  std::map<std::string, const syntax::Struct *> records;
  std::map<std::string, std::vector<KnownHead>> results;
  std::map<Key, std::vector<Target>> operators;

  mutable WorkBudget budget;
  mutable bool exhausted = false;
  std::map<std::string, Sorts> recordSorts;

  bool spend(size_t amount = 1) const {
    exhausted |= !budget.charge(WorkAccount::AuthoredStatic, amount);
    return !exhausted;
  }
  bool visit(unsigned depth) const {
    // The parser bounds body and expression nesting separately at 64. This
    // analysis combines them; leave room for both and projected record types.
    exhausted |= depth > 256;
    return !exhausted && spend();
  }
  Sorts sorts(llvm::ArrayRef<syntax::StaticParameter> parameters) const {
    Sorts out;
    for (const auto &p : parameters) {
      if (!spend(1 + p.bounds.size()))
        break;
      if (p.sort) {
        out.emplace(p.name, *p.sort);
        continue;
      }
      // Match ordinary checking: each bound must name one domain sort,
      // and all bounds must agree. Do not solve by intersecting ambiguities.
      std::optional<std::string> selected;
      for (const auto &bound : p.bounds) {
        auto candidates = capabilityDomainSorts(syntax::encode(bound));
        if (candidates.size() != 1 ||
            (selected && *selected != candidates.front())) {
          selected.reset();
          break;
        }
        selected = candidates.front();
      }
      if (selected)
        out.emplace(p.name, *selected);
    }
    return out;
  }
  KnownHead logical(llvm::StringRef name) const {
    for (const auto &t : protocol::boundTypeConstructors())
      if (t.name == name)
        return Head{Head::Kind::Logical, name.str()};
    return {};
  }
  KnownHead head(const syntax::Type &type, const Sorts &scope,
                 unsigned depth = 0) const {
    if (!visit(depth))
      return {};
    if (type.product || type.natural() || type.name == "Array")
      return {};
    if (type.members.empty()) {
      if (!type.quoted()) {
        if (const auto *d = context.lookup(type.name))
          if (d->kind == Declaration::Kind::Record)
            return Head{Head::Kind::Record, d->symbol};
        if (elementTypeFamily(type.name) && type.arguments.size() == 1) {
          auto element = head(type.arguments.front(), scope, depth + 1);
          if (element && element->kind == Head::Kind::Logical)
            return logical(familyResultConstructor(type.name, element->name));
          return {};
        }
        return logical(logicalConstructor(type.name));
      }
      auto parsed = protocol::parseBoundType(type.name, false);
      if (parsed)
        return logical(parsed->kind);
      llvm::consumeError(parsed.takeError());
      return {};
    }
    auto found = scope.find(type.name);
    llvm::StringRef sort = !type.quoted() && found != scope.end()
                               ? found->second
                               : protocol::installedIdentitySort(type.name);
    if (!spend(type.members.size()))
      return {};
    for (const auto &member : llvm::drop_end(type.members))
      sort = protocol::associatedMemberSort(sort, member);
    return logical(associatedTypeConstructor(sort, type.members.back()));
  }
  // A projected record field keeps its declared type's head. Other
  // selections, and non-local roots, are unknown here.
  KnownHead value(const syntax::Place &place, const Values &values) const {
    const auto *root = syntax::localRoot(place);
    if (!root || !visit(0) || !spend(1 + place.steps.size()))
      return {};
    auto found = values.find(*root);
    if (found == values.end())
      return {};
    auto current = found->second;
    for (const auto &step : place.steps) {
      if (!current || current->kind != Head::Kind::Record ||
          step.kind != syntax::Projection::Kind::Field)
        return {};
      auto record = records.find(current->name);
      if (record == records.end() || !spend(record->second->fields.size()))
        return {};
      auto field = llvm::find_if(record->second->fields, [&](const auto &f) {
        return f.name == step.key;
      });
      if (field == record->second->fields.end())
        return {};
      current = head(field->type, recordSorts.at(current->name));
    }
    return current;
  }
  KnownHead result(llvm::StringRef callee) const {
    auto found = results.find(callee.str());
    return found != results.end() && found->second.size() == 1
               ? found->second.front()
               : KnownHead{};
  }
  KnownHead use(const source::Node &node, llvm::StringRef symbol,
                llvm::ArrayRef<KnownHead> operands) {
    Key key{symbol.str(), {}};
    for (const auto &operand : operands) {
      if (!operand)
        return {};
      key.second.push_back(*operand);
    }
    auto found = operators.find(key);
    if (found == operators.end())
      return {};
    // Do not manufacture a selection when whole-installation coherence fails.
    if (found->second.size() != 1)
      return {};
    const auto &target = found->second.front();
    if (target.installed) {
      if (!context.operationAvailable(node, target.callee))
        return {};
    } else {
      if (!context.sourceOperatorAvailable(node, target.callee))
        return {};
      if (const auto *owner = context.enclosing(node))
        references.push_back(
            {owner->symbol, target.callee, node.location, false});
    }
    return target.result;
  }
  KnownHead expression(const syntax::Expression &expr, Values &values,
                       const Sorts &scope, unsigned depth = 0) {
    if (!visit(depth))
      return {};
    std::vector<KnownHead> operands;
    for (const auto &operand : expr.operands)
      operands.push_back(expression(operand, values, scope, depth + 1));
    if (expr.traversal) {
      if (!spend(values.size()))
        return {};
      auto nested = values;
      nested[expr.traversal->element] = {};
      if (!expr.traversal->state.empty())
        nested[expr.traversal->state] = {};
      body(expr.traversal->body, nested, scope, depth + 1);
    }
    using K = syntax::Expression::Kind;
    switch (expr.kind) {
    case K::Name:
    case K::Field:
      if (auto place = syntax::placeCandidate(expr))
        return value(*place, values);
      return {};
    case K::Index:
    case K::Length:
      return logical("index");
    case K::Boolean:
      return logical("bool");
    case K::Struct:
      if (records.count(syntax::encode(expr.reference)))
        return Head{Head::Kind::Record, syntax::encode(expr.reference)};
      return {};
    case K::Call:
      return result(syntax::encode(expr.reference));
    case K::Operator:
      return use(expr, expr.name, operands);
    default:
      return {};
    }
  }
  void body(const syntax::Body &instructions, const Values &incoming,
            const Sorts &scope, unsigned depth = 0) {
    if (!visit(depth) || !spend(incoming.size()))
      return;
    auto values = incoming;
    for (const auto &instruction : instructions) {
      if (!spend())
        return;
      std::visit(
          [&](const auto &v) {
            using T = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<T, syntax::Binding>) {
              auto inferred =
                  expression(v.expression, values, scope, depth + 1);
              for (size_t i = 0; i < v.outputs.size(); ++i)
                values[v.outputs[i]] = v.annotation && i < v.annotation->size()
                                           ? head((*v.annotation)[i], scope)
                                       : v.outputs.size() == 1 ? inferred
                                                               : KnownHead{};
            } else if constexpr (std::is_same_v<T, syntax::Exit>) {
              expression(v.expression, values, scope, depth + 1);
            } else if constexpr (std::is_same_v<T, syntax::Call>) {
              std::vector<KnownHead> outputs;
              if (v.operatorSymbol) {
                std::vector<KnownHead> operands;
                for (const auto &input : v.inputs)
                  operands.push_back(value(input, values));
                outputs.push_back(use(v, *v.operatorSymbol, operands));
              } else if (auto found = results.find(syntax::encode(v.callee));
                         found != results.end())
                outputs = found->second;
              for (size_t i = 0; i < v.outputs.size(); ++i)
                values[v.outputs[i]] = v.annotation && i < v.annotation->size()
                                           ? head((*v.annotation)[i], scope)
                                       : i < outputs.size() ? outputs[i]
                                                            : KnownHead{};
            } else if constexpr (std::is_same_v<T, syntax::Conditional>) {
              expression(v.condition, values, scope, depth + 1);
              body(v.thenBody, values, scope, depth + 1);
              body(v.elseBody, values, scope, depth + 1);
              for (const auto &output : v.outputs)
                values[output] = {};
            } else if constexpr (std::is_same_v<T, syntax::For> ||
                                 std::is_same_v<T, syntax::Loop> ||
                                 std::is_same_v<T, syntax::ArrayTraversal>) {
              if (!spend(values.size()))
                return;
              auto nested = values;
              if constexpr (std::is_same_v<T, syntax::For>) {
                expression(v.lower, values, scope, depth + 1);
                expression(v.upper, values, scope, depth + 1);
                nested[v.induction] = logical("index");
              }
              if constexpr (std::is_same_v<T, syntax::ArrayTraversal>)
                nested[v.element] = {};
              for (const auto &[name, input] : v.carried)
                nested[name] = value(input, values);
              body(v.body, nested, scope, depth + 1);
              for (const auto &output : v.outputs)
                values[output] = {};
            } else if constexpr (std::is_same_v<T, syntax::Placement>) {
              body(v.body, values, scope, depth + 1);
              for (const auto &output : v.outputs)
                values[output] =
                    v.annotation ? head(*v.annotation, scope) : KnownHead{};
            } else if constexpr (std::is_same_v<T, syntax::Match>) {
              for (const auto &arm : v.arms) {
                if (!spend(values.size()))
                  return;
                auto nested = values;
                for (const auto &name : arm.payload)
                  nested[name] = {};
                body(arm.body, nested, scope, depth + 1);
              }
              for (const auto &output : v.outputs)
                values[output] = {};
            } else if constexpr (std::is_same_v<T, syntax::Invocation>) {
              for (const auto &output : v.outputs)
                values[output] = {};
            } else if constexpr (std::is_same_v<T, syntax::Message>) {
              // Unmodelled producers must kill previous evidence for a name.
              values[v.output] = {};
            }
          },
          instruction.value);
    }
  }
  template <typename Arguments>
  void function(const std::optional<syntax::Body> &instructions,
                const Arguments &arguments, const Sorts &scope) {
    if (!instructions || !spend(arguments.size()))
      return;
    Values values;
    for (const auto &argument : arguments)
      values.emplace(argument.name, head(argument.type, scope));
    body(*instructions, values, scope);
  }

public:
  OperatorRecovery(const syntax::Module &module, const Context &context,
                   size_t limit)
      : module(module), context(context), budget({limit, 0, 0, 0}) {}
  std::optional<std::vector<Context::Reference>> record() {
    for (const auto &r : module.structs) {
      if (!spend())
        break;
      records.emplace(r.name, &r);
      recordSorts.emplace(r.name, sorts(r.parameters));
    }
    for (const auto &op : protocol::boundOperationContracts())
      for (const auto &output : op.signature.outputs)
        results[op.name].push_back(logical(output.constructor));
    for (const auto &f : module.functions) {
      if (!spend())
        break;
      auto scope = sorts(f.parameters);
      for (const auto &type : f.results)
        results[f.name].push_back(head(type, scope));
    }
    for (const auto &binding : protocol::sourceOperatorBindings()) {
      Key key{binding.symbol, {}};
      for (const auto &operand : binding.operands)
        key.second.push_back({Head::Kind::Logical, operand});
      operators[key].push_back(
          {binding.contract, true, result(binding.contract)});
    }
    for (const auto &f : module.functions) {
      if (!spend())
        break;
      if (!f.operatorHook)
        continue;
      auto hook = *f.operatorHook;
      if ((hook != "add" && hook != "sub" && hook != "mul" && hook != "neg") ||
          f.arguments.size() != (hook == "neg" ? 1u : 2u))
        continue;
      auto scope = sorts(f.parameters);
      Key key{hook == "add" ? "+" : hook == "mul" ? "*" : "-", {}};
      for (const auto &argument : f.arguments) {
        auto operand = head(argument.type, scope);
        if (!operand)
          break;
        key.second.push_back(*operand);
      }
      if (key.second.size() == f.arguments.size())
        operators[key].push_back({f.name, false, result(f.name)});
    }
    for (const auto &f : module.functions)
      function(f.body, f.arguments, sorts(f.parameters));
    for (const auto &p : module.protocols)
      function(p.body, p.arguments, sorts(p.staticParameters));
    for (const auto &c : module.libraryComponents)
      for (const auto &f : c.functions) {
        auto scope = sorts(c.parameters);
        auto local = sorts(f.parameters);
        scope.insert(local.begin(), local.end());
        function(f.body, f.arguments, scope);
      }
    if (exhausted)
      return std::nullopt;
    return std::move(references);
  }
};
} // namespace zkc::frontend::resolution
#endif
