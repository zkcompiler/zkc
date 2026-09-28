#ifndef ZKC_FRONTEND_SEMANTICS_OPERATORS_H
#define ZKC_FRONTEND_SEMANTICS_OPERATORS_H

#include "../Resolution/Project.h"
#include "../Static/Structural.h"
#include "Local.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "llvm/ADT/STLExtras.h"
#include <functional>
#include <set>

namespace zkc::frontend {
/// Heads carry either a resolved nominal declaration identity or an installed
/// logical constructor. Static arguments and result types never select a hook.
inline std::string nominalOperatorHead(const library::QualifiedDecl &identity) {
  return "record:" + library::identity(identity);
}
inline std::string logicalOperatorHead(llvm::StringRef constructor) {
  for (const auto &type : protocol::boundTypeConstructors())
    if (type.name == constructor)
      return "logical:" + constructor.str();
  return {};
}
inline std::string operatorHead(llvm::StringRef type,
                                const resolution::Context &project) {
  // The local elaborator tags retained record shapes explicitly. A logical
  // type and a record with the same readable name must remain distinct.
  if (type.consume_front("record:")) {
    if (const auto *declaration = project.lookup(type))
      if (declaration->kind == resolution::Declaration::Kind::Record)
        return nominalOperatorHead(declaration->identity);
    return {};
  }
  auto parsed = splitLogical(type);
  return parsed ? logicalOperatorHead(parsed->constructor) : std::string{};
}

class OperatorBindings {
  struct Candidate {
    std::string symbol;
    std::vector<std::string> heads;
    OperatorTarget target;
  };
  std::vector<Candidate> candidates;

public:
  using Failure = std::function<void(const source::Node &, llvm::StringRef,
                                     const llvm::Twine &)>;
  using Head = std::function<std::string(const syntax::Function &,
                                         const syntax::Type &)>;

  /// Form the whole dependency union, including unused declarations. Nominal
  /// ownership uses resolved package identities; an alias cannot create it.
  bool form(const syntax::Module &module, const resolution::Context &project,
            const Head &head, const Failure &fail) {
    candidates.clear();
    std::set<std::pair<std::string, std::vector<std::string>>> keys;
    auto add = [&](Candidate candidate, const source::Node &node) {
      if (!keys.emplace(candidate.symbol, candidate.heads).second) {
        fail(node, "source-operator-duplicate",
             "duplicate operator binding for the same nominal operand heads");
        return false;
      }
      candidates.push_back(std::move(candidate));
      return true;
    };
    for (const auto &binding : protocol::sourceOperatorBindings()) {
      auto operation = llvm::find_if(
          protocol::boundOperationContracts(),
          [&](const auto &op) { return op.name == binding.contract; });
      const auto arity = binding.operands.size();
      bool valid =
          operation != protocol::boundOperationContracts().end() &&
          protocol::authoringStage(binding.contract) ==
              protocol::AuthoringStage::Source &&
          operation->signature.inputs.size() == arity &&
          operation->signature.outputs.size() == 1 &&
          binding.order.size() == arity &&
          ((arity == 1 && binding.symbol == "-") ||
           (arity == 2 && (binding.symbol == "+" || binding.symbol == "-" ||
                           binding.symbol == "*")));
      std::set<unsigned> ports;
      for (unsigned k = 0; valid && k < arity; ++k)
        valid = binding.order[k] < arity &&
                ports.insert(binding.order[k]).second &&
                operation->signature.inputs[k].constructor ==
                    binding.operands[binding.order[k]];
      Candidate candidate{
          binding.symbol,
          {},
          {syntax::Target::operation(binding.contract), binding.order}};
      for (const auto &operand : binding.operands) {
        candidate.heads.push_back(logicalOperatorHead(operand));
        valid &= !candidate.heads.back().empty();
      }
      if (!valid) {
        fail(module, "source-operator-table",
             "installed operator binding disagrees with its logical contract");
        return false;
      }
      if (!add(std::move(candidate), module))
        return false;
    }
    for (const auto &function : module.functions) {
      if (!function.operatorHook)
        continue;
      const auto &hook = *function.operatorHook;
      if (hook != "add" && hook != "sub" && hook != "mul" && hook != "neg") {
        fail(function, "source-operator-attribute", "unknown operator hook");
        return false;
      }
      if (function.arguments.size() != (hook == "neg" ? 1u : 2u)) {
        fail(function, "source-operator-arity",
             "operator hook has the wrong number of arguments");
        return false;
      }
      if (function.results.size() != 1 || function.results.front().product) {
        fail(function, "source-operator-result",
             "operator function must return one non-product value");
        return false;
      }
      if (!function.body) {
        fail(function, "source-operator-body",
             "source operator binding requires a checked function body");
        return false;
      }
      Candidate candidate{hook == "add"   ? "+"
                          : hook == "mul" ? "*"
                                          : "-",
                          {},
                          {syntax::Target::declaration(function.name), {}}};
      const auto *owner = project.lookup(function.name);
      bool ownsOperand = false;
      for (const auto &argument : function.arguments) {
        const auto &type = argument.type;
        std::string resolved;
        if (!type.product && !type.quoted() && type.members.empty())
          if (const auto *record = project.lookup(type.name))
            if (record->kind == resolution::Declaration::Kind::Record) {
              resolved = nominalOperatorHead(record->identity);
              ownsOperand |= owner && owner->owner == record->owner;
            }
        if (resolved.empty())
          resolved = head(function, type);
        if (resolved.empty()) {
          fail(type, "source-operator-head",
               "operator operands require known nominal constructors; "
               "use a named function for opaque or structural types");
          return false;
        }
        candidate.target.order.push_back(candidate.heads.size());
        candidate.heads.push_back(std::move(resolved));
      }
      if (!ownsOperand) {
        fail(function, "source-operator-ownership",
             "operator function must own at least one nominal operand "
             "constructor; imported aliases do not confer ownership");
        return false;
      }
      if (!add(std::move(candidate), function))
        return false;
    }
    return true;
  }

  std::optional<OperatorTarget> resolve(const source::Node &node,
                                        llvm::StringRef symbol,
                                        llvm::ArrayRef<std::string> heads,
                                        const resolution::Context &project,
                                        const Failure &fail) const {
    for (const auto &candidate : candidates) {
      if (candidate.symbol != symbol ||
          llvm::ArrayRef(candidate.heads) != heads)
        continue;
      const auto &target = candidate.target.target;
      if (target.kind == syntax::Target::Kind::Operation
              ? !project.operationAvailable(node, target.symbol)
              : !project.sourceOperatorAvailable(node, target.symbol))
        continue;
      return candidate.target;
    }
    fail(node, "source-operator-unresolved",
         "no visible operator binding for these nominal operand heads; "
         "use an imported named function");
    return {};
  }
};
} // namespace zkc::frontend
#endif
