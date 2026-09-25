#include "Captures.h"
#include <algorithm>
#include <set>
using namespace llvm;
namespace zkc::frontend::semantics {
namespace {
using Names = std::set<std::string>;
class FreePlaces {
  Names available, seen;
  source::Names places;

  void use(StringRef name, const Names &bound) {
    auto root = name.split('.').first.str();
    if (bound.count(root) || !available.count(root) ||
        !seen.insert(name.str()).second)
      return;
    // Capture the union of inferred places. A whole aggregate subsumes its
    // projections, but occupies their earliest first-use position. This does
    // not relax the body checker: repeated affine reads still refuse there.
    size_t first = places.size();
    for (size_t i = 0; i < places.size(); ++i) {
      if (name == places[i] || name.starts_with(places[i] + "."))
        return;
      if (StringRef(places[i]).starts_with(name.str() + "."))
        first = std::min(first, i);
    }
    if (first == places.size())
      places.push_back(name.str());
    else {
      places[first] = name.str();
      for (size_t i = places.size(); i-- > first + 1;)
        if (StringRef(places[i]).starts_with(name.str() + "."))
          places.erase(places.begin() + i);
    }
  }
  void uses(const source::Names &names, const Names &bound) {
    for (const auto &n : names)
      use(n, bound);
  }
  void expression(const syntax::Expression &e, const Names &bound) {
    // Retain literal place paths until typed resolution. The ordinary checker
    // distinguishes aggregate projections from runtime collection indexing.
    auto place = [&](auto &&self, const syntax::Expression &v) -> std::string {
      if (v.kind == syntax::Expression::Kind::Name && !v.quoted)
        return v.name;
      if (v.kind != syntax::Expression::Kind::Get || v.operands.size() != 2 ||
          v.operands[1].kind != syntax::Expression::Kind::Index)
        return {};
      auto base = self(self, v.operands.front());
      return base.empty() ? std::string{} : base + "." + v.operands[1].name;
    };
    if (e.kind == syntax::Expression::Kind::Get) {
      auto p = place(place, e);
      if (!p.empty()) {
        use(p, bound);
        return;
      }
    }
    if (e.kind == syntax::Expression::Kind::Name && !e.quoted)
      use(e.name, bound);
    for (const auto &o : e.operands)
      expression(o, bound);
    if (e.traversal) {
      auto inner = bound;
      inner.insert(e.traversal->element);
      if (!e.traversal->state.empty())
        inner.insert(e.traversal->state);
      body(e.traversal->body, std::move(inner));
    }
  }

public:
  explicit FreePlaces(Names available) : available(std::move(available)) {}
  void body(const syntax::Body &body, Names bound = {}) {
    for (const auto &i : body)
      std::visit(
          [&](const auto &v) {
            using T = std::decay_t<decltype(v)>;
            if constexpr (std::is_same_v<T, syntax::Call>) {
              for (size_t i = 0; i < v.inputs.size(); ++i)
                if (i >= v.inputAtoms.size() ||
                    v.inputAtoms[i].kind == syntax::Atom::Kind::Name)
                  use(v.inputs[i], bound);
              bound.insert(v.outputs.begin(), v.outputs.end());
            } else if constexpr (std::is_same_v<T, syntax::Binding>) {
              expression(v.expression, bound);
              if (v.assignment)
                uses(v.outputs, bound);
              bound.insert(v.outputs.begin(), v.outputs.end());
            } else if constexpr (std::is_same_v<T, syntax::Exit>) {
              expression(v.expression, bound);
            } else if constexpr (std::is_same_v<T, source::Return> ||
                                 std::is_same_v<T, source::Yield>) {
              uses(v.values, bound);
            } else if constexpr (std::is_same_v<T, syntax::Conditional>) {
              expression(v.condition, bound);
              this->body(v.thenBody, bound);
              this->body(v.elseBody, bound);
              bound.insert(v.outputs.begin(), v.outputs.end());
            } else if constexpr (std::is_same_v<T, syntax::Match>) {
              use(v.input, bound);
              for (const auto &a : v.arms) {
                auto inner = bound;
                inner.insert(a.payload.begin(), a.payload.end());
                this->body(a.body, std::move(inner));
              }
              bound.insert(v.outputs.begin(), v.outputs.end());
            } else if constexpr (std::is_same_v<T, syntax::For> ||
                                 std::is_same_v<T, syntax::Loop> ||
                                 std::is_same_v<T, syntax::ArrayTraversal>) {
              auto inner = bound;
              if constexpr (std::is_same_v<T, syntax::For>) {
                expression(v.lower, bound);
                expression(v.upper, bound);
                inner.insert(v.induction);
              } else if constexpr (std::is_same_v<T, syntax::ArrayTraversal>) {
                use(v.input, bound);
                inner.insert(v.element);
              }
              for (const auto &p : v.carried) {
                use(p.second, bound);
                inner.insert(p.first);
              }
              this->body(v.body, std::move(inner));
              bound.insert(v.outputs.begin(), v.outputs.end());
            } else if constexpr (std::is_same_v<T, syntax::Placement>) {
              this->body(v.body, bound);
              bound.insert(v.outputs.begin(), v.outputs.end());
            } else if constexpr (std::is_same_v<T, syntax::Invocation>) {
              uses(v.inputs, bound);
              bound.insert(v.outputs.begin(), v.outputs.end());
            } else if constexpr (std::is_same_v<T, source::Message>) {
              use(v.input, bound);
              bound.insert(v.output);
            } else if constexpr (std::is_same_v<T, syntax::Finish>) {
              for (const auto &p : v.values)
                use(p.second, bound);
            }
          },
          i.value);
  }
  source::Names take() { return std::move(places); }
};
void infer(syntax::Body &body, Names bound);
void inferExpression(syntax::Expression &e, const Names &bound) {
  for (auto &operand : e.operands)
    inferExpression(operand, bound);
  if (!e.traversal)
    return;
  Names parameters{e.traversal->element};
  if (!e.traversal->state.empty())
    parameters.insert(e.traversal->state);
  FreePlaces free(bound);
  free.body(e.traversal->body, parameters);
  e.traversal->captures = free.take();
  parameters.insert(bound.begin(), bound.end());
  infer(e.traversal->body, std::move(parameters));
}
void infer(syntax::Body &body, Names bound) {
  for (auto &i : body)
    std::visit(
        [&](auto &v) {
          using T = std::decay_t<decltype(v)>;
          if constexpr (std::is_same_v<T, syntax::Binding> ||
                        std::is_same_v<T, syntax::Exit>)
            inferExpression(v.expression, bound);
          if constexpr (std::is_same_v<T, syntax::Conditional>) {
            inferExpression(v.condition, bound);
            if (v.explicitRegion && !v.explicitCaptures) {
              FreePlaces free(bound);
              free.body(v.thenBody);
              free.body(v.elseBody);
              v.captures = free.take();
            }
            infer(v.thenBody, bound);
            infer(v.elseBody, bound);
          } else if constexpr (std::is_same_v<T, syntax::Match>) {
            if (!v.explicitCaptures) {
              FreePlaces free(bound);
              for (const auto &a : v.arms)
                free.body(a.body, Names(a.payload.begin(), a.payload.end()));
              v.captures = free.take();
            }
            for (auto &a : v.arms) {
              auto inner = bound;
              inner.insert(a.payload.begin(), a.payload.end());
              infer(a.body, std::move(inner));
            }
          } else if constexpr (std::is_same_v<T, syntax::For> ||
                               std::is_same_v<T, syntax::Loop> ||
                               std::is_same_v<T, syntax::ArrayTraversal>) {
            Names parameters;
            if constexpr (std::is_same_v<T, syntax::For>) {
              inferExpression(v.lower, bound);
              inferExpression(v.upper, bound);
              parameters.insert(v.induction);
            }
            if constexpr (std::is_same_v<T, syntax::ArrayTraversal>)
              parameters.insert(v.element);
            for (const auto &p : v.carried)
              parameters.insert(p.first);
            if (!v.explicitCaptures) {
              FreePlaces free(bound);
              free.body(v.body, parameters);
              v.captures = free.take();
            }
            parameters.insert(bound.begin(), bound.end());
            infer(v.body, std::move(parameters));
          } else if constexpr (std::is_same_v<T, syntax::Placement>)
            infer(v.body, bound);
          // All region forms expose their declared outputs to following code.
          if constexpr (std::is_same_v<T, syntax::Call> ||
                        std::is_same_v<T, syntax::Binding> ||
                        std::is_same_v<T, syntax::Conditional> ||
                        std::is_same_v<T, syntax::Match> ||
                        std::is_same_v<T, syntax::For> ||
                        std::is_same_v<T, syntax::Loop> ||
                        std::is_same_v<T, syntax::ArrayTraversal> ||
                        std::is_same_v<T, syntax::Placement> ||
                        std::is_same_v<T, syntax::Invocation>)
            bound.insert(v.outputs.begin(), v.outputs.end());
          else if constexpr (std::is_same_v<T, source::Message>)
            bound.insert(v.output);
        },
        i.value);
}
template <class Function> void function(Function &f) {
  if (!f.body)
    return;
  Names bound;
  for (const auto &a : f.arguments)
    bound.insert(a.name);
  infer(*f.body, std::move(bound));
}
} // namespace
void inferCaptures(syntax::Module &m) {
  for (auto &f : m.functions)
    function(f);
  for (auto &p : m.protocols)
    function(p);
  for (auto &c : m.libraryComponents)
    for (auto &f : c.functions)
      function(f);
}
bool hasLexicalTraversals(const syntax::Body &body) {
  auto expression = [&](auto &&self, const syntax::Expression &e) -> bool {
    if (e.traversal)
      return true;
    for (const auto &operand : e.operands)
      if (self(self, operand))
        return true;
    return false;
  };
  for (const auto &i : body)
    if (std::visit(
            [&](const auto &v) -> bool {
              using T = std::decay_t<decltype(v)>;
              if constexpr (std::is_same_v<T, syntax::Binding> ||
                            std::is_same_v<T, syntax::Exit>)
                return expression(expression, v.expression);
              else if constexpr (std::is_same_v<T, syntax::Conditional>)
                return expression(expression, v.condition) ||
                       hasLexicalTraversals(v.thenBody) ||
                       hasLexicalTraversals(v.elseBody);
              else if constexpr (std::is_same_v<T, syntax::Match>) {
                for (const auto &arm : v.arms)
                  if (hasLexicalTraversals(arm.body))
                    return true;
                return false;
              } else if constexpr (std::is_same_v<T, syntax::For>)
                return expression(expression, v.lower) ||
                       expression(expression, v.upper) ||
                       hasLexicalTraversals(v.body);
              else if constexpr (std::is_same_v<T, syntax::Loop> ||
                                 std::is_same_v<T, syntax::ArrayTraversal> ||
                                 std::is_same_v<T, syntax::Placement>)
                return hasLexicalTraversals(v.body);
              else
                return false;
            },
            i.value))
      return true;
  return false;
}
} // namespace zkc::frontend::semantics
