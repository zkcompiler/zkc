#include "Naturals.h"
#include "zkc/Frontend/Diagnostic.h"
#include <limits>
#include <set>
using namespace llvm;
namespace zkc::frontend::static_eval {
namespace {
using syntax::Expression;
constexpr uint64_t maxNatural = std::numeric_limits<uint32_t>::max();
constexpr unsigned maxDepth = 64;
class Evaluator {
  StringRef text, filename;
  const ProjectInput *project;
  Error error = Error::success();
  WorkBudget &budget;
  std::map<std::string, const syntax::Constant *> constants;
  std::map<std::string, uint64_t> values;
  std::map<std::string, unsigned> constantHeights;
  std::set<std::string> evaluating;
  bool good() { return !error; }
  bool fail(const source::Node &node, StringRef code, const Twine &message) {
    if (good())
      error = project
                  ? diagnostic(*project, node.location.value_or(source::Span{}),
                               code, message)
                  : diagnostic(text, filename,
                               node.location ? node.location->offset : 0, code,
                               message);
    return false;
  }
  bool tick(const source::Node &node) {
    return budget.charge(WorkAccount::AuthoredStatic) ||
           fail(node, "source-staging-limit",
                "compiler work budget exhausted: authored-static");
  }
  bool chargeExpression(const Expression &expression, unsigned depth = 0) {
    if (!tick(expression))
      return false;
    if (depth > maxDepth)
      return fail(expression, "source-constant-depth",
                  "constant dependency/expression depth exceeds 64");
    for (const auto &operand : expression.operands)
      if (!chargeExpression(operand, depth + 1))
        return false;
    return true;
  }
  uint64_t natural(const Expression &e, unsigned depth,
                   unsigned *height = nullptr) {
    if (height)
      *height = 0;
    if (!good())
      return 0;
    if (depth > maxDepth) {
      fail(e, "source-constant-depth",
           "constant dependency/expression depth exceeds 64");
      return 0;
    }
    if (e.kind == Expression::Kind::Index) {
      uint64_t result = 0;
      if (StringRef(e.name).getAsInteger(10, result) || result > maxNatural)
        fail(e, "source-constant-overflow",
             "natural constant exceeds 4294967295");
      return result;
    }
    if (e.kind == Expression::Kind::Name && !e.quoted) {
      auto found = constants.find(e.name);
      if (found == constants.end()) {
        fail(e, "source-constant-reference",
             "unknown natural constant '" + e.name + "'");
        return 0;
      }
      if (auto known = values.find(e.name); known != values.end()) {
        unsigned h = constantHeights.at(e.name);
        if (height)
          *height = h;
        if (depth + h > maxDepth)
          fail(e, "source-constant-depth",
               "constant dependency/expression depth exceeds 64");
        return known->second;
      }
      if (!evaluating.insert(e.name).second) {
        fail(e, "source-constant-cycle",
             "cyclic natural constant '" + e.name + "'");
        return 0;
      }
      unsigned h = 0;
      uint64_t result = natural(found->second->expression, depth + 1, &h);
      if (height)
        *height = h + 1;
      evaluating.erase(e.name);
      if (good()) {
        values.emplace(e.name, result);
        constantHeights.emplace(e.name, h + 1);
      }
      return result;
    }
    if (e.kind != Expression::Kind::Operator || e.operands.size() != 2) {
      fail(e, "source-constant-expression",
           "expected a pure natural expression using +, -, *, /, %");
      return 0;
    }
    unsigned leftHeight = 0, rightHeight = 0;
    uint64_t a = natural(e.operands[0], depth + 1, &leftHeight);
    uint64_t b = natural(e.operands[1], depth + 1, &rightHeight);
    if (height)
      *height = 1 + std::max(leftHeight, rightHeight);
    if (!good())
      return 0;
    uint64_t result = 0;
    if (e.name == "+")
      result = a + b;
    else if (e.name == "*")
      result = a * b;
    else if (e.name == "-") {
      if (a < b) {
        fail(e, "source-constant-underflow", "natural subtraction underflows");
        return 0;
      }
      result = a - b;
    } else if (e.name == "/" || e.name == "%") {
      if (!b) {
        fail(e, "source-constant-zero-divisor", "natural division by zero");
        return 0;
      }
      result = e.name == "/" ? a / b : a % b;
    } else
      fail(e, "source-constant-expression", "unsupported natural operator");
    if (result > maxNatural)
      fail(e, "source-constant-overflow", "natural arithmetic overflows");
    return result;
  }

public:
  Evaluator(StringRef text, StringRef filename, const ProjectInput *project,
            WorkBudget &budget)
      : text(text), filename(filename), project(project), budget(budget) {}
  Expected<std::map<std::string, uint64_t>>
  run(ArrayRef<syntax::Constant> input) {
    for (const auto &constant : input) {
      // One declaration and every written expression occurrence. Charge before
      // maps/evaluation, independently of memoization and declaration order.
      if (!tick(constant) || !chargeExpression(constant.expression))
        return std::move(error);
      if (!constants.emplace(constant.name, &constant).second) {
        fail(constant, "source-static-duplicate", "duplicate natural constant");
        return std::move(error);
      }
    }
    for (const auto &constant : input) {
      Expression expression;
      expression.name = constant.name;
      expression.location = constant.location;
      natural(expression, 0);
      if (!good())
        return std::move(error);
    }
    return std::move(values);
  }
};
} // namespace
Expected<std::map<std::string, uint64_t>>
evaluateNaturals(ArrayRef<syntax::Constant> constants, StringRef text,
                 StringRef filename, const ProjectInput *project,
                 WorkBudget &budget) {
  return Evaluator(text, filename, project, budget).run(constants);
}
} // namespace zkc::frontend::static_eval
