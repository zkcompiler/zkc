#include "../lib/Frontend/Resolution/OperatorRecovery.h"
#include "support/NativeCases.h"

using namespace zkc;
using namespace zkc::frontend;
using namespace zkc::test;

namespace {
syntax::Module expressionModule(unsigned depth) {
  syntax::Expression expression;
  expression.kind = syntax::Expression::Kind::Boolean;
  for (unsigned i = 0; i < depth; ++i) {
    syntax::Expression parent;
    parent.kind = syntax::Expression::Kind::Operator;
    parent.name = "-";
    parent.operands.push_back(std::move(expression));
    expression = std::move(parent);
  }
  syntax::Exit exit;
  exit.expression = std::move(expression);
  syntax::Instruction instruction;
  instruction.value = std::move(exit);
  syntax::Function function;
  function.name = "Example";
  function.body = syntax::Body{std::move(instruction)};
  syntax::Module module;
  module.functions.push_back(std::move(function));
  return module;
}
resolution::Context context() {
  return resolution::Context(ProjectInput::single(Input::withoutFile("")));
}
} // namespace

int main() {
  Cases cases;
  cases.run("recovery edges remain local to the dependency analysis", [] {
    auto resolved = resolution::resolve(ProjectInput::single(Input::withoutFile(
        " struct R { value: index } #[operator(add)] fn Add(a: R, b: R) -> R { "
        "return a; } fn User(a: R, b: R) -> R { return a + b; } ")));
    require(resolved.diagnostics.empty(), "fixture resolves independently");
    auto &module = std::get<syntax::Module>(resolved.content);
    const auto &project = *resolved.context;
    auto original = project.references.size();
    auto edges = resolution::OperatorRecovery(module, project, 4096).record();
    require(edges && edges->size() == 1 && edges->front().source == "User" &&
                edges->front().target == "Add",
            "known nominal operands supply a local dependency");
    require(project.references.size() == original,
            "successful recovery does not publish provenance or routing facts");

    // A producer outside this abstract interpretation must kill old evidence.
    // This models a message output shadowing a name in a protocol body.
    syntax::Message message;
    message.output = "a";
    syntax::Instruction instruction;
    instruction.value = std::move(message);
    auto &body = *module.functions.back().body;
    body.insert(body.begin(), std::move(instruction));
    edges = resolution::OperatorRecovery(module, project, 4096).record();
    require(edges && edges->empty(),
            "an unmodelled message result does not retain the old record head");
  });
  cases.run("bounded recovery does not authorize an unknown operator", [] {
    auto module = expressionModule(2);
    auto project = context();
    require(bool(resolution::OperatorRecovery(module, project, 1024).record()),
            "small dependency walk completes");
    require(project.references.empty(), "boolean negation has no known hook");
  });
  cases.run("work exhaustion retains preexisting reference evidence", [] {
    auto module = expressionModule(8);
    auto project = context();
    project.references.push_back({"Caller", "Callee", {}, false});
    require(!resolution::OperatorRecovery(module, project, 4).record(),
            "recovery stops within its independent work allowance");
    require(project.references.size() == 1 &&
                project.references.front().source == "Caller" &&
                project.references.front().target == "Callee",
            "failed recovery cannot replace original dependency evidence");
  });
  cases.run("depth limit is independent of work allowance", [] {
    auto module = expressionModule(512);
    auto project = context();
    require(!resolution::OperatorRecovery(module, project, 262144).record(),
            "internal syntax cannot bypass the recovery stack bound");
    require(project.references.empty(), "incomplete walk publishes no edges");
  });
  cases.run("separate source expression and block bounds fit together", [] {
    auto module = expressionModule(64);
    auto &body = *module.functions.front().body;
    for (unsigned i = 0; i < 64; ++i) {
      syntax::Conditional conditional;
      conditional.condition.kind = syntax::Expression::Kind::Boolean;
      conditional.thenBody = std::move(body);
      syntax::Instruction instruction;
      instruction.value = std::move(conditional);
      body = {std::move(instruction)};
    }
    auto project = context();
    require(
        bool(resolution::OperatorRecovery(module, project, 262144).record()),
        "combined traversal does not narrow the separate source bounds");
  });
  return cases.result();
}
