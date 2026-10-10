#include "../lib/Language/BindingWitness.h"
#include "../lib/Language/OperatorInference.h"
#include "support/NativeCases.h"
using namespace zkc::language;
using namespace zkc::language::detail;
using zkc::test::require;
namespace {
constexpr Span site{{0}, 0, 1};
Declaration signature(unsigned id, std::vector<Type> inputs, Type output) {
  Declaration result;
  result.id = {id};
  result.kind = Declaration::Kind::Math;
  result.qualifiedName = "test::operation" + std::to_string(id);
  result.span = site;
  for (auto &type : inputs)
    result.inputs.push_back({"x", type, {}, site});
  result.outputs.push_back({"out", std::move(output), {}, site});
  return result;
}
OperatorInference::Candidate candidate(unsigned id) {
  return {{{id}, {}}, {}, site};
}
struct Fixture {
  Limits limits;
  Work work{limits};
  std::vector<Declaration> declarations;
  Semantics semantics{declarations, {}, work};
  TypeInference types{semantics};
  OperatorInference operators{types, semantics, declarations};
  TypeInference::Variable known(Type type) { return types.known(type, site); }
  void refusal(llvm::StringRef code) {
    auto result = operators.solve(site, [] { return true; });
    require(!result && semantics.diagnostic &&
                semantics.diagnostic->code == code,
            "unexpected operator inference outcome");
  }
};
} // namespace
int main() {
  zkc::test::Cases cases;
  const Type field(Type::Kind::Field, "bls12-381.fr"), index(Type::Kind::Index),
      boolean;
  cases.run("result types constrain literals without a default scalar", [&] {
    for (const auto &expected : {field, index}) {
      Fixture f;
      f.declarations = {signature(0, {field, field}, field),
                        signature(1, {index, index}, index)};
      auto left = f.types.fresh(site), right = f.types.fresh(site);
      f.types.requireKinds(left, {Type::Kind::Field, Type::Kind::Index}, site);
      f.types.requireKinds(right, {Type::Kind::Field, Type::Kind::Index}, site);
      f.operators.add(0, site, {left, right}, f.known(expected),
                      {candidate(0), candidate(1)});
      auto result = f.operators.solve(site, [] { return true; });
      require(result && result->size() == 1,
              "literal operands did not resolve");
      require(result->at(0).constraints.target.declaration.index ==
                  (expected == field ? 0u : 1u),
              "result annotation selected the wrong input signature");
    }
  });
  cases.run("return context cannot choose meanings for fixed inputs", [&] {
    Fixture f;
    f.declarations = {signature(0, {field, field}, field),
                      signature(1, {field, field}, boolean)};
    f.operators.add(0, site, {f.known(field), f.known(field)}, f.known(field),
                    {candidate(0), candidate(1)});
    f.refusal("source.operator");
  });
  cases.run("joint constraints settle coupled occurrences", [&] {
    Fixture f;
    f.declarations = {signature(0, {field, field}, field),
                      signature(1, {index, index}, index),
                      signature(2, {field, index}, boolean)};
    auto left = f.types.fresh(site), right = f.types.fresh(site);
    f.operators.add(0, site, {left, left}, left, {candidate(0), candidate(1)});
    f.operators.add(1, site, {right, right}, right,
                    {candidate(0), candidate(1)});
    f.operators.add(2, site, {left, right}, f.known(boolean), {candidate(2)});
    auto result = f.operators.solve(site, [] { return true; });
    require(result && result->size() == 3, "coupled statement did not resolve");
    require(f.types.get(left, site) == field &&
                f.types.get(right, site) == index,
            "constraints did not flow through the complete statement");
  });
  cases.run("all branches are explored before accepting uniqueness", [&] {
    Fixture f;
    f.declarations = {signature(0, {field, field}, boolean),
                      signature(1, {index, index}, boolean)};
    auto operand = f.types.fresh(site);
    f.operators.add(0, site, {operand, operand}, f.known(boolean),
                    {candidate(0), candidate(1)});
    f.refusal("source.operator");
  });
  cases.run("an unresolved surrounding call does not become a solution", [&] {
    Fixture f;
    f.declarations = {signature(0, {field, field}, field)};
    f.operators.add(0, site, {f.known(field), f.known(field)}, f.known(field),
                    {candidate(0)});
    auto result = f.operators.solve(site, [] { return false; });
    require(!result && f.semantics.diagnostic &&
                f.semantics.diagnostic->code == "source.inference",
            "unresolved branch was silently accepted");
  });
  cases.run("failed probes roll back equations but never work", [&] {
    Fixture f;
    auto variable = f.types.fresh(site);
    auto checkpoint = f.types.checkpoint(site);
    require(checkpoint.has_value(), "checkpoint failed");
    f.types.equal(variable, f.known(field), site);
    auto before = f.work.used;
    require(f.types.restore(*checkpoint, site), "restore failed");
    require(f.work.used > before && !f.types.get(variable, site),
            "restore refunded work or retained speculative type");
    require(f.types.equal(variable, f.known(index), site),
            "speculative field type leaked into another branch");
  });
  cases.run("candidate search respects the invocation work ceiling", [&] {
    Fixture f;
    f.declarations = {signature(0, {field, field}, field),
                      signature(1, {index, index}, index)};
    auto operand = f.types.fresh(site);
    f.operators.add(0, site, {operand, operand}, f.known(field),
                    {candidate(0), candidate(1)});
    f.limits.work = f.work.used + 1;
    f.refusal("source.limit");
  });
  cases.run(
      "independent binding evidence rejects scope and target mutations", [&] {
        for (unsigned mutation = 0; mutation < 5; ++mutation) {
          Fixture f;
          f.declarations = {signature(0, {field, field}, field),
                            signature(1, {index, index}, index)};
          std::vector<OperatorBinding> family{{"+", {{0}, {}}, {}, site},
                                              {"+", {{1}, {}}, {}, site}};
          CallBinding witness{{{0}, {}}, {}, {{0}, {1}}, "+", {}, site};
          for (const auto &binding : family)
            witness.family.push_back(
                operatorBindingKey(binding, f.declarations));
          require(checkOperatorWitness(f.semantics, f.declarations, family,
                                       witness, {field, field}, field, site),
                  "valid scope witness refused");
          if (mutation == 0)
            witness.family.pop_back();
          if (mutation == 1)
            witness.target.declaration = {1};
          if (mutation == 2)
            witness.arguments.push_back(field);
          if (mutation == 3)
            witness.origin->begin = 1;
          if (mutation == 4)
            witness.symbol = "*";
          require(!checkOperatorWitness(f.semantics, f.declarations, family,
                                        witness, {field, field}, field, site) &&
                      f.semantics.diagnostic &&
                      f.semantics.diagnostic->code == "source.binding-witness",
                  "corrupted scope witness accepted");
        }
      });
  cases.run("operand witness refuses reordered operator input mappings", [&] {
    for (unsigned mutation = 0; mutation < 2; ++mutation) {
      Fixture f;
      CallBinding witness{{{0}, {}}, {}, {{0}, {1}}, "-", {}, site};
      std::vector<unsigned> order{0, 1};
      require(
          checkOperatorOperands(f.semantics, witness, order, {{0}, {1}}, site),
          "valid operands refused");
      if (mutation == 0)
        std::swap(order[0], order[1]);
      else
        std::swap(witness.operands[0], witness.operands[1]);
      require(!checkOperatorOperands(f.semantics, witness, order, {{0}, {1}},
                                     site) &&
                  f.semantics.diagnostic &&
                  f.semantics.diagnostic->code == "source.binding-witness",
              "mutated authored operand order accepted");
    }
  });
  cases.run("native action is checked independently of call resolution", [&] {
    for (unsigned mutation = 0; mutation < 4; ++mutation) {
      Fixture f;
      f.declarations = {signature(0, {field, field}, field)};
      f.declarations.front().primitive =
          PrimitiveDefinition{"field.add", {field}};
      Body body;
      body.mode = Body::Mode::Math;
      body.values = {{field, {}, site}, {field, {}, site}, {field, {}, site}};
      Operation operation{
          MathValue{zkc::MathematicalIdentity::FieldAdd, {{0}, {1}}, {}},
          {{2}},
          site,
          0};
      operation.binding = CallBinding{{{0}, {}}, {}, {{0}, {1}}, {}, {}, {}};
      require(checkCallAction(f.semantics, f.declarations, body, operation),
              "valid native call witness refused");
      auto &action = std::get<MathValue>(operation.action);
      if (mutation == 0)
        std::swap(action.operands[0], action.operands[1]);
      if (mutation == 1)
        action.identity = zkc::MathematicalIdentity::FieldMultiply;
      if (mutation == 2)
        action.staticArguments.push_back(field);
      if (mutation == 3)
        operation.binding->operands.front() = {2};
      require(!checkCallAction(f.semantics, f.declarations, body, operation) &&
                  f.semantics.diagnostic &&
                  f.semantics.diagnostic->code == "source.binding-witness",
              "corrupted native call witness accepted");
    }
  });
  return cases.result();
}
