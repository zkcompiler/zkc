#include "../lib/Language/BindingWitness.h"
#include "../lib/Language/OperatorInference.h"
#include "support/NativeCases.h"
#include <numeric>
using namespace zkc::language;
using namespace zkc::language::detail;
using zkc::test::require;
namespace {
constexpr Span site{{0}, 0, 1};
using Position = NotationDescriptor::Position;
using Association = NotationDescriptor::Association;
std::shared_ptr<const NotationDescriptor>
descriptor(Position position = Position::Infix, unsigned arity = 2,
           std::string symbol = "+") {
  NotationDescriptor value;
  value.position = position;
  value.association =
      position == Position::Infix ? Association::Left : Association::None;
  value.symbol = std::move(symbol);
  value.arity = arity;
  value.precedence = position == Position::Delimited ? 0 : 65;
  if (position == Position::Infix && value.symbol == "==") {
    value.association = Association::None;
    value.precedence = 50;
  }
  if (position == Position::Delimited)
    value.closing = "⟫";
  return std::make_shared<const NotationDescriptor>(std::move(value));
}
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
          auto notation = descriptor();
          std::vector<OperatorBinding> family{
              {"+", {{0}, {}}, {}, site, notation},
              {"+", {{1}, {}}, {}, site, notation}};
          CallBinding witness{{{0}, {}}, {},   {{0}, {1}}, "+",
                              {},        site, *notation};
          for (const auto &binding : family)
            witness.family.push_back(
                operatorBindingKey(binding, f.declarations));
          require(checkOperatorWitness(f.semantics, f.declarations, family,
                                       *notation, witness, {field, field},
                                       field, site),
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
                                        *notation, witness, {field, field},
                                        field, site) &&
                      f.semantics.diagnostic &&
                      f.semantics.diagnostic->code == "source.binding-witness",
                  "corrupted scope witness accepted");
        }
      });
  cases.run("operand witness refuses reordered operator input mappings", [&] {
    for (unsigned mutation = 0; mutation < 2; ++mutation) {
      Fixture f;
      auto notation = descriptor(Position::Infix, 2, "-");
      CallBinding witness{{{0}, {}}, {}, {{0}, {1}}, "-", {}, site, *notation};
      std::vector<unsigned> order{0, 1};
      require(checkOperatorOperands(f.semantics, *notation, witness, order,
                                    {{0}, {1}}, site),
              "valid operands refused");
      if (mutation == 0)
        std::swap(order[0], order[1]);
      else
        std::swap(witness.operands[0], witness.operands[1]);
      require(!checkOperatorOperands(f.semantics, *notation, witness, order,
                                     {{0}, {1}}, site) &&
                  f.semantics.diagnostic &&
                  f.semantics.diagnostic->code == "source.binding-witness",
              "mutated authored operand order accepted");
    }
  });
  cases.run("named call input mappings must be permutations", [&] {
    for (const auto &mapping :
         std::vector<std::vector<unsigned>>{{0, 0}, {0, 2}, {0}}) {
      Fixture f;
      require(checkCallInputMapping(f.semantics, {1, 0}, 2, site),
              "valid named mapping refused");
      require(!checkCallInputMapping(f.semantics, mapping, 2, site) &&
                  f.semantics.diagnostic &&
                  f.semantics.diagnostic->code == "source.binding-witness",
              "invalid named mapping accepted");
    }
  });
  cases.run("local and protocol call actions retain primitive identity", [&] {
    for (auto mode : {Body::Mode::Local, Body::Mode::Protocol})
      for (unsigned mutation = 0; mutation < 3; ++mutation) {
        Fixture f;
        f.declarations = {signature(0, {index, index}, index)};
        auto &callee = f.declarations.front();
        callee.kind = Declaration::Kind::Local;
        callee.primitive = PrimitiveDefinition{"index.add", {}};
        Body body;
        body.mode = mode;
        body.values = {{index, {}, site}, {index, {}, site}, {index, {}, site}};
        LocalPrimitive local{"index.add", {{0}, {1}}, {}};
        local.bindingArguments = std::vector<Type>{};
        HelperCall helper{{0}, {{0}, {1}}, {}, {}, {}};
        Operation op{local, {{2}}, site, 0};
        if (mode == Body::Mode::Protocol)
          op.action = helper;
        op.binding = CallBinding{{{0}, {}}, {}, {{0}, {1}}, {}, {}, {}, {}};
        require(checkCallAction(f.semantics, f.declarations, body, op),
                "valid primitive call action refused");
        if (mode == Body::Mode::Local) {
          auto &action = std::get<LocalPrimitive>(op.action);
          if (mutation == 0)
            action.contract = "index.sub";
          if (mutation == 1)
            action.bindingArguments->push_back(field);
          if (mutation == 2)
            op.action = helper;
        } else {
          auto &action = std::get<HelperCall>(op.action);
          if (mutation == 0)
            action.callee = {1};
          if (mutation == 1)
            action.arguments.push_back(field);
          if (mutation == 2)
            op.action = local;
        }
        require(!checkCallAction(f.semantics, f.declarations, body, op) &&
                    f.semantics.diagnostic &&
                    f.semantics.diagnostic->code == "source.binding-witness",
                "mutated primitive call action accepted");
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
      operation.binding =
          CallBinding{{{0}, {}}, {}, {{0}, {1}}, {}, {}, {}, {}};
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
  cases.run(
      "mathematical primitive actions agree across executable modes", [&] {
        for (bool scalar : {false, true})
          for (auto mode : {Body::Mode::Local, Body::Mode::Protocol}) {
            Fixture f;
            auto type = scalar ? field : boolean;
            auto identity = scalar ? "field.add" : "bool.and";
            auto mathIdentity = scalar ? zkc::MathematicalIdentity::FieldAdd
                                       : zkc::MathematicalIdentity::BooleanAnd;
            f.declarations = {signature(0, {type, type}, type)};
            f.declarations.front().primitive =
                PrimitiveDefinition{identity, scalar ? std::vector<Type>{field}
                                                     : std::vector<Type>{}};
            Body body;
            body.mode = mode;
            body.values = {
                {type, {}, site}, {type, {}, site}, {type, {}, site}};
            Operation op{
                MathValue{mathIdentity, {{0}, {1}}, {}}, {{2}}, site, 0};
            if (mode == Body::Mode::Local) {
              if (scalar)
                op.action = LocalPrimitive{identity, {{0}, {1}}, {}};
              else
                op.action = HelperCall{{0}, {{0}, {1}}, {}, {}, {}};
            }
            op.binding = CallBinding{{{0}, {}}, {}, {{0}, {1}}, {}, {}, {}, {}};
            require(checkCallAction(f.semantics, f.declarations, body, op),
                    "valid mathematical primitive action refused");
            if (mode == Body::Mode::Local && scalar)
              std::get<LocalPrimitive>(op.action).bindingArguments =
                  std::vector<Type>{field};
            else if (mode == Body::Mode::Local)
              op.action = LocalPrimitive{identity, {{0}, {1}}, {}};
            else
              op.action = HelperCall{{0}, {{0}, {1}}, {}, {}, {}};
            require(!checkCallAction(f.semantics, f.declarations, body, op) &&
                        f.semantics.diagnostic &&
                        f.semantics.diagnostic->code ==
                            "source.binding-witness",
                    "wrong mathematical primitive boundary accepted");
          }
      });
  for (const auto &notation :
       {descriptor(Position::Prefix, 1, "⊖"),
        descriptor(Position::Postfix, 1, "⊖"), descriptor(),
        descriptor(Position::Delimited, 1, "⟪"),
        descriptor(Position::Delimited, 3, "⟪"),
        descriptor(Position::Delimited, 64, "⟪")}) {
    cases.run(
        "notation inference and witness: " + notation->key() + "/" +
            std::to_string(notation->arity),
        [&] {
          Fixture f;
          std::vector<Type> inputs(notation->arity, field);
          f.declarations = {signature(0, inputs, field)};
          std::vector<TypeInference::Variable> variables;
          std::vector<unsigned> order(notation->arity);
          std::iota(order.begin(), order.end(), 0);
          std::vector<ValueId> operands;
          for (auto i : order) {
            variables.push_back(f.known(field));
            operands.push_back({i});
          }
          f.operators.add(0, site, variables, f.known(field), {candidate(0)});
          auto result = f.operators.solve(site, [] { return true; });
          require(result && result->at(0).constraints.inputs.size() ==
                                notation->arity,
                  "notation did not use the ordinary variable-arity solver");
          std::vector<OperatorBinding> family{
              {notation->symbol, {{0}, {}}, {}, site, notation}};
          CallBinding witness{
              {{0}, {}},
              {},
              operands,
              notation->symbol,
              {operatorBindingKey(family.front(), f.declarations)},
              site,
              *notation};
          Expression expr;
          expr.kind = Expression::Kind::NotationCall;
          expr.span = site;
          expr.notation = notation;
          expr.children = order;
          NotationEnvironment environment{{notation->key(), {notation, site}}};
          require(checkNotationOccurrence(f.semantics, expr, environment),
                  "valid lexical descriptor refused");
          require(checkOperatorWitness(f.semantics, f.declarations, family,
                                       *notation, witness, inputs, field, site),
                  "valid notation binding refused");
          require(checkOperatorOperands(f.semantics, *notation, witness, order,
                                        operands, site),
                  "valid notation operand order refused");
        });
  }
  for (unsigned mutation = 0; mutation < 6; ++mutation) {
    cases.run("descriptor shape mutation " + std::to_string(mutation), [&] {
      Fixture f;
      f.declarations = {signature(0, {field, field, field}, field)};
      auto notation = descriptor(Position::Delimited, 3, "⟪");
      auto altered = *notation;
      switch (mutation) {
      case 0:
        altered.position = Position::Prefix;
        break;
      case 1:
        altered.symbol = "⟨";
        break;
      case 2:
        altered.closing = "⟩";
        break;
      case 3:
        altered.precedence = 1;
        break;
      case 4:
        altered.association = Association::Right;
        break;
      case 5:
        altered.arity = 2;
        break;
      }
      Expression expr;
      expr.kind = Expression::Kind::NotationCall;
      expr.span = site;
      expr.notation = std::make_shared<const NotationDescriptor>(altered);
      expr.children = {0, 1, 2};
      NotationEnvironment environment{{notation->key(), {notation, site}}};
      require(!checkNotationOccurrence(f.semantics, expr, environment) &&
                  f.semantics.diagnostic &&
                  f.semantics.diagnostic->code == "source.binding-witness",
              "expression descriptor overrode its lexical environment");
      f.semantics.diagnostic.reset();
      std::vector<OperatorBinding> family{{"⟪", {{0}, {}}, {}, site, notation}};
      const auto key = operatorBindingKey(family.front(), f.declarations);
      auto other = family.front();
      other.notation = expr.notation;
      require(operatorBindingKey(other, f.declarations) != key,
              "canonical family key omitted descriptor shape");
      CallBinding witness{{{0}, {}}, {},   {{0}, {1}, {2}}, "⟪",
                          {key},     site, altered};
      require(!checkOperatorWitness(f.semantics, f.declarations, family,
                                    *notation, witness, {field, field, field},
                                    field, site) &&
                  f.semantics.diagnostic &&
                  f.semantics.diagnostic->code == "source.binding-witness",
              "retained descriptor mutation accepted");
    });
  }
  cases.run("notation visibility is independent of operand types", [&] {
    Fixture f;
    auto prefix = descriptor(Position::Prefix, 1, "⊖");
    auto infix = descriptor(Position::Infix, 2, "⊖");
    Expression expr;
    expr.kind = Expression::Kind::NotationCall;
    expr.span = site;
    expr.notation = prefix;
    expr.children = {0};
    NotationEnvironment environment{{infix->key(), {infix, site}}};
    require(!checkNotationOccurrence(f.semantics, expr, environment) &&
                f.semantics.diagnostic &&
                f.semantics.diagnostic->code == "source.binding-witness",
            "an infix descriptor made an invisible prefix visible");
  });
  cases.run(
      "descriptor identity is structural rather than pointer identity", [&] {
        Fixture f;
        auto notation = descriptor(Position::Prefix, 1, "⊖");
        Expression expr;
        expr.kind = Expression::Kind::NotationCall;
        expr.span = site;
        expr.notation = std::make_shared<const NotationDescriptor>(*notation);
        expr.children = {0};
        NotationEnvironment environment{{notation->key(), {notation, site}}};
        require(checkNotationOccurrence(f.semantics, expr, environment),
                "equal descriptor values required shared allocation identity");
        expr.notation.reset();
        require(!checkNotationOccurrence(f.semantics, expr, environment) &&
                    f.semantics.diagnostic &&
                    f.semantics.diagnostic->code == "source.binding-witness",
                "unfinished notation occurrence was accepted");
      });
  for (unsigned mutation = 0; mutation < 7; ++mutation) {
    cases.run(
        "notation family integrity mutation " + std::to_string(mutation), [&] {
          Fixture f;
          auto notation = descriptor(Position::Delimited, 3, "⟪");
          f.declarations = {signature(0, {field, field, field}, field),
                            signature(1, {index, index, index}, index)};
          std::vector<OperatorBinding> family{
              {"⟪", {{0}, {}}, {}, site, notation},
              {"⟪", {{1}, {}}, {}, site, notation}};
          CallBinding witness{{{0}, {}}, {},   {{0}, {1}, {2}}, "⟪",
                              {},        site, *notation};
          for (const auto &binding : family)
            witness.family.push_back(
                operatorBindingKey(binding, f.declarations));
          require(checkOperatorWitness(f.semantics, f.declarations, family,
                                       *notation, witness,
                                       {field, field, field}, field, site),
                  "valid delimiter family refused");
          switch (mutation) {
          case 0:
            family.front().notation.reset();
            break;
          case 1:
            family.front().arguments.push_back(field);
            break;
          case 2:
            family.back().target.declaration = {2};
            break;
          case 3:
            f.declarations.back().inputs.pop_back();
            break;
          case 4:
            f.declarations.back().outputs.clear();
            break;
          case 5:
            witness.notation.reset();
            break;
          case 6:
            witness.operands.pop_back();
            break;
          }
          require(!checkOperatorWitness(f.semantics, f.declarations, family,
                                        *notation, witness,
                                        {field, field, field}, field, site) &&
                      f.semantics.diagnostic &&
                      f.semantics.diagnostic->code == "source.binding-witness",
                  "malformed family or retained witness accepted");
        });
  }
  cases.run("forged arity cannot certify its own shortened operands", [&] {
    Fixture f;
    auto notation = descriptor(Position::Delimited, 2, "⟪");
    f.declarations = {signature(0, {field, field, field}, field)};
    std::vector<OperatorBinding> family{{"⟪", {{0}, {}}, {}, site, notation}};
    CallBinding witness{{{0}, {}},
                        {},
                        {{0}, {1}},
                        "⟪",
                        {operatorBindingKey(family.front(), f.declarations)},
                        site,
                        *notation};
    require(!checkOperatorWitness(f.semantics, f.declarations, family,
                                  *notation, witness, {field, field}, field,
                                  site) &&
                f.semantics.diagnostic &&
                f.semantics.diagnostic->code == "source.binding-witness",
            "matching forged descriptor and operands bypassed the target "
            "signature");
  });
  for (const auto &notation : {descriptor(Position::Prefix, 2, "⊖"),
                               descriptor(Position::Postfix, 2, "⊖"),
                               descriptor(Position::Infix, 1, "⊖"),
                               descriptor(Position::Delimited, 0, "⟪"),
                               descriptor(Position::Delimited, 65, "⟪")}) {
    cases.run(
        "invalid notation arity: " + notation->key() + "/" +
            std::to_string(notation->arity),
        [&] {
          Fixture f;
          Expression expr;
          expr.kind = Expression::Kind::NotationCall;
          expr.span = site;
          expr.notation = notation;
          expr.children.resize(notation->arity);
          NotationEnvironment environment{{notation->key(), {notation, site}}};
          require(!checkNotationOccurrence(f.semantics, expr, environment) &&
                      f.semantics.diagnostic &&
                      f.semantics.diagnostic->code ==
                          (notation->arity > 64 ? "source.limit"
                                                : "source.binding-witness"),
                  "invalid positional arity accepted");
        });
  }
  cases.run("notation witnesses honor a lowered hole budget", [&] {
    Fixture f;
    f.limits.notationHoles = 2;
    auto notation = descriptor(Position::Delimited, 3, "⟪");
    Expression expr;
    expr.kind = Expression::Kind::NotationCall;
    expr.span = site;
    expr.notation = notation;
    expr.children = {0, 1, 2};
    NotationEnvironment environment{{notation->key(), {notation, site}}};
    require(!checkNotationOccurrence(f.semantics, expr, environment) &&
                f.semantics.diagnostic &&
                f.semantics.diagnostic->code == "source.limit",
            "witness ignored the caller's notation hole ceiling");
  });
  for (const auto &order : std::vector<std::vector<unsigned>>{
           {2, 1, 0}, {0, 1, 1}, {0, 1}, {0, 1, 3}}) {
    cases.run(
        "delimiter operand mapping mutation " + std::to_string(order.back()),
        [&] {
          Fixture f;
          auto notation = descriptor(Position::Delimited, 3, "⟪");
          CallBinding witness{{{0}, {}}, {},   {{0}, {1}, {2}}, "⟪",
                              {},        site, *notation};
          require(!checkOperatorOperands(f.semantics, *notation, witness, order,
                                         {{0}, {1}, {2}}, site) &&
                      f.semantics.diagnostic &&
                      f.semantics.diagnostic->code == "source.binding-witness",
                  "delimiter mapping lost authored order");
        });
  }
  for (unsigned arity : {1u, 3u}) {
    cases.run("fixed inputs remain ambiguous at arity " + std::to_string(arity),
              [&] {
                Fixture f;
                std::vector<Type> inputs(arity, field);
                f.declarations = {signature(0, inputs, field),
                                  signature(1, inputs, boolean)};
                std::vector<TypeInference::Variable> variables;
                for (unsigned i = 0; i < arity; ++i)
                  variables.push_back(f.known(field));
                f.operators.add(0, site, variables, f.known(field),
                                {candidate(0), candidate(1)});
                f.refusal("source.operator");
              });
  }
  cases.run("only fixed infix equality requires a Boolean result", [&] {
    for (const auto &symbol : {"==", "≡"}) {
      Fixture f;
      auto notation = descriptor(Position::Infix, 2, symbol);
      f.declarations = {signature(0, {field, field}, field)};
      std::vector<OperatorBinding> family{
          {symbol, {{0}, {}}, {}, site, notation}};
      CallBinding witness{{{0}, {}},
                          {},
                          {{0}, {1}},
                          symbol,
                          {operatorBindingKey(family.front(), f.declarations)},
                          site,
                          *notation};
      bool accepted =
          checkOperatorWitness(f.semantics, f.declarations, family, *notation,
                               witness, {field, field}, field, site);
      require(accepted == (llvm::StringRef(symbol) != "=="),
              "Boolean result rule escaped the fixed equality descriptor");
    }
  });
  cases.run(
      "retained native action rechecks notation arity against its target", [&] {
        Fixture f;
        auto notation = descriptor(Position::Delimited, 3, "⟪");
        f.declarations = {signature(0, {field, field, field}, field)};
        Body body;
        body.mode = Body::Mode::Math;
        body.values = {{field, {}, site},
                       {field, {}, site},
                       {field, {}, site},
                       {field, {}, site}};
        Operation op{
            HelperCall{{0}, {{0}, {1}, {2}}, {}, {}, {}}, {{3}}, site, 0};
        OperatorBinding binding{"⟪", {{0}, {}}, {}, site, notation};
        op.binding = CallBinding{{{0}, {}},
                                 {},
                                 {{0}, {1}, {2}},
                                 "⟪",
                                 {operatorBindingKey(binding, f.declarations)},
                                 site,
                                 *notation};
        require(checkCallAction(f.semantics, f.declarations, body, op),
                "valid delimited helper action refused");
        op.binding->notation->arity = 2;
        require(!checkCallAction(f.semantics, f.declarations, body, op) &&
                    f.semantics.diagnostic &&
                    f.semantics.diagnostic->code == "source.binding-witness",
                "action accepted a descriptor with the wrong target arity");
      });
  return cases.result();
}
