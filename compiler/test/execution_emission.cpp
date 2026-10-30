#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/ExecutionModel.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Program/Admission.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Execution.h"
#include "llvm/Support/MemoryBuffer.h"
#include <filesystem>
#include <fstream>
#include <map>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
using Names = program::Names;
using Body = program::Body;
using Env = std::map<std::string, std::string>;
Names uses(const Names &values, const Env &env) {
  Names result;
  for (const auto &value : values)
    result.push_back(env.at(value));
  return result;
}
Names definitions(const Names &values, Env &env, unsigned &next) {
  Names result;
  for (const auto &value : values) {
    auto name = "v" + std::to_string(next++);
    env[value] = name;
    result.push_back(name);
  }
  return result;
}
// Test-only alpha normalization of admitted native records. Preserve every
// instruction, occurrence, constant, port, capture and binding identity.
void normalize(Body &body, Env env, unsigned &next) {
  for (auto &instruction : body) {
    if (auto op = instruction.get<program::Operation>()) {
      op->inputs = uses(op->inputs, env);
      op->outputs = definitions(op->outputs, env, next);
    } else if (auto op = instruction.get<program::BooleanConstant>()) {
      op->output = definitions({op->output}, env, next).front();
    } else if (auto op = instruction.get<program::VariantConstruct>()) {
      op->payload = uses(op->payload, env);
      op->output = definitions({op->output}, env, next).front();
    } else if (auto op = instruction.get<program::Conditional>()) {
      op->condition = env.at(op->condition);
      op->captures = uses(op->captures, env);
      normalize(op->thenBody, env, next);
      normalize(op->elseBody, env, next);
      op->outputs = definitions(op->outputs, env, next);
    } else if (auto op = instruction.get<program::Match>()) {
      op->input = env.at(op->input);
      op->captures = uses(op->captures, env);
      for (auto &arm : op->arms) {
        auto inner = env;
        arm.payload = definitions(arm.payload, inner, next);
        normalize(arm.body, std::move(inner), next);
      }
      op->outputs = definitions(op->outputs, env, next);
    } else if (auto op = instruction.get<program::For>()) {
      op->lower = env.at(op->lower);
      op->upper = env.at(op->upper);
      op->captures = uses(op->captures, env);
      auto inner = env;
      op->induction = definitions({op->induction}, inner, next).front();
      for (auto &[name, seed] : op->carried) {
        seed = env.at(seed);
        name = definitions({name}, inner, next).front();
      }
      normalize(op->body, std::move(inner), next);
      op->outputs = definitions(op->outputs, env, next);
    } else if (auto op = instruction.get<program::Release>()) {
      op->values = uses(op->values, env);
    } else if (auto op = instruction.get<program::Return>()) {
      op->values = uses(op->values, env);
    } else if (auto op = instruction.get<program::Yield>()) {
      op->values = uses(op->values, env);
    } else
      require(instruction.get<program::Stop>(), "unexpected test instruction");
  }
}
program::Participants programOf(program::LocalDefinitions definitions,
                                bool normalized = false) {
  program::Participants model;
  model.stage = program::Participants::Stage::Physical;
  model.bindings = std::move(definitions.bindings);
  model.functions = std::move(definitions.functions);
  if (normalized) {
    unsigned next = 0;
    for (auto &function : model.functions) {
      Env env;
      for (auto &arg : function.arguments)
        arg.name = ::definitions({arg.name}, env, next).front();
      normalize(function.body, std::move(env), next);
    }
  }
  auto &function = model.functions.front();
  Names inputs, results;
  for (const auto &argument : function.arguments)
    inputs.push_back(argument.name);
  for (unsigned i = 0; i < function.results.size(); ++i)
    results.push_back("result" + std::to_string(i));
  program::Participant participant;
  participant.name = "root";
  participant.instance = "execution_test";
  participant.role = "P";
  participant.arguments = function.arguments;
  participant.results = function.results;
  participant.body = {
      {"run", program::LocalCall{function.name, inputs, results}},
      {"", program::Return{results}}};
  model.participants.push_back(std::move(participant));
  model.entries.push_back({"main", {{"P", "root"}}});
  if (auto e = protocol::admit(model))
    throw std::runtime_error(llvm::toString(std::move(e)));
  if (auto e = program::checkStructure(model))
    throw std::runtime_error(llvm::toString(std::move(e)));
  return model;
}
std::string encoded(program::LocalDefinitions model, bool normalize = false) {
  return printJson(program::encode(programOf(std::move(model), normalize)));
}
std::string physical(StringRef logical) {
  auto type = protocol::parseBoundType(logical, false);
  require(bool(type), "invalid test type");
  auto represented = protocol::defaultRepresentation(*type);
  require(bool(represented), "missing test representation");
  return represented->spelling();
}
program::LocalDefinitions nested(bool conditional, bool reject = false) {
  auto field = physical("field:bls12-381.fr");
  auto boolean = physical("bool"), index = physical("index");
  auto variant = physical(*protocol::encodeVariant(
      {"ExecutionChoice",
       {{"left", {"field:bls12-381.fr"}}, {"right", {"field:bls12-381.fr"}}}}));
  program::LocalDefinitions model;
  model.bindings = {
      {"add", {"field.add", {"bls12-381.fr"}, "arkworks/field.add"}},
      {"multiply", {"field.mul", {"bls12-381.fr"}, "arkworks/field.mul"}}};
  program::Conditional choose{
      "again",
      {"payload", "y"},
      {{"add_value", program::Operation{"add", {}, {"payload", "y"}, {"sum"}}},
       {"", program::Yield{{"sum"}}}},
      reject ? Body{{"reject_value", program::Stop{"refused"}}}
             : Body{{"multiply_value",
                     program::Operation{
                         "multiply", {}, {"payload", "y"}, {"product"}}},
                    {"", program::Yield{{"product"}}}},
      {"chosen"}};
  program::Match match{
      "variant",
      {"again", "y"},
      {{"left",
        {"payload"},
        {{"choose", choose}, {"", program::Yield{{"chosen"}}}}},
       {"right", {"payload"}, {{"", program::Yield{{"payload"}}}}}},
      {"next"}};
  program::For loop{
      "i",
      "lower",
      "upper",
      {{"state", "x"}},
      {"again", "y"},
      {{"pack",
        program::VariantConstruct{variant, "left", {"state"}, "variant"}},
       {"select", match},
       {"",
        program::Yield{conditional ? Names{"again", "next"} : Names{"next"}}}},
      {"answer"},
      conditional};
  model.functions.push_back(
      {"work",
       {{"lower", index},
        {"upper", index},
        {"again", boolean},
        {"x", field},
        {"y", field}},
       {field},
       {{"iterate", loop}, {"", program::Return{{"answer"}}}},
       program::LogicalOrigin{"work", {{"F", "bls12-381.fr"}}}});
  return model;
}
} // namespace
int main(int argc, char **argv) {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  cases.run("scoped execution needs no Local dialect", [] {
    DialectRegistry registry;
    registry.insert<algebra::AlgebraDialect, data::DataDialect,
                    runtime::RuntimeDialect>();
    MLIRContext context(registry);
    context.loadAllAvailableDialects();
    auto expected = nested(true);
    auto emitted = take(protocol::writeLocalExecution(context, expected, true));
    auto actual = take(protocol::readLocalExecution(*emitted, true));
    if (auto e = protocol::verifyLocalExecution(*emitted, expected, true))
      throw std::runtime_error(llvm::toString(std::move(e)));
    require(encoded(actual, true) == encoded(expected, true),
            "Runtime-only binding path changed execution records");
    require(!context.getLoadedDialect("local"),
            "execution loaded the removed binding owner");
  });
  cases.run(
      "physical conversion declarations retain their selected ports", [&] {
        auto source = physical("field:bls12-381.fr");
        std::string target = "field:bls12-381.fr@blst/fr";
        program::LocalDefinitions expected;
        expected.bindings.push_back({"convert",
                                     {"representation.convert",
                                      {"field:bls12-381.fr"},
                                      "native/representation.convert",
                                      {source, target}}});
        expected.functions.push_back(
            {"convert_field",
             {{"x", source}},
             {target},
             {{"convert", program::Operation{"convert", {}, {"x"}, {"y"}}},
              {"", program::Return{{"y"}}}},
             program::LogicalOrigin{"convert_field", {}}});
        auto emitted =
            take(protocol::writeLocalExecution(context, expected, true));
        auto actual = take(protocol::readLocalExecution(*emitted, true));
        require(encoded(actual, true) == encoded(expected, true),
                "physical conversion lost its exact layout endpoints");
        if (auto e = protocol::verifyLocalExecution(*emitted, expected, true))
          throw std::runtime_error(llvm::toString(std::move(e)));
        // The native declaration is physical before byte conversion is read.
        refuses(protocol::readLocalExecution(*emitted, false), "binding-stage");
        auto binding = *emitted->getOps<runtime::BindingOp>().begin();
        binding.setFunctionType(
            take(protocol::bindingSignature(&context,
                                            {"representation.convert",
                                             {"field:bls12-381.fr"},
                                             "native/representation.convert",
                                             {target, source}},
                                            true)));
        require(
            succeeded(binding.verify()) && failed(verify(*emitted)),
            "formed reversed endpoints must invalidate the actual call ABI");
        auto reread = protocol::readLocalExecution(*emitted, true);
        require(!reread,
                "reader accepted reversed endpoints after its first read");
        llvm::consumeError(reread.takeError());
        auto rejected =
            protocol::verifyLocalExecution(*emitted, expected, true);
        require(bool(rejected),
                "reversed physical layout endpoints were accepted");
        llvm::consumeError(std::move(rejected));
      });
  auto mixed = [&](const program::LocalDefinitions &expected) {
    auto module = take(protocol::writeLocalExecution(context, expected, true));
    Builder builder(&context);
    module->setSymNameAttr(builder.getStringAttr("protocol"));
    auto mathematics = ModuleOp::create(builder.getUnknownLoc(), "mathematics");
    module->getBody()->push_back(mathematics);
    return module;
  };
  auto acceptedDefinitions = [&](ModuleOp module,
                                 const program::LocalDefinitions &expected) {
    auto actual = take(protocol::readExecutionDefinitions(module, true));
    require(encoded(actual, true) == encoded(expected, true),
            "mixed scope changed execution records");
    if (auto e = protocol::verifyExecutionDefinitions(module, expected, true))
      throw std::runtime_error(llvm::toString(std::move(e)));
  };
  auto refusedDefinitions = [&](Operation *scope,
                                const program::LocalDefinitions &expected) {
    auto actual = protocol::readExecutionDefinitions(scope, true);
    require(!actual, "mixed reader accepted invalid execution definitions");
    llvm::consumeError(actual.takeError());
    auto error = protocol::verifyExecutionDefinitions(scope, expected, true);
    require(bool(error),
            "mixed comparison accepted invalid execution definitions");
    llvm::consumeError(std::move(error));
  };
  cases.run(
      "mixed symbol table preserves the complete execution inventory", [&] {
        auto expected = nested(true);
        auto module = mixed(expected);
        require(succeeded(verify(*module)), "mixed module formation");
        acceptedDefinitions(*module, expected);
        refuses(protocol::readLocalExecution(*module, true), "execution-cfg");
        auto error = protocol::verifyLocalExecution(*module, expected, true);
        require(bool(error), "closed profile accepted a mixed scope");
        llvm::consumeError(std::move(error));
      });
  cases.run("mixed definitions do not claim to verify other declarations", [&] {
    auto expected = nested(true);
    auto module = mixed(expected);
    auto mathematics = *module->getOps<ModuleOp>().begin();
    mathematics->setAttr("sym_visibility",
                         Builder(&context).getStringAttr("invalid"));
    // The enclosing profile owns this malformed sibling. Owned Func and Runtime
    // definitions can still be inspected without recursively verifying it.
    acceptedDefinitions(*module, expected);
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(verify(*module)),
            "malformed sibling must fail full verification");
  });
  cases.run("mixed lookup rejects collisions with other declarations", [&] {
    auto expected = nested(true);
    auto module = mixed(expected);
    acceptedDefinitions(*module, expected);
    auto mathematics = *module->getOps<ModuleOp>().begin();
    mathematics.setSymNameAttr(Builder(&context).getStringAttr("work"));
    refusedDefinitions(module->getOperation(), expected);
  });
  cases.run("mixed execution rechecks actual same-typed operands", [&] {
    auto expected = nested(true);
    auto module = mixed(expected);
    acceptedDefinitions(*module, expected);
    exec::ApplyOp selected;
    module->walk([&](exec::ApplyOp op) {
      if (!selected)
        selected = op;
    });
    require(selected && selected->getNumOperands() == 3,
            "missing binary application");
    auto first = selected->getOperand(1);
    selected->setOperand(1, selected->getOperand(2));
    selected->setOperand(2, first);
    require(succeeded(verify(*module)),
            "same-typed mutation must remain well formed");
    auto actual = take(protocol::readExecutionDefinitions(*module, true));
    require(encoded(actual, true) != encoded(expected, true),
            "reader ignored changed actual operands");
    auto error = protocol::verifyExecutionDefinitions(*module, expected, true);
    require(bool(error), "comparison ignored changed actual operands");
    llvm::consumeError(std::move(error));
  });
  cases.run("dormant functions remain owned by the selected scope", [&] {
    auto expected = nested(true);
    auto module = mixed(expected);
    auto root = module->lookupSymbol<func::FuncOp>("work");
    auto dormant = cast<func::FuncOp>(root->clone());
    dormant.setName("dormant");
    module->getBody()->push_back(dormant);
    require(succeeded(verify(*module)), "dormant root formation");
    auto actual = take(protocol::readExecutionDefinitions(*module, true));
    require(actual.functions.size() == 2, "dormant root was omitted");
    auto error = protocol::verifyExecutionDefinitions(*module, expected, true);
    require(bool(error), "comparison omitted an extra dormant root");
    llvm::consumeError(std::move(error));
    dormant->removeAttr("runtime.origin");
    refusedDefinitions(module->getOperation(), expected);
  });
  cases.run("outlined call cannot escape the selected symbol table", [&] {
    auto expected = nested(true);
    auto module = mixed(expected);
    acceptedDefinitions(*module, expected);
    func::CallOp selected;
    module->walk([&](func::CallOp call) {
      if (!selected)
        selected = call;
    });
    require(bool(selected), "missing outlined call");
    auto callee = module->lookupSymbol<func::FuncOp>(selected.getCallee());
    auto mathematics = *module->getOps<ModuleOp>().begin();
    callee->moveBefore(mathematics.getBody(), mathematics.getBody()->end());
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    refusedDefinitions(module->getOperation(), expected);
  });
  cases.run("execution definition scope must be an actual symbol table", [&] {
    auto expected = nested(true);
    auto module = mixed(expected);
    refusedDefinitions(nullptr, expected);
    refusedDefinitions(module->lookupSymbol<func::FuncOp>("work"), expected);
  });
  for (bool bindingLimit : {false, true})
    cases.run(
        bindingLimit ? "binding inventory is independent of definitions"
                     : "definition inventory is independent of bindings",
        [&] {
          program::LocalDefinitions expected;
          expected.bindings.push_back(
              {"add", {"field.add", {"bls12-381.fr"}, "arkworks/field.add"}});
          expected.functions.push_back({"work",
                                        {{"x", physical("field:bls12-381.fr")}},
                                        {physical("field:bls12-381.fr")},
                                        {{"", program::Return{{"x"}}}},
                                        program::LogicalOrigin{"work", {}}});
          for (unsigned i = 1; i < 4096; ++i) {
            if (bindingLimit) {
              auto binding = expected.bindings.front();
              binding.name = "unused" + std::to_string(i);
              expected.bindings.push_back(std::move(binding));
            } else {
              auto function = expected.functions.front();
              function.name = "unused" + std::to_string(i);
              expected.functions.push_back(std::move(function));
            }
          }
          // Control outlines are not additional native callable definitions.
          // Put a branch in one root after filling the exact inventory.
          expected.functions.front().body = {
              {"condition", program::BooleanConstant{"condition", true}},
              {"choose", program::Conditional{"condition",
                                              {"x"},
                                              {{"", program::Yield{{"x"}}}},
                                              {{"", program::Yield{{"x"}}}},
                                              {"answer"}}},
              {"", program::Return{{"answer"}}}};
          auto module =
              take(protocol::writeLocalExecution(context, expected, true));
          auto actual = take(protocol::readLocalExecution(*module, true));
          require(actual.functions.size() == expected.functions.size() &&
                      actual.bindings.size() == expected.bindings.size(),
                  "exact inventory boundary was truncated");
          if (auto error =
                  protocol::verifyLocalExecution(*module, expected, true))
            throw std::runtime_error(llvm::toString(std::move(error)));
          // A declaration owned by the enclosing profile shares collision work,
          // but cannot consume the independent execution inventory.
          auto extra = ModuleOp::create(module->getLoc(), "other_profile");
          module->getBody()->push_back(extra);
          auto mixedActual =
              take(protocol::readExecutionDefinitions(*module, true));
          require(mixedActual.functions.size() == expected.functions.size() &&
                      mixedActual.bindings.size() == expected.bindings.size(),
                  "enclosing declaration changed execution coverage");
          Operation *last =
              bindingLimit
                  ? (*module->getOps<runtime::BindingOp>().begin())
                        .getOperation()
                  : (*module->getOps<func::FuncOp>().begin()).getOperation();
          auto *overflow = last->clone();
          overflow->setAttr("sym_name",
                            StringAttr::get(&context, "one_too_many"));
          module->getBody()->push_back(overflow);
          refusedDefinitions(module->getOperation(), expected);
          overflow->erase();
          // Foreign declarations still cannot shadow an owned symbol.
          extra->setAttr("sym_name", StringAttr::get(&context, "work"));
          refusedDefinitions(module->getOperation(), expected);
        });
  auto check = [&](const program::LocalDefinitions &model, StringRef name) {
    auto emitted = protocol::writeLocalExecution(context, model, true);
    if (!emitted)
      throw std::runtime_error(llvm::toString(emitted.takeError()));
    require(succeeded(verify(**emitted)), "generated module formation");
    if (auto error = protocol::verifyLocalExecution(**emitted, model, true))
      throw std::runtime_error(llvm::toString(std::move(error)));
    auto read = protocol::readLocalExecution(**emitted, true);
    if (!read)
      throw std::runtime_error(llvm::toString(read.takeError()));
    require(encoded(model, true) == encoded(*read, true),
            "generated CFG changed native program");
    if (argc == 2) {
      auto directory = std::filesystem::path(argv[1]);
      std::filesystem::create_directories(directory);
      for (auto [suffix, bytes] :
           {std::pair{"-baseline.json", encoded(model)},
            std::pair{"-generated.json", encoded(*read)}}) {
        std::ofstream output(directory / (name.str() + suffix));
        output << bytes << '\n';
        require(bool(output), "cannot write native fixture");
      }
      std::string text;
      llvm::raw_string_ostream out(text);
      (*emitted)->print(out);
      std::ofstream output(directory / (name.str() + ".mlir"));
      output << text << '\n';
      require(bool(output), "cannot write execution CFG");
    }
  };
  for (bool conditional : {false, true})
    for (bool reject : {false, true}) {
      auto name = std::string(conditional ? "conditional" : "unconditional") +
                  (reject ? "-stop" : "-return");
      cases.run(name, [&] { check(nested(conditional, reject), name); });
    }
  cases.run("outlined helper names avoid root and binding collisions", [&] {
    auto model = nested(true);
    model.functions[0].name = "execution_region_0";
    model.bindings.push_back(
        {"execution_region_1",
         {"field.add", {"bls12-381.fr"}, "arkworks/field.add"}});
    check(model, "name-collisions");
  });
  cases.run(
      "native literal and empty completion need no unconditional stop block",
      [&] {
        program::LocalDefinitions model;
        model.functions.push_back(
            {"empty",
             {},
             {},
             {{"literal", program::BooleanConstant{"unused", true}},
              {"", program::Release{{"unused"}}},
              {"", program::Return{}}},
             program::LogicalOrigin{"empty", {}}});
        check(model, "empty");
        model.functions[0].body = {{"", program::Return{}}};
        check(model, "empty-only");
      });
  cases.run("terminal root carries its signature without a successful path",
            [&] {
              auto model = nested(true);
              model.functions[0].body = {{"stop", program::Stop{"abort"}}};
              check(model, "stopped");
            });
  cases.run("both terminal arms have an empty continuation", [&] {
    auto model = nested(false);
    model.functions[0].body = {
        {"choose", program::Conditional{"again",
                                        {},
                                        {{"left", program::Stop{"refused"}}},
                                        {{"right", program::Stop{"reject"}}},
                                        {}}},
        {"", program::Return{{"x"}}}};
    check(model, "terminal-arms");
  });
  cases.run("admission rejects incorrect captures before code generation", [&] {
    auto model = nested(true);
    model.functions[0].body[0].get<program::For>()->captures.clear();
    auto emitted = protocol::writeLocalExecution(context, model, true);
    refuses(std::move(emitted), "interactive-unavailable");
  });
  cases.run("stage selection is explicit", [&] {
    auto emitted = protocol::writeLocalExecution(context, nested(true), false);
    refuses(std::move(emitted), "binding-type");
  });
  cases.run("missing native value dialect is a checked emission refusal", [&] {
    MLIRContext empty;
    refuses(protocol::writeLocalExecution(empty, nested(true), true),
            "execution-emission");
  });
  cases.run("outlined control uses the native instruction bound", [&] {
    for (unsigned branches :
         {2048u, unsigned(program::staticInstructionLimit / 3 + 1)}) {
      auto model = nested(false);
      auto &body = model.functions[0].body;
      body.clear();
      for (unsigned i = 0; i < branches; ++i) {
        auto suffix = std::to_string(i);
        body.push_back({"choose_" + suffix,
                        program::Conditional{
                            "again",
                            {},
                            {{"left_" + suffix, program::Stop{"refused"}}},
                            {{"right_" + suffix, program::Stop{"reject"}}},
                            {}}});
      }
      body.push_back({"", program::Return{{"x"}}});
      if (branches == 2048)
        check(model, "many-outlined-bodies");
      else
        refuses(protocol::writeLocalExecution(context, model, true),
                "interactive-instruction-limit");
    }
  });
  cases.run(
      "writer preserves the stricter native carrier nesting boundary", [&] {
        for (unsigned depth : {29, 30}) {
          auto model = nested(false);
          Body body{{"", program::Yield{{"x"}}}};
          for (unsigned i = 0; i < depth; ++i) {
            auto name = "nested_" + std::to_string(i);
            body = {{name, program::Conditional{"again",
                                                {"again", "x"},
                                                std::move(body),
                                                {{"", program::Yield{{"x"}}}},
                                                {name}}},
                    {"", program::Yield{{name}}}};
          }
          body.back().value =
              program::Return{body.back().get<program::Yield>()->values};
          model.functions[0].body = std::move(body);
          if (depth == 29) {
            auto emitted =
                take(protocol::writeLocalExecution(context, model, true));
            auto decoded = take(protocol::readLocalExecution(*emitted, true));
            require(decoded.functions.size() == 1,
                    "maximum native conditional nesting");
          } else
            refuses(protocol::writeLocalExecution(context, model, true),
                    "interactive-json-depth");
        }
      });
  cases.run("represented variant alternative is independently bound", [&] {
    auto model = nested(true);
    auto emitted = take(protocol::writeLocalExecution(context, model, true));
    auto &body = model.functions[0].body[0].get<program::For>()->body;
    body[0].get<program::VariantConstruct>()->alternative = "right";
    auto error = protocol::verifyLocalExecution(*emitted, model, true);
    require(bool(error), "changed alternative escaped independent comparison");
    require(namesIdentifier(llvm::toString(std::move(error)),
                            "execution-correspondence"),
            "wrong variant comparison refusal");
  });
  cases.run("unused native literal value is independently bound", [&] {
    auto model = nested(true);
    auto &body = model.functions[0].body;
    body.insert(body.begin(),
                {"literal", program::BooleanConstant{"unused", true}});
    auto emitted = take(protocol::writeLocalExecution(context, model, true));
    body.front().get<program::BooleanConstant>()->value = false;
    auto error = protocol::verifyLocalExecution(*emitted, model, true);
    require(bool(error), "changed literal escaped independent comparison");
    require(namesIdentifier(llvm::toString(std::move(error)),
                            "execution-correspondence"),
            "wrong literal comparison refusal");
  });
  for (StringRef name : {"execution-conditional", "execution-loop"})
    cases.run(name, [&] {
      auto file = llvm::MemoryBuffer::getFile(
          std::string(ZKC_FIXTURES) + "/runtime/" + name.str() + ".mlir");
      require(bool(file), "missing logical fixture");
      auto module = parseSourceString<ModuleOp>((*file)->getBuffer(), &context);
      auto first = protocol::readLocalExecution(*module, false);
      require(bool(first), "logical input fixture");
      auto emitted = protocol::writeLocalExecution(context, *first, false);
      if (!emitted)
        throw std::runtime_error(llvm::toString(emitted.takeError()));
      auto second = protocol::readLocalExecution(**emitted, false);
      require(bool(second) && second->functions[0].arguments.size() ==
                                  first->functions[0].arguments.size(),
              "logical execution reconstruction");
    });
  return cases.result();
}
