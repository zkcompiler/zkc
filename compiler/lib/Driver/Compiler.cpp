#include "zkc/Driver/Compiler.h"
#include "../Support/Input.h"
#include "Language.h"
#include "Relations.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Compiler/Compilation.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Compiler/PolynomialReduction.h"
#include "zkc/Compiler/PublicCoin.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/MLIRInput.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <filesystem>
#include <map>
#include <set>
using namespace llvm;
int zkc::runCompiler(int argc, char **argv,
                     const mlir::DialectRegistry &extensions) {
  if (argc >= 2 && StringRef(argv[1]).starts_with("language-"))
    return runLanguageCompiler(argc, argv);
  mlir::DialectRegistry registry;
  registerDialects(registry);
  extensions.appendTo(registry);
  if (argc == 2 &&
      (StringRef(argv[1]) == "--help" || StringRef(argv[1]) == "-h")) {
    outs()
        << "usage: zkc-compile COMMAND FILE\n\n"
           "Language (.zkc; explicit module map):\n"
           "  language-check | language-emit | language-interface | "
           "language-bundle | language-package\n"
           "    --source-format=zkc --entry=MODULE::ENTRY "
           "--module=MODULE=FILE.zkc\n"
           "    [--module=MODULE=FILE.zkc ...] [--asset=NAME=FORMAT=FILE ...]\n"
           "    [--no-simplify] [--release-storage]\n\n"
           "Mathematical MLIR and native participant programs:\n"
           "  protocol-export FILE.mlir\n"
           "  protocol-bundle FILE.mlir [--entry=NAME] [--no-simplify] "
           "[--release-storage]\n"
           "    [--fix-polynomial-factors]\n"
           "  protocol-checked-bundle FILE.mlir [--requirements=FILE] "
           "[--public-coin=FILE]\n"
           "  protocol-check-reductions SOURCE.mlir REQUIREMENTS.json "
           "CANDIDATE.mlir\n"
           "  protocol-public-coin SOURCE.mlir REQUIREMENT.json\n"
           "  protocol-check-public-coin SOURCE.mlir REQUIREMENT.json "
           "REPORT.json\n"
           "  protocol-proof FILE.mlir POLICY [--no-simplify] "
           "[--release-storage]\n"
           "  protocol-construct-proof FILE.mlir POLICY\n"
           "  protocol-check-proof FILE.mlir POLICY CANDIDATE.mlir\n\n"
           "Relation data (binary R1CS or canonical JSON):\n"
           "  relation-read | relation-inspect | relation-matrices FILE\n"
           "  relation-import FILE [SYMBOL] | relation-export FILE.mlir\n"
           "  relation-protocol | relation-requirements FILE\n"
           "  relation-evaluate FILE STATEMENT ASSIGNMENT\n"
           "  relation-air-read | relation-air-inspect FILE\n"
           "  relation-air-import FILE [SYMBOL] | relation-air-export "
           "FILE.mlir\n"
           "  relation-air-plan FILE HEIGHT | relation-air-evaluate FILE TRACE "
           "STATEMENT\n";
    return 0;
  }
  if (argc < 3) {
    errs() << "usage: zkc-compile COMMAND FILE\n"
              "Run zkc-compile --help for commands and options.\n";
    return 2;
  }
  if (StringRef(argv[1]).starts_with("relation-"))
    return relation::runCommand(argc, argv, registry);
  auto fail = [](Error e) {
    errs() << toString(std::move(e)) << '\n';
    return 1;
  };
  StringRef mode(argv[1]);
  if (mode == "protocol-proof" || mode == "protocol-construct-proof" ||
      mode == "protocol-check-proof") {
    if (argc < 4)
      return fail(error("native-proof-options"));
    auto source = readInput(argv[2], 16 * 1024 * 1024);
    if (!source)
      return fail(source.takeError());
    auto selected = readInput(argv[3], 1024 * 1024);
    if (!selected)
      return fail(selected.takeError());
    if (mode == "protocol-proof") {
      NativeProofOptions options;
      options.policy = *selected;
      std::set<std::string> seen;
      for (int i = 4; i < argc; ++i) {
        StringRef option(argv[i]);
        if (!seen.insert(option.str()).second)
          return fail(error("native-proof-options"));
        if (option == "--no-simplify")
          options.simplify = false;
        else if (option == "--release-storage")
          options.releaseStorage = true;
        else
          return fail(error("native-proof-options"));
      }
      auto compiled = compileNativeProof(*source, argv[2], options, registry);
      if (!compiled)
        return fail(compiled.takeError());
      outs() << compiled->deployment << '\n';
      return 0;
    }
    bool check = mode == "protocol-check-proof";
    if (argc != (check ? 5 : 4) || !mlirNestingWithinLimit(*source))
      return fail(error("native-proof-options"));
    auto policy = parseNativeProofPolicy(*selected);
    if (!policy)
      return fail(policy.takeError());
    mlir::MLIRContext context(registry);
    context.loadAllAvailableDialects();
    auto original = mlir::parseSourceString<mlir::ModuleOp>(*source, &context);
    if (!original)
      return fail(error("native-proof-source"));
    if (check) {
      auto bytes = readInput(argv[4], 16 * 1024 * 1024);
      if (!bytes)
        return fail(bytes.takeError());
      if (!mlirNestingWithinLimit(*bytes))
        return fail(error("native-proof-candidate-limit"));
      auto candidate =
          mlir::parseSourceString<mlir::ModuleOp>(*bytes, &context);
      if (!candidate)
        return fail(error("native-proof-candidate"));
      if (auto e = checkNativeProof(*original, *candidate, *policy))
        return fail(std::move(e));
      outs() << "[\"zkc.native-proof-checked/1\"]\n";
    } else {
      auto constructed = constructNativeProof(*original, *policy);
      if (!constructed)
        return fail(constructed.takeError());
      constructed->module->print(outs());
      outs() << '\n';
    }
    return 0;
  }
  if (mode == "protocol-public-coin" || mode == "protocol-check-public-coin") {
    bool check = mode == "protocol-check-public-coin";
    if (argc != (check ? 5 : 4))
      return fail(error("public-coin-options"));
    auto source = readInput(argv[2], 16 * 1024 * 1024);
    if (!source)
      return fail(source.takeError());
    auto requirement = readInput(argv[3], 1024 * 1024);
    if (!requirement)
      return fail(requirement.takeError());
    if (!mlirNestingWithinLimit(*source))
      return fail(error("public-coin-limit"));
    mlir::MLIRContext context(registry);
    context.loadAllAvailableDialects();
    auto original = mlir::parseSourceString<mlir::ModuleOp>(*source, &context);
    if (!original)
      return fail(error("public-coin-module"));
    if (check) {
      auto report = readInput(argv[4], 8 * 1024 * 1024);
      if (!report)
        return fail(report.takeError());
      if (auto error = checkPublicCoin(*original, *requirement, *report))
        return fail(std::move(error));
      outs() << "{\"format\":\"zkc.public-coin-checked/1\"}\n";
    } else {
      auto report = analyzePublicCoin(*original, *requirement);
      if (!report)
        return fail(report.takeError());
      outs() << *report << '\n';
    }
    return 0;
  }
  if (mode == "protocol-check-reductions") {
    if (argc != 5)
      return fail(error("polynomial-requirement-options"));
    auto source = readInput(argv[2], 16 * 1024 * 1024);
    if (!source)
      return fail(source.takeError());
    auto requirements = readInput(argv[3], 1024 * 1024);
    if (!requirements)
      return fail(requirements.takeError());
    auto candidate = readInput(argv[4], 16 * 1024 * 1024);
    if (!candidate)
      return fail(candidate.takeError());
    if (!mlirNestingWithinLimit(*source) || !mlirNestingWithinLimit(*candidate))
      return fail(error("polynomial-requirement-limit"));
    mlir::MLIRContext context(registry);
    context.loadAllAvailableDialects();
    auto original = mlir::parseSourceString<mlir::ModuleOp>(*source, &context);
    auto proposed =
        mlir::parseSourceString<mlir::ModuleOp>(*candidate, &context);
    if (!original || !proposed)
      return fail(error("polynomial-correspondence-module"));
    auto checked =
        checkPolynomialReductions(*original, *proposed, *requirements);
    if (!checked)
      return fail(checked.takeError());
    outs() << *checked << '\n';
    return 0;
  }
  if (mode == "protocol-bundle" || mode == "protocol-checked-bundle") {
    RunOptions options;
    std::set<std::string> seen;
    for (int i = 3; i < argc; ++i) {
      StringRef argument(argv[i]);
      auto name = argument.split('=').first;
      if (!seen.insert(name.str()).second)
        return fail(error("run-duplicate-option"));
      if (argument.consume_front("--entry="))
        options.entry = argument.str();
      else if (argument == "--no-simplify")
        options.simplify = false;
      else if (argument == "--release-storage")
        options.releaseStorage = true;
      else if (argument == "--fix-polynomial-factors")
        options.fixPolynomialFactors = true;
      else if (mode == "protocol-checked-bundle" &&
               argument.consume_front("--requirements=")) {
        auto requirements = readInput(argument, 1024 * 1024);
        if (!requirements)
          return fail(requirements.takeError());
        options.polynomialRequirements = std::move(*requirements);
      } else if (mode == "protocol-checked-bundle" &&
                 argument.consume_front("--public-coin=")) {
        auto requirement = readInput(argument, 1024 * 1024);
        if (!requirement)
          return fail(requirement.takeError());
        options.publicCoinRequirement = std::move(*requirement);
      } else
        return fail(error("run-option"));
    }
    if (mode == "protocol-checked-bundle" && !options.polynomialRequirements &&
        !options.publicCoinRequirement)
      return fail(error("checked-bundle-requirement-missing"));
    auto text = readInput(argv[2], 16 * 1024 * 1024);
    if (!text)
      return fail(text.takeError());
    auto result = compileRun(*text, argv[2], options, registry);
    if (!result)
      return fail(result.takeError());
    if (result->publicCoin || result->correspondence)
      outs() << json::Value(json::Object{
                    {"format", "zkc.checked-run/1"},
                    {"bundle", result->bundle},
                    {"correspondence",
                     result->correspondence
                         ? cantFail(json::parse(*result->correspondence))
                         : json::Value(nullptr)},
                    {"public_coin",
                     result->publicCoin
                         ? cantFail(json::parse(*result->publicCoin))
                         : json::Value(nullptr)}})
             << '\n';
    else
      outs() << result->bundle;
    return 0;
  }
  if (mode == "protocol-export") {
    if (argc != 3)
      return fail(error("unsupported-option"));
    auto text = readInput(argv[2], 16 * 1024 * 1024);
    if (!text)
      return fail(text.takeError());
    if (!mlirNestingWithinLimit(*text))
      return fail(error("mlir-depth-limit"));
    mlir::MLIRContext context(registry);
    auto module = mlir::parseSourceString<mlir::ModuleOp>(*text, &context);
    if (!module)
      return fail(error("interactive-malformed-ir"));
    auto result = protocol::exportModule(*module);
    if (!result)
      return fail(result.takeError());
    outs() << printJson(*result) << '\n';
    return 0;
  }
  return fail(error("unknown-command"));
}
