#include "zkc/Driver/Compiler.h"
#include "../Support/Input.h"
#include "Claims.h"
#include "InspectionPrinter.h"
#include "Language.h"
#include "Relations.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Analysis/OracleAccess.h"
#include "zkc/Analysis/PolynomialDomains.h"
#include "zkc/Compiler/Compilation.h"
#include "zkc/Compiler/Construction.h"
#include "zkc/Compiler/Inspection.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Compiler/PolynomialReduction.h"
#include "zkc/Compiler/PublicCoin.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Compiler/Source.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Frontend/Analysis.h"
#include "zkc/Frontend/Compile.h"
#include "zkc/Frontend/Inspection.h"
#include "zkc/Frontend/Loading.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Protocol/PhysicalOptions.h"
#include "zkc/Source/Codec.h"
#include "zkc/Support/MLIRInput.h"
#include "zkc/Translation/Protocol.h"
#include "zkc/Translation/Table.h"
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
           "Fresh source language (.zkc; explicit captured module map):\n"
           "  language-check | language-emit | language-interface | "
           "language-bundle\n"
           "    --source-format=zkc --entry=MODULE::ENTRY\n"
           "    --module=MODULE=FILE.zkc [--module=MODULE=FILE.zkc ...]\n"
           "    [--no-simplify] [--release-storage]\n\n"
           "Protocol developer sources (.pir or JSON; '-' reads stdin):\n"
           "  protocol-resolve       load bounded relation assets into a "
           "frozen project snapshot\n"
           "  protocol-materialize   verify relation views and explicitly "
           "lower "
           "to ordinary source\n"
           "  protocol-relation-data SNAPSHOT VIEW  emit identity-stamped "
           "matrix payloads\n"
           "  protocol-source        emit the existing JSON interchange\n"
           "  protocol-parse         emit syntax without semantic admission\n"
           "  protocol-explain       explain checked requirements and choices\n"
           "  protocol-inspect       machine-readable explanation and source\n"
           "  protocol-analyze       retained source types, references and "
           "diagnostics\n"
           "  domain-inspect SOURCE ENTRY [--compare=LEFT,RIGHT]\n"
           "  protocol-prepare       instantiate locals with source names\n"
           "  protocol-format        print readable source; retain text "
           "comments\n"
           "  protocol-format-check  fail when text formatting would change\n"
           "  protocol-admit         check protocol declarations\n"
           "  protocol-import        print common algorithm MLIR\n"
           "  protocol-expand        emit canonical expanded common source\n"
           "  protocol-algorithm-map emit local occurrence origins/accounting "
           "policy\n"
           "  protocol-project       emit logical participant JSON\n"
           "  protocol-compile       emit physical participant JSON\n"
           "  protocol-physical-ir   print physical participant MLIR\n"
           "  protocol-export        read MLIR and emit JSON\n"
           "  protocol-proof FILE.mlir POLICY [--no-simplify] "
           "[--release-storage]\n"
           "                  emit a source-checked flat proof deployment\n"
           "  protocol-construct-proof FILE.mlir POLICY\n"
           "                  emit constructed participant mathematics\n"
           "  protocol-check-proof FILE.mlir POLICY CANDIDATE.mlir\n"
           "                  compare actual candidate with admitted "
           "construction\n"
           "  protocol-bundle FILE.mlir [--entry=NAME] [--no-simplify]\n"
           "                  [--release-storage] [--fix-polynomial-factors]\n"
           "  protocol-checked-bundle FILE.mlir [--requirements=FILE] "
           "[--entry=NAME]\n"
           "                  emit a native bundle with checked "
           "correspondence\n"
           "                  [--public-coin=FILE] require at least one check\n"
           "  protocol-public-coin SOURCE.mlir REQUIREMENT.json\n"
           "  protocol-check-public-coin SOURCE.mlir REQUIREMENT.json "
           "REPORT.json\n"
           "  protocol-check-reductions SOURCE.mlir REQUIREMENTS.json "
           "CANDIDATE.mlir\n\n"
           "Relation definitions (binary R1CS or canonical relation JSON):\n"
           "  relation-protocol FILE         emit native R1CS Sumcheck MLIR\n"
           "  relation-requirements FILE     emit independent relation "
           "requirements\n"
           "  relation-read FILE             emit canonical relation JSON\n"
           "  relation-inspect FILE          inspect relation and public "
           "layout\n"
           "  relation-import FILE [SYMBOL]  emit structured relation MLIR\n"
           "  relation-compile FILE [PREFIX] emit specialized PIR local "
           "library\n"
           "  relation-compile-data FILE [PREFIX] emit PIR with public matrix "
           "inputs\n"
           "  relation-matrices FILE        emit padded public matrix "
           "payloads\n"
           "  relation-export FILE.mlir     emit canonical relation JSON\n"
           "  relation-lower FILE.mlir      specialize relation MLIR to PIR\n"
           "  relation-lower-data FILE.mlir lower with public matrix inputs\n"
           "  relation-evaluate FILE STATEMENT ASSIGNMENT\n"
           "  relation-air-read FILE        normalize finite AIR JSON\n"
           "  relation-air-import FILE [SYMBOL] emit structured AIR MLIR\n"
           "  relation-air-export FILE.mlir emit finite AIR JSON\n"
           "  relation-air-inspect FILE     derive AIR read/degree facts\n"
           "  relation-air-plan FILE HEIGHT emit a shared read schedule\n"
           "  relation-air-evaluate FILE TRACE STATEMENT\n\n"
           "  Source, analysis and execution commands accept repeated\n"
           "    --library=FILE (explicit source library roots)\n"
           "    File sources capture declared modules and relation assets.\n"
           "    Parse/format, JSON input and stdin do not accept libraries.\n\n"
           "  protocol-compile and protocol-physical-ir accept\n"
           "    --implementations=FILE (explicit binding selections)\n"
           "    --linear-contractions (local diagonal physical selection; "
           "default off)\n"
           "    --release-storage (ordinary local storage lifetime; default "
           "off)\n\n"
           "  protocol-import and protocol-physical-ir also accept\n"
           "    --locations (print diagnostic source locations)\n\n"
           "Construction (SOURCE and DESCRIPTOR may use .pir or JSON):\n"
           "  protocol-construct SOURCE DESCRIPTOR\n"
           "  protocol-construct-ir SOURCE DESCRIPTOR\n"
           "  protocol-check-construction SOURCE DESCRIPTOR CANDIDATE\n\n"
           "Execution-bound conditional claims (independent caller contract):\n"
           "  claim-inspect SOURCE ENTRY\n"
           "  claim-derive SOURCE CONTRACT\n"
           "  claim-check SOURCE CONTRACT CANDIDATE\n"
           "  claim-import SOURCE CONTRACT CANDIDATE\n"
           "  claim-check-ir SOURCE CONTRACT CANDIDATE.mlir\n"
           "  claim-check-construction SOURCE CONTRACT CANDIDATE DESCRIPTOR "
           "ARTIFACT\n"
           "  claim-check-lowering SOURCE CONTRACT CANDIDATE DESCRIPTOR "
           "ARTIFACT PHYSICAL\n"
           "    [--linear-contractions] [--release-storage] "
           "[--implementations=FILE]\n\n"
           "Authenticated oracle dataflow (recomputed from admitted source):\n"
           "  oracle-inspect SOURCE ENTRY\n"
           "  oracle-check SOURCE ENTRY [--publication-before-queries]\n"
           "    [--queries-before-responses] [--sampled-queries]\n"
           "    [--accept-result=N] (zero-based, all entry result ports)\n\n"
           "Earlier table path:\n"
           "  import|compile|export FILE [--simplify] "
           "[--physical=lazy|materialized]\n";
    return 0;
  }
  if (argc < 3) {
    errs() << "usage: zkc-compile COMMAND FILE\n"
              "Run zkc-compile --help for commands and options.\n";
    return 2;
  }
  if (StringRef(argv[1]).starts_with("claim-"))
    return claims::runCommand(argc, argv, registry);
  if (StringRef(argv[1]).starts_with("relation-"))
    return relation::runCommand(argc, argv, registry);
  auto fail = [](Error e) {
    errs() << toString(std::move(e)) << '\n';
    return 1;
  };
  if (StringRef(argv[1]).starts_with("oracle-")) {
    StringRef command(argv[1]);
    if ((command != "oracle-inspect" && command != "oracle-check") ||
        argc < 4 || argc > 8 || (command == "oracle-inspect" && argc != 4))
      return fail(zkc::error("unsupported-option"));
    OraclePolicy policy;
    for (int i = 4; i < argc; ++i) {
      StringRef option(argv[i]);
      if (option == "--publication-before-queries" &&
          !policy.publicationBeforeQueries)
        policy.publicationBeforeQueries = true;
      else if (option == "--queries-before-responses" &&
               !policy.queriesBeforeResponses)
        policy.queriesBeforeResponses = true;
      else if (option == "--sampled-queries" && !policy.sampledQueries)
        policy.sampledQueries = true;
      else if (option.consume_front("--accept-result=") &&
               !policy.acceptanceResult) {
        unsigned index;
        if (option.getAsInteger(10, index))
          return fail(zkc::error("unsupported-option"));
        policy.acceptanceResult = index;
      } else
        return fail(zkc::error("unsupported-option"));
    }
    auto text = readInput(argv[2], sourceByteLimit);
    if (!text)
      return fail(text.takeError());
    auto source = frontend::parseProtocolDocument(*text, argv[2]);
    if (!source)
      return fail(source.takeError());
    if (!source->module())
      return fail(zkc::error("oracle-source"));
    auto report = inspectOracleAccess(*source->module(), argv[3], policy);
    if (!report)
      return fail(report.takeError());
    outs() << encodeOracleAccess(*report) << '\n';
    return command == "oracle-check" && !report->findings.empty();
  }
  if (StringRef(argv[1]) == "domain-inspect") {
    if (argc != 4 && argc != 5)
      return fail(zkc::error("unsupported-option"));
    std::optional<std::pair<unsigned, unsigned>> comparison;
    if (argc == 5) {
      StringRef option(argv[4]);
      if (!option.consume_front("--compare="))
        return fail(zkc::error("unsupported-option"));
      auto parts = option.split(',');
      unsigned left, right;
      if (parts.first.getAsInteger(10, left) ||
          parts.second.getAsInteger(10, right))
        return fail(zkc::error("unsupported-option"));
      comparison = {left, right};
    }
    auto text = readInput(argv[2], sourceByteLimit);
    if (!text)
      return fail(text.takeError());
    auto document = frontend::parseProtocolDocument(*text, argv[2]);
    if (!document)
      return fail(document.takeError());
    if (!document->module())
      return fail(zkc::error("execution-unsupported-scope"));
    auto report = inspectPolynomialDomains(*document->module(), argv[3]);
    if (!report)
      return fail(report.takeError());
    auto encoded = encodePolynomialDomains(*report);
    if (comparison)
      (*encoded.getAsObject())["comparison"] =
          encodeDomainComparison(comparePolynomialDomains(
              *report, comparison->first, comparison->second));
    outs() << encoded << '\n';
    return 0;
  }
  if (StringRef(argv[1]) == "protocol-relation-data") {
    if (argc != 4)
      return fail(zkc::error("unsupported-option"));
    auto text = readInput(argv[2], relation::DependencyLimits::snapshotBytes);
    if (!text)
      return fail(text.takeError());
    auto document = frontend::parseProtocolDocument(*text, argv[2]);
    if (!document)
      return fail(document.takeError());
    if (auto e = frontend::checkProtocolDocument(*document))
      return fail(std::move(e));
    auto *module = document->module();
    if (!module)
      return fail(zkc::error("relation-source-shape"));
    auto view = llvm::find_if(module->relationViews,
                              [&](const auto &v) { return v.name == argv[3]; });
    if (view == module->relationViews.end())
      return fail(zkc::error("relation-view-target"));
    auto owner = llvm::find_if(module->relations, [&](const auto &r) {
      return r.name == view->relation;
    });
    if (owner == module->relations.end())
      return fail(zkc::error("relation-view-target"));
    auto *r1cs =
        std::get_if<std::shared_ptr<const relation::R1CS>>(&owner->value);
    if (!r1cs)
      return fail(zkc::error("relation-view-family"));
    outs() << printJson(json::Array{
                  "zkc.relation-matrices/1", view->name, owner->name,
                  relation::identity(*owner),
                  relation::matrixValues(**r1cs, view->kind == "multilinear")})
           << '\n';
    return 0;
  }
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
  StringRef physical;
  StringRef implementationPath;
  bool interactiveCommand = mode.starts_with("protocol-");
  bool construction = mode == "protocol-construct" ||
                      mode == "protocol-construct-ir" ||
                      mode == "protocol-check-construction";
  bool supportsSelection =
      mode == "protocol-compile" || mode == "protocol-physical-ir";
  bool supportsLocations =
      mode == "protocol-import" || mode == "protocol-physical-ir";
  bool showLocations = false;
  zkc::protocol::PhysicalOptions options;
  bool supportsProject =
      construction || mode == "protocol-resolve" ||
      mode == "protocol-materialize" || mode == "protocol-source" ||
      mode == "protocol-analyze" || mode == "protocol-prepare" ||
      mode == "protocol-inspect" || mode == "protocol-explain" ||
      mode == "protocol-admit" || mode == "protocol-import" ||
      mode == "protocol-expand" || mode == "protocol-algorithm-map" ||
      mode == "protocol-project" || supportsSelection;
  int optionStart =
      construction ? (mode == "protocol-check-construction" ? 5 : 4) : 3;
  if (argc < optionStart)
    return fail(zkc::error("unsupported-option"));
  std::vector<StringRef> libraryPaths;
  std::set<std::string> uniqueLibraries;
  bool simplify = false;
  for (int i = optionStart; i < argc; ++i) {
    StringRef option(argv[i]);
    if (supportsProject && option.consume_front("--library=")) {
      if (option.empty() || option == "-")
        return fail(zkc::error("unsupported-option"));
      if (!uniqueLibraries.insert(option.str()).second)
        return fail(zkc::error("duplicate-option"));
      if (libraryPaths.size() == frontend::ProjectInput::maxLibraries - 1)
        return fail(zkc::error("project-library-limit"));
      libraryPaths.push_back(option);
      continue;
    }
    if (supportsSelection && option == "--linear-contractions") {
      if (options.linearContractions)
        return fail(zkc::error("duplicate-option"));
      options.linearContractions = true;
      continue;
    }
    if (supportsSelection && option == "--release-storage") {
      if (options.releaseStorage)
        return fail(zkc::error("duplicate-option"));
      options.releaseStorage = true;
      continue;
    }
    if (supportsLocations && option == "--locations") {
      if (showLocations)
        return fail(zkc::error("duplicate-option"));
      showLocations = true;
      continue;
    }
    if (supportsSelection && option.consume_front("--implementations=")) {
      if (option.empty() || !implementationPath.empty())
        return fail(zkc::error("binding-selection-option"));
      implementationPath = option;
      continue;
    }
    if (mode != "compile")
      return fail(zkc::error("unsupported-option"));
    if (option == "--simplify") {
      if (simplify)
        return fail(zkc::error("duplicate-option"));
      simplify = true;
    } else if (option.consume_front("--physical=")) {
      if (!physical.empty())
        return fail(zkc::error("duplicate-option"));
      if (option != "lazy" && option != "materialized")
        return fail(zkc::error("unsupported-preparation-mode"));
      physical = option;
    } else
      return fail(zkc::error("unsupported-option"));
  }
  if (simplify && physical.empty())
    return fail(zkc::error("simplification-requires-physical"));
  auto text = readInput(
      argv[2], mode == "export" || mode == "protocol-export" ? mlirByteLimit
               : interactiveCommand ? relation::DependencyLimits::snapshotBytes
                                    : sourceByteLimit);
  if (!text)
    return fail(text.takeError());
  const auto documentForm = frontend::classifyDocument(*text);
  const bool commonSource = frontend::isCommonDocument(documentForm);
  if (interactiveCommand && mode != "protocol-export" &&
      text->size() > sourceByteLimit &&
      documentForm != frontend::SourceForm::CommonJSON)
    return fail(zkc::error("byte-limit"));
  if (!libraryPaths.empty() && (commonSource || StringRef(argv[2]) == "-"))
    return fail(zkc::error("unsupported-option"));
  std::optional<frontend::ProjectInput> project;
  std::optional<frontend::Analysis> sourceAnalysis;
  auto captureSource = [&]() -> Error {
    if (project)
      return Error::success();
    if (StringRef(argv[2]) == "-") {
      project = frontend::ProjectInput::single(
          frontend::Input::withoutFile(*text, argv[2]));
      return Error::success();
    }
    frontend::Input application(*text, argv[2]);
    std::vector<frontend::Input> libraries;
    std::error_code ec;
    auto applicationPath = std::filesystem::canonical(argv[2], ec);
    if (ec)
      return zkc::error("project-source-missing");
    std::map<std::filesystem::path, std::string> rootBytes;
    rootBytes.emplace(applicationPath, *text);
    size_t total = text->size();
    for (auto path : libraryPaths) {
      auto physical = std::filesystem::canonical(path.str(), ec);
      if (ec || !std::filesystem::is_regular_file(physical, ec) || ec)
        return zkc::error("project-source-missing");
      auto maximum =
          std::min(frontend::ProjectInput::maxSourceBytes,
                   frontend::ProjectInput::maxTotalSourceBytes - total);
      auto found = rootBytes.find(physical);
      if (found == rootBytes.end()) {
        auto contents = readInput(physical.string(), maximum);
        if (!contents)
          return contents.takeError();
        found = rootBytes.emplace(physical, std::move(*contents)).first;
      }
      if (found->second.size() > maximum)
        return zkc::error("project-source-limit");
      total += found->second.size();
      libraries.emplace_back(found->second, path.str());
    }
    auto captured = frontend::captureProject(std::move(application), libraries);
    if (!captured)
      return captured.takeError();
    project = std::move(*captured);
    return Error::success();
  };
  auto loadSourceDocument = [&]() -> Expected<source::Document> {
    if (commonSource)
      return frontend::parseProtocolDocument(*text, argv[2]);
    if (auto error = captureSource())
      return std::move(error);
    sourceAnalysis = frontend::analyzeProject(*project);
    return lowerSource(*sourceAnalysis);
  };
  if (mode == "protocol-resolve") {
    auto document = loadSourceDocument();
    if (!document)
      return fail(document.takeError());
    if (auto error = frontend::checkProtocolDocument(*document))
      return fail(std::move(error));
    outs() << printJson(source::encode(document->root())) << '\n';
    return 0;
  }
  if (mode == "protocol-materialize") {
    auto document = loadSourceDocument();
    if (!document)
      return fail(document.takeError());
    if (auto e = frontend::checkProtocolDocument(*document))
      return fail(std::move(e));
    if (!document->module())
      return fail(zkc::error("relation-materialize-source"));
    auto materialized = relation::materializeRelations(*document->module());
    if (!materialized)
      return fail(materialized.takeError());
    outs() << printJson(source::encode(*materialized)) << '\n';
    return 0;
  }
  if (!implementationPath.empty()) {
    auto contents = readInput(implementationPath, sourceByteLimit);
    if (!contents)
      return fail(contents.takeError());
    auto parsed = zkc::parseJson(*contents);
    if (!parsed)
      return fail(parsed.takeError());
    auto selection = protocol::decodeImplementationSelection(*parsed);
    if (!selection)
      return fail(selection.takeError());
    options.implementations = std::move(*selection);
  }

  if (mode == "protocol-format" || mode == "protocol-format-check") {
    auto formatted = frontend::formatProtocol(*text, argv[2]);
    if (!formatted)
      return fail(formatted.takeError());
    if (mode == "protocol-format-check") {
      if (*formatted != *text) {
        errs() << argv[2] << ": source-not-formatted: run protocol-format\n";
        return 1;
      }
    } else
      outs() << *formatted;
    return 0;
  }
  if (mode == "protocol-analyze") {
    if (!commonSource)
      if (auto error = captureSource())
        return fail(std::move(error));
    auto analysis = commonSource ? frontend::analyzeProtocol(*text, argv[2])
                                 : frontend::analyzeProject(*project);
    outs() << printJson(frontend::inspectAnalysis(analysis)) << '\n';
    return 0;
  }
  if (mode == "protocol-parse") {
    auto syntax = frontend::inspectProtocolSyntax(*text, argv[2]);
    if (!syntax)
      return fail(syntax.takeError());
    outs() << printJson(*syntax) << '\n';
    return 0;
  }
  if (mode == "protocol-source" || mode == "protocol-prepare" ||
      mode == "protocol-inspect" || mode == "protocol-explain") {
    auto document = loadSourceDocument();
    if (!document)
      return fail(document.takeError());
    if (mode == "protocol-inspect" || mode == "protocol-explain") {
      auto report =
          inspectSource(*document, sourceAnalysis ? &*sourceAnalysis : nullptr);
      if (!report)
        return fail(report.takeError());
      if (mode == "protocol-inspect")
        outs() << printJson(*report) << '\n';
      else
        printSourceInspection(*report, outs());
      return 0;
    }
    if (mode == "protocol-prepare") {
      mlir::MLIRContext context(registry);
      context.printOpOnDiagnostic(false);
      context.loadAllAvailableDialects();
      auto prepared = prepareSource(*document, context);
      if (!prepared)
        return fail(prepared.takeError());
      outs() << printJson(source::encode(*prepared)) << '\n';
    } else {
      if (auto e = frontend::checkProtocolDocument(*document))
        return fail(std::move(e));
      outs() << printJson(source::encode(document->root())) << '\n';
    }
    return 0;
  }
  std::unique_ptr<mlir::MLIRContext> context;
  if (construction || mode == "export" || mode == "protocol-export") {
    context = std::make_unique<mlir::MLIRContext>(registry);
    context->printOpOnDiagnostic(false);
    context->loadAllAvailableDialects();
  }
  mlir::OwningOpRef<mlir::ModuleOp> module;
  if (construction) {
    auto source = loadSourceDocument();
    if (!source)
      return fail(source.takeError());
    auto descriptorText = readInput(argv[3], sourceByteLimit);
    if (!descriptorText)
      return fail(descriptorText.takeError());
    auto descriptor = frontend::parseProtocolDocument(*descriptorText, argv[3]);
    if (!descriptor)
      return fail(descriptor.takeError());
    if (!source->module() || !descriptor->construction())
      return fail(zkc::error("construction-input-kind"));
    auto constructionDescriptor = *descriptor->construction();
    if (project) {
      auto checked = sourceAnalysis->checkedModule();
      if (!checked)
        return fail(checked.takeError());
      auto bound = frontend::bindConstruction(
          *checked, std::move(constructionDescriptor));
      if (!bound)
        return fail(bound.takeError());
      constructionDescriptor = std::move(*bound);
    }
    if (mode == "protocol-check-construction") {
      auto candidateText = readInput(argv[4], sourceByteLimit);
      if (!candidateText)
        return fail(candidateText.takeError());
      auto candidate = zkc::parseJson(*candidateText);
      if (!candidate)
        return fail(candidate.takeError());
      if (auto e = zkc::protocol::checkConstruction(
              *source->module(), constructionDescriptor, *candidate, *context))
        return fail(std::move(e));
      outs() << "construction-checked\n";
      return 0;
    }
    auto result = zkc::protocol::construct(*source->module(),
                                           constructionDescriptor, *context);
    if (!result)
      return fail(result.takeError());
    if (mode == "protocol-construct-ir") {
      result->module->print(outs());
      outs() << '\n';
    } else
      outs() << zkc::printJson(result->certificate) << '\n';
    return 0;
  }
  if (interactiveCommand) {
    if (mode == "protocol-export") {
      if (!mlirNestingWithinLimit(*text))
        return fail(zkc::error("mlir-depth-limit"));
      module = mlir::parseSourceString<mlir::ModuleOp>(*text, context.get());
      if (!module)
        return 1;
    } else {
      auto document = loadSourceDocument();
      if (!document)
        return fail(document.takeError());
      if (mode == "protocol-admit") {
        if (document->construction())
          return fail(zkc::error("interactive-format"));
        if (auto e = frontend::checkProtocolDocument(*document))
          return fail(std::move(e));
        outs() << "declaration-admitted\n";
        return 0;
      }
      ProtocolOptions request;
      request.physical = options;
      if (mode == "protocol-import")
        request.action = ProtocolAction::Import;
      else if (mode == "protocol-expand" || mode == "protocol-algorithm-map")
        request.action = ProtocolAction::Expand;
      else if (mode == "protocol-project")
        request.action = ProtocolAction::Project;
      else if (mode == "protocol-compile" || mode == "protocol-physical-ir")
        request.action = ProtocolAction::Plan;
      else
        return fail(zkc::error("unknown-command"));
      auto compiled = compileProtocol(std::move(*document), request, registry);
      if (!compiled)
        return fail(compiled.takeError());
      if (options.linearContractions)
        printLinearContractionStats(compiled->statistics(), errs());
      if (mode == "protocol-import" || mode == "protocol-physical-ir") {
        compiled->module().print(
            outs(), mlir::OpPrintingFlags().enableDebugInfo(showLocations));
        outs() << '\n';
      } else if (mode == "protocol-algorithm-map") {
        json::Array rows;
        for (const auto &origin : compiled->origins()) {
          json::Array path;
          for (const auto &[site, callee] : origin.path)
            path.push_back(json::Array{site, callee});
          rows.push_back(json::Array{origin.function, origin.site,
                                     origin.definition, origin.originalSite,
                                     std::move(path)});
        }
        outs() << printJson(json::Array{"zkc.algorithm-expansion/1",
                                        "canonical-expanded-locals/1",
                                        std::move(rows)})
               << '\n';
      } else {
        auto result = protocol::exportModule(compiled->module());
        if (!result)
          return fail(result.takeError());
        outs() << printJson(*result) << '\n';
      }
      return 0;
    }
    auto result = zkc::protocol::exportModule(*module);
    if (!result)
      return fail(result.takeError());
    outs() << zkc::printJson(*result) << '\n';
    return 0;
  }
  if (mode == "export") {
    if (!mlirNestingWithinLimit(*text))
      return fail(zkc::error("mlir-depth-limit"));
    module = mlir::parseSourceString<mlir::ModuleOp>(*text, context.get());
    if (!module)
      return 1;
  } else if (mode == "import" || mode == "compile") {
    auto json = zkc::parseJson(*text);
    if (!json)
      return fail(json.takeError());
    TableOptions request;
    request.simplify = simplify;
    request.action = mode == "import"             ? TableAction::Import
                     : physical == "lazy"         ? TableAction::Lazy
                     : physical == "materialized" ? TableAction::Materialized
                                                  : TableAction::Plan;
    auto compiled = compileTable(*json, request, registry);
    if (!compiled)
      return fail(compiled.takeError());
    if (mode == "import") {
      compiled->module().print(outs());
      outs() << '\n';
    } else {
      auto plan = exportPlan(compiled->module());
      if (!plan)
        return fail(plan.takeError());
      outs() << printJson(*plan) << '\n';
    }
    return 0;
  } else
    return fail(zkc::error("unknown-command"));
  auto plan = zkc::exportPlan(*module);
  if (!plan)
    return fail(plan.takeError());
  outs() << zkc::printJson(*plan) << '\n';
  return 0;
}
