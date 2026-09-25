#include "zkc/Driver/Compiler.h"
#include "../Support/Input.h"
#include "Claims.h"
#include "InspectionPrinter.h"
#include "Relations.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Analysis/OracleAccess.h"
#include "zkc/Analysis/PolynomialDomains.h"
#include "zkc/Compiler/Compilation.h"
#include "zkc/Compiler/Construction.h"
#include "zkc/Compiler/Inspection.h"
#include "zkc/Compiler/Source.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Frontend/Analysis.h"
#include "zkc/Frontend/Compile.h"
#include "zkc/Frontend/Inspection.h"
#include "zkc/Frontend/Loading.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Protocol/Instantiation.h"
#include "zkc/Protocol/PhysicalOptions.h"
#include "zkc/Source/Codec.h"
#include "zkc/Support/MLIRInput.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Translation/Protocol.h"
#include "zkc/Translation/Table.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <filesystem>
#include <map>
#include <set>
using namespace llvm;
int zkc::runCompiler(int argc, char **argv,
                     const mlir::DialectRegistry &extensions) {
  mlir::DialectRegistry registry;
  registerDialects(registry);
  extensions.appendTo(registry);
  if (argc == 2 &&
      (StringRef(argv[1]) == "--help" || StringRef(argv[1]) == "-h")) {
    outs()
        << "usage: zkc-compile COMMAND FILE\n\n"
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
           "  protocol-export        read MLIR and emit JSON\n\n"
           "Relation definitions (binary R1CS or canonical relation JSON):\n"
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
  if (interactiveCommand && mode != "protocol-export" &&
      text->size() > sourceByteLimit &&
      !StringRef(*text).ltrim().starts_with("["))
    return fail(zkc::error("byte-limit"));
  bool jsonSource = StringRef(*text).ltrim().starts_with("[");
  if (!libraryPaths.empty() && (jsonSource || StringRef(argv[2]) == "-"))
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
    if (jsonSource)
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
    if (!jsonSource)
      if (auto error = captureSource())
        return fail(std::move(error));
    auto analysis = jsonSource ? frontend::analyzeProtocol(*text, argv[2])
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
