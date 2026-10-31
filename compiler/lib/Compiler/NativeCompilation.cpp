#include "../Transforms/PreparedProtocol.h"
#include "CompilationState.h"
#include "NativeDeployment.h"
#include "Run.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Compiler/Compilation.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Compiler/Observation.h"
#include "zkc/Compiler/PolynomialReduction.h"
#include "zkc/Compiler/PublicCoin.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/LogicalTree.h"
#include "zkc/Support/MLIRInput.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Transforms/Stages.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/TimeProfiler.h"

using namespace llvm;
using namespace mlir;
namespace zkc {
using detail::compilationError;
using detail::Diagnostics;
namespace {
Expected<OwningOpRef<ModuleOp>> parseNativeSource(StringRef text,
                                                  StringRef filename,
                                                  MLIRContext &context,
                                                  Diagnostics &diagnostics) {
  if (text.size() > 16 * 1024 * 1024 || filename.size() > 4096 ||
      !mlirNestingWithinLimit(text))
    return diagnostics.failure(error("run-input-limit"));
  context.loadAllAvailableDialects();
  if (diagnostics.hasErrors())
    return diagnostics.failure();
  SourceMgr source;
  source.AddNewSourceBuffer(MemoryBuffer::getMemBufferCopy(text, filename),
                            SMLoc());
  auto module = parseSourceFile<ModuleOp>(source, &context);
  if (!module || failed(zkc::admitStage(*module)) || diagnostics.hasErrors())
    return diagnostics.failure();
  auto roots = module->getOps<protocol_ir::ProtocolModuleOp>();
  if (!llvm::hasSingleElement(roots) ||
      (*roots.begin()).getProfile() != protocol_ir::Profile::Protocol)
    return diagnostics.failure(error("run-source-profile"));
  diagnostics.atRoot(module->getLoc());
  return module;
}
LogicalResult lowerProgram(ModuleOp module, bool simplify, bool fixPolynomials,
                           bool releaseStorage,
                           MathematicalSelectionPolicy mathematicalSelection,
                           LinearContractionStats &statistics,
                           json::Array *stages = nullptr,
                           StringRef selectedRole = {},
                           CompilationObservation *observations = nullptr,
                           const target::CpuTarget &cpuTarget = {}) {
  TimeTraceScope timing("zkc.lower-participants");
  PassManager pipeline(module.getContext());
  mathematical::RealizationTrace trace;
  trace.eventLimit = 4096;
  if (observations)
    observations->instrument(pipeline);
  buildExecutionPipeline(pipeline, simplify, fixPolynomials,
                         mathematicalSelection,
                         observations ? &trace : nullptr);
  if (stages)
    for (auto &pass : pipeline.getPasses())
      stages->push_back(pass.getArgument().str());
  auto outcome = pipeline.run(module);
  if (observations)
    observations->decisions(module, trace);
  if (failed(outcome))
    return failure();
  if (!selectedRole.empty()) {
    auto owner = *module.getOps<protocol_ir::ProtocolModuleOp>().begin();
    SymbolTable table(owner);
    llvm::StringSet<> reached;
    SmallVector<Operation *> pending;
    for (auto endpoint :
         owner.getBody().front().getOps<protocol_ir::ParticipantOp>())
      if (endpoint.getRole() == selectedRole)
        pending.push_back(endpoint);
    if (pending.size() != 1)
      return failure();
    for (auto entry :
         owner.getBody().front().getOps<protocol_ir::ProtocolEntryOp>()) {
      SmallVector<Attribute> targets;
      for (auto value : entry.getTargets()) {
        auto pair = cast<ArrayAttr>(value);
        if (cast<StringAttr>(pair[0]).getValue() == selectedRole)
          targets.push_back(pair);
      }
      if (!targets.empty()) {
        entry.setTargetsAttr(ArrayAttr::get(module.getContext(), targets));
        pending.push_back(entry);
      }
    }
    while (!pending.empty()) {
      auto *definition = pending.pop_back_val();
      auto name = SymbolTable::getSymbolName(definition);
      if (!name || !reached.insert(name.getValue()).second)
        continue;
      auto uses = SymbolTable::getSymbolUses(definition);
      if (!uses)
        return failure();
      for (const auto &use : *uses)
        if (auto *target =
                table.lookup(use.getSymbolRef().getRootReference().getValue()))
          pending.push_back(target);
    }
    for (auto &definition : make_early_inc_range(owner.getBody().front())) {
      auto name = SymbolTable::getSymbolName(&definition);
      if (!name || !reached.contains(name.getValue()))
        definition.erase();
    }
  }
  PassManager physical(module.getContext());
  if (observations)
    observations->instrument(physical);
  PhysicalPipelineOptions options;
  options.releaseStorage = releaseStorage;
  options.statistics = &statistics;
  options.mathematics = mathematicalSelection;
  options.cpuTarget = cpuTarget;
  buildPhysicalPipeline(physical, options);
  if (stages)
    for (auto &pass : physical.getPasses())
      stages->push_back(pass.getArgument().str());
  auto physicalOutcome = physical.run(module);
  if (observations && succeeded(physicalOutcome))
    observations->phase("physical", module);
  return physicalOutcome;
}
} // namespace
Expected<CompiledRun> compileRun(StringRef text, StringRef filename,
                                 const RunOptions &options,
                                 const DialectRegistry &registry) {
  if (text.size() > 16 * 1024 * 1024 || options.entry.empty() ||
      options.entry.size() > 4096 || filename.size() > 4096 ||
      !mlirNestingWithinLimit(text))
    return compilationError(error("run-input-limit"));
  auto result = std::make_unique<Compilation::Storage>(registry);
  Diagnostics diagnostics(result->context);
  auto parsed = parseNativeSource(text, filename, result->context, diagnostics);
  if (!parsed)
    return parsed.takeError();
  result->module = std::move(*parsed);
  if (options.observations)
    options.observations->phase("protocol", *result->module);
  std::optional<json::Value> publicCoin;
  if (options.publicCoinRequirement) {
    auto checked =
        analyzePublicCoin(*result->module, *options.publicCoinRequirement,
                          options.mathematicalSelection);
    if (!checked)
      return diagnostics.failure(checked.takeError());
    if (checked->getAsObject()->getString("entry") != options.entry)
      return diagnostics.failure(error("public-coin-interface"));
    publicCoin = std::move(*checked);
  }
  // Freeze the source before helper expansion. Checked candidates are projected
  // without folding, checked once, and then lowered in this same invocation.
  std::optional<json::Value> correspondence;
  OwningOpRef<ModuleOp> original;
  if (options.polynomialRequirements)
    original = cast<ModuleOp>(result->module->getOperation()->clone());
  mathematical::RealizationTrace preparationTrace;
  preparationTrace.eventLimit = 4096;
  auto preparation = [&] {
    TimeTraceScope timing("zkc.prepare-protocol");
    return mathematical::PreparedProtocol::prepare(
        *result->module, options.mathematicalSelection,
        options.observations ? &preparationTrace : nullptr);
  }();
  if (options.observations)
    options.observations->decisions(*result->module, preparationTrace);
  if (!preparation || diagnostics.hasErrors())
    return diagnostics.failure();
  // Library declarations have already been admitted and expanded into actual
  // callers. Only explicit deployment roots acquire external oracle ingress.
  // Keep every companion whose bytes the correspondence report will publish.
  SmallVector<std::string> companionEntries;
  if (options.polynomialRequirements) {
    auto entries = polynomialRequirementEntries(*options.polynomialRequirements);
    if (!entries)
      return diagnostics.failure(entries.takeError());
    companionEntries = std::move(*entries);
  }
  SmallVector<StringRef> entries{options.entry};
  for (const auto &entry : companionEntries)
    if (!is_contained(entries, StringRef(entry)))
      entries.push_back(entry);
  if (failed(preparation->selectEntries(entries)) || diagnostics.hasErrors())
    return diagnostics.failure();
  auto realization = mathematical::RealizedProtocol::realize(
      std::move(*preparation), options.oracleRealization);
  if (!realization)
    return diagnostics.failure(realization.takeError());
  result->realization.emplace(std::move(*realization));
  // Native scheduling consumes the actual represented interface. The original
  // logical clauses remain owned alongside the checked edge through
  // publication.
  auto prepared = result->realization->candidateSnapshot();
  if (options.observations)
    options.observations->phase("realized", *prepared);
  result->module = result->realization->project(
      !options.polynomialRequirements && options.simplify);
  if (!result->module || diagnostics.hasErrors())
    return diagnostics.failure();
  if (options.polynomialRequirements) {
    auto checked = checkPolynomialReductions(*original, *result->module,
                                             *options.polynomialRequirements,
                                             options.mathematicalSelection);
    if (!checked)
      return diagnostics.failure(checked.takeError());
    bool covered = false;
    for (auto &item : *checked->getAsObject()->getArray("requirements")) {
      auto &record = *item.getAsObject();
      covered |= record.getString("reduction") == options.entry ||
                 record.getString("terminal") == options.entry;
      if (auto *composition = record.getObject("composition"))
        covered |= composition->getString("entry") == options.entry;
    }
    if (!covered)
      return diagnostics.failure(error("polynomial-correspondence-entry"));
    correspondence = std::move(*checked);
  }
  if (options.observations)
    options.observations->phase("participant", *result->module);
  json::Array loweringStages;
  if (failed(lowerProgram(*result->module, options.simplify,
                          options.fixPolynomialFactors, options.releaseStorage,
                          options.mathematicalSelection, result->statistics,
                          &loweringStages, {}, options.observations,
                          options.cpuTarget)) ||
      diagnostics.hasErrors())
    return diagnostics.failure();
  auto bundle =
      detail::buildRunBundle(*prepared, *result->module, options.entry);
  if (!bundle)
    return diagnostics.failure(bundle.takeError());
  if (diagnostics.hasErrors())
    return diagnostics.failure();
  std::optional<std::string> report;
  if (correspondence) {
    auto digest = [](StringRef value) {
      return llvm::toHex(SHA256::hash(arrayRefFromStringRef(value)), true);
    };
    auto &object = *correspondence->getAsObject();
    object["source_sha256"] = digest(text);
    object["requirements_input_sha256"] =
        digest(*options.polynomialRequirements);
    object["bundle_sha256"] = digest(*bundle);
    object["entry"] = options.entry;
    object["simplify"] = options.simplify;
    object["release_storage"] = options.releaseStorage;
    object["finite_bulk"] = options.mathematicalSelection.finiteBulk;
    object["fuse_vector_reductions"] =
        options.mathematicalSelection.vectorReductionFusion;
    object["fuse_collect_fold"] =
        options.mathematicalSelection.collectFoldFusion;
    object["calculation_batching"] =
        options.mathematicalSelection.calculationBatching;
    object["fix_polynomial_factors"] = options.fixPolynomialFactors;
    object["post_check_passes"] = json::Array(loweringStages);
    // Bind every checked entry from the same final module, including a
    // composed caller when a standalone component is the selected output.
    json::Object hashes;
    hashes[options.entry] = digest(*bundle);
    for (auto &item : *object.getArray("requirements")) {
      auto &record = *item.getAsObject();
      SmallVector<StringRef> entries{*record.getString("reduction"),
                                     *record.getString("terminal")};
      if (auto *composition = record.getObject("composition"))
        entries.push_back(*composition->getString("entry"));
      for (StringRef entry : entries) {
        if (hashes.get(entry))
          continue;
        auto companion =
            detail::buildRunBundle(*prepared, *result->module, entry);
        if (!companion)
          return diagnostics.failure(companion.takeError());
        hashes[entry.str()] = digest(*companion);
      }
    }
    object["bundles_sha256"] = std::move(hashes);
    report.emplace();
    raw_string_ostream(*report) << *correspondence;
  }
  std::optional<std::string> viewReport;
  if (publicCoin) {
    auto digest = [](StringRef value) {
      return llvm::toHex(SHA256::hash(arrayRefFromStringRef(value)), true);
    };
    json::Value record(json::Object{
        {"format", "zkc.compiled-public-coin/0"},
        {"view", std::move(*publicCoin)},
        {"source_sha256", digest(text)},
        {"bundle_sha256", digest(*bundle)},
        {"simplify", options.simplify},
        {"release_storage", options.releaseStorage},
        {"finite_bulk", options.mathematicalSelection.finiteBulk},
        {"fuse_vector_reductions",
         options.mathematicalSelection.vectorReductionFusion},
        {"fuse_collect_fold", options.mathematicalSelection.collectFoldFusion},
        {"calculation_batching",
         options.mathematicalSelection.calculationBatching},
        {"fix_polynomial_factors", options.fixPolynomialFactors}});
    // Describe semantic pipeline stages with their public pass names. This is
    // not a PassManager execution trace: preparation is implicit here, and
    // projection consumes the privately owned prepared subject above.
    json::Array passes;
    passes.push_back("zkc-prepare-protocol");
    passes.push_back("zkc-project-protocol");
    for (auto &stage : loweringStages)
      passes.push_back(stage);
    (*record.getAsObject())["post_analysis_passes"] = std::move(passes);
    (*record.getAsObject())["projection_simplify"] =
        !options.polynomialRequirements && options.simplify;
    viewReport.emplace();
    raw_string_ostream(*viewReport) << record;
  }
  return CompiledRun{Compilation(std::move(result)), std::move(*bundle),
                     std::move(report), std::move(viewReport)};
}
Expected<CompiledNativeProof>
compileNativeProof(StringRef text, StringRef filename,
                   const NativeProofOptions &options,
                   const DialectRegistry &registry) {
  auto result = std::make_unique<Compilation::Storage>(registry);
  Diagnostics diagnostics(result->context);
  std::optional<NativeProofPolicy> policy;
  if (const auto *explicitPolicy = std::get_if<std::string>(&options.policy)) {
    auto parsed = parseNativeProofPolicy(*explicitPolicy);
    if (!parsed)
      return diagnostics.failure(parsed.takeError());
    policy = std::move(*parsed);
  }
  auto parsed = parseNativeSource(text, filename, result->context, diagnostics);
  if (!parsed)
    return parsed.takeError();
  auto original = std::move(*parsed);
  if (options.observations)
    options.observations->phase("protocol", *original);
  if (!policy) {
    auto selected = selectNativeProofDraws(
        *original, std::get<NativeProofSelection>(options.policy).policy,
        options.mathematicalSelection);
    if (!selected)
      return diagnostics.failure(selected.takeError());
    policy = std::move(*selected);
  }
  auto constructed =
      constructNativeProof(*original, *policy, options.mathematicalSelection);
  if (!constructed)
    return diagnostics.failure(constructed.takeError());
  result->module = std::move(constructed->module);
  if (options.observations)
    options.observations->phase("participant", *result->module);
  auto constructedRoot =
      *result->module->getOps<protocol_ir::ProtocolModuleOp>().begin();
  auto retainedProjection = *constructedRoot.getBody()
                                 .front()
                                 .getOps<protocol_ir::ProjectionOp>()
                                 .begin();
  auto interface = cast<DictionaryAttr>(retainedProjection.getInterfaces()[0]);
  StringRef selectedRole;
  if (options.operation)
    selectedRole = *options.operation == NativeProofOperation::Verify
                       ? policy->validator
                       : policy->producer;
  if (failed(lowerProgram(*result->module, options.simplify, false,
                          options.releaseStorage, options.mathematicalSelection,
                          result->statistics, nullptr, selectedRole,
                          options.observations, options.cpuTarget)) ||
      diagnostics.hasErrors())
    return diagnostics.failure();
  auto exported = protocol::exportModule(*result->module);
  if (!exported)
    return diagnostics.failure(exported.takeError());
  auto candidate = printJson(*exported);
  if (candidate.size() > program::artifactByteLimit)
    return diagnostics.failure(error("native-proof-candidate-limit"));
  auto root = *result->module->getOps<protocol_ir::ProtocolModuleOp>().begin();

  auto type =
      cast<FunctionType>(interface.getAs<TypeAttr>("original_type").getValue());
  json::Array maps;
  for (auto item : interface.getAs<ArrayAttr>("participants")) {
    auto port = cast<DictionaryAttr>(item);
    json::Array inputs, outputs, services;
    auto data = [&](ArrayAttr ports, bool input, json::Array &out) -> Error {
      for (auto value : ports) {
        auto index = cast<IntegerAttr>(value).getInt();
        auto logical = protocol::encodeBoundType(
            input ? type.getInput(index) : type.getResult(index), false);
        if (!logical)
          return logical.takeError();
        out.push_back(json::Array{std::to_string(index), logical->spelling()});
      }
      return Error::success();
    };
    if (auto e = data(port.getAs<ArrayAttr>("inputs"), true, inputs))
      return diagnostics.failure(std::move(e));
    if (auto e = data(port.getAs<ArrayAttr>("outputs"), false, outputs))
      return diagnostics.failure(std::move(e));
    auto role = port.getAs<StringAttr>("role").str();
    if (!selectedRole.empty() && role != selectedRole)
      continue;
    auto participant =
        cast<protocol_ir::ParticipantOp>(SymbolTable::lookupSymbolIn(
            root, port.getAs<FlatSymbolRefAttr>("participant")));
    auto installed = participant->getAttrOfType<ArrayAttr>("service_ports");
    unsigned serviceIndex = 0;
    for (auto input : port.getAs<ArrayAttr>("service_inputs")) {
      auto originalInput = cast<IntegerAttr>(input).getInt();
      if (is_contained(policy->services, originalInput))
        continue;
      // Projection verification owns the service map. Serialize its installed
      // names and ingress indices instead of reconstructing generated names.
      auto service = cast<ArrayAttr>(installed[serviceIndex++]);
      services.push_back(json::Array{
          std::to_string(originalInput), cast<StringAttr>(service[0]).str(),
          cast<StringAttr>(service[1]).str(),
          std::to_string(cast<IntegerAttr>(service[2]).getInt())});
    }
    std::string acceptance;
    if (role == policy->validator)
      for (auto [i, originalOutput] :
           llvm::enumerate(port.getAs<ArrayAttr>("outputs")))
        if (cast<IntegerAttr>(originalOutput).getInt() == policy->acceptance)
          acceptance = std::to_string(i);
    maps.push_back(json::Array{
        role, port.getAs<FlatSymbolRefAttr>("participant").getValue().str(),
        std::move(inputs), std::move(outputs), std::move(services),
        std::move(acceptance)});
  }
  auto descriptorBytes = encodeLogicalTree(constructed->descriptor);
  if (!descriptorBytes)
    return diagnostics.failure(descriptorBytes.takeError());
  auto digest = [](StringRef bytes) {
    return toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
  };
  json::Value deployment(json::Array{
      "zkc.native-proof/0", digest(text), constructed->descriptor,
      digest(*descriptorBytes), candidate, digest(candidate), std::move(maps),
      json::Array{
          options.simplify ? "true" : "false",
          options.releaseStorage ? "true" : "false",
          options.mathematicalSelection.vectorReductionFusion ? "true"
                                                              : "false",
          options.mathematicalSelection.finiteBulk ? "true" : "false",
          options.mathematicalSelection.collectFoldFusion ? "true" : "false",
          options.mathematicalSelection.calculationBatching ? "true" : "false"},
      json::Array(constructed->wireSites)});
  auto encoded = printJson(deployment);
  if (encoded.size() > 16 * 1024 * 1024)
    return diagnostics.failure(error("native-proof-deployment-limit"));
  if (auto e = detail::verifyNativeDeployment(
          *original, *result->module, text, *policy, options,
          constructed->descriptor, constructed->wireSites, encoded))
    return diagnostics.failure(std::move(e));
  return CompiledNativeProof{Compilation(std::move(result)), std::move(encoded),
                             std::move(*policy)};
}
} // namespace zkc
