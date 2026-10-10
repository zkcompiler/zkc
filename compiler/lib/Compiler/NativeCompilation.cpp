#include "../Transforms/PreparedProtocol.h"
#include "CompilationState.h"
#include "NativeDeployment.h"
#include "Run.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Compiler/Compilation.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Compiler/PolynomialReduction.h"
#include "zkc/Compiler/PublicCoin.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/LogicalTree.h"
#include "zkc/Support/MLIRInput.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/SourceMgr.h"

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
  if (!module || diagnostics.hasErrors())
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
                           LinearContractionStats &statistics) {
  PassManager pipeline(module.getContext());
  if (simplify)
    pipeline.addPass(protocol::createSimplifyParticipantPass());
  if (fixPolynomials)
    pipeline.addPass(protocol::createFixPolynomialFactorsPass());
  pipeline.addPass(protocol::createEliminatePolynomialsPass());
  pipeline.addPass(protocol::createLowerMathPass());
  pipeline.addPass(protocol::createSelectPhysicalPass({}, false, releaseStorage,
                                                      &statistics));
  return pipeline.run(module);
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
  std::optional<json::Value> publicCoin;
  if (options.publicCoinRequirement) {
    auto checked =
        analyzePublicCoin(*result->module, *options.publicCoinRequirement);
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
  auto preparation = mathematical::PreparedProtocol::prepare(
      *result->module, options.fuseVectorReductions);
  if (!preparation || diagnostics.hasErrors())
    return diagnostics.failure();
  auto prepared = preparation->snapshot();
  result->module =
      std::move(*preparation)
          .project(!options.polynomialRequirements && options.simplify);
  if (!result->module || diagnostics.hasErrors())
    return diagnostics.failure();
  if (options.polynomialRequirements) {
    auto checked = checkPolynomialReductions(*original, *result->module,
                                             *options.polynomialRequirements,
                                             options.fuseVectorReductions);
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
  if (failed(lowerProgram(*result->module, options.simplify,
                          options.fixPolynomialFactors, options.releaseStorage,
                          result->statistics)) ||
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
    object["fuse_vector_reductions"] = options.fuseVectorReductions;
    object["fix_polynomial_factors"] = options.fixPolynomialFactors;
    json::Array passes;
    if (options.simplify) {
      passes.push_back("zkc-simplify-participant");
    }
    if (options.fixPolynomialFactors)
      passes.push_back("zkc-fix-polynomial-factors");
    passes.push_back("zkc-eliminate-polynomials");
    passes.push_back("zkc-lower-math");
    passes.push_back("zkc-select-physical");
    object["post_check_passes"] = std::move(passes);
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
    json::Value record(
        json::Object{{"format", "zkc.compiled-public-coin/0"},
                     {"view", std::move(*publicCoin)},
                     {"source_sha256", digest(text)},
                     {"bundle_sha256", digest(*bundle)},
                     {"simplify", options.simplify},
                     {"release_storage", options.releaseStorage},
                     {"fuse_vector_reductions", options.fuseVectorReductions},
                     {"fix_polynomial_factors", options.fixPolynomialFactors}});
    // Describe semantic pipeline stages with their public pass names. This is
    // not a PassManager execution trace: preparation is implicit here, and
    // projection consumes the privately owned prepared subject above.
    json::Array passes;
    passes.push_back("zkc-prepare-protocol");
    passes.push_back("zkc-project-protocol");
    if (options.simplify)
      passes.push_back("zkc-simplify-participant");
    if (options.fixPolynomialFactors)
      passes.push_back("zkc-fix-polynomial-factors");
    passes.push_back("zkc-eliminate-polynomials");
    passes.push_back("zkc-lower-math");
    passes.push_back("zkc-select-physical");
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
  if (!policy) {
    auto selected = selectNativeProofDraws(
        *original, std::get<NativeProofSelection>(options.policy).policy,
        options.fuseVectorReductions);
    if (!selected)
      return diagnostics.failure(selected.takeError());
    policy = std::move(*selected);
  }
  auto constructed =
      constructNativeProof(*original, *policy, options.fuseVectorReductions);
  if (!constructed)
    return diagnostics.failure(constructed.takeError());
  result->module = std::move(constructed->module);
  if (failed(lowerProgram(*result->module, options.simplify, false,
                          options.releaseStorage, result->statistics)) ||
      diagnostics.hasErrors())
    return diagnostics.failure();
  auto exported = protocol::exportModule(*result->module);
  if (!exported)
    return diagnostics.failure(exported.takeError());
  auto candidate = printJson(*exported);
  if (candidate.size() > program::artifactByteLimit)
    return diagnostics.failure(error("native-proof-candidate-limit"));
  auto root = *result->module->getOps<protocol_ir::ProtocolModuleOp>().begin();
  auto projection =
      *root.getBody().front().getOps<protocol_ir::ProjectionOp>().begin();
  auto interface = cast<DictionaryAttr>(projection.getInterfaces()[0]);
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
    auto participant =
        cast<protocol_ir::ParticipantOp>(SymbolTable::lookupSymbolIn(
            root, port.getAs<FlatSymbolRefAttr>("participant")));
    auto installed = participant->getAttrOfType<ArrayAttr>("service_ports");
    unsigned serviceIndex = 0;
    for (auto input : port.getAs<ArrayAttr>("service_inputs")) {
      auto originalInput = cast<IntegerAttr>(input).getInt();
      if (policy->service == originalInput)
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
      json::Array{options.simplify ? "true" : "false",
                  options.releaseStorage ? "true" : "false",
                  options.fuseVectorReductions ? "true" : "false"},
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
