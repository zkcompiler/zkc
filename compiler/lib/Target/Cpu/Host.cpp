#include "zkc/Compiler/Host.h"
#include "../../Compiler/CompilationState.h"
#include "../../Compiler/HostReferences.h"
#include "../../Compiler/LanguageInterface.h"
#include "../../Compiler/LanguagePackageReader.h"
#include "../../Compiler/NativeDeployment.h"
#include "../../Compiler/Run.h"
#include "../../Transforms/PreparedProtocol.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Compiler/LanguagePackage.h"
#include "zkc/Compiler/NativeLanguage.h"
#include "zkc/Compiler/Observation.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Names.h"
#include "zkc/Program/Admission.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Target/Cpu/Stages.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Transforms/Protocol.h"
#include "zkc/Transforms/Stages.h"
#include "zkc/Translation/Entry.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/TimeProfiler.h"
#include <map>
#include <set>
using namespace llvm;
namespace zkc::language {
namespace {
Expected<std::string> numerical(mlir::ModuleOp original, StringRef root,
                                const EntryOptions &options) {
  TimeTraceScope timing("zkc.lower-entry-calculation");
  zkc::detail::Diagnostics diagnostics(*original.getContext());
  diagnostics.atRoot(original.getLoc());
  auto *observations = options.observations;
  if (observations)
    observations->phase("protocol", original);
  mathematical::RealizationTrace trace;
  trace.eventLimit = 4096;
  auto preparation = mathematical::PreparedProtocol::prepare(
      original, options.mathematicalSelection, observations ? &trace : nullptr);
  if (observations)
    observations->decisions(original, trace);
  if (!preparation)
    return diagnostics.failure(
        error("entry.numeric", "numerical helper preparation failed"));
  auto prepared = std::move(*preparation).execute();
  if (!prepared)
    return diagnostics.failure(
        error("entry.numeric", "numerical execution preparation failed"));
  if (observations)
    observations->phase("execution", *prepared);
  mlir::PassManager pipeline(prepared->getContext());
  if (observations)
    observations->instrument(pipeline);
  PhysicalPipelineOptions physicalOptions;
  physicalOptions.releaseStorage = options.releaseStorage;
  physicalOptions.mathematics = options.mathematicalSelection;
  physicalOptions.cpuTarget = options.cpuTarget;
  buildPhysicalPipeline(pipeline, physicalOptions);
  auto outcome = pipeline.run(*prepared);
  if (mlir::failed(outcome) || diagnostics.hasErrors())
    return diagnostics.failure(
        error("entry.numeric", "numerical physical lowering failed"));
  if (observations)
    observations->phase("physical", *prepared);
  auto result = protocol::exportModule(*prepared);
  if (!result)
    return result.takeError();
  auto bytes = printJson(*result);
  auto checked = protocol::verifyProgramArtifact(*prepared, bytes);
  if (!checked)
    return checked.takeError();
  if (!checked->participants.empty() || !checked->entries.empty() ||
      none_of(checked->functions,
              [&](const auto &f) { return f.name == root; }))
    return error("entry.numeric", "numerical Program root differs");
  return bytes;
}
json::Array schemas(ArrayRef<Port> ports, Layouts &layouts, Error &failure) {
  json::Array out;
  for (const auto &p : ports) {
    auto layout = layouts.get(p.type);
    if (!layout) {
      failure = layout.takeError();
      return {};
    }
    out.push_back(encodeEntrySchema(**layout));
  }
  return out;
}
// Host pass-through values may never enter a numerical Program. Check their
// existing logical layouts here, including inactive and zero-length children.
class HostTargetCheck {
  Layouts &layouts;
  const target::CpuTarget &cpuTarget;
  std::set<const Layout *> visited;

  Error checkLayout(const Layout &layout) {
    if (!visited.insert(&layout).second)
      return Error::success();
    for (const auto &leaf : layout.leaves)
      if (const auto *data = leaf.data()) {
        auto logical = protocol::parseBoundType(*data, false);
        if (!logical)
          return logical.takeError();
        auto physical = protocol::defaultRepresentation(*logical);
        if (!physical)
          return physical.takeError();
        if (auto e = cpuTarget.checkType(*physical))
          return e;
      }
    for (const auto &field : layout.fields)
      if (auto e = checkLayout(*field.layout))
        return e;
    for (const auto &alternative : layout.alternatives)
      for (const auto &field : alternative.fields)
        if (auto e = checkLayout(*field.layout))
          return e;
    if (layout.type.kind == Type::Kind::Array && layout.fields.empty())
      return check(layout.type.arguments.front());
    return Error::success();
  }

public:
  HostTargetCheck(Layouts &layouts, const target::CpuTarget &cpuTarget)
      : layouts(layouts), cpuTarget(cpuTarget) {}
  Error check(const Type &type) {
    auto layout = layouts.get(type);
    if (!layout)
      return layout.takeError();
    return checkLayout(**layout);
  }
  Error check(const Body &body) {
    for (const auto &value : body.values)
      if (auto e = check(value.type))
        return e;
    for (const auto &operation : body.operations)
      if (const auto *control = std::get_if<LocalControl>(&operation.action))
        for (const auto &region : control->regions)
          if (auto e = check(*region))
            return e;
    return Error::success();
  }
};
} // namespace
Expected<CompiledHost> compileHost(const CheckedOriginal &original,
                                   const EntryOptions &options) {
  TimeTraceScope timing("zkc.compile-entry-host");
  const auto &entry = original.entry();
  const auto &limits = original.admissionLimits();
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry, mlir::MLIRContext::Threading::DISABLED);
  context.loadAllAvailableDialects();
  auto module =
      mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
  if (!module)
    return error("entry.original", "admitted Host original no longer parses");
  if (options.observations)
    options.observations->phase("entry", *module);
  auto analysis = analyzeHostOriginal(entry, *module, limits);
  if (!analysis)
    return analysis.takeError();
  json::Array calculations, deployments;
  Layouts layouts(entry, limits);
  HostTargetCheck targetCheck(layouts, options.cpuTarget);
  for (const auto &declaration : entry.declarations()) {
    if (declaration.kind != Declaration::Kind::EntryFunction ||
        !declaration.body || !declaration.parameters.empty())
      continue;
    for (const auto *ports : {&declaration.inputs, &declaration.outputs})
      for (const auto &port : *ports)
        if (auto e = targetCheck.check(port.type))
          return e;
    if (auto e = targetCheck.check(*declaration.body))
      return e;
  }
  Error failure = Error::success();
  for (const auto &fragment : analysis->calculations) {
    mlir::ModuleOp nested;
    for (auto child : module->getOps<mlir::ModuleOp>())
      if (child->getAttrOfType<mlir::StringAttr>("entry.calculation")
              .getValue() == fragment.id)
        nested = child;
    if (!nested)
      return error("entry.closure", "missing numerical original");
    auto copy = mlir::OwningOpRef<mlir::ModuleOp>(
        mlir::cast<mlir::ModuleOp>(nested->clone()));
    copy->getOperation()->removeAttr("entry.calculation");
    auto calculationScope = options.observations
                                ? options.observations->scope(fragment.id)
                                : CompilationObservation::Scope{};
    auto program = numerical(*copy, fragment.id, options);
    if (!program)
      return program.takeError();
    auto inputs = schemas(fragment.definition.inputs, layouts, failure);
    if (failure)
      return std::move(failure);
    auto outputs = schemas(fragment.definition.outputs, layouts, failure);
    if (failure)
      return std::move(failure);
    calculations.push_back(json::Object{{"id", fragment.id},
                                        {"parameters", std::move(inputs)},
                                        {"results", std::move(outputs)},
                                        {"function", fragment.id},
                                        {"program", std::move(*program)}});
  }
  std::map<std::string, std::pair<json::Array, json::Array>> required;
  for (const auto &f : analysis->functions)
    if (auto e = references(*f.getAsObject()->get("body"), required))
      return e;
  for (const auto &invocation : entry.invocations()) {
    auto operation = invocation.kind == HostInvocation::Kind::Run ? "run"
                     : invocation.kind == HostInvocation::Kind::Prove
                         ? "prove"
                         : "verify";
    const auto &target =
        entry.project().declarations()[invocation.target.index];
    auto id =
        entryDeploymentId(invocation.kind, target.symbol, invocation.arguments);
    auto signature = required.find(id);
    if (signature == required.end() || !invocation.deployment)
      return error("entry.closure", "child deployment reference differs");
    auto source = prepareOriginal(*invocation.deployment, limits);
    if (!source)
      return source.takeError();
    auto deploymentScope = options.observations
                               ? options.observations->scope(id)
                               : CompilationObservation::Scope{};
    auto compiled = compileEntry(*source, options);
    if (!compiled)
      return compiled.takeError();
    auto package = packageEntry(*compiled);
    if (!package)
      return package.takeError();
    deployments.push_back(
        json::Object{{"id", id},
                     {"operation", operation},
                     {"parameters", std::move(signature->second.first)},
                     {"results", std::move(signature->second.second)},
                     {"package", package->bytes().str()}});
    required.erase(signature);
  }
  if (!required.empty())
    return error("entry.closure", "missing child deployment");
  auto artifact =
      printJson(json::Object{{"format", "zkc.host/0"},
                             {"original", original.identity().str()},
                             {"entry", entry.root().symbol},
                             {"functions", std::move(analysis->functions)},
                             {"calculations", std::move(calculations)},
                             {"deployments", std::move(deployments)}});
  if (auto e = checkHostArtifact(artifact, original.interface(), limits))
    return std::move(e);
  return CompiledHost{std::move(artifact)};
}
} // namespace zkc::language
