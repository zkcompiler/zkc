#include "Driver.h"
#include "../Support/Input.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Claims/Claims.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Support/MLIRInput.h"
#include "zkc/Target/Json.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
namespace zkc::claims {
namespace {
Expected<source::Document> document(StringRef path) {
  auto text = readInput(path, sourceByteLimit);
  if (!text)
    return text.takeError();
  return frontend::parseProtocolDocument(*text, path);
}
Expected<json::Value> jsonFile(StringRef path) {
  auto text = readInput(path, sourceByteLimit);
  if (!text)
    return text.takeError();
  return parseJson(*text);
}
} // namespace
int runCommand(int argc, char **argv, const mlir::DialectRegistry &registry) {
  auto fail = [](Error e) {
    errs() << toString(std::move(e)) << '\n';
    return 1;
  };
  StringRef mode(argv[1]);
  bool inspection = mode == "claim-inspect";
  bool derivation = mode == "claim-derive";
  bool lowering = mode == "claim-check-lowering";
  bool construction = mode == "claim-check-construction" || lowering;
  if (!(inspection || derivation || construction || mode == "claim-check" ||
        mode == "claim-import" || mode == "claim-check-ir") ||
      (lowering ? argc < 8 || argc > 11
                : argc != (inspection || derivation ? 4
                           : construction           ? 7
                                                    : 5)))
    return fail(error("unsupported-option"));
  protocol::PhysicalOptions options;
  StringRef implementationPath;
  for (int i = 8; lowering && i < argc; ++i) {
    StringRef option(argv[i]);
    if (option == "--linear-contractions") {
      if (options.linearContractions)
        return fail(error("duplicate-option"));
      options.linearContractions = true;
    } else if (option == "--release-storage") {
      if (options.releaseStorage)
        return fail(error("duplicate-option"));
      options.releaseStorage = true;
    } else if (option.consume_front("--implementations=")) {
      if (option.empty() || !implementationPath.empty())
        return fail(error("binding-selection-option"));
      implementationPath = option;
    } else
      return fail(error("unsupported-option"));
  }
  if (!implementationPath.empty()) {
    auto value = jsonFile(implementationPath);
    if (!value)
      return fail(value.takeError());
    auto selection = protocol::decodeImplementationSelection(*value);
    if (!selection)
      return fail(selection.takeError());
    options.implementations = std::move(*selection);
  }
  auto source = document(argv[2]);
  if (!source)
    return fail(source.takeError());
  if (!source->module())
    return fail(error("claim-source"));
  if (inspection) {
    auto report = inspect(*source->module(), argv[3]);
    if (!report)
      return fail(report.takeError());
    outs() << *report << '\n'; // Reports, unlike contracts, use object JSON.
    return 0;
  }
  auto encoded = jsonFile(argv[3]);
  if (!encoded)
    return fail(encoded.takeError());
  auto contract = decodeContract(*encoded);
  if (!contract)
    return fail(contract.takeError());
  if (derivation) {
    auto result = derive(*source->module(), *contract);
    if (!result)
      return fail(result.takeError());
    outs() << printJson(encode(*result)) << '\n';
    return 0;
  }
  mlir::MLIRContext ctx(registry);
  ctx.loadAllAvailableDialects();
  if (mode == "claim-check-ir") {
    auto text = readInput(argv[4], mlirByteLimit);
    if (!text)
      return fail(text.takeError());
    if (!mlirNestingWithinLimit(*text))
      return fail(error("claim-ir-depth-limit"));
    auto candidate = mlir::parseSourceString<mlir::ModuleOp>(*text, &ctx);
    if (!candidate)
      return fail(error("claim-ir"));
    if (auto e = checkIR(*source->module(), *contract, *candidate))
      return fail(std::move(e));
  } else {
    auto encodedCandidate = jsonFile(argv[4]);
    if (!encodedCandidate)
      return fail(encodedCandidate.takeError());
    auto candidate = decodeCertificate(*encodedCandidate);
    if (!candidate)
      return fail(candidate.takeError());
    if (mode == "claim-import") {
      auto result = import(*source->module(), *contract, *candidate, ctx);
      if (!result)
        return fail(result.takeError());
      (*result)->print(outs());
      outs() << '\n';
      return 0;
    }
    if (construction) {
      auto descriptor = document(argv[5]);
      if (!descriptor)
        return fail(descriptor.takeError());
      if (!descriptor->construction())
        return fail(error("claim-construction-binding"));
      auto artifact = jsonFile(argv[6]);
      if (!artifact)
        return fail(artifact.takeError());
      if (lowering) {
        auto physical = jsonFile(argv[7]);
        if (!physical)
          return fail(physical.takeError());
        if (auto e = checkLowering(*source->module(), *contract, *candidate,
                                   *descriptor->construction(), *artifact,
                                   *physical, ctx, options))
          return fail(std::move(e));
      } else if (auto e = checkConstruction(
                     *source->module(), *contract, *candidate,
                     *descriptor->construction(), *artifact, ctx))
        return fail(std::move(e));
    } else if (auto e = check(*source->module(), *contract, *candidate)) {
      return fail(std::move(e));
    }
  }
  outs() << "checked conditional claim closure; " << contract->laws.size()
         << " caller trust premises; no cryptographic security theorem\n";
  return 0;
}
} // namespace zkc::claims
