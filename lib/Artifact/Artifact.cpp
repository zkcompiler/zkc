//===- Artifact.cpp - Sealed artifact write and fail-closed load -*- C++
//-*-===//
#include "ArtifactInternal.h"

#include "mlir/Bytecode/BytecodeReader.h"
#include "mlir/Bytecode/BytecodeWriter.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Artifact/SealedGuard.h"
#include "zkc/Encoding/CanonicalEncoder.h"
#include "zkc/Registry/ProtocolEnvironment.h"
#include "zkc/Semantics/SealEngine.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"

using namespace mlir;
using namespace zkc;

struct artifact::DecodedPirArtifact::Storage {
  std::shared_ptr<MLIRContext> context;
  OwningOpRef<pir::SealedOp> sealed;
  std::string id;
};

struct artifact::AdmittedPirArtifact::Storage {
  Storage(DecodedPirArtifact decoded, registry::ProtocolEnvironment environment)
      : decoded(std::move(decoded)), environment(std::move(environment)) {}

  DecodedPirArtifact decoded;
  registry::ProtocolEnvironment environment;
};

namespace {

struct DecodedParts {
  std::shared_ptr<MLIRContext> context;
  OwningOpRef<pir::SealedOp> sealed;
  std::string id;
};

} // namespace

std::string artifact::producerString() { return "zkc_v" ZKC_VERSION_STRING; }

LogicalResult artifact::writeArtifact(pir::SealedOp sealed,
                                      llvm::raw_ostream &os) {
  llvm::Expected<std::string> recomputed = encoding::computeId(sealed);
  if (!recomputed) {
    sealed.emitOpError()
        << "[zkc-E803] artifact identity cannot be recomputed before write: "
        << llvm::toString(recomputed.takeError());
    return failure();
  }
  if (*recomputed != sealed.getId()) {
    sealed.emitOpError() << "[zkc-E801] artifact id mismatch before write: "
                         << "stored " << sealed.getId() << ", recomputed "
                         << *recomputed;
    return failure();
  }

  BytecodeWriterConfig config(producerString());
  return writeBytecodeToFile(sealed, os, config);
}

/// Reads the producer string out of the bytecode header without
/// involving a context: magic number, bytecode-version varint, then the
/// NUL-terminated producer — the layout the upstream writer emits.
static llvm::Expected<llvm::StringRef>
readProducer(llvm::MemoryBufferRef buffer) {
  if (!isBytecode(buffer))
    return llvm::createStringError(
        "[zkc-E803] malformed artifact: not MLIR bytecode");
  llvm::StringRef bytes = buffer.getBuffer().drop_front(4);
  if (bytes.empty())
    return llvm::createStringError(
        "[zkc-E803] malformed artifact: truncated header");
  // Prefix varint: the count of trailing zero bits in the first byte is
  // the count of additional bytes (an all-zero byte means eight more).
  uint8_t first = static_cast<uint8_t>(bytes.front());
  unsigned extraBytes = first == 0 ? 8 : llvm::countr_zero(first);
  if (bytes.size() <= 1 + extraBytes)
    return llvm::createStringError(
        "[zkc-E803] malformed artifact: truncated header");
  bytes = bytes.drop_front(1 + extraBytes);
  size_t nul = bytes.find('\0');
  if (nul == llvm::StringRef::npos)
    return llvm::createStringError(
        "[zkc-E803] malformed artifact: unterminated producer string");
  return bytes.take_front(nul);
}

/// The producer marker is error locality, not a compatibility contract:
/// identity recheck is the real gate, and at v0 nothing negotiates
/// versions. The marker names a stale or foreign artifact clearly — the
/// release number between the two anchors carries no acceptance meaning.
static bool isCurrentEncoderProducer(llvm::StringRef producer) {
  return producer.starts_with("zkc_v");
}

static llvm::Expected<DecodedParts> decodeArtifact(llvm::MemoryBufferRef ref,
                                                   llvm::StringRef expectedId) {
  llvm::Expected<llvm::StringRef> producer = readProducer(ref);
  if (!producer)
    return producer.takeError();
  if (!isCurrentEncoderProducer(*producer))
    return llvm::createStringError("[zkc-E802] producer/version rejected: '" +
                                   *producer +
                                   "' (a zkc artifact's producer marker "
                                   "begins with zkc_v)");

  DecodedParts result;
  result.context =
      std::make_shared<MLIRContext>(MLIRContext::Threading::DISABLED);
  result.context->loadDialect<pir::PirDialect>();
  installSealedGuard(*result.context);

  // The loader is a library; collect diagnostics into the returned
  // error instead of assuming the caller installed a handler.
  std::string detail;
  ScopedDiagnosticHandler handler(result.context.get(),
                                  [&](Diagnostic &diagnostic) {
                                    if (!detail.empty())
                                      detail += "; ";
                                    detail += diagnostic.str();
                                    return success();
                                  });

  ParserConfig config(result.context.get());
  Block block;
  BytecodeReader reader(ref, config, /*lazyLoad=*/false);
  if (failed(reader.readTopLevel(&block)) || failed(reader.finalize()))
    return llvm::createStringError("[zkc-E803] malformed artifact: " + detail);
  if (block.getOperations().size() != 1 || !isa<pir::SealedOp>(block.front()))
    return llvm::createStringError(
        "[zkc-E803] malformed artifact: expected exactly one pir.sealed");
  auto sealed = cast<pir::SealedOp>(block.front());
  if (failed(verify(sealed)))
    return llvm::createStringError("[zkc-E803] malformed artifact: " + detail);

  llvm::Expected<std::string> recomputed = encoding::computeId(sealed);
  if (!recomputed)
    return llvm::createStringError("[zkc-E803] malformed artifact: " +
                                   llvm::toString(recomputed.takeError()));
  if (*recomputed != sealed.getId())
    return llvm::createStringError("[zkc-E801] artifact id mismatch: stored " +
                                   sealed.getId() + ", recomputed " +
                                   *recomputed);
  if (!expectedId.empty() && expectedId != *recomputed)
    return llvm::createStringError(
        "[zkc-E801] artifact id mismatch: requested " + expectedId +
        ", recomputed " + *recomputed);

  sealed->remove();
  result.sealed = OwningOpRef<pir::SealedOp>(sealed);
  result.id = std::move(*recomputed);
  return std::move(result);
}

llvm::StringRef artifact::DecodedPirArtifact::id() const {
  return storage_->id;
}

void artifact::DecodedPirArtifact::print(llvm::raw_ostream &os) const {
  (*storage_->sealed).print(os);
}

llvm::StringRef artifact::AdmittedPirArtifact::id() const {
  return storage_->decoded.id();
}

const registry::ProtocolEnvironment &
artifact::AdmittedPirArtifact::environment() const {
  return storage_->environment;
}

pir::SealedOp artifact::detail::MutablePirArtifact::sealed() const {
  auto sealed = (*module_).getOps<pir::SealedOp>();
  assert(llvm::hasSingleElement(sealed) &&
         "mutable PIR clone lost its sealed root");
  return *sealed.begin();
}

llvm::Expected<artifact::DecodedPirArtifact>
artifact::loadArtifact(llvm::StringRef path, llvm::StringRef expectedId) {
  llvm::ErrorOr<std::unique_ptr<llvm::MemoryBuffer>> buffer =
      llvm::MemoryBuffer::getFile(path);
  if (!buffer)
    return llvm::createStringError(buffer.getError(),
                                   "[zkc-E803] cannot read artifact '%s'",
                                   path.str().c_str());

  auto decoded = decodeArtifact((*buffer)->getMemBufferRef(), expectedId);
  if (!decoded)
    return decoded.takeError();
  auto storage = std::make_shared<DecodedPirArtifact::Storage>();
  storage->context = std::move(decoded->context);
  storage->sealed = std::move(decoded->sealed);
  storage->id = std::move(decoded->id);
  return DecodedPirArtifact(std::move(storage));
}

llvm::Expected<artifact::DecodedPirArtifact>
artifact::snapshotArtifact(pir::SealedOp sealed) {
  llvm::SmallVector<char> bytes;
  llvm::raw_svector_ostream stream(bytes);
  if (failed(writeArtifact(sealed, stream)))
    return llvm::createStringError(
        "cannot snapshot an invalid pir.sealed artifact");

  llvm::MemoryBufferRef buffer(llvm::StringRef(bytes.data(), bytes.size()),
                               "<pir-artifact-snapshot>");
  auto decoded = decodeArtifact(buffer, /*expectedId=*/{});
  if (!decoded)
    return decoded.takeError();
  auto storage = std::make_shared<DecodedPirArtifact::Storage>();
  storage->context = std::move(decoded->context);
  storage->sealed = std::move(decoded->sealed);
  storage->id = std::move(decoded->id);
  return DecodedPirArtifact(std::move(storage));
}

llvm::Expected<artifact::AdmittedPirArtifact>
artifact::admitArtifact(DecodedPirArtifact decoded,
                        registry::ProtocolEnvironment environment) {
  std::string detail;
  ScopedDiagnosticHandler handler(decoded.storage_->context.get(),
                                  [&](Diagnostic &diagnostic) {
                                    if (!detail.empty())
                                      detail += "; ";
                                    detail += diagnostic.str();
                                    return success();
                                  });
  if (failed(semantics::SealEngine(environment)
                 .recheck(*decoded.storage_->sealed))) {
    if (detail.empty())
      detail = "registry-backed seal judgment failed";
    return llvm::createStringError("artifact admission refused: " + detail);
  }
  auto storage = std::make_shared<AdmittedPirArtifact::Storage>(
      std::move(decoded), std::move(environment));
  return AdmittedPirArtifact(std::move(storage));
}

llvm::Expected<artifact::AdmittedPirArtifact>
artifact::loadAndAdmitArtifact(llvm::StringRef path,
                               registry::ProtocolEnvironment environment,
                               llvm::StringRef expectedId) {
  auto decoded = loadArtifact(path, expectedId);
  if (!decoded)
    return decoded.takeError();
  return admitArtifact(std::move(*decoded), std::move(environment));
}

artifact::detail::MutablePirArtifact
artifact::detail::ArtifactAccess::cloneForReopen(
    const AdmittedPirArtifact &artifact) {
  const DecodedPirArtifact &decoded = artifact.storage_->decoded;
  auto module = OwningOpRef<ModuleOp>(
      ModuleOp::create(UnknownLoc::get(decoded.storage_->context.get())));
  module->getBody()->push_back((*decoded.storage_->sealed)->clone());
  return MutablePirArtifact(decoded.storage_->context, std::move(module));
}
