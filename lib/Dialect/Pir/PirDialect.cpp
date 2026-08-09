//===- PirDialect.cpp - Protocol IR dialect ---------------------*- C++ -*-===//
#include "zkc/Dialect/Pir/PirDialect.h"

#include "mlir/Bytecode/BytecodeImplementation.h"
#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Dialect/Pir/PirTypes.h"

#include "zkc/Dialect/Pir/PirOpsDialect.cpp.inc"

namespace {

/// In-memory form of the version blob bytecode artifacts carry for this
/// dialect. 0.0 is the pre-release carrier described in docs/spec/carrier.md
/// §9; any other blob is refused rather than upgraded — decoding a different
/// layout as the current semantic carrier would be a fail-open interpretation,
/// not compatibility.
struct PirDialectVersion : public mlir::DialectVersion {
  uint64_t major = 0;
  uint64_t minor = 0;
};

/// Versioned bytecode support (carrier.md §9): every artifact records
/// the dialect version it was written under, and reading fails closed
/// on any version this build does not know — including future ones.
/// Types and attributes keep the default textual encodings — custom
/// encodings can land later without affecting protocol identity, which
/// never derives from carrier bytes.
struct PirBytecodeInterface : public mlir::BytecodeDialectInterface {
  using BytecodeDialectInterface::BytecodeDialectInterface;

  void writeVersion(mlir::DialectBytecodeWriter &writer) const override {
    // Derived from the version struct's default: the shipped
    // version has exactly one spelling.
    writer.writeVarInt(PirDialectVersion().major);
    writer.writeVarInt(0); // minor
  }

  std::unique_ptr<mlir::DialectVersion>
  readVersion(mlir::DialectBytecodeReader &reader) const override {
    auto version = std::make_unique<PirDialectVersion>();
    if (failed(reader.readVarInt(version->major)) ||
        failed(reader.readVarInt(version->minor)))
      return nullptr;
    const PirDialectVersion current;
    if (version->major != current.major || version->minor != current.minor) {
      reader.emitError() << "unsupported pir dialect version " << version->major
                         << "." << version->minor;
      return nullptr;
    }
    return version;
  }
};

} // namespace

void zkc::pir::PirDialect::initialize() {
  registerTypes();
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Pir/PirOps.cpp.inc"
      >();
  addInterfaces<PirBytecodeInterface>();
}
