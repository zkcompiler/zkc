//===- OirDialect.cpp - Operator-layer dialect ------------------*- C++ -*-===//
#include "zkc/Dialect/Oir/OirDialect.h"

#include "mlir/Bytecode/BytecodeImplementation.h"
#include "zkc/Dialect/Oir/OirOps.h"

#include "zkc/Dialect/Oir/OirOpsDialect.cpp.inc"

namespace {

/// In-memory form of the version blob bytecode artifacts carry for this
/// dialect (carrier.md §9). Endpoint artifacts are not persisted as
/// bytecode yet; the blob exists from the first version so that no
/// blob-less corpus can accumulate — an unversioned artifact is the one
/// thing an upgrade hook can never repair.
struct OirDialectVersion : public mlir::DialectVersion {
  uint64_t major = 0;
  uint64_t minor = 0;
};

struct OirBytecodeInterface : public mlir::BytecodeDialectInterface {
  using BytecodeDialectInterface::BytecodeDialectInterface;

  void writeVersion(mlir::DialectBytecodeWriter &writer) const override {
    // Derived from the version struct's default: the shipped
    // version has exactly one spelling.
    writer.writeVarInt(OirDialectVersion().major);
    writer.writeVarInt(0); // minor
  }

  std::unique_ptr<mlir::DialectVersion>
  readVersion(mlir::DialectBytecodeReader &reader) const override {
    auto version = std::make_unique<OirDialectVersion>();
    if (failed(reader.readVarInt(version->major)) ||
        failed(reader.readVarInt(version->minor)))
      return nullptr;
    const OirDialectVersion current;
    if (version->major != current.major || version->minor != current.minor) {
      reader.emitError() << "unsupported oir dialect version " << version->major
                         << "." << version->minor;
      return nullptr;
    }
    return version;
  }
};

} // namespace

void zkc::oir::OirDialect::initialize() {
  addOperations<
#define GET_OP_LIST
#include "zkc/Dialect/Oir/OirOps.cpp.inc"
      >();
  registerTypes();
  addInterfaces<OirBytecodeInterface>();
}
