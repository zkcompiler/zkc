#ifndef ZKC_LIB_COMPILER_APPLICATIONMAPDATA_H
#define ZKC_LIB_COMPILER_APPLICATIONMAPDATA_H

#include "SourceView.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Support/Json.h"
#include <deque>
#include <map>
#include <vector>

namespace zkc::protocol::application_map {
using Path = std::vector<unsigned>;
constexpr size_t byteLimit = 32 * 1024 * 1024;
constexpr unsigned rowLimit = 100000;
struct Budget {
  size_t remaining = 1000000;
  bool charge(size_t amount = 1) {
    if (amount > remaining)
      return false;
    remaining -= amount;
    return true;
  }
};
// Analysis coordinates reference the actual admitted MLIR, never a decoded
// structured-source program. This layer contains no expansion algorithm.
using Instruction = SourceInstruction;
using Block = SourceBlock;
using Roles = std::map<std::string, std::string>;
struct Definition : SourceDefinition {
  std::vector<bool> restrictInputs, restrictOutputs;
};
struct View {
  mlir::OwningOpRef<mlir::ModuleOp> native;
  std::string identity, entry;
  std::vector<Definition> definitions;
  std::map<std::string, unsigned> names;
  const Definition *find(llvm::StringRef name) const;
};
struct Value {
  std::string definition;
  Path region;
  bool argument = true;
  unsigned instruction = 0, port = 0;
};
using ValueContext = std::deque<Value>;
llvm::Expected<View> readView(llvm::StringRef bytes, llvm::StringRef entry,
                              mlir::MLIRContext &context, Budget &budget,
                              StructuredSourceProfile profile);
llvm::Error compareNative(View &source, View &candidate);
llvm::Error compareInventory(const View &source, const View &candidate);
llvm::Error chargeTree(const llvm::json::Value &value, Budget &budget);
llvm::Expected<llvm::json::Value> parseRecord(llvm::StringRef bytes);
// Implemented by the independent reader, also used to reject an invalid
// proposal before returning it. It never calls the producer.
llvm::Error checkRecord(View &source, View &candidate,
                        const llvm::json::Value &record, Budget &budget);
llvm::json::Array encodePath(llvm::ArrayRef<unsigned> path);
llvm::json::Value encodeValue(const Value &value);
Path instructionPath(const Path &region, unsigned instruction);
Path regionPath(const Path &region, unsigned instruction, unsigned nested);
ValueContext arguments(llvm::StringRef definition, const Path &region,
                       unsigned count);
void prependResults(ValueContext &context, llvm::StringRef definition,
                    const Path &region, unsigned instruction, unsigned count);
llvm::StringRef opcode(const Instruction &instruction);
bool sameDescriptor(const Instruction &, const Instruction &,
                    const Roles &roles = {});
mlir::ArrayAttr applicationRoles(const Instruction &);
llvm::Error chargeTypes(llvm::ArrayRef<mlir::Type>, Budget &);
llvm::Error chargeInstruction(const Instruction &, Budget &);
llvm::StringRef callee(const Instruction &instruction);
} // namespace zkc::protocol::application_map
#endif
