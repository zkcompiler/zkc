#ifndef ZKC_LIB_COMPILER_APPLICATIONMAPDATA_H
#define ZKC_LIB_COMPILER_APPLICATIONMAPDATA_H

#include "mlir/IR/BuiltinOps.h"
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
// These records decode the already-admitted structured view. Types and
// descriptors remain complete structured data; no printed type or SSA spelling
// participates in matching. This layer contains no expansion or map algorithm.
struct Block;
struct Instruction {
  llvm::json::Value descriptor = nullptr;
  std::vector<unsigned> operands;
  std::vector<llvm::json::Value> results;
  std::vector<Block> regions;
  std::string site;
};
struct Block {
  std::vector<llvm::json::Value> inputs, outputs;
  std::vector<Instruction> instructions;
  llvm::json::Value terminator = nullptr;
  std::vector<unsigned> returned;
};
struct Definition {
  std::string name, kind;
  llvm::json::Value declaration = nullptr;
  std::vector<std::string> roles;
  std::vector<std::vector<std::string>> inputRoles, outputRoles;
  std::vector<bool> restrictInputs, restrictOutputs;
  bool hasBody = false;
  Block body;
};
struct View {
  llvm::json::Value wire = nullptr;
  mlir::OwningOpRef<mlir::ModuleOp> native;
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
llvm::StringRef callee(const Instruction &instruction);
} // namespace zkc::protocol::application_map
#endif
