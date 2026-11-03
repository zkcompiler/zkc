#include "zkc/Program/Admission.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include <cstring>
// Without arguments, decode, admit and re-encode the program on standard
// input, or print the refusal and fail. With --report, print one normalized
// result instead: ["admitted", program, static instructions, descriptor
// charge] or ["refused", class, code].
int main(int argc, char **argv) {
  bool report = argc == 2 && std::strcmp(argv[1], "--report") == 0;
  if (argc != 1 && !report)
    return 2;
  auto input = llvm::MemoryBuffer::getSTDIN();
  if (!input)
    return 2;
  auto refused = [&](llvm::Error error) {
    if (!report) {
      llvm::errs() << llvm::toString(std::move(error));
      return 1;
    }
    llvm::json::Array result{"refused", "unclassified", ""};
    llvm::handleAllErrors(
        std::move(error),
        [&](const zkc::program::ProgramRefusal &refusal) {
          result = llvm::json::Array{
              "refused", zkc::program::refusalClassName(refusal.kind),
              refusal.code};
        },
        [&](const zkc::Refusal &refusal) { result[2] = refusal.code; });
    llvm::outs() << zkc::printJson(std::move(result)) << "\n";
    return 0;
  };
  auto program = zkc::program::parse((*input)->getBuffer());
  if (!program)
    return refused(program.takeError());
  zkc::protocol::AdmissionReport measures;
  if (auto error = zkc::protocol::admit(*program, &measures))
    return refused(std::move(error));
  auto encoded = zkc::program::encode(*program);
  if (!report) {
    llvm::outs() << zkc::printJson(encoded);
    return 0;
  }
  llvm::outs() << zkc::printJson(
                      llvm::json::Array{"admitted", std::move(encoded),
                                        int64_t(measures.staticInstructions),
                                        int64_t(measures.descriptorCharge)})
               << "\n";
  return 0;
}
