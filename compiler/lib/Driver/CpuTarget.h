#ifndef ZKC_DRIVER_CPU_TARGET_H
#define ZKC_DRIVER_CPU_TARGET_H
#include "../Support/Input.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Target/CpuTarget.h"

namespace zkc {
inline llvm::Expected<target::CpuTarget> readCpuTarget(llvm::StringRef path) {
  if (path.empty() || path.size() > 4096)
    return error("cpu-target-invalid");
  auto text = readInput(path, target::CpuTarget::descriptorByteLimit);
  if (!text)
    return llvm::handleErrors(
        text.takeError(), [](const Refusal &refusal) -> llvm::Error {
          return error(refusal.code == "byte-limit" ? "cpu-target-limit"
                                                    : refusal.code,
                       refusal.detail);
        });
  return target::CpuTarget::parse(*text);
}
} // namespace zkc
#endif
