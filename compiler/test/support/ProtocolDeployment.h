#ifndef ZKC_TEST_SUPPORT_PROTOCOL_DEPLOYMENT_H
#define ZKC_TEST_SUPPORT_PROTOCOL_DEPLOYMENT_H

#include "zkc/Language/Project.h"
#include "llvm/Support/Error.h"

namespace zkc::test {
/// Native joint tests can close a protocol directly, including affine outputs
/// that deliberately cannot cross an ordinary source Host-function boundary.
inline llvm::Expected<language::ClosedEntry>
closeNativeRun(const language::CheckedProject &project,
               llvm::StringRef protocol, const language::Limits &limits = {},
               std::vector<language::Type> arguments = {}) {
  for (const auto &declaration : project.declarations())
    if (declaration.qualifiedName == protocol &&
        declaration.kind == language::Declaration::Kind::Protocol)
      return language::closeInvocation(project,
                                       {language::HostInvocation::Kind::Run,
                                        declaration.id,
                                        std::move(arguments),
                                        {}},
                                       limits);
  return llvm::createStringError("test.protocol-deployment: missing protocol");
}

/// Select the native deployment whose original/projection these tests inspect.
/// Proof declarations already own a deployment. A source wrapper must close to
/// exactly one Run invocation; its Host function is tested separately.
inline llvm::Expected<language::ClosedEntry>
closeProtocolDeployment(const language::CheckedProject &project,
                        llvm::StringRef name,
                        const language::Limits &limits = {},
                        std::optional<language::EntryKind> kind = {}) {
  auto selected = language::closeEntry(project, name, limits, kind);
  if (!selected)
    return selected.takeError();
  if (selected->entry().kind != language::Declaration::Kind::EntryFunction)
    return std::move(*selected);
  auto invocations = selected->invocations();
  if (invocations.size() != 1 ||
      invocations.front().kind != language::HostInvocation::Kind::Run ||
      !invocations.front().deployment)
    return llvm::createStringError(
        "test.protocol-deployment: expected exactly one closed Run invocation");
  return *invocations.front().deployment;
}
} // namespace zkc::test
#endif
