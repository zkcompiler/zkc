#include "ArtifactJson.h"
#include "NativeDeployment.h"
#include "Run.h"
#include "zkc/Program/Admission.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/LogicalTree.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
using namespace llvm;
namespace zkc::detail {
namespace {
std::string digest(StringRef bytes) {
  return toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
}
} // namespace
Error checkCpuOperationArtifact(StringRef bytes, StringRef original,
                                StringRef role) {
  auto artifact = parseJson(bytes, 16 * 1024 * 1024);
  if (!artifact)
    return artifact.takeError();
  auto *deployment = artifact->getAsArray();
  if (!deployment || deployment->size() != 9 ||
      (*deployment)[0].getAsString() != "zkc.native-proof/0" ||
      (*deployment)[1].getAsString() != original ||
      !(*deployment)[4].getAsString() || !(*deployment)[6].getAsArray() ||
      (*deployment)[6].getAsArray()->size() != 1)
    return error("entry.deployment",
                 "invalid operation-specific native proof deployment");
  auto descriptor = encodeLogicalTree((*deployment)[2]);
  if (!descriptor)
    return descriptor.takeError();
  auto candidate = *(*deployment)[4].getAsString();
  if ((*deployment)[3].getAsString() != digest(*descriptor) ||
      (*deployment)[5].getAsString() != digest(candidate))
    return error("entry.deployment",
                 "child native deployment identities differ");
  auto program = program::parse(candidate);
  if (!program)
    return program.takeError();
  if (auto e = protocol::admit(*program))
    return e;
  if (program->participants.size() != 1 || program->entries.size() != 1 ||
      program->participants.front().role != role)
    return error("entry.closure",
                 "proof child retained the wrong operation closure");
  auto *map = (*(*deployment)[6].getAsArray())[0].getAsArray();
  if (!map || map->size() != 6 || (*map)[0].getAsString() != role ||
      (*map)[1].getAsString() != program->participants.front().name)
    return error("entry.signature", "proof child port map differs");
  return Error::success();
}
Expected<program::Participants> readRunProgram(StringRef bytes) {
  auto artifact = parseNaturalJson(bytes, 16 * 1024 * 1024, 256,
                                   "entry.deployment", "source.limit");
  if (!artifact)
    return artifact.takeError();
  auto *bundle = artifact->getAsObject();
  if (!bundle || bundle->size() != 5 ||
      bundle->getString("format") != "zkc.run/0" ||
      !bundle->getString("candidate"))
    return error("entry.deployment", "invalid child joint deployment");
  auto program = program::parse(*bundle->getString("candidate"));
  if (!program)
    return program.takeError();
  if (auto e = protocol::admit(*program))
    return e;
  return std::move(*program);
}
} // namespace zkc::detail
