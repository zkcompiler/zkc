#include "zkc/Target/Evm/Transcript.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Instances.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Support/Refusal.h"

using namespace llvm;
namespace zkc::evm {
Expected<TranscriptRealization> realizeTranscript(NativeLayouts &layouts,
                                                  mlir::MLIRContext &context,
                                                  StringRef suite) {
  const auto *row = protocol::instances::domain(suite);
  if (!row || !row->transcript)
    return zkc::error("evm.construction",
                      "transcript suite is not an installed transcript");
  const auto &facts = *row->transcript;
  if (facts.family != "hash-chain" || facts.hash != "keccak256")
    return zkc::error("evm.construction",
                      "EVM realizes only the keccak256 hash-chain transcript "
                      "family, not " +
                          facts.family);
  if (!facts.bindsSuite)
    return zkc::error("evm.construction",
                      "EVM transcript initialization binds the suite identity");
  if (facts.decoder != "fr64be" && facts.decoder != "rejection31le")
    return zkc::error("evm.construction", "EVM has no realization of the " +
                                              facts.decoder +
                                              " challenge decoder");
  auto field = protocol::installedDomains().associatedIdentity(
      row->identity, "ChallengeField");
  if (field.empty())
    return zkc::error("evm.construction",
                      "transcript suite has no challenge field");
  auto challenge =
      layouts.field(algebra::FieldType::get(&context, StringRef(field)));
  if (!challenge)
    return challenge.takeError();
  bool rejection = facts.decoder == "rejection31le";
  if (!rejection && (*challenge)->degree != 1)
    return zkc::error("evm.construction",
                      "the fr64be decoder requires a prime challenge field");
  if (rejection && ((*challenge)->degree < 2 ||
                    (*challenge)->modulus.uge(uint64_t(1) << 31)))
    return zkc::error("evm.construction",
                      "the rejection31le decoder requires an ascending "
                      "extension over a prime below 2^31");
  const auto &catalog = protocol::installedDomains();
  return TranscriptRealization{
      row->identity, *challenge,
      rejection ? TranscriptRealization::Decoder::Rejection31Le
                : TranscriptRealization::Decoder::Fr64Be,
      catalog.hasFact("IndexTranscript", {row->identity}),
      catalog.hasFact("IndexBlockTranscript", {row->identity})};
}

bool realizedChallengeField(NativeLayouts &layouts, mlir::MLIRContext &context,
                            StringRef field) {
  for (const auto &row : protocol::instances::domains()) {
    if (!row.transcript)
      continue;
    auto realized = realizeTranscript(layouts, context, row.identity);
    if (!realized) {
      consumeError(realized.takeError());
      continue;
    }
    if (realized->challenge->type.getDomain() == field)
      return true;
  }
  return false;
}
} // namespace zkc::evm
