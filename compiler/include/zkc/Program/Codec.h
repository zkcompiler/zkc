#ifndef ZKC_PROGRAM_CODEC_H
#define ZKC_PROGRAM_CODEC_H
#include "zkc/Program/Model.h"
#include "zkc/Support/Refusal.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"
namespace zkc::program {
/// The carrier bounds of docs/spec/formats/program-bytes.md. Every bound is
/// inclusive: a quantity equal to it is admitted and one more is refused.
/// Readers check a count before decoding or allocating the counted elements;
/// producers check the same bounds before emission.
///
/// Raw input bytes, and separately the compact encoding a producer writes.
inline constexpr size_t artifactByteLimit = 4 * 1024 * 1024;
/// Arrays, strings and Boolean literals of the whole input.
inline constexpr size_t artifactNodeLimit = 400000;
/// Arrays on one path through the input; the root array is level 1.
inline constexpr size_t jsonDepthLimit = 64;
/// Elements of any one array.
inline constexpr size_t arrayElementLimit = 32768;
/// Decoded bytes of one string other than an operation attribute, including
/// type spellings, contract identities and static arguments.
inline constexpr size_t stringByteLimit = 4096;
/// Decoded bytes of one operation attribute.
inline constexpr size_t parameterByteLimit = 16384;
/// Names and sites.
inline constexpr size_t identifierByteLimit = 128;
inline constexpr size_t bindingLimit = 4096;
/// Static arguments and, separately, physical arguments of one binding.
inline constexpr size_t bindingArgumentLimit = 128;
/// Assignments of one function origin.
inline constexpr size_t originAssignmentLimit = 128;
/// Functions plus participants.
inline constexpr size_t definitionLimit = 4096;
inline constexpr size_t entryLimit = 4096;
/// Entries of every name and row list: ports, results, service ports, capture
/// lists and rows, carried rows, outputs, operation, call and query inputs and
/// outputs, variant payload values, match payload bindings, release, yield
/// and return values, `return_if` values and continuations, and entry role
/// maps. A `for_while` yield counts its condition.
inline constexpr size_t listEntryLimit = 1024;
/// Inputs plus service ports of one participant.
inline constexpr size_t participantInterfaceLimit = 1024;
/// Attributes of one operation.
inline constexpr size_t attributeLimit = 16384;
/// Instruction records across all bodies of a program.
inline constexpr size_t staticInstructionLimit = 65536;
/// Bodies nested below a definition body, which is level 0.
inline constexpr size_t bodyNestingLimit = 64;
/// A `match` has one arm per alternative of a variant whose type the program
/// spells within `stringByteLimit`, so it has at most 64 arms.
inline constexpr size_t matchAlternativeLimit = 64;
/// The static maximum of a participant loop count.
inline constexpr uint64_t loopMaximumLimit = 1048576;
/// Cumulative descriptor charge units of one program.
inline constexpr uint64_t descriptorChargeLimit = 64 * 1024 * 1024;
/// Descriptor charge units of one stored child slot of an aggregate layout.
inline constexpr uint64_t descriptorChildCharge = 88;

/// Shared refusal classes of independent Program readers. Diagnostic codes
/// remain reader-specific; the class is what readers agree on.
enum class RefusalClass {
  Syntax,
  Capacity,
  NamesAndSsa,
  Types,
  AffineUse,
  UnsupportedProfile,
};
llvm::StringRef refusalClassName(RefusalClass);
/// A Program refusal with its class. Consumers that only need the identifier
/// handle the parent `zkc::Refusal`.
class ProgramRefusal : public llvm::ErrorInfo<ProgramRefusal, Refusal> {
public:
  static char ID;
  RefusalClass kind;
  ProgramRefusal(RefusalClass kind, std::string code, std::string detail)
      : ErrorInfo(std::move(code), std::move(detail)), kind(kind) {}
};
llvm::Error refuse(RefusalClass, llvm::StringRef code,
                   const llvm::Twine &detail = {});
/// Names and sites: `[A-Za-z_][A-Za-z0-9_.-]*` within identifierByteLimit.
bool isIdentifier(llvm::StringRef);

/// Parse under the Program byte, node and nesting ceilings before any JSON
/// value is allocated, then decode the current carrier.
llvm::Expected<Participants> parse(llvm::StringRef);
/// Read only zkc.program/0 physical programs. Structural decoding does not
/// replace semantic admission.
llvm::Expected<Participants> decode(const llvm::json::Value &);
/// Precondition: checkStructure has succeeded for this unchanged program.
/// Physical-only, preserving the zkc.program/0 carrier and declaration order.
llvm::json::Value encode(const Participants &);
llvm::Error checkStructure(const Participants &);
} // namespace zkc::program
#endif
