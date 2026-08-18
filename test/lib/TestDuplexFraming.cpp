//===- TestDuplexFraming.cpp - duplex framing corpus test pass --*- C++ -*-===//
//
// The duplex framing rule as vectors (docs/spec/vocabularies.md §7): the
// rate slots an absorption did not overwrite are zeroed, the absorbed
// length binds into the first capacity element, outputs pop last-in
// first-out, and the IV is absorbed as big-endian four-byte chunks with
// a short final chunk. Each rule lived as prose satisfied by hand in
// three legs; this pass holds the C++ leg to the checked-in corpus the
// reference twin minted, so a framing divergence is a failing diff
// rather than a silent transcript fork.
//
//===----------------------------------------------------------------------===//
#include "mlir/IR/BuiltinOps.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Interpreter/ExecutionProfile.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"

#include <map>
#include <string>
#include <vector>

using namespace mlir;

namespace {

/// The BabyBear prime. A corpus word at or above it is refused rather
/// than reduced: the emitted runtime asserts canonicality on absorb, so
/// a loader that quietly reduced would make the two legs disagree in
/// kind — a panic against a different value — instead of in value.
constexpr uint64_t kBabyBear = 2013265921;

/// One element as the supplier frames it: a big-endian four-byte word.
void appendElement(llvm::SmallVectorImpl<uint8_t> &out, uint64_t element) {
  out.push_back((element >> 24) & 0xff);
  out.push_back((element >> 16) & 0xff);
  out.push_back((element >> 8) & 0xff);
  out.push_back(element & 0xff);
}

uint64_t readElement(llvm::ArrayRef<uint8_t> bytes, unsigned index) {
  unsigned at = index * 4;
  return ((uint64_t)bytes[at] << 24) | ((uint64_t)bytes[at + 1] << 16) |
         ((uint64_t)bytes[at + 2] << 8) | bytes[at + 3];
}

struct TestDuplexFramingPass
    : public PassWrapper<TestDuplexFramingPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(TestDuplexFramingPass)

  TestDuplexFramingPass() = default;
  TestDuplexFramingPass(const TestDuplexFramingPass &other)
      : PassWrapper(other) {}

  StringRef getArgument() const override { return "test-duplex-framing"; }
  StringRef getDescription() const override {
    return "Hold the pinned plonky3 duplex to the framing KAT corpus";
  }

  Option<std::string> corpusPath{*this, "kat",
                                 llvm::cl::desc("framing corpus path")};

  void runOnOperation() override {
    auto fail = [&](const llvm::Twine &message) {
      getOperation().emitError() << message;
      signalPassFailure();
    };

    auto buffer = llvm::MemoryBuffer::getFile(corpusPath);
    if (!buffer)
      return fail("cannot read the framing corpus at '" + corpusPath + "'");
    auto parsed = llvm::json::parse((*buffer)->getBuffer());
    if (!parsed)
      return fail("the framing corpus does not parse: " +
                  llvm::toString(parsed.takeError()));
    const llvm::json::Object *corpus = parsed->getAsObject();
    const llvm::json::Array *cases =
        corpus ? corpus->getArray("cases") : nullptr;
    const llvm::json::Array *distinct =
        corpus ? corpus->getArray("distinct") : nullptr;
    if (!cases || !distinct)
      return fail("the framing corpus needs 'cases' and 'distinct'");

    // Transparent comparator: the corpus hands out `StringRef`s and
    // this is the repository's idiom for looking one up without a
    // temporary `std::string` per probe.
    std::map<std::string, std::vector<std::string>, std::less<>> outputsByName;
    for (const llvm::json::Value &entry : *cases) {
      const llvm::json::Object *kase = entry.getAsObject();
      std::optional<llvm::StringRef> name =
          kase ? kase->getString("name") : std::nullopt;
      std::optional<llvm::StringRef> iv =
          kase ? kase->getString("iv") : std::nullopt;
      const llvm::json::Array *steps = kase ? kase->getArray("steps") : nullptr;
      const llvm::json::Array *expected =
          kase ? kase->getArray("outputs") : nullptr;
      if (!name || !iv || !steps || !expected)
        return fail("a framing case needs name, iv, steps, and outputs");

      std::unique_ptr<zkc::interpreter::SpongeState> duplex =
          zkc::interpreter::rawPlonky3Duplex(*iv);
      std::vector<std::string> outputs;
      for (const llvm::json::Value &stepValue : *steps) {
        const llvm::json::Object *step = stepValue.getAsObject();
        if (const llvm::json::Array *absorb =
                step ? step->getArray("absorb") : nullptr) {
          llvm::SmallVector<uint8_t> framed;
          for (const llvm::json::Value &element : *absorb) {
            uint64_t word = 0;
            std::optional<llvm::StringRef> text = element.getAsString();
            if (!text || text->getAsInteger(10, word))
              return fail("a framing absorb element is not a decimal string");
            if (word >= kBabyBear)
              return fail("a framing absorb element is not canonical for the "
                          "field");
            appendElement(framed, word);
          }
          duplex->absorb(framed);
          continue;
        }
        std::optional<int64_t> count =
            step ? step->getInteger("squeeze") : std::nullopt;
        if (!count || *count < 1)
          return fail("a framing step is neither an absorb nor a squeeze");
        llvm::SmallVector<uint8_t, 32> squeezed =
            duplex->squeeze(/*domain=*/"", (unsigned)*count);
        for (unsigned i = 0; i < (unsigned)*count; ++i)
          outputs.push_back(std::to_string(readElement(squeezed, i)));
      }

      std::vector<std::string> want;
      for (const llvm::json::Value &value : *expected) {
        std::optional<llvm::StringRef> text = value.getAsString();
        if (!text)
          return fail("a framing case output is not a decimal string");
        want.push_back(text->str());
      }
      if (outputs != want)
        return fail("framing case '" + *name +
                    "': this leg disagrees with the corpus");
      outputsByName[name->str()] = std::move(outputs);
    }

    // The pairs the length binding exists to separate: a value and the
    // same value zero-padded to another length must not collide.
    for (const llvm::json::Value &pairValue : *distinct) {
      const llvm::json::Array *pair = pairValue.getAsArray();
      if (!pair || pair->size() != 2)
        return fail("a distinct entry is not a pair of case names");
      std::optional<llvm::StringRef> leftName = (*pair)[0].getAsString();
      std::optional<llvm::StringRef> rightName = (*pair)[1].getAsString();
      if (!leftName || !rightName)
        return fail("a distinct pair does not name two cases as strings");
      auto left = outputsByName.find(*leftName);
      auto right = outputsByName.find(*rightName);
      if (left == outputsByName.end() || right == outputsByName.end())
        return fail("a distinct pair names an unknown case");
      if (left->second == right->second)
        return fail("distinct framing cases collided: the length binding "
                    "is not separating them");
    }

    llvm::outs() << "duplex framing corpus: " << cases->size()
                 << " cases agree, " << distinct->size()
                 << " distinct pair(s) separate\n";
  }
};

} // namespace

namespace zkc::test {
void registerTestDuplexFramingPass() {
  PassRegistration<TestDuplexFramingPass>();
}
} // namespace zkc::test
