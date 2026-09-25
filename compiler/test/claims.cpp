#include "zkc/Claims/Claims.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Compiler/Inspection.h"
#include "zkc/Dialect/Claim/IR/ClaimDialect.h"
#include "zkc/Dialect/Oracle/IR/OracleDialect.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Protocol/PhysicalOptions.h"
#include "zkc/Source/Snapshot.h"
#include "zkc/Translation/Claims.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace zkc;

namespace {
void require(bool condition, StringRef message) {
  if (!condition) {
    errs() << message << '\n';
    std::exit(1);
  }
}
template <typename T> T take(Expected<T> result) {
  if (!result) {
    errs() << toString(result.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*result);
}
void success(Error result) {
  if (result) {
    errs() << toString(std::move(result)) << '\n';
    std::exit(1);
  }
}
template <typename T> void refuses(Expected<T> result, StringRef code) {
  require(!result, "unexpected acceptance");
  require(toString(result.takeError()) == code, "wrong refusal code");
}
} // namespace

int main() {
  auto document = take(frontend::parseProtocolDocument(R"pir(module {
    bind require = control.require();
    fn Check(ok: bool) -> (bool) {
      require(ok);
      return (ok);
    }
    protocol Checked {
      roles (Verifier);
      inputs (Verifier ok: bool);
      outputs (Verifier bool);
      local Verifier: let accepted = Check(ok);
      return (accepted);
    }
    instance checked: Checked { roles (Verifier = Validator); }
    entry main = checked;
  })pir"));
  const auto &source = *document.module();
  auto catalog = take(claims::inspect(source, "main"));
  claims::Contract contract;
  contract.sourceDigest =
      catalog.getAsObject()->getString("source_digest")->str();
  contract.entry = "main";
  contract.validator = "Validator";
  contract.kinds = {{"accepted", {"bool"}, "The input Boolean is true"}};
  contract.claims = {{"guard", "guard", {"v0"}},
                     {"result", "accepted", {"v0"}}};
  contract.required = {"result"};
  contract.terminals = {{"guard", "$/0/0"}};
  contract.laws = {{"check", "The Check body enforces its exact input"}};
  contract.rules = {{"accept",
                     "check",
                     "$/0",
                     "Check",
                     {"v0"},
                     {"v0"},
                     {"$/0/0"},
                     {"guard"},
                     "result"}};
  auto certificate = take(claims::derive(source, contract));
  require(certificate.steps == source::Names{"accept"},
          "unexpected derivation");
  success(claims::check(source, contract, certificate));

  // Translation initializes the dialects it creates in a fresh context.
  mlir::MLIRContext context;
  auto ir = take(claims::import(source, contract, certificate, context));
  success(claims::checkIR(source, contract, *ir));

  // Parsing a Boolean-only candidate loads only its actual Claim dialect.
  // Checking it must neither require nor initialize unrelated dialects.
  std::string text;
  raw_string_ostream stream(text);
  ir->print(stream);
  mlir::MLIRContext minimal;
  minimal.loadDialect<ClaimDialect>();
  auto candidate = mlir::parseSourceString<mlir::ModuleOp>(text, &minimal);
  require(bool(candidate), "minimal-context candidate did not parse");
  const auto loaded = minimal.getLoadedDialects().size();
  success(claims::checkIR(source, contract, *candidate));
  require(minimal.getLoadedDialects().size() == loaded,
          "candidate checking loaded an unrelated dialect");

  // Source execution records include oracle-valued inputs even when the
  // conditional claim itself concerns only a Boolean guard.
  auto oracleSource = source;
  oracleSource.protocols.front().arguments.push_back(
      {"root", "Verifier", "commitment:rows.merkle-keccak256.koala-bear/1"});
  auto oracleContract = contract;
  oracleContract.sourceDigest = take(claims::inspect(oracleSource, "main"))
                                    .getAsObject()
                                    ->getString("source_digest")
                                    ->str();
  auto oracleCertificate = take(claims::derive(oracleSource, oracleContract));
  mlir::MLIRContext oracleContext;
  auto oracleIR = take(claims::import(oracleSource, oracleContract,
                                      oracleCertificate, oracleContext));
  require(oracleContext.getLoadedDialect<OracleDialect>() != nullptr,
          "fresh claim import did not initialize oracle subject types");
  success(claims::checkIR(oracleSource, oracleContract, *oracleIR));

  // Selection custody uses the actual source entering physical planning.
  // Typed callers must receive the same admission as JSON callers.
  protocol::ImplementationSelection selected;
  selected.sourceSnapshot = take(source::snapshot(document.root()));
  selected.choices = {{"require", "arkworks/control.require"}};
  success(protocol::checkImplementationSelection(selected, document.root()));
  for (unsigned mutation = 0; mutation < 6; ++mutation) {
    auto invalid = selected;
    StringRef expected;
    switch (mutation) {
    case 0:
      invalid.sourceSnapshot.assign(64, '0');
      expected = "binding-stale-selection";
      break;
    case 1:
      invalid.sourceSnapshot = "not-a-digest";
      expected = "binding-selection-snapshot";
      break;
    case 2:
      invalid.choices.push_back(invalid.choices.front());
      expected = "binding-duplicate-selection";
      break;
    case 3:
      invalid.choices.front().first = std::string("a\0b", 3);
      expected = "binding-selection-format";
      break;
    case 4:
      invalid.choices.front().second.assign(1, static_cast<char>(0xff));
      expected = "binding-selection-format";
      break;
    default:
      invalid.choices.resize(4097, {"require", "arkworks/control.require"});
      expected = "binding-selection-format";
      break;
    }
    auto result =
        protocol::checkImplementationSelection(invalid, document.root());
    require(bool(result), "malformed typed selection accepted");
    require(toString(std::move(result)) == expected, "wrong selection refusal");
  }

  // Installed callers can build malformed typed modules. Admission must run
  // before expansion's internal lookups, including missing symbol/scope cases.
  for (unsigned change = 0; change < 3; ++change) {
    auto malformed = source;
    if (change == 0)
      malformed.entries.front().instance = "missing";
    else if (change == 1)
      malformed.functions.clear();
    else
      malformed.bindings.clear();
    auto result = claims::inspect(malformed, "main");
    require(!result, "malformed typed source reached expansion");
    consumeError(result.takeError());
  }

  auto stale = contract;
  stale.sourceDigest.assign(64, '0');
  refuses(claims::derive(source, stale), "claim-source-mismatch");
  auto oversized = contract;
  oversized.required.resize(32769, "result");
  refuses(claims::derive(source, oversized), "claim-contract-format");

  // These clients bypass the JSON parser. Invalid strings must be refused
  // before LLVM's JSON encoder can normalize them into different valid text.
  for (bool law : {false, true}) {
    auto changed = contract;
    auto &text =
        law ? changed.laws.front().premise : changed.kinds.front().meaning;
    for (const auto &bad :
         {std::string(1, static_cast<char>(0xff)),
          std::string("embedded\0zero", 13), std::string(4097, 'x')}) {
      text = bad;
      refuses(claims::derive(source, changed), "claim-contract-format");
    }
    text = "\xEF\xBF\xBD";
    auto unicode = take(claims::derive(source, changed));
    require(unicode.contractDigest != certificate.contractDigest,
            "distinct valid authority text shared an identity");
    success(claims::check(source, changed, unicode));
    auto error = claims::check(source, changed, certificate);
    require(bool(error), "stale authority certificate accepted");
    require(toString(std::move(error)) == "claim-certificate-mismatch",
            "wrong authority mismatch code");
  }
  outs() << "typed claims API admission, identity and fresh-context controls "
            "passed\n";
}
