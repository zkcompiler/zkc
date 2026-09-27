#include "mlir/AsmParser/AsmParser.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Frontend/Analysis.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#if EXPECT_ENVELOPE
#include "envelope/Envelope.h"
#endif
using namespace llvm;
using namespace mlir;
using namespace zkc::protocol;
int main(int argc, char **argv) {
  if (argc == 2 && StringRef(argv[1]) == "--checked-identities") {
    // Identical checked source under two installations captures each installed
    // declaration environment. Return exact keys, not hashes used as evidence.
    auto common = zkc::frontend::analyzeProtocol(R"(
      library(namespace="example", name="installation", version="1",
              resolution="installed-consumer");
      interface Cell { local keep(value: bool) -> bool; }
      component Plain: Cell {
        local keep(value: bool) -> bool { return value; }
      }
      fn Client<C: Cell>(value: bool) -> bool { return C::keep(value); }
      link Selected = Client<Plain>;
    )",
                                                 "identity.pir");
    if (!common.complete()) {
      for (const auto &diagnostic : common.diagnostics())
        errs() << diagnostic.code << ": " << diagnostic.message << '\n';
      return 1;
    }
    json::Array identities;
    for (const auto &dependency : common.dependencies())
      if (dependency.kind ==
          zkc::frontend::SemanticDependency::Kind::LinkLayout)
        identities.push_back(dependency.target);
    if (identities.empty())
      return 1;
    outs() << json::Value(std::move(identities)) << '\n';
    return 0;
  }
  if (argc != 1)
    return 2;
  auto analysis = zkc::frontend::analyzeProtocol(R"(
    use zkc::envelope::{Envelope, keep};
    fn Keep<T: Type, N: nat>(value: Envelope<T,N>) -> Envelope<T,N> {
      return keep(value);
    }
  )",
                                                 "envelope.pir");
#if !EXPECT_ENVELOPE
  for (const auto &diagnostic : analysis.diagnostics())
    if (diagnostic.code == "source-name-unresolved") {
      outs() << "base installation refuses the absent source vocabulary\n";
      return 0;
    }
  errs() << "base installation did not refuse the absent vocabulary\n";
  return 1;
#else
  auto require = [](bool accepted, StringRef why) {
    if (!accepted) {
      errs() << why << '\n';
      std::exit(1);
    }
  };
  if (!analysis.complete())
    for (const auto &diagnostic : analysis.diagnostics())
      errs() << diagnostic.code << ": " << diagnostic.message << '\n';
  require(analysis.complete(), "contributed source export did not check");
  auto lowered = analysis.lower();
  if (!lowered) {
    errs() << toString(lowered.takeError()) << '\n';
    return 1;
  }
  for (StringRef call : {"let pair = envelope::pair::<U,K,L>(x,y);",
                         "let pair = envelope::pair(x,y);",
                         "let pair: (FixedVector<U,K>, FixedVector<U,L>) = "
                         "envelope::pair(x,y);"}) {
    auto generic = zkc::frontend::analyzeProtocol((R"(
      use zkc::algebra::FixedVector;
      use zkc::envelope;
      fn Pair<U: Type, K: nat, L: nat>(x: FixedVector<U,K>, y: FixedVector<U,L>)
          -> (FixedVector<U,K>, FixedVector<U,L>) {
    )" + call + "return pair; }")
                                                      .str(),
                                                  "pair.pir");
    require(generic.complete(),
            "contributed generic multi-result source did not check");
    bool solved = false;
    for (const auto &binding : generic.bindings())
      if (binding.name == "pair")
        solved = generic.display(binding.type) ==
                 "(fixed_vector<U,K>, fixed_vector<U,L>)";
    require(solved, "multi-result type arguments differ");
    auto model = generic.lower();
    if (!model) {
      errs() << toString(model.takeError()) << '\n';
      return 1;
    }
  }
  auto protocol = zkc::frontend::analyzeProtocol(R"(
    use zkc::envelope::Capability;
    protocol Abstract<D: Capability> { roles(P); return; }
  )",
                                                 "bound.pir");
  require(protocol.complete(),
          "contributed protocol domain-sort bound did not check");
  DialectRegistry registry;
  zkc::registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  require(zkc::hasProtocolDialects(context),
          "installation did not register its dialects");
  auto logical = parseBoundType("envelope<field:koala-bear,4>", false);
  if (!logical) {
    errs() << toString(logical.takeError()) << '\n';
    return 1;
  }
  auto expected = envelope::EnvelopeType::get(
      &context, zkc::FieldType::get(&context, "koala-bear"), 4);
  require(decodeBoundType(&context, *logical) == expected,
          "wrong contributed native type");
  auto encoded = encodeBoundType(expected, false);
  if (!encoded) {
    errs() << toString(encoded.takeError()) << '\n';
    return 1;
  }
  require(*encoded == *logical, "logical roundtrip changed the descriptor");
  std::string assembly;
  raw_string_ostream stream(assembly);
  Type(expected).print(stream);
  require(parseType(assembly, &context) == expected,
          "native assembly did not roundtrip");
  auto nested = parseBoundType("fixed_vector<envelope<bool,2>,3>", false);
  if (!nested) {
    errs() << toString(nested.takeError()) << '\n';
    return 1;
  }
  auto nestedNative = decodeBoundType(&context, *nested);
  auto nestedExpected = zkc::FixedVectorType::get(
      &context,
      envelope::EnvelopeType::get(&context, IntegerType::get(&context, 1), 2),
      3);
  require(nestedNative == nestedExpected,
          "cross-domain nested native type differs");
  auto nestedBack = encodeBoundType(nestedNative, false);
  if (!nestedBack) {
    errs() << toString(nestedBack.takeError()) << '\n';
    return 1;
  }
  require(*nestedBack == *nested, "cross-domain roundtrip differs");
  require(boundOperationName("envelope.keep") == "envelope.keep",
          "contributed ODS contract mapping is missing");
  require(boundOperationName("envelope.pair").empty(),
          "logical-only declaration gained an invented native mapping");
  auto concrete = zkc::frontend::analyzeProtocol(R"(
    use zkc::envelope::{Envelope, keep};
    fn Keep(value: Envelope<"koala-bear"::Element,4>)
        -> Envelope<"koala-bear"::Element,4> {
      return keep(value);
    }
  )",
                                                 "concrete.pir");
  require(concrete.complete(), "concrete contributed source did not check");
  auto source = concrete.lower();
  if (!source) {
    errs() << toString(source.takeError()) << '\n';
    return 1;
  }
  auto imported = importModule(*source, context);
  if (!imported) {
    errs() << toString(imported.takeError()) << '\n';
    return 1;
  }
  require(succeeded(verify(**imported)),
          "contributed operation did not verify");
  unsigned operations = 0;
  (*imported)->walk([&](envelope::KeepOp operation) {
    ++operations;
    auto original = operation->getResult(0).getType();
    operation->getResult(0).setType(IntegerType::get(&context, 1));
    {
      ScopedDiagnosticHandler silence(&context,
                                      [](Diagnostic &) { return success(); });
      require(failed(verify(**imported)),
              "standard verifier admitted the wrong result type");
    }
    operation->getResult(0).setType(original);
  });
  require(operations == 1 && succeeded(verify(**imported)),
          "contributed operation import or restoration failed");
  // An unknown owned property must fail during parsing, before an incomplete
  // operation could fail for an unrelated signature or binding reason.
  bool unknownProperty = false;
  {
    ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
      std::string message;
      raw_string_ostream stream(message);
      diagnostic.print(stream);
      unknownProperty |= StringRef(message).contains("mlir-unknown-property");
      return success();
    });
    auto malformed = parseSourceString<ModuleOp>(
        R"(module { "envelope.keep"() <{surprise = "must-not-disappear"}> : () -> () })",
        &context);
    require(!malformed, "unknown contributed owned property disappeared");
  }
  require(unknownProperty, "contributed parsing did not use strict properties");
  auto selected = defaultRepresentation(*logical);
  require(!selected,
          "logical registration silently supplied a physical implementation");
  outs() << "source checking/lowering, native expectations and nested "
            "roundtrips passed; physical selection refuses: "
         << toString(selected.takeError()) << '\n';
  return 0;
#endif
}
