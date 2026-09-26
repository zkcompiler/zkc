#include "zkc/Compiler/Compilation.h"
#include "mlir/IR/Location.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Compiler/Claims.h"
#include "zkc/Compiler/Construction.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Compiler/Inspection.h"
#include "zkc/Compiler/Source.h"
#include "zkc/Dialect/PIR/IR/PIRDialect.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/TableLibrary.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Interfaces/SourceLibrary.h"
#include "zkc/Source/Codec.h"
#include "zkc/Source/Snapshot.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Protocol.h"
#include "zkc/Translation/Table.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace zkc;
namespace {
void require(bool value, StringRef message) {
  if (!value) {
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
constexpr StringLiteral program = R"(module {
  fn Identity(x: bool) -> bool { return x; }
  fn Nested(flag: bool, x: bool) -> bool {
    let mut result = x;
    if flag { result = Identity(x); }
    return result;
  }
  protocol Send {
    roles(P, V);
    inputs(P x: bool);
    outputs(V bool);
    local P: let a = Identity(x);
    message value: P(a) -> V(y);
    return y;
  }
  instance run: Send { roles(P = prover, V = verifier); }
  entry main = run;
})";
Compilation compile(ProtocolAction action) {
  // Both the caller's registry and analysis die before using the returned IR.
  mlir::DialectRegistry registry;
  // Built-ins are initialized by the invocation, even with an empty registry.
  auto analysis = frontend::analyzeProtocol(program, "owned.pir");
  auto document = take(lowerSource(analysis));
  return take(compileProtocol(std::move(document), {action, {}}, registry));
}
void ownership() {
  auto first = compile(ProtocolAction::Import);
  auto second = compile(ProtocolAction::Plan);
  require(first.module().getContext() != second.module().getContext(),
          "invocations share mutable contexts");
  require(first.source()->text() == program, "source spelling was not owned");
  auto prepared =
      take(prepareSource(*first.source(), *first.module().getContext()));
  bool calls = false;
  for (const auto &function : std::get<source::Module>(prepared).functions)
    if (function.body)
      source::walk(*function.body, [&](const source::Instruction &instruction) {
        calls |= instruction.get<source::AlgorithmCall>() != nullptr;
      });
  require(!calls,
          "source preparation missed a call nested inside local control");
  auto expected = take(protocol::exportModule(second.module()));
  first = std::move(second); // destroys old IR before its old context
  require(succeeded(mlir::verify(first.module())), "moved IR lost its context");
  require(take(protocol::exportModule(first.module())) == expected,
          "move assignment changed the artifact");
  auto expansion = compile(ProtocolAction::Expand);
  require(expansion.source()->filename() == "owned.pir", "source name lost");
  auto projected = compile(ProtocolAction::Project);
  auto content = take(protocol::exportSource(projected.module()));
  require(std::get<source::Participants>(content).stage ==
              source::Participants::Stage::Logical,
          "projection did not stop");
}
void selectionAndFailure() {
  mlir::DialectRegistry registry;
  registerDialects(registry);
  auto document = take(frontend::parseProtocolDocument(program, "refusal.pir"));
  ProtocolOptions options;
  options.physical.implementations.sourceSnapshot.assign(64, '0');
  options.physical.implementations.choices = {{"missing", "missing"}};
  auto stale = compileProtocol(document, options, registry);
  require(!stale, "stale selection accepted");
  bool structured = false;
  handleAllErrors(stale.takeError(), [&](const CompilationError &e) {
    structured = e.refusals.size() == 1 &&
                 e.refusals.front().code == "binding-stale-selection";
  });
  require(structured, "source selection did not preserve its code");
  auto projected = compile(ProtocolAction::Project);
  auto logical = take(protocol::exportSource(projected.module()));
  auto rejected = compileProtocol(source::Document(logical), {}, registry);
  require(!rejected, "projection of participant input accepted");
  structured = false;
  handleAllErrors(rejected.takeError(), [&](const CompilationError &e) {
    for (const auto &refusal : e.refusals)
      structured |= refusal.code == "interactive-projection-stage";
  });
  require(structured, "pass refusal metadata lost at invocation teardown");
  auto malformed = *document.module();
  malformed.entries[0].instance = "missing";
  auto bad = compileProtocol(source::Document(malformed), {}, registry);
  require(!bad, "malformed typed source accepted");
  structured = false;
  handleAllErrors(bad.takeError(), [&](const CompilationError &e) {
    structured = !e.refusals.empty() && !e.message.empty();
  });
  require(structured, "located source refusal lost its structured identity");
}

Compilation table(TableAction action) {
  auto request = take(parseJson(R"(["zkc-request",1,"finite-source-1",
    ["trace",[["x",["scalar","f7"],["shared"],"argument"]],
      ["scalar","f7"],[["table-protocol","1"]]],[],["return",0]])"));
  mlir::DialectRegistry registry;
  registerTableLibrary(registry);
  return take(compileTable(request, {action, false}, registry));
}
// A deliberately misbehaving extension emits an error while returning a valid
// type. The workflow must not publish an artifact on that apparent success.
class NoisyLibrary : public SourceLibraryInterface {
public:
  using SourceLibraryInterface::SourceLibraryInterface;
  json::Value dependencies() const final {
    return json::Array{json::Array{"noisy", "1"}};
  }
  mlir::Type conditionType(mlir::Builder &b) const final {
    return b.getI1Type();
  }
  Expected<mlir::Type> decodeType(const json::Value &,
                                  mlir::Builder &b) const override {
    auto diagnostic =
        mlir::emitError(b.getUnknownLoc(), "extension reported an error");
    diagnostic.attachNote(
        mlir::FileLineColLoc::get(b.getContext(), "extension.pir", 7, 3))
        << "additional context";
    return mlir::Type(b.getI1Type());
  }
  Expected<json::Value> encodeType(mlir::Type) const final {
    return json::Value(json::Array{"bool"});
  }
  Expected<ResolvedOperation> resolveOperation(const json::Value &,
                                               mlir::Builder &) const final {
    return error("unknown-operation");
  }
};
// Exercise Compiler's LLVM-error adapter independently of MLIR emission.
class SetupFailureLibrary final : public NoisyLibrary {
public:
  using NoisyLibrary::NoisyLibrary;
  Expected<mlir::Type> decodeType(const json::Value &,
                                  mlir::Builder &) const final {
    return make_error<DialectRegistrationError>(
        InvocationPrecondition::LoadedProtocolDialects,
        "extension invocation setup failed");
  }
};
void tableOwnership() {
  mlir::DialectRegistry unloadedRegistry;
  registerDialects(unloadedRegistry);
  registerTableLibrary(unloadedRegistry);
  mlir::MLIRContext unloaded(unloadedRegistry);
  auto requestBeforeLoad = take(parseJson(R"(["zkc-request",1,"finite-source-1",
    ["trace",[["x",["scalar","f7"],["shared"],"argument"]],
      ["scalar","f7"],[["table-protocol","1"]]],[],["return",0]])"));
  auto importedBeforeLoad = importSource(requestBeforeLoad, unloaded);
  require(!importedBeforeLoad, "table import accepted an unloaded dialect");
  bool tablePrecondition = false;
  handleAllErrors(
      importedBeforeLoad.takeError(), [&](const DialectRegistrationError &e) {
        tablePrecondition =
            e.precondition == InvocationPrecondition::LoadedPIRDialect &&
            e.detail == "table import requires the loaded pir dialect";
      });
  require(tablePrecondition && unloaded.getLoadedDialects().size() == 1,
          "table import must refuse without changing the caller's context");
  for (auto action : {TableAction::Import, TableAction::Plan, TableAction::Lazy,
                      TableAction::Materialized}) {
    auto compiled = table(action);
    require(!compiled.source(), "table result claimed an interactive source");
    require(succeeded(mlir::verify(compiled.module())),
            "table result lost its registered library or context");
    if (action != TableAction::Import)
      (void)take(exportPlan(compiled.module()));
  }
  mlir::DialectRegistry registry;
  auto rejected =
      compileTable(json::Value(nullptr), {TableAction::Plan, true}, registry);
  require(!rejected, "logical-only simplification accepted");
  bool structured = false;
  handleAllErrors(rejected.takeError(), [&](const CompilationError &e) {
    structured = e.message == "simplification-requires-physical" &&
                 e.refusals.size() == 1;
  });
  require(structured, "table option failure was not one CompilationError");
  auto request = take(parseJson(R"(["zkc-request",1,"finite-source-1",
    ["trace",[["x",["bool"],["shared"],"argument"]],
      ["bool"],[["noisy","1"]]],[],["return",0]])"));
  auto missing = compileTable(request, {TableAction::Import, false}, registry);
  require(!missing, "table library was installed implicitly");
  structured = false;
  handleAllErrors(missing.takeError(), [&](const CompilationError &e) {
    structured = e.refusals.size() == 1 &&
                 e.refusals.front().code == "unresolved-dependency";
  });
  require(structured, "missing library failure lost its type or code");
  registry.addExtension(+[](mlir::MLIRContext *, PIRDialect *dialect) {
    dialect->addInterfaces<NoisyLibrary>();
  });
  auto noisy = compileTable(request, {TableAction::Import, false}, registry);
  require(!noisy, "successful extension hid its error diagnostic");
  structured = false;
  handleAllErrors(noisy.takeError(), [&](const CompilationError &e) {
    bool notes = !e.locations.empty();
    for (const auto &location : e.locations)
      notes &= location.filename == "extension.pir" && location.line == 7 &&
               location.column == 3;
    structured = e.refusals.empty() &&
                 StringRef(e.message).starts_with(
                     "error: extension reported an error") &&
                 StringRef(e.message).contains("note: additional context") &&
                 notes;
  });
  require(structured,
          "upstream error was not retained without inventing a code");
  mlir::DialectRegistry setupRegistry;
  setupRegistry.addExtension(+[](mlir::MLIRContext *, PIRDialect *dialect) {
    dialect->addInterfaces<SetupFailureLibrary>();
  });
  auto setup =
      compileTable(request, {TableAction::Import, false}, setupRegistry);
  require(!setup, "extension setup failure published a compilation");
  structured = false;
  handleAllErrors(setup.takeError(), [&](const CompilationError &e) {
    structured =
        e.message == "extension invocation setup failed" &&
        e.refusals.empty() && e.locations.empty() &&
        e.invocationPreconditions ==
            std::vector{InvocationPrecondition::LoadedProtocolDialects};
  });
  require(structured, "Compiler lost an extension invocation precondition");
}
void constructionOwnership() {
  constexpr StringLiteral text = R"(module {
    fn Draw(r: Rng<"bls12-381.fr">) -> ("bls12-381.fr"::Element, Rng<"bls12-381.fr">) {
      [pick] let (x, next) = random::draw::<bls12-381.fr>(r);
      return (x, next);
    }
    fn Check(x: "bls12-381.fr"::Element) -> bool {
      let ok = field::equal::<bls12-381.fr>(x, x);
      control::require(ok);
      ok
    }
    protocol Main {
      roles(P, V); inputs(V coins: Rng<"bls12-381.fr">);
      outputs(V bool, V Rng<"bls12-381.fr">);
      local V: let (x, next) = Draw(coins);
      message sample: V(x) -> P(seen);
      local V: let ok = Check(x);
      return (ok, next);
    }
    instance run: Main { roles(P = P, V = V); }
    entry main = run;
  })";
  source::Construction descriptor;
  descriptor.identity = source::Construction::Identity::Exact;
  descriptor.entry = "main";
  descriptor.producer = "P";
  descriptor.validator = "V";
  descriptor.randomness = "coins";
  descriptor.draws = {{"Draw", "pick"}};
  descriptor.acceptance = "0";
  descriptor.suite = "merlin3.bls12-381.fr64be/1";
  auto result = [&] {
    auto analysis = frontend::analyzeProtocol(text, "construction.pir");
    mlir::DialectRegistry registry;
    return take(constructProtocol(analysis, descriptor, registry));
  }();
  require(succeeded(mlir::verify(result.compilation.module())),
          "constructed protocol lost its context");
  require(result.compilation.source()->text() == text,
          "construction lost its original subject");
  auto source = take(protocol::exportModule(result.compilation.module()));
  auto encoded = take(source::decode((*result.certificate.getAsArray())[2]));
  auto importedCandidate = take(protocol::importModule(
      encoded, *result.compilation.module().getContext()));
  require(source == take(protocol::exportModule(*importedCandidate)),
          "construction result and certificate have different subjects");
  auto &original = *result.compilation.source()->module();
  mlir::MLIRContext fresh;
  auto imported = protocol::importModule(original, fresh);
  require(!imported, "uninitialized import context accepted");
  auto missingDialects = imported.takeError();
  bool precondition = false;
  visitErrors(missingDialects, [&](const ErrorInfoBase &e) {
    precondition = e.isA<DialectRegistrationError>() && !e.isA<Refusal>();
  });
  require(precondition, "missing dialects became a semantic refusal");
  auto wrapped = sourceDiagnostic(*result.compilation.source(),
                                  std::move(missingDialects));
  precondition = false;
  handleAllErrors(std::move(wrapped), [&](const CompilationError &e) {
    precondition =
        e.message == "protocol import requires loaded zkc dialects" &&
        e.refusals.empty() && e.locations.empty() &&
        e.invocationPreconditions ==
            std::vector{InvocationPrecondition::LoadedProtocolDialects};
  });
  require(precondition, "invocation setup failure acquired source blame");
  auto uninitialized = protocol::construct(original, descriptor, fresh);
  require(!uninitialized, "uninitialized construction context accepted");
  precondition = false;
  handleAllErrors(
      uninitialized.takeError(), [&](const DialectRegistrationError &e) {
        precondition =
            e.detail == "protocol import requires loaded zkc dialects";
      });
  require(precondition, "construction lost its invocation precondition");
  require(fresh.getLoadedDialects().size() == 1,
          "low-level import changed the caller's context");
  auto catalog = take(claims::inspect(original, "main"));
  claims::Contract contract;
  contract.sourceDigest =
      catalog.getAsObject()->getString("source_digest")->str();
  contract.entry = "main";
  contract.validator = "V";
  auto certificate = take(claims::derive(original, contract));
  for (bool physical : {false, true}) {
    auto refused =
        physical
            ? claims::checkLowering(original, contract, certificate, descriptor,
                                    result.certificate, json::Value(nullptr),
                                    fresh)
            : claims::checkConstruction(original, contract, certificate,
                                        descriptor, result.certificate, fresh);
    require(bool(refused), "claim checking initialized the caller's context");
    require(toString(std::move(refused)) ==
                    "protocol import requires loaded zkc dialects" &&
                fresh.getLoadedDialects().size() == 1,
            "claim checker lost its loaded-context precondition");
  }
  auto failed = frontend::analyzeProtocol("module {", "broken.pir");
  auto bad = constructProtocol(failed, descriptor, mlir::DialectRegistry{});
  require(!bad, "incomplete analysis constructed a protocol");
  bool located = false;
  handleAllErrors(bad.takeError(), [&](const CompilationError &e) {
    located = e.refusals.size() == 1 &&
              e.refusals.front().code == "source-syntax" &&
              !e.refusals.front().detail.empty() && e.locations.size() == 1 &&
              e.locations.front().filename == "broken.pir" &&
              e.locations.front().line == 1 && e.locations.front().column == 9;
  });
  require(located, "construction discarded structured frontend diagnostics");
  // A diagnostic in a captured child must use that file's text, not the root's.
  auto project = take(frontend::ProjectInput::capture(
      {{{{{}, frontend::Input("module { mod child; }", "root.pir")},
         {{"child"},
          frontend::Input("module {\n  fn Broken(x: Absent) -> () "
                          "{ return (); }\n}",
                          "child.pir")}}}}));
  auto invalidProject = frontend::analyzeProject(project);
  auto childError =
      constructProtocol(invalidProject, descriptor, mlir::DialectRegistry{});
  require(!childError, "invalid child module constructed a protocol");
  located = false;
  handleAllErrors(childError.takeError(), [&](const CompilationError &e) {
    located =
        !e.refusals.empty() && !e.locations.empty() &&
        e.refusals.front().code == invalidProject.diagnostics().front().code &&
        e.locations.front().filename == "child.pir" &&
        e.locations.front().line == 2 && e.locations.front().column > 1;
  });
  require(located, "construction used root coordinates for a child diagnostic");
}
void copiedLocations() {
  auto document = take(frontend::parseProtocolDocument(program, "copied.pir"));
  auto copy = document.module()->functions.front();
  auto span = document.diagnosticSpan(copy);
  require(bool(span), "copied node lost its captured span");
  auto coordinate = document.lineColumn(span->offset, span->file);
  require(coordinate.first > 1, "copied location test is trivial");
  auto failure = sourceDiagnostic(document, error("test-refusal"), &copy);
  bool located = false;
  handleAllErrors(std::move(failure), [&](const CompilationError &e) {
    located = e.locations.size() == 1 &&
              e.locations.front().filename == "copied.pir" &&
              e.locations.front().line == coordinate.first &&
              e.locations.front().column == coordinate.second;
  });
  require(located, "owned diagnostic lost the elaborated node's coordinates");
  copy.location->file = 999;
  require(!document.diagnosticSpan(copy), "foreign file span accepted");
}
void registryPreconditions() {
  auto document = take(frontend::parseProtocolDocument(program, "setup.pir"));
  // Neither registering without loading nor loading only some dialects
  // satisfies the import precondition. Failure must not initialize the context.
  for (bool partial : {false, true}) {
    auto failure = [&]() -> Error {
      mlir::DialectRegistry registry;
      registerDialects(registry);
      mlir::MLIRContext context(registry);
      if (partial)
        context.getOrLoadDialect<PIRDialect>();
      auto count = context.getLoadedDialects().size();
      auto result = protocol::importModule(*document.module(), context);
      require(!result, "incompletely initialized registry imported source");
      require(context.getLoadedDialects().size() == count,
              "failed import loaded missing dialects");
      return result.takeError();
    }();
    bool structured = false;
    handleAllErrors(std::move(failure), [&](const DialectRegistrationError &e) {
      structured = e.detail == "protocol import requires loaded zkc dialects";
    });
    require(structured, "registry failure did not survive context teardown");
  }
  // A joined source error retains its identifier and coordinate without
  // giving the embedding failure a semantic identifier.
  auto mixed = sourceDiagnostic(
      document, joinErrors(make_error<DialectRegistrationError>(
                               InvocationPrecondition::LoadedProtocolDialects,
                               "setup detail"),
                           error("source-test", "source detail")));
  bool structured = false;
  handleAllErrors(std::move(mixed), [&](const CompilationError &e) {
    structured =
        e.refusals.size() == 1 && e.refusals[0].code == "source-test" &&
        e.refusals[0].detail == "source detail" && e.locations.size() == 1 &&
        e.locations[0].filename == "setup.pir" &&
        e.invocationPreconditions ==
            std::vector{InvocationPrecondition::LoadedProtocolDialects};
  });
  require(structured,
          "mixed source and invocation failures lost their boundary");
}
} // namespace
int main() {
  ownership();
  selectionAndFailure();
  tableOwnership();
  constructionOwnership();
  copiedLocations();
  registryPreconditions();
}
