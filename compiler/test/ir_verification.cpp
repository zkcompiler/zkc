#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Source/Relations.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace mlir;
using namespace zkc;

namespace {
void require(bool ok, const Twine &message) {
  if (!ok) {
    errs() << message << '\n';
    std::exit(1);
  }
}
template <typename T> T take(Expected<T> value) {
  if (!value) {
    errs() << toString(value.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*value);
}

// Keep every protocol namespace loaded while deliberately omitting algebra's
// native types and operations. This passes the existing namespace precondition.
class EmptyAlgebraDialect : public Dialect {
public:
  explicit EmptyAlgebraDialect(MLIRContext *context)
      : Dialect(getDialectNamespace(), context,
                TypeID::get<EmptyAlgebraDialect>()) {}
  static StringRef getDialectNamespace() { return "algebra"; }
};

template <typename Root>
void importRefuses(const Root &source, MLIRContext &incomplete,
                   MLIRContext &complete, StringRef code,
                   const source::Node *expectedLocation) {
  if (auto e = protocol::admit(source, false)) {
    errs() << toString(std::move(e)) << '\n';
    require(false, "missing-adapter fixture must pass source admission");
  }
  take(protocol::importModule(source, complete));
  const source::Node *location = nullptr;
  auto imported = protocol::importModule(source, incomplete, {}, &location);
  require(!imported, "incomplete native registration was accepted");
  require(toString(imported.takeError()) == code,
          "import refused after native construction or lost its refusal code");
  require(location == expectedLocation, "import refusal lost its source node");
}

void incompleteRegistration(MLIRContext &complete) {
  DialectRegistry registry;
  registry.insert<zkc::data::DataDialect, EmptyAlgebraDialect,
                  zkc::protocol_ir::ProtocolDialect, zkc::local::LocalDialect,
                  zkc::crypto::CryptoDialect, zkc::table::TableDialect,
                  zkc::poly::PolynomialDialect, zkc::plan::PlanDialect,
                  zkc::pcs::PCSDialect, zkc::oracle::OracleDialect,
                  zkc::relation::RelationDialect, zkc::claim::ClaimDialect,
                  func::FuncDialect>();
  MLIRContext incomplete(registry);
  incomplete.loadAllAvailableDialects();
  const auto initiallyLoadedDialects = incomplete.getLoadedDialects();
  require(hasProtocolDialects(incomplete),
          "fixture must pass the existing dialect precondition");
  source::Module module;
  module.bindings.push_back({{}, "add", {"field.add", {"koala-bear"}, {}}});
  require(!protocol::boundOperationName("field.add").empty(),
          "fixture must have an installed ODS mapping");
  importRefuses(module, incomplete, complete, "binding-operation",
                &module.bindings[0]);
  // Mapped PIR operations remain registered, but their input/output field
  // carriers are missing. Unused binding declarations are also preflighted.
  module.bindings[0] = {
      {},
      "challenge",
      {"transcript.challenge", {"merlin3.bls12-381.fr64be/1"}, {}}};
  importRefuses(module, incomplete, complete, "binding-type",
                &module.bindings[0]);
  module.bindings[0] = {{},
                        "observe",
                        {"transcript.observe.field",
                         {"merlin3.bls12-381.fr64be/1", "bls12-381.fr",
                          "zkcv.field.bls12-381.fr/1"},
                         {}}};
  importRefuses(module, incomplete, complete, "binding-type",
                &module.bindings[0]);
  module.bindings.clear();
  source::Function function;
  function.name = "external";
  function.origin = source::LogicalOrigin{"external", {}};
  function.arguments = {{"x", "fixed_vector<field:koala-bear,4>"}};
  module.functions = {function};
  importRefuses(module, incomplete, complete, "binding-type",
                &module.functions[0]);
  module.functions[0].arguments.clear();
  module.functions[0].results = {"field:koala-bear"};
  importRefuses(module, incomplete, complete, "binding-type",
                &module.functions[0]);
  source::Module protocolModule;
  source::Protocol protocol;
  protocol.name = "external_protocol";
  protocol.roles = {"Alice"};
  protocol.arguments = {{"x", "Alice", "field:koala-bear"}};
  protocolModule.protocols = {protocol};
  importRefuses(protocolModule, incomplete, complete, "binding-type",
                &protocolModule.protocols[0]);
  protocolModule.protocols[0].arguments.clear();
  protocolModule.protocols[0].results = {{"Alice", "field:koala-bear"}};
  importRefuses(protocolModule, incomplete, complete, "binding-type",
                &protocolModule.protocols[0]);

  auto variant = protocol::encodeVariant(
      {"Choice", {{"empty", {}}, {"value", {"field:koala-bear"}}}});
  require(bool(variant), "variant fixture refused");
  auto bound = take(protocol::parseBoundType(*variant, false));
  require(bool(protocol::decodeBoundType(&incomplete, bound)),
          "outer variant must decode without its payload's adapter");
  // A signature's opaque variant descriptor also owns match block types.
  module.functions[0].results = {*variant};
  importRefuses(module, incomplete, complete, "binding-type",
                &module.functions[0]);
  // These types occur only inside nested blocks, not in a binding/signature.
  source::Body arm{
      {{}, "pack", source::VariantConstruct{*variant, "empty", {}, "packed"}},
      {{}, {}, source::Yield{{}}}};
  auto otherArm = arm;
  otherArm.front().site = "other_pack";
  module.functions[0].arguments = {{"condition", "bool"}};
  module.functions[0].results.clear();
  module.functions[0].body = source::Body{
      {{}, "branch", source::Conditional{"condition", {}, arm, otherArm, {}}},
      {{}, {}, source::Return{{}}}};
  const auto &branch =
      *module.functions[0].body->front().get<source::Conditional>();
  importRefuses(module, incomplete, complete, "binding-type",
                &branch.thenBody.front());

  source::Participants participants;
  participants.stage = source::Participants::Stage::Physical;
  source::Participant participant;
  participant.name = "alice";
  participant.instance = "instance";
  participant.role = "Alice";
  participant.body = {{{}, {}, source::Return{{}}}};
  participants.participants = {participant};
  participants.entries.push_back({{}, "main", {{"Alice", "alice"}}});
  function.arguments = {
      {"x", "fixed_vector<field:koala-bear,4>@plonky3.fixed-vector/1"}};
  function.results = {function.arguments[0].type};
  function.body = source::Body{{{}, {}, source::Return{{"x"}}}};
  participants.functions = {function};
  importRefuses(participants, incomplete, complete, "binding-type",
                &participants.functions[0]);
  participants.functions.clear();
  participants.participants[0].arguments = function.arguments;
  participants.participants[0].results = function.results;
  participants.participants[0].body = *function.body;
  importRefuses(participants, incomplete, complete, "binding-type",
                &participants.participants[0]);
  participants.participants[0] = participant;
  // A physical adapter has no logical ODS mapping and uses
  // zkc::plan::ExecuteKernelOp.
  participants.bindings.push_back(
      {{},
       "relayout",
       {"table.relayout",
        {"bls12-381.fr", "arkworks.mle-lsb/1", "arkworks.mle-msb/1"},
        "arkworks/table.relayout"}});
  take(protocol::importModule(participants, complete));
  take(protocol::importModule(participants, incomplete));
  participants.bindings.clear();
  participants.stage = source::Participants::Stage::Logical;
  source::Loop loop;
  loop.count.value = "1";
  loop.body = {{{},
                "receive",
                source::Receive{"message", "Bob", "value", "field:koala-bear"}},
               {{}, {}, source::Yield{{}}}};
  participants.participants[0].body = {{{}, "loop", loop},
                                       {{}, {}, source::Return{{}}}};
  const auto &nested =
      *participants.participants[0].body.front().get<source::Loop>();
  importRefuses(participants, incomplete, complete, "binding-type",
                &nested.body.front());
  require(incomplete.getLoadedDialects() == initiallyLoadedDialects,
          "import changed the caller's loaded dialects");
}
void generatedView(source::Module source, MLIRContext &context) {
  if (auto e = relation::materializeViews(source)) {
    errs() << toString(std::move(e)) << '\n';
    std::exit(1);
  }
  auto module = take(protocol::importModule(source, context));
  auto exported = take(protocol::exportModule(module.get()));
  require(exported == source::encode(source),
          "relation view roundtrip changed");
  Operation *kernel = nullptr;
  module->walk([&](Operation *op) {
    if (!kernel && op->hasAttr("site") &&
        op->getParentOfType<zkc::local::FuncOp>())
      kernel = op;
  });
  require(kernel, "generated relation must contain local computation");
  kernel->setAttr("site", StringAttr::get(&context, "tampered"));
  // Local IR is well-formed. Only the complete source reconstruction can
  // establish that the generated code corresponds to the retained relation.
  require(succeeded(kernel->getName().verifyInvariants(kernel)),
          "mutation must preserve local operation invariants");
  std::vector<diagnostics::RefusalInfo> codes;
  ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
    auto found = diagnostics::refusals(diagnostic);
    llvm::append_range(codes, found);
    return success();
  });
  require(failed(verify(module.get())),
          "whole-root verification lost correspondence");
  require(llvm::any_of(codes,
                       [](const auto &r) {
                         return r.code == "relation-generated-function";
                       }),
          "whole-root refusal lost its native identifier");
  auto rejected = protocol::exportSource(module.get());
  require(!rejected, "public export must check mutated roots");
  require(toString(rejected.takeError()) == "relation-generated-function",
          "changed refusal precedence");
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  incompleteRegistration(context);
  relation::Constraint row{{{{2, "1"}}, {{3, "1"}}, {{1, "1"}}}};
  auto r1cs = take(relation::R1CS::create("bls12-381.fr", 4, 1, 1, {row}));
  for (auto kind : {"multilinear", "rank_one"})
    for (auto staging : {"specialized", "public_matrices"}) {
      source::Module source;
      source.relations.push_back(
          {{}, "Circuit", std::make_shared<const relation::R1CS>(r1cs)});
      source.relationViews.push_back(
          {{}, "Rows", "Circuit", kind, staging, {}});
      generatedView(std::move(source), context);
    }
  using N = relation::AIRNode;
  auto air = take(relation::AIR::create(
      "bls12-381.fr", 1, 0,
      {{{relation::AIRScopeKind::Transition, 1},
        {N::read(1, 0), N::read(0, 0), N::mul(1, 1), N::neg(2), N::add(0, 3)},
        {},
        {}}}));
  source::Module source;
  source.relations.push_back(
      {{}, "Trace", std::make_shared<const relation::AIR>(air)});
  source.relationViews.push_back(
      {{}, "Steps", "Trace", "arithmetic", "specialized", 3});
  generatedView(std::move(source), context);
  outs() << "five generated relation views retain exact root/export "
            "correspondence\n";
}
