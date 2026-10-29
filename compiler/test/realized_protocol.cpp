#include "../lib/Transforms/OracleCommonRealization.h"
#include "../lib/Transforms/RealizedProtocol.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/MemoryBuffer.h"
#include <type_traits>

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::mathematical;
using namespace zkc::test;
static_assert(!std::is_copy_constructible_v<RealizedProtocol>);
static_assert(!std::is_default_constructible_v<RealizedProtocol>);
namespace {
PreparedProtocol prepare(ModuleOp source) {
  auto result = PreparedProtocol::prepare(source);
  require(bool(result), "valid source did not prepare");
  return std::move(*result);
}
void checked(const RealizedProtocol &owner) {
  auto original = owner.originalSnapshot();
  auto candidate = owner.candidateSnapshot();
  require(bool(original) && bool(candidate), "checked edge lost a side");
  if (auto failure = protocol::checkIdealOracleRealization(
          *original, *candidate, owner.realizationRecord()))
    throw std::runtime_error(toString(std::move(failure)));
}
void changeRelation(ModuleOp module) {
  auto unit = cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  auto declarations = unit.getBody().front().getOps<relation::DeclareOp>();
  require(!declarations.empty(), "fixture has no logical relation");
  (*declarations.begin()).setKey("test/changed-predicate");
  require(succeeded(verify(module)), "mutation must remain well formed");
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler silence(&context,
                                  [](Diagnostic &) { return success(); });
  auto file = MemoryBuffer::getFile(ZKC_REALIZED_FIXTURES "/common-input.mlir");
  require(bool(file), "missing common input fixture");
  auto text = (*file)->getBuffer();
  auto source = parseSourceString<ModuleOp>(text, &context);
  require(bool(source), "invalid common input fixture");
  auto prepared = prepare(*source);
  auto frozen = prepared.snapshot();
  auto owner = take(RealizedProtocol::ideal(std::move(prepared)));
  Cases cases;
  cases.run(
      "checked owner retains both sides and serialized interpretation", [&] {
        checked(owner);
        auto original = owner.originalSnapshot();
        require(OperationEquivalence::isEquivalentTo(
                    *original, *frozen, OperationEquivalence::IgnoreLocations),
                "realization altered the retained prepared original");
        auto record = take(json::parse(owner.realizationRecord()));
        auto entries = record.getAsObject()->getArray("entries");
        require(
            entries && entries->size() == 1 &&
                entries->front().getAsObject()->getObject("contracts") &&
                entries->front().getAsObject()->getObject("logical_interface"),
            "owned record lost logical associations");
      });
  cases.run("consumed preparation grants no second realization", [&] {
    refuses(RealizedProtocol::ideal(std::move(prepared)),
            "oracle-realization-source");
  });
  cases.run("candidate snapshot mutation cannot change checked ownership", [&] {
    auto original = owner.originalSnapshot();
    auto candidate = owner.candidateSnapshot();
    changeRelation(*candidate);
    auto failure = protocol::checkIdealOracleRealization(
        *original, *candidate, owner.realizationRecord());
    require(bool(failure), "changed actual predicate retained correspondence");
    consumeError(std::move(failure));
    checked(owner);
  });
  cases.run(
      "original and caller mutations cannot rebind the checked edge", [&] {
        auto original = owner.originalSnapshot();
        auto candidate = owner.candidateSnapshot();
        changeRelation(*original);
        changeRelation(*source);
        auto failure = protocol::checkIdealOracleRealization(
            *original, *candidate, owner.realizationRecord());
        require(bool(failure), "changed original retained correspondence");
        consumeError(std::move(failure));
        checked(owner);
      });
  cases.run("ordinary modules use an exact identity edge", [&] {
    auto ordinary = parseSourceString<ModuleOp>(R"mlir(
module { "protocol.module"() ({
  "protocol.func"() ({ ^bb0(%value: ui64):
    "protocol.return"(%value) : (ui64) -> ()
  }) {sym_name="main",function_type=(ui64)->ui64,roles=["V"],
      input_roles=[["V"]],output_roles=[["V"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
)mlir",
                                                &context);
    require(bool(ordinary), "invalid ordinary fixture");
    auto identity = take(RealizedProtocol::ideal(prepare(*ordinary)));
    checked(identity);
    auto left = identity.originalSnapshot(),
         right = identity.candidateSnapshot();
    require(OperationEquivalence::isEquivalentTo(
                *left, *right, OperationEquivalence::IgnoreLocations),
            "identity edge altered ordinary source");
    auto record = take(json::parse(identity.realizationRecord()));
    require(record.getAsObject()->getArray("entries")->empty(),
            "identity edge invented an oracle entry");
  });
  auto clausesFile =
      MemoryBuffer::getFile(ZKC_REALIZED_FIXTURES "/common-clauses.mlir");
  require(bool(clausesFile), "missing logical clause fixture");
  auto logical =
      parseSourceString<ModuleOp>((*clausesFile)->getBuffer(), &context);
  require(bool(logical), "logical clause fixture must be admitted");
  auto clauses = take(RealizedProtocol::ideal(prepare(*logical)));
  auto main = [](ModuleOp module) {
    auto unit = cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
    return cast<protocol_ir::MathematicalOp>(
        SymbolTable::lookupSymbolIn(unit, "main"));
  };
  auto rejects = [&](ModuleOp original, ModuleOp candidate, StringRef record,
                     StringRef code) {
    auto failure =
        protocol::checkIdealOracleRealization(original, candidate, record);
    require(bool(failure), "changed edge retained correspondence");
    require(namesIdentifier(toString(std::move(failure)), code),
            "unexpected correspondence refusal");
  };
  cases.run("logical clauses stay on the original signature", [&] {
    checked(clauses);
    auto original = clauses.originalSnapshot(),
         candidate = clauses.candidateSnapshot();
    require(main(*original).getContracts()->size() == 5,
            "original lost a clause");
    require(!main(*candidate).getContracts(),
            "native signature inherited logical clauses");
    require(main(*candidate)
                .getBody()
                .front()
                .getOps<protocol_ir::StatementOp>()
                .empty(),
            "native candidate inherited a logical statement");
    auto record = take(json::parse(clauses.realizationRecord()));
    auto entry =
        record.getAsObject()->getArray("entries")->front().getAsObject();
    auto contracts = entry->getObject("contracts");
    auto selections = contracts->getArray("statements");
    require(contracts->getArray("clauses")->size() == 5 &&
                selections->size() == 1 &&
                selections->front().getAsObject()->getInteger("operation") ==
                    1 &&
                selections->front().getAsObject()->getInteger("target") == 4,
            "record lost the original clause inventory or exact selection");
    require(
        entry->getObject("logical_interface")->getArray("outputs")->size() ==
                1 &&
            entry->getArray("result_references")->size() == 1 &&
            !entry->getArray("result_stores")->empty(),
        "returned anchor lost its actual representation associations");
  });
  cases.run("equal predicates do not merge named target selections", [&] {
    auto original = clauses.originalSnapshot(),
         candidate = clauses.candidateSnapshot();
    auto record = take(json::parse(clauses.realizationRecord()));
    auto entry =
        record.getAsObject()->getArray("entries")->front().getAsObject();
    (*entry->getObject("contracts")->getArray("statements"))[0].getAsObject()->
    operator[]("target") = 3;
    std::string changed;
    raw_string_ostream(changed) << record;
    rejects(*original, *candidate, changed, "oracle-realization-record");
  });
  cases.run("identical native code cannot substitute a logical target", [&] {
    auto original = clauses.originalSnapshot(),
         candidate = clauses.candidateSnapshot();
    auto statements =
        main(*original).getBody().front().getOps<protocol_ir::StatementOp>();
    (*statements.begin())
        ->setAttr("target", StringAttr::get(&context, "decoy"));
    require(succeeded(verify(*original)), "alternate target must be admitted");
    auto changed = take(RealizedProtocol::ideal(prepare(*original)));
    checked(changed);
    auto other = changed.candidateSnapshot();
    require(OperationEquivalence::isEquivalentTo(
                *candidate, *other, OperationEquivalence::IgnoreLocations),
            "logical target unexpectedly changed native code");
    require(changed.realizationRecord() != clauses.realizationRecord(),
            "record collapsed distinct logical selections");
    rejects(*original, *candidate, clauses.realizationRecord(),
            "oracle-realization-record");
  });
  cases.run("candidate cannot insert its own ordinary clause", [&] {
    auto original = owner.originalSnapshot(),
         candidate = owner.candidateSnapshot();
    main(*candidate)
        ->setAttr("contracts", main(*original)->getAttr("contracts"));
    require(succeeded(verify(*candidate)),
            "ordinary clause mutation must be admitted");
    rejects(*original, *candidate, owner.realizationRecord(),
            "oracle-common-body");
    checked(owner);
  });
  return cases.result();
}
