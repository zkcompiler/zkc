#include "../lib/Transforms/OracleCommonRealization.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Observation.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/Support/FormatVariadic.h"
#include <filesystem>
#include <fstream>
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::test;
namespace pir = protocol_ir;
namespace {
Error checkCandidate(ModuleOp prepared, const OracleCommonRealization &actual) {
  auto record = serializeIdealOracleRealization(prepared, actual);
  if (!record)
    return record.takeError();
  return checkIdealOracleRealization(prepared, actual.module.get(), *record);
}
void checked(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
void refused(Error error, StringRef code) {
  require(bool(error), "expected refusal");
  auto message = toString(std::move(error));
  require(namesIdentifier(message, code), "unexpected refusal: " + message);
}
std::string print(Operation *op) {
  std::string text;
  raw_string_ostream stream(text);
  op->print(stream);
  return text;
}
} // namespace
int main(int argc, char **argv) {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  std::string diagnostics;
  ScopedDiagnosticHandler capture(&context, [&](Diagnostic &message) {
    raw_string_ostream stream(diagnostics);
    message.print(stream);
    return success();
  });
  Cases cases;
  bool compile = argc > 1 && (argc < 3 || StringRef(argv[2]) != "checks");
  bool mutations = argc < 3 || StringRef(argv[2]) != "compile";
  bool selectedFixture = false;
  for (StringRef fixture :
       {"common-recurrence", "common-holders", "common-input", "common-shape",
        "common-contents", "common-views", "common-entries", "common-return",
        "common-empty", "common-clauses"}) {
    if (argc > 3 && fixture != argv[3])
      continue;
    selectedFixture = true;
    std::ifstream in(std::filesystem::path(ZKC_ORACLE_FIXTURES) /
                     (fixture.str() + ".mlir"));
    std::string text((std::istreambuf_iterator<char>(in)), {});
    auto source =
        parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
    require(bool(source) && succeeded(verify(*source)),
            "source: " + diagnostics);
    auto prepared = mathematical::prepareProtocol(*source, false);
    require(bool(prepared), "prepare: " + diagnostics);
    auto frozen = print(*prepared);
    auto emitted = emitIdealOracleRealization(*prepared);
    require(bool(emitted),
            "emission: " +
                (emitted ? std::string() : toString(emitted.takeError())) +
                "\n" + diagnostics);
    auto candidate = std::move(*emitted);
    unsigned expectedEntries =
        fixture == "common-return"                                   ? 3
        : (fixture == "common-entries" || fixture == "common-empty") ? 2
                                                                     : 1;
    require(candidate.entries.size() == expectedEntries,
            "wrong oracle entry inventory");
    auto mainEntry = find_if(candidate.entries, [](const auto &item) {
      return item.entry == "main";
    });
    require(mainEntry != candidate.entries.end(), "missing main entry");
    auto &entry = *mainEntry;
    cases.run(fixture + " actual common body", [&] {
      checked(checkCandidate(*prepared, candidate));
      require(print(*prepared) == frozen,
              "emission or reading changed original");
      bool leftover = false;
      candidate.module->walk([&](Operation *op) {
        leftover |=
            op->getName().getStringRef().starts_with("protocol.oracle_") ||
            isa<pir::OracleDefinitionOp>(op);
        for (Type type : op->getOperandTypes())
          leftover |= isa<pir::OracleHandleType, pir::OracleSequenceType>(type);
        for (Type type : op->getResultTypes())
          leftover |= isa<pir::OracleHandleType, pir::OracleSequenceType>(type);
      });
      require(!leftover, "logical oracle survived common realization");
    });
    auto unit =
        cast<pir::ProtocolModuleOp>(candidate.module->getBody()->front());
    auto program =
        cast<pir::MathematicalOp>(SymbolTable::lookupSymbolIn(unit, "main"));
    if (mutations) {
      cases.run(fixture + " independent record and fresh candidate read", [&] {
        auto record =
            take(serializeIdealOracleRealization(*prepared, candidate));
        auto copy = parseSourceString<ModuleOp>(print(*candidate.module),
                                                ParserConfig(&context, false));
        require(bool(copy), "candidate text did not parse");
        checked(checkIdealOracleRealization(*prepared, *copy, record));
        require(record ==
                    take(serializeIdealOracleRealization(*prepared, candidate)),
                "record is not deterministic");
      });
    }
    if (mutations && fixture == "common-input") {
      auto record = take(serializeIdealOracleRealization(*prepared, candidate));
      auto changed = [&](StringRef name,
                         llvm::function_ref<void(json::Object &)> change) {
        cases.run("record refuses " + name, [&] {
          auto parsed = take(json::parse(record));
          change(*parsed.getAsObject());
          std::string text;
          raw_string_ostream(text) << parsed;
          refused(
              checkIdealOracleRealization(*prepared, *candidate.module, text),
              "oracle-realization-record");
        });
      };
      changed("missing contract", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        entry.getObject("contracts")->getArray("clauses")->pop_back();
      });
      changed("contract component port", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        auto &clause = *(*entry.getObject("contracts")->getArray("clauses"))[0]
                            .getAsObject();
        auto &operand = *(*clause.getObject("subject")->getArray("operands"))[0]
                             .getAsObject();
        (*operand.getObject("component"))["port"] = 1;
      });
      changed("contract relation", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        auto &clause = *(*entry.getObject("contracts")->getArray("clauses"))[0]
                            .getAsObject();
        (*clause.getObject("subject"))["relation"] = "other";
      });
      changed("continuation residual direction", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        auto &clause = *(*entry.getObject("contracts")->getArray("clauses"))[2]
                            .getAsObject();
        auto &operand =
            *(*clause.getObject("residual")->getArray("operands"))[0]
                 .getAsObject();
        (*operand.getObject("component"))["direction"] = "input";
      });
      changed("invented statement selection", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        entry.getObject("contracts")
            ->getArray("statements")
            ->push_back(json::Object{{"operation", 0}, {"target", 0}});
      });
      changed("unknown root field",
              [&](auto &value) { value["extra"] = true; });
      changed("other version", [&](auto &value) {
        value["format"] = "zkc.oracle-realization/1";
      });
      changed("other mode", [&](auto &value) { value["mode"] = "merkle"; });
      changed("unknown entry field", [&](auto &value) {
        (*value.getArray("entries"))[0].getAsObject()->insert({"extra", true});
      });
      changed("duplicate type", [&](auto &value) {
        auto &types = *value.getArray("types");
        types.push_back(types.front());
      });
      changed("unused type", [&](auto &value) {
        value.getArray("types")->push_back("bytes");
      });
      changed("missing helper", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        auto &controller = *(*entry.getArray("controllers"))[0].getAsObject();
        (*controller.getObject("body"))["initialize"] =
            "not_a_generated_helper";
      });
      changed("foreign type index", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        auto &controller = *(*entry.getArray("controllers"))[0].getAsObject();
        (*controller.getObject("body")->getArray("state"))[0] = 999999;
      });
      changed("changed source constructor", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        (*(*entry.getArray("constructors"))[0]
              .getAsObject())["maximum_instances"] = 2;
      });
      changed("changed occurrence path", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        (*(*entry.getArray("occurrences"))[0].getAsObject())["path"] =
            json::Array{999};
      });
      changed("changed output role", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        (*entry.getObject("interface"))["output_roles"] =
            json::Array{json::Array{"P"}};
      });
      auto inputPair = [&](json::Object &value) -> json::Object & {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        return *(*entry.getObject("logical_interface")->getArray("inputs"))[0]
                    .getAsObject();
      };
      changed("holder and receiver data ports swapped", [&](auto &value) {
        auto &pair = inputPair(value);
        std::swap(*pair.get("data"), *pair.get("anchor"));
      });
      changed("logical holder changed",
              [&](auto &value) { inputPair(value)["holder"] = "V"; });
      changed("logical receiver changed", [&](auto &value) {
        inputPair(value)["receivers"] = json::Array{"P"};
      });
      changed("logical input association dropped", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        (*entry.getObject("logical_interface"))["inputs"] = json::Array{};
      });
      changed("declaration order", [&](auto &value) {
        auto &declarations = *value.getArray("declarations");
        std::swap(declarations[0], declarations[1]);
      });
      cases.run("record refuses an oversized type table", [&] {
        auto parsed = take(json::parse(record));
        auto &types = *parsed.getAsObject()->getArray("types");
        while (types.size() <= 4096)
          types.push_back("ui64");
        std::string text;
        raw_string_ostream(text) << parsed;
        refused(checkIdealOracleRealization(*prepared, *candidate.module, text),
                "oracle-realization-record-limit");
      });
      cases.run("record refuses duplicate decoded keys", [&] {
        std::string duplicate = record;
        duplicate.insert(1, "\"mode\":\"ideal\",");
        refused(checkIdealOracleRealization(*prepared, *candidate.module,
                                            duplicate),
                "oracle-realization-record");
      });
      cases.run("record binds generated binding names", [&] {
        runtime::BindingOp binding;
        unit.walk([&](runtime::BindingOp op) {
          if (!binding && op.getSymName().starts_with("_oracle_"))
            binding = op;
        });
        require(bool(binding), "missing generated binding");
        auto original = binding.getSymNameAttr();
        auto replacement = StringAttr::get(&context, "changed_binding");
        require(succeeded(SymbolTable::replaceAllSymbolUses(binding,
                                                            replacement, unit)),
                "could not rename binding uses");
        binding->setAttr("sym_name", replacement);
        auto restore = llvm::scope_exit([&] {
          (void)SymbolTable::replaceAllSymbolUses(binding, original, unit);
          binding->setAttr("sym_name", original);
        });
        require(succeeded(verify(*candidate.module)),
                "renamed binding is malformed");
        refused(
            checkIdealOracleRealization(*prepared, *candidate.module, record),
            "oracle-realization-record");
      });
    }
    if (mutations && fixture == "common-empty") {
      cases.run("uninhabited handle uses retain a refusing controller", [&] {
        const auto &selected = candidate.entries[1];
        require(selected.entry == "at" && selected.controllers.size() == 1 &&
                    selected.allocators.empty(),
                "uninhabited entry layout");
        require(selected.controllers[0].body.constructors.empty() &&
                    selected.controllers[0].body.stores.empty(),
                "manufactured anchor or store");
        exec::RejectOp rejection;
        unit.walk([&](exec::RejectOp op) {
          if (!rejection && op.getSite() == "no_constructor")
            rejection = op;
        });
        require(bool(rejection), "missing uninhabited dispatch refusal");
        auto reason = rejection.getReasonAttr();
        auto restore =
            llvm::scope_exit([&] { rejection.setReasonAttr(reason); });
        rejection.setReason("abort");
        require(succeeded(verify(*candidate.module)),
                "changed cause malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-controller-body");
      });
      cases.run("empty sequence has no allocated anchor or controller", [&] {
        require(entry.controllers.empty() && entry.allocators.empty() &&
                    entry.locals.empty(),
                "invented an anchor for an empty collection");
      });
      cases.run("empty length cannot become an unrelated input", [&] {
        auto returned =
            cast<pir::MathematicalReturnOp>(program.getBody().front().back());
        Value original = returned->getOperand(0);
        auto restore =
            llvm::scope_exit([&] { returned->setOperand(0, original); });
        returned->setOperand(0, program.getBody().front().getArgument(0));
        require(succeeded(verify(*candidate.module)),
                "empty mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
    }
    if (mutations && fixture == "common-return") {
      cases.run(
          "returned logical pairs use distinct actual holder leaves", [&] {
            auto record = take(json::parse(
                take(serializeIdealOracleRealization(*prepared, candidate))));
            auto &entries = *record.getAsObject()->getArray("entries");
            auto found = find_if(entries, [](const auto &item) {
              return item.getAsObject()->getString("entry") == "main";
            });
            require(found != entries.end(), "missing main record");
            auto &outputs = *found->getAsObject()
                                 ->getObject("logical_interface")
                                 ->getArray("outputs");
            require(outputs.size() == 3, "wrong returned logical inventory");
            for (unsigned i = 0; i < outputs.size(); ++i) {
              auto &pair = *outputs[i].getAsObject();
              require(pair.getInteger("data") == 2 * i &&
                          pair.getInteger("anchor") == 2 * i + 1 &&
                          pair.getString("holder") == "P",
                      "logical aliases lost canonical pairing");
            }
            (*outputs[0].getAsObject())["data"] = 2;
            std::string changed;
            raw_string_ostream(changed) << record;
            refused(checkIdealOracleRealization(*prepared, *candidate.module,
                                                changed),
                    "oracle-realization-record");
          });
      cases.run("returned aliases share role-specific support stores", [&] {
        require(entry.resultStores == std::vector<OracleResultStore>(
                                          {{0, 1, 7}, {1, 1, 8}, {2, 1, 9}}),
                "result store layout differs from source custody");
        require(entry.resultReferences ==
                    std::vector<OracleResultReference>({{1, "V", {7, 8, 9}},
                                                        {3, "V", {7, 8, 9}},
                                                        {5, "V", {7, 8, 9}}}),
                "result reference layout lost aliases or source positions");
      });
      cases.run("changed logical result position refuses", [&] {
        auto original = entry.resultReferences[0].result;
        auto restore = llvm::scope_exit(
            [&] { entry.resultReferences[0].result = original; });
        entry.resultReferences[0].result = 3;
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("changed support role refuses", [&] {
        auto original = entry.resultStores[0].role;
        auto restore =
            llvm::scope_exit([&] { entry.resultStores[0].role = original; });
        entry.resultStores[0].role = 0;
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("changed native store position refuses", [&] {
        auto original = entry.resultStores[0].port;
        auto restore =
            llvm::scope_exit([&] { entry.resultStores[0].port = original; });
        entry.resultStores[0].port = 8;
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("missing support association refuses", [&] {
        auto &ports = entry.resultReferences[0].storePorts;
        auto original = ports.back();
        ports.pop_back();
        auto restore = llvm::scope_exit([&] { ports.push_back(original); });
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("same-typed returned reference substitution refuses", [&] {
        auto *returned = program.getBody().front().getTerminator();
        auto original = returned->getOperand(1);
        auto restore =
            llvm::scope_exit([&] { returned->setOperand(1, original); });
        returned->setOperand(1, returned->getOperand(5));
        require(succeeded(verify(*candidate.module)),
                "returned reference mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("stale returned store refuses", [&] {
        auto *returned = program.getBody().front().getTerminator();
        auto original = returned->getOperand(9);
        Value empty;
        for (auto &op : program.getBody().front())
          if (op.getName().getStringRef() == "data.sequence_empty" &&
              op.getResult(0).getType() == original.getType())
            empty = op.getResult(0);
        require(bool(empty), "missing initial virtual store");
        auto restore =
            llvm::scope_exit([&] { returned->setOperand(9, original); });
        returned->setOperand(9, empty);
        require(succeeded(verify(*candidate.module)),
                "returned store mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
    }
    if (mutations && fixture == "common-entries") {
      cases.run("shared virtual entries have distinct generated locals", [&] {
        require(candidate.entries[0].entry == "main" &&
                    candidate.entries[1].entry == "companion",
                "source entry order changed");
        require(candidate.entries[0].locals[0].getSymName() !=
                    candidate.entries[1].locals[0].getSymName(),
                "entry-local symbol collision");
        require(candidate.entries[0].locals[0].getSymName() !=
                        "_oracle_common_local_0_0" &&
                    candidate.entries[0].allocators[0][0].getSymName() !=
                        "_oracle_allocate_0_0",
                "authored symbol was reused");
        auto repeated = emitIdealOracleRealization(*prepared);
        require(bool(repeated), "repeat emission failed");
        require(print(*repeated->module) == print(*candidate.module),
                "emission depends on mutable naming state");
      });
      cases.run("reordered entry records refuse", [&] {
        std::swap(candidate.entries[0], candidate.entries[1]);
        auto restore = llvm::scope_exit(
            [&] { std::swap(candidate.entries[0], candidate.entries[1]); });
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("missing entry records refuse", [&] {
        auto missing = std::move(candidate.entries.back());
        candidate.entries.pop_back();
        auto restore = llvm::scope_exit(
            [&] { candidate.entries.push_back(std::move(missing)); });
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("duplicate entry identities refuse", [&] {
        auto original = candidate.entries[1].entry;
        auto restore =
            llvm::scope_exit([&] { candidate.entries[1].entry = original; });
        candidate.entries[1].entry = candidate.entries[0].entry;
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("same-typed entry body substitution refuses", [&] {
        auto companion = cast<pir::MathematicalOp>(
            SymbolTable::lookupSymbolIn(unit, "companion"));
        auto exchange = [&] {
          Region temporary;
          temporary.takeBody(program.getBody());
          program.getBody().takeBody(companion.getBody());
          companion.getBody().takeBody(temporary);
        };
        exchange();
        auto restore = llvm::scope_exit(exchange);
        require(succeeded(verify(*candidate.module)),
                "entry body swap is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("ordinary sibling body remains checked", [&] {
        auto ordinary = cast<pir::MathematicalOp>(
            SymbolTable::lookupSymbolIn(unit, "ordinary"));
        auto *returned = ordinary.getBody().front().getTerminator();
        auto original = returned->getOperand(0);
        auto restore =
            llvm::scope_exit([&] { returned->setOperand(0, original); });
        returned->setOperand(0, ordinary.getBody().front().getArgument(1));
        require(succeeded(verify(*candidate.module)),
                "ordinary sibling mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("ordinary-only modules use the same complete reader", [&] {
        OwningOpRef<ModuleOp> plain(cast<ModuleOp>(prepared->clone()));
        auto owner = cast<pir::ProtocolModuleOp>(plain->getBody()->front());
        for (auto &op : make_early_inc_range(owner.getBody().front()))
          if (isa<pir::OracleDefinitionOp>(op) ||
              (isa<pir::MathematicalOp>(op) &&
               SymbolTable::getSymbolName(&op).getValue() != "ordinary"))
            op.erase();
        auto realized = emitIdealOracleRealization(*plain);
        require(bool(realized), "ordinary emission failed");
        require(realized->entries.empty(), "invented oracle entry");
        checked(checkCandidate(*plain, *realized));
        require(print(*plain) == print(*realized->module),
                "ordinary declarations changed");
        auto after =
            cast<pir::ProtocolModuleOp>(realized->module->getBody()->front());
        auto ordinary = cast<pir::MathematicalOp>(
            SymbolTable::lookupSymbolIn(after, "ordinary"));
        ordinary.getBody().front().getTerminator()->setOperand(
            0, ordinary.getBody().front().getArgument(1));
        refused(checkCandidate(*plain, *realized), "oracle-common-body");
      });
    }
    if (mutations && fixture == "common-views") {
      cases.run("rebindings preserve the actual selected anchor", [&] {
        SmallVector<pir::RestrictRolesOp> rebindings;
        program.walk([&](pir::RestrictRolesOp op) {
          if (op.getRoles().size() == 2)
            rebindings.push_back(op);
        });
        require(rebindings.size() == 2, "expected two component rebindings");
        auto original = rebindings[1].getInput();
        auto restore = llvm::scope_exit(
            [&] { rebindings[1].getInputMutable().set(original); });
        rebindings[1].getInputMutable().set(rebindings[0].getInput());
        require(succeeded(verify(*candidate.module)),
                "rebind mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("pair-only component views do not materialize data", [&] {
        unsigned materializations = 0;
        program.walk([&](pir::LocalCallOp op) {
          materializations += op.getSite().ends_with("_component_data");
        });
        require(materializations == 1,
                "unused component data was materialized");
      });
    }
    if (mutations && fixture == "common-contents") {
      auto holder = find_if(entry.controllers, [](const auto &item) {
        return item.access == OracleControllerAccess::Holder;
      });
      require(holder != entry.controllers.end(), "missing holder controller");
      cases.run("holder domain excludes unrelated received anchors", [&] {
        require(holder->body.constructors.size() == 3,
                "holder domain includes unrelated received data");
      });
      cases.run("holder access metadata cannot widen custody", [&] {
        auto restore = llvm::scope_exit(
            [&] { holder->body.access = OracleControllerAccess::Holder; });
        holder->body.access = OracleControllerAccess::Available;
        refused(checkCandidate(*prepared, candidate), "oracle-controller-body");
      });
      cases.run("contents checks actual materialization upper bound", [&] {
        exec::RangeOp rows;
        candidate.module->walk([&](exec::RangeOp op) {
          if (op.getSite() == "rows" && !rows)
            rows = op;
        });
        require(bool(rows), "missing contents loop");
        // Range operands begin with scope, lower, upper. Changing the upper
        // to zero is formed but would silently drop the virtual table.
        auto upper = rows->getOperand(2);
        auto restore = llvm::scope_exit([&] { rows->setOperand(2, upper); });
        rows->setOperand(2, rows->getOperand(1));
        require(succeeded(verify(*candidate.module)),
                "loop mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-controller-body");
      });
      cases.run("shape observers cannot substitute structural leaf count", [&] {
        auto available = find_if(entry.controllers, [](const auto &item) {
          return item.access == OracleControllerAccess::Available &&
                 item.role == "P";
        });
        auto original = available->body.rowCounts[0];
        auto restore =
            llvm::scope_exit([&] { available->body.rowCounts[0] = original; });
        available->body.rowCounts[0] = available->body.leafCounts[0];
        refused(checkCandidate(*prepared, candidate), "oracle-controller-body");
      });
    }
    if (mutations && fixture != "common-empty") {
      SmallVector<pir::LocalCallOp> calls;
      program.walk([&](pir::LocalCallOp call) { calls.push_back(call); });
      cases.run(fixture + " changed query occurrence", [&] {
        auto found = find_if(calls, [](auto call) {
          return call.getSite().ends_with("_query");
        });
        require(found != calls.end(), "missing query call");
        auto original = found->getSiteAttr();
        auto restore = llvm::scope_exit([&] { found->setSiteAttr(original); });
        found->setSite("changed");
        require(succeeded(verify(*candidate.module)), "mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
        found->setSiteAttr(original);
      });
      if (fixture == "common-recurrence" || fixture == "common-holders")
        cases.run(fixture + " substituted same-typed actual anchor", [&] {
          auto found = find_if(calls, [](auto call) {
            return call.getSite().ends_with("_query");
          });
          auto original = found->getInputs()[0];
          Value replacement;
          for (auto assembly :
               program.getBody().front().getOps<pir::AssembleRolesOp>())
            if (assembly.getOutput().getType() == original.getType() &&
                assembly.getOutput() != original) {
              replacement = assembly.getOutput();
              break;
            }
          require(bool(replacement), "missing alternative anchor");
          auto restore = llvm::scope_exit(
              [&] { found->getInputsMutable()[0].set(original); });
          found->getInputsMutable()[0].set(replacement);
          require(succeeded(verify(*candidate.module)),
                  "anchor mutation is malformed");
          refused(checkCandidate(*prepared, candidate), "oracle-common-body");
          found->getInputsMutable()[0].set(original);
        });
      if (fixture != "common-input" && fixture != "common-clauses")
        cases.run(fixture + " changed delivery occurrence", [&] {
          pir::ExchangeOp exchange;
          program.walk([&](pir::ExchangeOp op) {
            if (!exchange)
              exchange = op;
          });
          require(bool(exchange), "missing delivery");
          auto original = exchange.getSiteAttr();
          auto restore =
              llvm::scope_exit([&] { exchange.setSiteAttr(original); });
          exchange.setSite("other_delivery");
          require(succeeded(verify(*candidate.module)),
                  "mutation is malformed");
          refused(checkCandidate(*prepared, candidate), "oracle-common-body");
          exchange.setSiteAttr(original);
        });
      cases.run(fixture + " changed shape predicate", [&] {
        exec::ApplyOp predicate;
        entry.locals.front().walk([&](exec::ApplyOp op) {
          auto binding =
              SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                  op, op.getBindingAttr());
          if (binding && binding.getContract() == "index.equal" && !predicate)
            predicate = op;
        });
        require(bool(predicate), "missing predicate");
        auto first = predicate.getInputs()[0],
             second = predicate.getInputs()[1];
        auto restore = llvm::scope_exit(
            [&] { predicate.getInputsMutable()[1].set(second); });
        predicate.getInputsMutable()[1].set(first);
        require(succeeded(verify(*candidate.module)), "mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
        predicate.getInputsMutable()[1].set(second);
      });
      cases.run(fixture + " extra body refuses", [&] {
        auto extra = cast<func::FuncOp>(entry.locals.front()->clone());
        extra.setSymName("unrelated");
        unit.getBody().front().push_back(extra);
        auto restore = llvm::scope_exit([&] { extra.erase(); });
        require(succeeded(verify(*candidate.module)), "mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run(fixture + " changed helper occurrence origin", [&] {
        auto helper = entry.locals.front();
        auto original = helper->getAttr("runtime.origin");
        auto restore = llvm::scope_exit(
            [&] { helper->setAttr("runtime.origin", original); });
        Builder builder(&context);
        helper->setAttr(
            "runtime.origin",
            builder.getArrayAttr({builder.getStringAttr("different"),
                                  builder.getArrayAttr({})}));
        require(succeeded(verify(*candidate.module)),
                "origin mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      if (fixture == "common-recurrence") {
        pir::RepeatOp repeat;
        program.walk([&](pir::RepeatOp op) { repeat = op; });
        cases.run("stale loop store refuses", [&] {
          auto yield = cast<pir::ProtocolYieldOp>(
              repeat.getBody().front().getTerminator());
          unsigned changed = 0;
          for (unsigned i = 1; i < yield.getInputs().size(); ++i)
            if (yield.getInputs()[i] !=
                repeat.getBody().front().getArgument(i + 1)) {
              changed = i;
              break;
            }
          require(changed != 0, "no store was updated");
          auto original = yield.getInputs()[changed];
          auto restore = llvm::scope_exit(
              [&] { yield.getInputsMutable()[changed].set(original); });
          yield.getInputsMutable()[changed].set(
              repeat.getBody().front().getArgument(changed + 1));
          require(succeeded(verify(*candidate.module)),
                  "stale store is malformed");
          refused(checkCandidate(*prepared, candidate), "oracle-common-body");
          yield.getInputsMutable()[changed].set(original);
        });
      }
    }
    if (compile) {
      SmallVector<StringRef> selected{"main"};
      if (fixture == "common-entries")
        append_range(selected, ArrayRef<StringRef>{"companion", "ordinary"});
      if (fixture == "common-return")
        selected.push_back("wrapper");
      if (fixture == "common-empty")
        selected.push_back("at");
      for (StringRef selectedEntry : selected)
        cases.run(fixture + " physical entry " + selectedEntry, [&] {
          auto logicalSource = print(*source);
          CompilationObservation observation;
          RunOptions options;
          options.entry = selectedEntry.str();
          options.observations = &observation;
          auto compiled = compileRun(logicalSource, "oracle-common.mlir",
                                     options, registry);
          std::string name = fixture.str();
          if (selectedEntry != "main")
            name += "-" + selectedEntry.str();
          if (argc > 1) {
            std::filesystem::create_directories(argv[1]);
            auto path =
                std::filesystem::path(argv[1]) / (name + ".compilation.json");
            std::ofstream(path) << formatv("{0:2}", observation.json()).str();
          }
          require(
              bool(compiled),
              "physical compilation: " +
                  (compiled ? std::string() : toString(compiled.takeError())) +
                  diagnostics);
          auto edge = compiled->compilation.oracleRealizationSnapshot();
          require(bool(edge), "production compilation lost realization");
          checked(checkIdealOracleRealization(*edge->original, *edge->candidate,
                                              edge->record));
          require(print(*edge->original) == frozen,
                  "production changed the retained logical subject");
          require(edge->record == take(serializeIdealOracleRealization(
                                      *prepared, candidate)),
                  "production record differs from the independently inspected "
                  "edge");
          if (argc > 1) {
            auto base = std::filesystem::path(argv[1]) / name;
            std::ofstream(base.string() + ".mlir") << print(*edge->candidate);
            std::ofstream(base.string() + ".original.mlir")
                << print(*edge->original);
            std::ofstream(base.string() + ".realization.json") << edge->record;
            std::ofstream(base.string() + ".bundle") << compiled->bundle;
          }
        });
    }
  }
  if (!selectedFixture) {
    errs() << "unknown common oracle fixture\n";
    return 1;
  }
  return cases.result();
}
