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
  for (StringRef fixture :
       {"common-recurrence", "common-holders", "common-input", "common-shape",
        "common-contents", "common-views", "common-entries"}) {
    if (argc > 3 && fixture != argv[3])
      continue;
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
    require(candidate.entries.size() == (fixture == "common-entries" ? 2 : 1),
            "wrong oracle entry inventory");
    auto &entry = candidate.entries.front();
    cases.run(fixture + " actual common body", [&] {
      checked(checkIdealOracleRealization(*prepared, candidate));
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
        refused(checkIdealOracleRealization(*prepared, candidate),
                "oracle-common-body");
      });
      cases.run("missing entry records refuse", [&] {
        auto missing = std::move(candidate.entries.back());
        candidate.entries.pop_back();
        auto restore = llvm::scope_exit(
            [&] { candidate.entries.push_back(std::move(missing)); });
        refused(checkIdealOracleRealization(*prepared, candidate),
                "oracle-common-body");
      });
      cases.run("duplicate entry identities refuse", [&] {
        auto original = candidate.entries[1].entry;
        auto restore =
            llvm::scope_exit([&] { candidate.entries[1].entry = original; });
        candidate.entries[1].entry = candidate.entries[0].entry;
        refused(checkIdealOracleRealization(*prepared, candidate),
                "oracle-common-body");
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
        refused(checkIdealOracleRealization(*prepared, candidate),
                "oracle-common-body");
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
        refused(checkIdealOracleRealization(*prepared, candidate),
                "oracle-common-body");
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
        checked(checkIdealOracleRealization(*plain, *realized));
        require(print(*plain) == print(*realized->module),
                "ordinary declarations changed");
        auto after =
            cast<pir::ProtocolModuleOp>(realized->module->getBody()->front());
        auto ordinary = cast<pir::MathematicalOp>(
            SymbolTable::lookupSymbolIn(after, "ordinary"));
        ordinary.getBody().front().getTerminator()->setOperand(
            0, ordinary.getBody().front().getArgument(1));
        refused(checkIdealOracleRealization(*plain, *realized),
                "oracle-common-body");
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
        refused(checkIdealOracleRealization(*prepared, candidate),
                "oracle-common-body");
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
        refused(checkIdealOracleRealization(*prepared, candidate),
                "oracle-controller-body");
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
        refused(checkIdealOracleRealization(*prepared, candidate),
                "oracle-controller-body");
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
        refused(checkIdealOracleRealization(*prepared, candidate),
                "oracle-controller-body");
      });
    }
    if (mutations) {
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
        refused(checkIdealOracleRealization(*prepared, candidate),
                "oracle-common-body");
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
          refused(checkIdealOracleRealization(*prepared, candidate),
                  "oracle-common-body");
          found->getInputsMutable()[0].set(original);
        });
      if (fixture != "common-input")
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
          refused(checkIdealOracleRealization(*prepared, candidate),
                  "oracle-common-body");
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
        refused(checkIdealOracleRealization(*prepared, candidate),
                "oracle-common-body");
        predicate.getInputsMutable()[1].set(second);
      });
      cases.run(fixture + " extra body refuses", [&] {
        auto extra = cast<func::FuncOp>(entry.locals.front()->clone());
        extra.setSymName("unrelated");
        unit.getBody().front().push_back(extra);
        auto restore = llvm::scope_exit([&] { extra.erase(); });
        require(succeeded(verify(*candidate.module)), "mutation is malformed");
        refused(checkIdealOracleRealization(*prepared, candidate),
                "oracle-common-body");
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
        refused(checkIdealOracleRealization(*prepared, candidate),
                "oracle-common-body");
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
          refused(checkIdealOracleRealization(*prepared, candidate),
                  "oracle-common-body");
          yield.getInputsMutable()[changed].set(original);
        });
      }
    }
    if (compile) {
      SmallVector<StringRef> selected{"main"};
      if (fixture == "common-entries")
        append_range(selected, ArrayRef<StringRef>{"companion", "ordinary"});
      for (StringRef selectedEntry : selected)
        cases.run(fixture + " physical entry " + selectedEntry, [&] {
          auto realized = print(*candidate.module);
          CompilationObservation observation;
          RunOptions options;
          options.entry = selectedEntry.str();
          options.observations = &observation;
          auto compiled =
              compileRun(realized, "oracle-common.mlir", options, registry);
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
          if (argc > 1) {
            auto base = std::filesystem::path(argv[1]) / name;
            std::ofstream(base.string() + ".mlir") << realized;
            std::ofstream(base.string() + ".bundle") << compiled->bundle;
          }
        });
    }
  }
  return cases.result();
}
