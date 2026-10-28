#include "../lib/Transforms/OracleCommonRealization.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/ScopeExit.h"
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
  for (StringRef fixture : {"common-recurrence", "common-holders",
                            "common-input", "common-shape"}) {
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
    auto emitted = emitIdealOracleRealization(*prepared, "main");
    require(bool(emitted),
            "emission: " +
                (emitted ? std::string() : toString(emitted.takeError())) +
                "\n" + diagnostics);
    auto candidate = std::move(*emitted);
    cases.run(fixture + " actual common body", [&] {
      checked(checkIdealOracleRealization(*prepared, "main", candidate));
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
        refused(checkIdealOracleRealization(*prepared, "main", candidate),
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
          refused(checkIdealOracleRealization(*prepared, "main", candidate),
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
          refused(checkIdealOracleRealization(*prepared, "main", candidate),
                  "oracle-common-body");
          exchange.setSiteAttr(original);
        });
      cases.run(fixture + " changed shape predicate", [&] {
        exec::ApplyOp predicate;
        candidate.locals.front().walk([&](exec::ApplyOp op) {
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
        refused(checkIdealOracleRealization(*prepared, "main", candidate),
                "oracle-common-body");
        predicate.getInputsMutable()[1].set(second);
      });
      cases.run(fixture + " extra body refuses", [&] {
        auto extra = cast<func::FuncOp>(candidate.locals.front()->clone());
        extra.setSymName("unrelated");
        unit.getBody().front().push_back(extra);
        auto restore = llvm::scope_exit([&] { extra.erase(); });
        require(succeeded(verify(*candidate.module)), "mutation is malformed");
        refused(checkIdealOracleRealization(*prepared, "main", candidate),
                "oracle-common-body");
      });
      cases.run(fixture + " changed helper occurrence origin", [&] {
        auto helper = candidate.locals.front();
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
        refused(checkIdealOracleRealization(*prepared, "main", candidate),
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
          refused(checkIdealOracleRealization(*prepared, "main", candidate),
                  "oracle-common-body");
          yield.getInputsMutable()[changed].set(original);
        });
      }
    }
    if (compile)
      cases.run(fixture + " ordinary physical pipeline", [&] {
        auto realized = print(*candidate.module);
        auto compiled =
            compileRun(realized, "oracle-common.mlir", {}, registry);
        require(
            bool(compiled),
            "physical compilation: " +
                (compiled ? std::string() : toString(compiled.takeError())) +
                diagnostics);
        if (argc > 1) {
          std::filesystem::create_directories(argv[1]);
          auto base = std::filesystem::path(argv[1]) / fixture.str();
          std::ofstream(base.string() + ".mlir") << realized;
          std::ofstream(base.string() + ".bundle") << compiled->bundle;
        }
      });
  }
  return cases.result();
}
