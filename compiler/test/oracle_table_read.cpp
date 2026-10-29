#include "../lib/Transforms/OracleTableRead.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include <filesystem>
#include <fstream>
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::test;
namespace {
OwningOpRef<ModuleOp> fresh(MLIRContext &context) {
  return parseSourceString<ModuleOp>(R"mlir(
module { "protocol.module"() ({
 "protocol.func"() ({ %ok = arith.constant true
 "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",function_type=()->i1,roles=["V"],input_roles=[],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir",
                                     &context);
}
std::string client(ModuleOp candidate, func::FuncOp read,
                   protocol_ir::OracleKindAttr kind,
                   const DialectRegistry &registry) {
  auto unit = cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  SymbolTable::lookupSymbolIn(unit, "main")->erase();
  OpBuilder builder(candidate.getContext());
  auto loc = candidate.getLoc();
  auto index =
      IntegerType::get(candidate.getContext(), 64, IntegerType::Unsigned);
  auto owner = builder.getArrayAttr({builder.getStringAttr("V")});
  auto observer = builder.getArrayAttr({builder.getStringAttr("Observer")});
  SmallVector<Type> inputs{kind.getDataType(), index, index, index};
  OperationState state(loc, "protocol.func");
  state.addAttribute("sym_name", builder.getStringAttr("main"));
  state.addAttribute("roles",
                     builder.getArrayAttr({builder.getStringAttr("V"),
                                           builder.getStringAttr("Observer")}));
  state.addAttribute("input_roles",
                     builder.getArrayAttr({owner, owner, owner, owner}));
  state.addAttribute("output_roles",
                     builder.getArrayAttr({observer, observer}));
  state.addAttribute("function_type", TypeAttr::get(builder.getFunctionType(
                                          inputs, {kind.getAnswerType(),
                                                   kind.getAnswerType()})));
  auto *body = new Block();
  body->addArguments(inputs, SmallVector<Location>(inputs.size(), loc));
  state.addRegion()->push_back(body);
  builder.setInsertionPointToEnd(&unit.getBody().front());
  builder.create(state);
  builder.setInsertionPointToEnd(body);
  SmallVector<Value> outputs;
  for (unsigned i = 0; i < 2; ++i) {
    auto site = "query_" + std::to_string(i);
    auto call = protocol_ir::LocalCallOp::create(
        builder, loc, kind.getAnswerType(),
        ValueRange{body->getArgument(0), body->getArgument(1),
                   body->getArgument(i + 2)},
        read.getSymName(), site, "V");
    auto message = protocol_ir::ExchangeOp::create(
        builder, loc, kind.getAnswerType(), call.getOutputs()[0],
        "answer_" + std::to_string(i), "V", "Observer");
    outputs.push_back(message);
  }
  protocol_ir::MathematicalReturnOp::create(builder, loc, outputs);
  require(succeeded(verify(candidate)), "query client formation failed");
  std::string source;
  raw_string_ostream text(source);
  candidate.print(text);
  return take(compileRun(source, "oracle-table-read.mlir", {}, registry))
      .bundle;
}
} // namespace
int main(int argc, char **argv) {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  for (StringRef spelling :
       {"field:koala-bear.ext4-binomial3", "group:bls12-381.g1", "index",
        "bool", "bytes", "sequence<bool>"}) {
    auto answer =
        decodeBoundType(&context, take(parseBoundType(spelling, false)));
    auto kind = protocol_ir::OracleKindAttr::get(
        &context, "table", ArrayAttr::get(&context, {TypeAttr::get(answer)}));
    cases.run("ordered read and physical compilation: " + spelling, [&] {
      auto candidate = fresh(context);
      auto read = take(emitOracleTableRead(*candidate, kind));
      if (auto e = checkOracleTableRead(*candidate, read, kind))
        throw std::runtime_error(toString(std::move(e)));
      auto bundle = client(*candidate, read, kind, registry);
      require(!bundle.empty(), "query primitive did not compile");
      if (argc == 2 && spelling == "index") {
        std::filesystem::create_directories(argv[1]);
        std::ofstream out(std::filesystem::path(argv[1]) / "ordered.bundle");
        out << bundle;
        require(bool(out), "could not retain native query client");
      }
    });
    for (unsigned mutation = 0; mutation < 3; ++mutation)
      cases.run(
          "well-formed query mutation " + spelling + " " + Twine(mutation),
          [&] {
            auto candidate = fresh(context);
            auto read = take(emitOracleTableRead(*candidate, kind));
            read.walk([&](exec::ApplyOp op) {
              if (mutation == 0 && op.getSite() == "domain") {
                auto inputs = SmallVector<Value>(op.getInputs());
                std::swap(inputs[0], inputs[1]);
                op.getInputsMutable().assign(inputs);
              }
              if (mutation == 1 && op.getSite() == "domain") {
                auto binding =
                    SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                        op, op.getBindingAttr());
                binding.setContract("index.equal");
              }
              if (mutation == 2 && op.getSite() == "read")
                op.getInputsMutable()[1].set(read.getArgument(2));
            });
            require(succeeded(verify(*candidate)),
                    "mutation only failed formation");
            auto refusal = checkOracleTableRead(*candidate, read, kind);
            require(bool(refusal), "changed query primitive passed");
            require(namesIdentifier(toString(std::move(refusal)),
                                    "oracle-table-read-body"),
                    "unexpected query refusal");
          });
  }
  cases.run("invalid query primitive selections refuse", [&] {
    auto candidate = fresh(context);
    refuses(emitOracleTableRead(*candidate, {}), "oracle-table-read");
    auto bad = protocol_ir::OracleKindAttr::get(&context, "unsupported",
                                                ArrayAttr::get(&context, {}));
    refuses(emitOracleTableRead(*candidate, bad), "oracle-table-read");
  });
  return cases.result();
}
