#include "../lib/Transforms/OracleMerkle.h"
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
constexpr StringLiteral scheme =
    "rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0";
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
std::string client(ModuleOp candidate, const OracleMerkleFunctions &f,
                   protocol_ir::OracleKindAttr kind, bool positions,
                   const DialectRegistry &registry) {
  auto unit = cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  SymbolTable::lookupSymbolIn(unit, "main")->erase();
  OpBuilder builder(candidate.getContext());
  auto loc = candidate.getLoc();
  auto index =
      IntegerType::get(candidate.getContext(), 64, IntegerType::Unsigned);
  SmallVector<Type> inputs =
      positions
          ? SmallVector<Type>{index, index}
          : SmallVector<Type>{kind.getDataType(), index, index, index, index};
  SmallVector<Type> outputs = positions
                                  ? SmallVector<Type>{index, index, index}
                                  : SmallVector<Type>{kind.getAnswerType()};
  auto owner = builder.getArrayAttr({builder.getStringAttr("V")});
  OperationState state(loc, "protocol.func");
  state.addAttribute("sym_name", builder.getStringAttr("main"));
  auto holder = builder.getArrayAttr({builder.getStringAttr("P")});
  state.addAttribute(
      "roles", positions ? owner
                         : builder.getArrayAttr({builder.getStringAttr("P"),
                                                 builder.getStringAttr("V")}));
  state.addAttribute(
      "input_roles",
      positions
          ? builder.getArrayAttr(SmallVector<Attribute>(inputs.size(), owner))
          : builder.getArrayAttr({holder, holder, holder, owner, owner}));
  state.addAttribute(
      "output_roles",
      builder.getArrayAttr(SmallVector<Attribute>(outputs.size(), owner)));
  state.addAttribute("function_type",
                     TypeAttr::get(builder.getFunctionType(inputs, outputs)));
  auto *body = new Block();
  body->addArguments(inputs, SmallVector<Location>(inputs.size(), loc));
  state.addRegion()->push_back(body);
  builder.setInsertionPointToEnd(&unit.getBody().front());
  builder.create(state);
  builder.setInsertionPointToEnd(body);
  auto call = [&](func::FuncOp fn, ValueRange args, StringRef site,
                  StringRef role = "V") {
    return protocol_ir::LocalCallOp::create(
               builder, loc, scopedDataSignature(fn).getResults(), args,
               fn.getSymName(), site, role)
        .getOutputs();
  };
  if (positions) {
    auto result = call(f.position, body->getArguments(), "position");
    protocol_ir::MathematicalReturnOp::create(builder, loc, result);
  } else {
    auto committed = call(
        f.commit, {body->getArgument(0), body->getArgument(1)}, "commit", "P");
    auto opened =
        call(f.open, {committed[1], body->getArgument(1), body->getArgument(2)},
             "open", "P");
    auto exchange = [&](Value value, StringRef site) -> Value {
      return protocol_ir::ExchangeOp::create(builder, loc, value.getType(),
                                             value, site, "P", "V");
    };
    auto root = exchange(committed[0], "root");
    auto row = exchange(opened[0], "row");
    auto proof = exchange(opened[1], "proof");
    auto answer =
        call(f.authenticate,
             {root, body->getArgument(3), body->getArgument(4), row, proof},
             "authenticate");
    protocol_ir::MathematicalReturnOp::create(builder, loc, answer);
  }
  require(succeeded(verify(candidate)), "Merkle client formation failed");
  std::string source;
  raw_string_ostream text(source);
  candidate.print(text);
  return take(compileRun(source, "oracle-merkle.mlir", {}, registry)).bundle;
}
} // namespace
int main(int argc, char **argv) {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto answer = decodeBoundType(
      &context, take(parseBoundType("field:koala-bear.ext4-binomial3", false)));
  auto kind = protocol_ir::OracleKindAttr::get(
      &context, "table", ArrayAttr::get(&context, {TypeAttr::get(answer)}));
  Cases cases;
  for (auto grouping :
       {OracleLeafGrouping::Individual, OracleLeafGrouping::AntipodalPairs})
    for (auto order :
         {OracleLeafOrder::Natural, OracleLeafOrder::BitReversed}) {
      std::string name = std::to_string(unsigned(grouping)) + "-" +
                         std::to_string(unsigned(order));
      for (bool positions : {true, false})
        cases.run(
            "checked native compilation " + name +
                (positions ? " positions" : " authentication"),
            [&] {
              auto candidate = fresh(context);
              auto helpers = take(
                  emitOracleMerkle(*candidate, kind, scheme, grouping, order));
              if (auto e = checkOracleMerkle(*candidate, helpers, kind, scheme,
                                             grouping, order))
                throw std::runtime_error(toString(std::move(e)));
              auto bundle =
                  client(*candidate, helpers, kind, positions, registry);
              require(!bundle.empty(), "empty Merkle bundle");
              if (argc == 2) {
                std::filesystem::create_directories(argv[1]);
                std::ofstream out(std::filesystem::path(argv[1]) /
                                  ((positions ? "positions-" : "merkle-") +
                                   name + ".bundle"));
                out << bundle;
                require(bool(out), "could not retain Merkle client");
              }
            });
      cases.run("independently parsed bodies " + name, [&] {
        auto candidate = fresh(context);
        auto original =
            take(emitOracleMerkle(*candidate, kind, scheme, grouping, order));
        std::string text;
        raw_string_ostream stream(text);
        candidate->print(stream);
        auto parsed = parseSourceString<ModuleOp>(text, &context);
        require(bool(parsed), "Merkle candidate did not parse");
        auto unit =
            cast<protocol_ir::ProtocolModuleOp>(parsed->getBody()->front());
        auto find = [&](func::FuncOp helper) {
          return dyn_cast_or_null<func::FuncOp>(
              SymbolTable::lookupSymbolIn(unit, helper.getSymName()));
        };
        OracleMerkleFunctions actual{find(original.position),
                                     find(original.commit), find(original.open),
                                     find(original.authenticate)};
        if (auto e = checkOracleMerkle(*parsed, actual, kind, scheme, grouping,
                                       order))
          throw std::runtime_error(toString(std::move(e)));
      });
      for (unsigned mutation = 0; mutation < 10; ++mutation)
        cases.run(
            "well-formed body mutation " + name + " " +
                std::to_string(mutation),
            [&] {
              auto candidate = fresh(context);
              auto helpers = take(
                  emitOracleMerkle(*candidate, kind, scheme, grouping, order));
              candidate->walk([&](exec::ApplyOp op) {
                auto swap = [&](unsigned a, unsigned b) {
                  auto values = SmallVector<Value>(op.getInputs());
                  std::swap(values[a], values[b]);
                  op.getInputsMutable().assign(values);
                };
                if (mutation == 0 && op.getSite() == "in_domain")
                  swap(0, 1);
                if (mutation == 1 && op.getSite() == "authenticate")
                  swap(1, 2);
                if (mutation == 2 && op.getSite() == "authenticate")
                  swap(2, 3);
                if (mutation == 3 && op.getSite() == "slot")
                  swap(0, 1);
                if (mutation == 4 && op.getSite() == "width")
                  op.setParametersAttr(ArrayAttr::get(
                      &context, {StringAttr::get(&context, "3")}));
                if (mutation == 5 && op.getSite() == "even_span") {
                  auto binding =
                      SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                          op, op.getBindingAttr());
                  binding.setContract("index.less");
                }
                if (mutation == 7 && op.getSite() == "actual_rows")
                  op.setSite("unbound_data");
                if (mutation == 8 && op.getSite() == "more_bits")
                  swap(0, 1);
                if (mutation == 9 && op.getSite() == "authenticate") {
                  // Preserve a well-formed guard, but replace its
                  // authentication predicate by true. Formation alone cannot
                  // catch this.
                  OpBuilder builder(op);
                  OperationState constant(op.getLoc(), "exec.boolean");
                  constant.addOperands(op.getScope());
                  constant.addTypes(op.getOutcome().getType());
                  constant.addAttribute("value", builder.getBoolAttr(true));
                  constant.addAttribute("site", op.getSiteAttr());
                  auto *replacement = builder.create(constant);
                  op->replaceAllUsesWith(replacement->getResults());
                  op.erase();
                }
              });
              if (mutation == 6)
                helpers.authenticate.walk([&](func::CallOp op) {
                  auto args = SmallVector<Value>(op.getOperands());
                  std::swap(args[1], args[2]);
                  op.getOperandsMutable().assign(args);
                });
              require(succeeded(verify(*candidate)),
                      "mutation only failed formation");
              auto refused = checkOracleMerkle(*candidate, helpers, kind,
                                               scheme, grouping, order);
              require(bool(refused), "mutated Merkle body passed");
              require(namesIdentifier(toString(std::move(refused)),
                                      "oracle-merkle-body"),
                      "wrong refusal");
            });
    }
  cases.run("invalid selection", [&] {
    auto candidate = fresh(context);
    refuses(emitOracleMerkle(*candidate, {}, scheme,
                             OracleLeafGrouping::Individual,
                             OracleLeafOrder::Natural),
            "oracle-merkle");
    refuses(emitOracleMerkle(*candidate, kind, "missing",
                             OracleLeafGrouping::Individual,
                             OracleLeafOrder::Natural),
            "oracle-merkle");
    refuses(emitOracleMerkle(*candidate, kind, scheme, OracleLeafGrouping(99),
                             OracleLeafOrder::Natural),
            "oracle-merkle");
    refuses(emitOracleMerkle(*candidate, kind, scheme,
                             OracleLeafGrouping::Individual,
                             OracleLeafOrder(99)),
            "oracle-merkle");
    refuses(emitOracleMerkle(
                *candidate, kind, "rows.merkle-keccak256.koala-bear/0",
                OracleLeafGrouping::Individual, OracleLeafOrder::Natural),
            "oracle-merkle");
  });
  return cases.result();
}
