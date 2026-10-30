#include "../lib/Transforms/OracleTableRead.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/TypeFormation.h"
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
  cases.run(
      "native sequence read exceeds byte depth without widening publication",
      [&] {
        auto emit = [&] { return emitError(UnknownLoc::get(&context)); };
        Type row = IntegerType::get(&context, 1);
        for (unsigned i = 0; i < 12; ++i) {
          row = constructLogicalType(emit, &context,
                                     {"sequence", {TypeAttr::get(row)}});
          require(bool(row), "native sequence formation failed");
        }
        auto bytes = encodeBoundType(row, false);
        require(!bytes, "native formation widened byte publication");
        consumeError(bytes.takeError());
        auto kind = protocol_ir::OracleKindAttr::getChecked(
            emit, &context, StringRef("table"),
            ArrayAttr::get(&context, {TypeAttr::get(row)}));
        require(bool(kind), "native table kind inherited byte depth");
        auto candidate = fresh(context);
        auto read = take(emitOracleTableRead(*candidate, kind));
        require(succeeded(verify(*candidate)), "deep native read is malformed");
        if (auto failure = checkOracleTableRead(*candidate, read, kind))
          throw std::runtime_error(toString(std::move(failure)));
        bool typedArgument = false;
        read.walk([&](exec::ApplyOp op) {
          if (op.getSite() != "read")
            return;
          auto binding =
              SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                  op, op.getBindingAttr());
          typedArgument = binding.getArguments() ==
                          ArrayAttr::get(&context, {TypeAttr::get(row)});
          op.getInputsMutable()[1].set(read.getArgument(2));
        });
        require(typedArgument, "sequence element did not remain a native type");
        require(succeeded(verify(*candidate)),
                "mutation only failed formation");
        auto refusal = checkOracleTableRead(*candidate, read, kind);
        require(bool(refusal) && namesIdentifier(toString(std::move(refusal)),
                                                 "oracle-table-read-body"),
                "deep actual-body mutation passed independent readback");
        // No executable byte installation is claimed for this native-only row.
      });
  cases.run("equal payloads retain different nominal row identities", [&] {
    auto kind = [&](StringRef identity) {
      auto nominal = data::importVariantIdentity(
          &context, json::Array{"oracle-row-test/0", identity.str()});
      auto arm = data::AlternativeAttr::get(
          &context, StringAttr::get(&context, "Record"),
          ArrayRef<Type>{IntegerType::get(&context, 1)});
      auto row = data::VariantType::getChecked(
          UnknownLoc::get(&context), &context, nominal,
          ArrayRef<data::AlternativeAttr>{arm});
      require(bool(row), "nominal row formation failed");
      return protocol_ir::OracleKindAttr::get(
          &context, "table", ArrayAttr::get(&context, {TypeAttr::get(row)}));
    };
    auto original = kind("original"), other = kind("other");
    auto candidate = fresh(context);
    auto read = take(emitOracleTableRead(*candidate, original));
    require(succeeded(verify(*candidate)), "nominal read is malformed");
    if (auto failure = checkOracleTableRead(*candidate, read, original))
      throw std::runtime_error(toString(std::move(failure)));
    auto refusal = checkOracleTableRead(*candidate, read, other);
    require(bool(refusal) && namesIdentifier(toString(std::move(refusal)),
                                             "oracle-table-read-body"),
            "checker erased the nominal row identity");
  });
  cases.run("native sequence construction refuses a missing owner", [&] {
    MLIRContext minimal(registry);
    ScopedDiagnosticHandler silence(&minimal,
                                    [](Diagnostic &) { return success(); });
    require(!minimal.getLoadedDialect<data::DataDialect>(),
            "Data already loaded");
    auto sequence = constructLogicalType(
        [&] { return emitError(UnknownLoc::get(&minimal)); }, &minimal,
        {"sequence", {TypeAttr::get(IntegerType::get(&minimal, 1))}});
    require(!sequence && !minimal.getLoadedDialect<data::DataDialect>(),
            "native construction loaded an unrequested owner");
  });
  cases.run("native sequence checks inactive arms and exact carrier kind", [&] {
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    auto emit = [&] { return emitError(UnknownLoc::get(&context)); };
    auto nominal = data::importVariantIdentity(
        &context, json::Array{"oracle-row-test/0", "inactive"});
    auto affine = runtime::CapabilityType::get(
        &context, runtime::CapabilityKind::Random, "bls12-381.fr");
    auto row = data::VariantType::getChecked(
        emit, &context, nominal,
        {data::AlternativeAttr::get(&context,
                                    StringAttr::get(&context, "Empty"), {}),
         data::AlternativeAttr::get(
             &context, StringAttr::get(&context, "Dormant"), {affine})});
    require(bool(row), "affine variant should form independently");
    require(!constructLogicalType(emit, &context,
                                  {"sequence", {TypeAttr::get(row)}}),
            "inactive affine arm acquired sequence permissions");
    require(!constructLogicalType(
                emit, &context,
                {"sequence", {TypeAttr::get(IntegerType::get(&context, 64))}}),
            "signless integer was confused with the native index carrier");
  });
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
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    auto bad = protocol_ir::OracleKindAttr::getChecked(
        [&] { return emitError(UnknownLoc::get(&context)); }, &context,
        StringRef("unsupported"), ArrayAttr::get(&context, {}));
    require(!bad, "unsupported oracle kind passed checked construction");
    MLIRContext other(registry);
    other.loadAllAvailableDialects();
    auto foreign = protocol_ir::OracleKindAttr::get(
        &other, "table",
        ArrayAttr::get(&other, {TypeAttr::get(IntegerType::get(&other, 1))}));
    refuses(emitOracleTableRead(*candidate, foreign), "oracle-table-read");
  });
  return cases.result();
}
