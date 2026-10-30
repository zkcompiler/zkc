#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include <filesystem>
#include <fstream>
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace {
constexpr StringLiteral fixture = R"mlir(
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%n:ui64,%a:i1,%b:i1,%c:i1):
  %joined = "protocol.assemble_roles"(%a,%b,%c) {roles=["P","V","Observer"]} : (i1,i1,i1)->i1
  %state = "protocol.repeat"(%n,%joined,%joined) ({
  ^loop(%i:ui64,%old:i1,%captured:i1):
   %yes = arith.constant true
   %next = arith.select %yes,%captured,%old : i1
   "protocol.yield"(%next) : (i1)->()
  }) {site="round",carried=1:i64,maximum=4:i64,roles=["P","V","Observer"],carried_roles=[["P","V","Observer"]]} : (ui64,i1,i1)->i1
  "protocol.return"(%state) : (i1)->()
 }) {sym_name="main",origin=["main",[]],function_type=(ui64,i1,i1,i1)->i1,roles=["P","V","Observer"],input_roles=[["P","V","Observer"],["P"],["V"],["Observer"]],output_roles=[["P","V","Observer"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
constexpr StringLiteral application = R"mlir(
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%x:i1,%y:i1):
  %r = "protocol.assemble_roles"(%x,%y) {roles=["A","B"]} : (i1,i1)->i1
  "protocol.return"(%r) : (i1)->()
 }) {sym_name="child",origin=["child",[]],function_type=(i1,i1)->i1,roles=["A","B"],input_roles=[["A"],["B"]],output_roles=[["A","B"]]} : ()->()
 "protocol.func"() ({
 ^entry(%x:i1,%y:i1):
  %r = protocol.apply @child(%x,%y) {roles=["V","P"],site="child_call"} : (i1,i1)->i1
  "protocol.return"(%r) : (i1)->()
 }) {sym_name="main",origin=["main",[]],function_type=(i1,i1)->i1,roles=["P","V"],input_roles=[["V"],["P"]],output_roles=[["P","V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
constexpr StringLiteral localCalls = R"mlir(
module { "protocol.module"() ({
 func.func private @identity(%scope:!runtime.scope,%value:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["identity",[]]} {
  %r = "exec.returned"(%value) : (i1)->!exec.outcome<(i1)>
  func.return %r : !exec.outcome<(i1)>
 }
 "protocol.func"() ({
 ^entry(%x:i1,%y:i1):
  %a = "protocol.local_call"(%x) {callee=@identity,role="P",site="left"} : (i1)->i1
  %b = "protocol.local_call"(%y) {callee=@identity,role="V",site="right"} : (i1)->i1
  %r = "protocol.assemble_roles"(%a,%b) {roles=["P","V"]} : (i1,i1)->i1
  "protocol.return"(%r) : (i1)->()
 }) {sym_name="main",origin=["main",[]],function_type=(i1,i1)->i1,roles=["P","V"],input_roles=[["P"],["V"]],output_roles=[["P","V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
void project(ModuleOp source, bool simplify) {
  PassManager manager(source.getContext());
  manager.addPass(protocol::createProjectProtocolPass(simplify));
  require(succeeded(manager.run(source)), "role projection failed");
}
std::string text(ModuleOp module) {
  std::string result;
  raw_string_ostream out(result);
  module.print(out);
  return result;
}
} // namespace
int main(int argc, char **argv) {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  for (auto source : {fixture, application, localCalls})
    for (bool simplify : {false, true})
      cases.run(
          Twine("component projection ") + Twine(simplify) +
              (source == fixture       ? " repeat"
               : source == application ? " application"
                                       : " local calls"),
          [&] {
            auto original = parseSourceString<ModuleOp>(source, &context);
            require(bool(original), "source formation failed");
            auto frozen = text(*original);
            OwningOpRef<ModuleOp> target(cast<ModuleOp>((*original)->clone()));
            project(*target, simplify);
            require(succeeded(mathematical::verifyProjectionPreserved(*original,
                                                                      *target)),
                    "independent projection check failed");
            require(text(*original) == frozen, "projection mutated original");
            unsigned residual = 0, messages = 0;
            target->walk([&](protocol_ir::AssembleRolesOp) { ++residual; });
            target->walk([&](protocol_ir::EmitOp) { ++messages; });
            require(!residual && !messages,
                    "assembly introduced communication or survived projection");
            auto compiled =
                take(compileRun(source, "assembly.mlir", {}, registry));
            require(!compiled.bundle.empty(), "physical compilation failed");
          });
  cases.run("structured source retains ordered component selection", [&] {
    auto exported =
        take(protocol::exportStructuredSource(fixture, "main", context));
    require(exported.bytes.find("assemble") != std::string::npos,
            "assembly missing from original snapshot");
    if (argc == 2) {
      std::filesystem::create_directories(argv[1]);
      std::ofstream out(std::filesystem::path(argv[1]) / "assembly.json");
      out << exported.bytes;
      require(bool(out), "could not retain assembly source");
    }
  });
  for (unsigned mutation = 0; mutation < 5; ++mutation)
    cases.run(Twine("assembly admission refusal ") + Twine(mutation), [&] {
      auto source = parseSourceString<ModuleOp>(fixture, &context);
      protocol_ir::AssembleRolesOp assembly;
      source->walk([&](protocol_ir::AssembleRolesOp op) { assembly = op; });
      Builder builder(&context);
      if (mutation == 0)
        assembly.setRolesAttr(builder.getArrayAttr({}));
      if (mutation == 1)
        assembly.setRolesAttr(builder.getStrArrayAttr({"P", "P", "Observer"}));
      if (mutation == 2)
        assembly.setRolesAttr(builder.getStrArrayAttr({"P", "V", "unknown"}));
      if (mutation == 3)
        assembly.setRolesAttr(builder.getStrArrayAttr({"V", "P", "Observer"}));
      if (mutation == 4)
        assembly.getInputsMutable()[0].set(assembly.getInputs()[1]);
      bool code = false;
      ScopedDiagnosticHandler expected(&context, [&](Diagnostic &d) {
        code |= namesIdentifier(d.str(), "mathematical-formation");
        return success();
      });
      // Arity and duplicate roles are local invariants. Availability and the
      // enclosing role roster belong to complete protocol admission.
      if (mutation >= 2)
        require(succeeded(verify(*source)),
                "role availability mutation lost structural validity");
      auto admitted = mutation < 2 ? verify(*source) : zkc::admitStage(*source);
      require(failed(admitted) && code, "invalid assembly was not refused");
    });
  cases.run("changed role-selected return is refused by correspondence", [&] {
    auto original = parseSourceString<ModuleOp>(application, &context);
    OwningOpRef<ModuleOp> target(cast<ModuleOp>((*original)->clone()));
    project(*target, false);
    target->walk([&](protocol_ir::ParticipantOp participant) {
      if (participant.getRole() != "V")
        return;
      auto &block = participant.getBody().front();
      OpBuilder builder(block.getTerminator());
      auto replacement = arith::ConstantOp::create(
          builder, participant.getLoc(), builder.getBoolAttr(true));
      block.getTerminator()->setOperand(0, replacement);
    });
    require(succeeded(verify(*target)), "mutation only failed formation");
    ScopedDiagnosticHandler expected(&context,
                                     [](Diagnostic &) { return success(); });
    require(failed(mathematical::verifyProjectionPreserved(*original, *target)),
            "changed selected component passed correspondence");
  });
  for (StringRef type :
       {StringRef("!protocol.service_ref<\"random.koala-bear/0\">"),
        StringRef("!protocol.oracle<#protocol.oracle_kind<\"table\", [i1]>>")})
    cases.run("unused non-data assembly refuses: " + type, [&] {
      std::string source =
          "module { \"protocol.module\"() ({ \"protocol.func\"() ({ "
          "^entry(%value:" +
          type.str() +
          "): %bad = \"protocol.assemble_roles\"(%value) {roles=[\"P\"]} : (" +
          type.str() + ")->" + type.str() +
          " \"protocol.return\"() : ()->() }) "
          "{sym_name=\"main\",function_type=(" +
          type.str() +
          ")->(),roles=[\"P\"],input_roles=[[\"P\"]],output_roles=[]} : ()->() "
          "}) {profile=#protocol.profile<protocol>} : ()->() }";
      auto module =
          parseSourceString<ModuleOp>(source, ParserConfig(&context, false));
      require(bool(module), "refusal control did not parse");
      bool code = false;
      ScopedDiagnosticHandler expected(&context, [&](Diagnostic &d) {
        code |= namesIdentifier(d.str(), "mathematical-formation");
        return success();
      });
      require(failed(zkc::admitStage(*module)) && code,
              "non-data assembly passed formation");
    });
  cases.run("assembly cannot reactivate an inactive repeat role", [&] {
    auto source = parseSourceString<ModuleOp>(fixture, &context);
    protocol_ir::RepeatOp repeat;
    source->walk([&](protocol_ir::RepeatOp op) { repeat = op; });
    OpBuilder builder(&context);
    repeat.setRolesAttr(builder.getStrArrayAttr({"P", "V"}));
    repeat.setCarriedRolesAttr(
        builder.getArrayAttr({builder.getStrArrayAttr({"P", "V"})}));
    auto &body = repeat.getBody().front();
    builder.setInsertionPointToStart(&body);
    auto one = arith::ConstantOp::create(builder, repeat.getLoc(),
                                         builder.getBoolAttr(true));
    protocol_ir::AssembleRolesOp::create(builder, repeat.getLoc(),
                                         builder.getI1Type(), ValueRange{one},
                                         builder.getStrArrayAttr({"Observer"}));
    bool code = false;
    ScopedDiagnosticHandler expected(&context, [&](Diagnostic &d) {
      code |= namesIdentifier(d.str(), "mathematical-formation");
      return success();
    });
    require(failed(zkc::admitStage(*source)) && code,
            "inactive assembly role passed formation");
  });
  cases.run("preparation checks whole role families before projection", [&] {
    auto source = parseSourceString<ModuleOp>(application, &context);
    source->walk([&](protocol_ir::MathematicalOp function) {
      Builder builder(&context);
      function.setInputRolesAttr(
          builder.getArrayAttr({function.getRoles(), function.getRoles()}));
    });
    auto prepared = mathematical::prepareProtocol(*source, false);
    {
      ScopedDiagnosticHandler expected(&context,
                                       [](Diagnostic &) { return success(); });
      require(failed(mathematical::verifyProtocolPreparationPreserved(
                  *source, *prepared)),
              "preparation comparison admitted outer container as an empty "
              "protocol");
    }
    require(bool(prepared), "shared-input preparation failed");
    require(succeeded(mathematical::verifyProtocolPreparationPreserved(
                &source->getBody()->front(), &prepared->getBody()->front())),
            "unchanged assembly failed preparation comparison");
    prepared->walk([&](protocol_ir::AssembleRolesOp assembly) {
      auto a = assembly.getInputs()[0], b = assembly.getInputs()[1];
      assembly.getInputsMutable()[0].set(b);
      assembly.getInputsMutable()[1].set(a);
    });
    require(succeeded(verify(*prepared)),
            "crossed operands failed only formation");
    ScopedDiagnosticHandler expected(&context,
                                     [](Diagnostic &) { return success(); });
    require(failed(mathematical::verifyProtocolPreparationPreserved(
                &source->getBody()->front(), &prepared->getBody()->front())),
            "changed component assignment passed preparation comparison");
  });
  return cases.result();
}
