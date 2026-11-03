// Low-level native admission controls; no checked source model is fabricated.
#include "mlir/IR/Verifier.h"
#include "support/NativeCases.h"
#include "support/ResourceSources.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/ResourceOrigins.h"
using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
using zkc::test::resource_sources::Source;
func::FuncOp fresh(Source &source, StringRef name) {
  auto helper = source.function(name, {}, source.unit);
  helper.setPrivate();
  exec::ScopedExecutionBuilder control(source.builder, helper);
  auto unit = source.invoke(control, "create", {}, source.unit, "custody");
  control.returned(unit);
  return helper;
}
Operation *common(Source &source, ArrayRef<func::FuncOp> helpers) {
  auto &builder = source.builder;
  builder.setInsertionPointToEnd(&source.owner.getBody().front());
  auto *function = source.operation(
      "protocol.func", {}, {},
      {source.text("sym_name", "root"),
       builder.getNamedAttr("function_type",
                            TypeAttr::get(builder.getFunctionType(
                                {}, {source.unit, source.unit}))),
       builder.getNamedAttr("roles", builder.getStrArrayAttr({"P", "V"})),
       builder.getNamedAttr("input_roles", builder.getArrayAttr({})),
       builder.getNamedAttr(
           "output_roles",
           builder.getArrayAttr({builder.getStrArrayAttr({"P"}),
                                 builder.getStrArrayAttr({"V"})}))},
      true);
  auto *body = new Block();
  function->getRegion(0).push_back(body);
  builder.setInsertionPointToEnd(body);
  SmallVector<Value> values;
  for (auto [index, declaration] : llvm::enumerate(helpers)) {
    auto helper = declaration;
    auto *call = source.operation(
        "protocol.local_call", {}, source.unit,
        {source.symbol("callee", helper.getSymName()),
         source.text("role", index ? "V" : "P"),
         source.text("site", index ? "create_v" : "create_p")});
    values.push_back(call->getResult(0));
  }
  source.operation("protocol.return", values);
  return function;
}
} // namespace
int main() {
  Cases cases;
  cases.run(
      "role-local custody creation admits actual scoped helper bodies", [] {
        Source source;
        source.binding("create", "resource_unit.create", {"Slot.A"});
        auto p = fresh(source, "zkl_custody_0");
        auto v = fresh(source, "zkl_custody_1");
        common(source, {p, v});
        require(succeeded(admitStage(source.owner)),
                "role-local unit construction failed native admission");
        auto closure = take(protocol::readSourceExecutionClosure(source.owner));
        uint64_t work = 100000;
        auto origins = take(exec::ResourceOriginAnalysis::create(
            source.owner, std::move(closure), work));
        require(take(origins->get(p)).roots.empty() &&
                    take(origins->get(v)).roots.empty(),
                "equal static unit types invented an existing dynamic root");
      });
  cases.run(
      "equal nominal unit types preserve distinct dynamic input roots", [] {
        Source source;
        auto helper =
            source.function("forward_fields", {source.unit, source.unit},
                            {source.unit, source.unit});
        exec::ScopedExecutionBuilder control(source.builder, helper);
        control.returned({helper.getArgument(2), helper.getArgument(1)});
        require(succeeded(admitStage(source.owner)),
                "invalid native unit passage");
        auto closure = take(protocol::readSourceExecutionClosure(source.owner));
        uint64_t work = 100000;
        auto origins = take(exec::ResourceOriginAnalysis::create(
            source.owner, std::move(closure), work));
        require(take(origins->get(helper)).roots ==
                    std::map<unsigned, unsigned>{{0, 1}, {1, 0}},
                "equal nominal types merged independent actual unit roots");
      });
  cases.run("custody helpers require valid native callable origin names", [] {
    Source source;
    source.binding("create", "resource_unit.create", {"Slot.A"});
    auto helper = fresh(source, "zkl_custody_0");
    helper->setAttr("runtime.origin",
                    source.builder.getArrayAttr(
                        {source.builder.getStringAttr("zkc.language.custody/0"),
                         source.builder.getArrayAttr({})}));
    refuses(protocol::readSourceExecutionClosure(source.owner),
            "execution-cfg");
  });
  cases.run("same unit type cannot substitute another fragment's role", [] {
    Source source;
    source.binding("create", "resource_unit.create", {"Slot.A"});
    auto p = fresh(source, "zkl_custody_0");
    auto v = fresh(source, "zkl_custody_1");
    auto *root = common(source, {p, v});
    require(succeeded(admitStage(source.owner)), "invalid native fixture");
    auto &returned = root->getRegion(0).front().back();
    returned.setOperand(0, returned.getOperand(1));
    std::string diagnostics;
    ScopedDiagnosticHandler handler(&source.context,
                                    [&](Diagnostic &diagnostic) {
                                      raw_string_ostream out(diagnostics);
                                      diagnostic.print(out);
                                      return success();
                                    });
    require(failed(admitStage(source.owner)) &&
                diagnostics.find("mathematical-formation") != std::string::npos,
            "wrong native fragment refusal: " + diagnostics);
  });
  return cases.result();
}
