#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
std::string edit(StringRef source, StringRef from, StringRef to) {
  auto text = source.str();
  auto pos = text.find(from.str());
  require(pos != std::string::npos, "missing fixture edit: " + from);
  text.replace(pos, from.size(), to.str());
  return text;
}
OwningOpRef<ModuleOp> copy(ModuleOp module) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
}
local::FuncOp function(ModuleOp module, StringRef name) {
  local::FuncOp found;
  module.walk([&](local::FuncOp candidate) {
    if (candidate.getSymName() == name)
      found = candidate;
  });
  require(bool(found), "missing function " + name);
  return found;
}
// Bound operations of one generated body, in order, with their contracts.
SmallVector<std::pair<std::string, Operation *>> actions(ModuleOp module,
                                                         StringRef name) {
  SymbolTable symbols(&module.getBody()->front());
  SmallVector<std::pair<std::string, Operation *>> result;
  for (auto &op : function(module, name).getBody().front()) {
    auto ref = op.getAttrOfType<FlatSymbolRefAttr>("binding");
    auto binding =
        ref ? symbols.lookup<local::OperationBindingOp>(ref.getValue())
            : local::OperationBindingOp();
    result.emplace_back(binding ? binding.getContract().str()
                                : op.getName().getStringRef().str(),
                        &op);
  }
  return result;
}
Operation *nth(ModuleOp module, StringRef name, StringRef contract,
               unsigned index = 0) {
  for (auto &[found, op] : actions(module, name))
    if (found == contract && !index--)
      return op;
  require(false, "missing action " + contract);
  return nullptr;
}
} // namespace

int main(int argc, char **argv) {
  require(argc == 2, "expected a map fixture path");
  auto bytes = llvm::MemoryBuffer::getFile(argv[1]);
  require(bool(bytes), "cannot read map fixture");
  StringRef fixture = (*bytes)->getBuffer();
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry, MLIRContext::Threading::DISABLED);
  context.loadAllAvailableDialects();
  auto source = parseSourceString<ModuleOp>(fixture, &context);
  require(bool(source), "map fixture refused");
  auto expanded = copy(*source);
  require(succeeded(mathematical::expandMapRealizations(*expanded)),
          "map realization failed");
  auto named = [&](StringRef code, function_ref<bool()> body) {
    bool seen = false;
    ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
      seen |= diagnostic.str().find(code.str()) != std::string::npos;
      return success();
    });
    return body() && seen;
  };

  cases.run("guards precede formula and every operation is checked", [&] {
    std::vector<std::string> contracts;
    for (auto &[contract, op] : actions(*expanded, "mapped"))
      contracts.push_back(contract);
    std::vector<std::string> expected = {
        "vector.length", "vector.length", "index.equal",     "control.require",
        "vector.length", "index.equal",   "control.require", "field.constant",
        "vector.mul",    "vector.sub",    "field.add",       "vector.scale",
        "vector.fill",   "vector.add",    "local.return"};
    require(contracts == expected, "unexpected realization schedule");
    // The scalar subexpression stays scalar; the scale takes the rows first.
    auto scale = nth(*expanded, "mapped", "vector.scale");
    auto vectorSub = nth(*expanded, "mapped", "vector.sub");
    auto fieldAdd = nth(*expanded, "mapped", "field.add");
    require(scale->getOperand(0) == vectorSub->getResult(0) &&
                scale->getOperand(1) == fieldAdd->getResult(0),
            "scalar factor is not a scale");
    // The unused third input is measured and compared with the first.
    auto third = nth(*expanded, "mapped", "vector.length", 2);
    auto mapped = function(*expanded, "mapped");
    require(third->getOperand(0) == mapped.getArgument(2),
            "unused rowwise input escaped its shape check");
    require(succeeded(mathematical::verifyMapRealizationsPreserved(*source,
                                                                   *expanded)),
            "valid realization refused");
    bool residual = false;
    expanded->walk([&](algebra::MapRealizeOp) { residual = true; });
    require(!residual, "map declaration survived realization");
    require(bool(SymbolTable::lookupNearestSymbolFrom(
                &expanded->getBody()->front(),
                StringAttr::get(&context, "formula"))),
            "original scalar helper was not retained");
  });

  cases.run("realization is deterministic", [&] {
    auto again = copy(*source);
    require(succeeded(mathematical::expandMapRealizations(*again)),
            "second realization failed");
    std::string first, second;
    llvm::raw_string_ostream(first) << *expanded;
    llvm::raw_string_ostream(second) << *again;
    require(first == second, "realization differs between runs");
  });

  auto mutation = [&](StringRef label, function_ref<void(ModuleOp)> change) {
    cases.run(label, [&] {
      auto candidate = copy(*expanded);
      change(*candidate);
      require(named("algebra-map-correspondence",
                    [&] {
                      return failed(
                          mathematical::verifyMapRealizationsPreserved(
                              *source, *candidate));
                    }),
              "changed realization escaped correspondence checking");
    });
  };
  mutation("compare a length with itself", [&](ModuleOp module) {
    auto equal = nth(module, "mapped", "index.equal", 1);
    equal->setOperand(1, equal->getOperand(0));
  });
  mutation("drop an unused input guard", [&](ModuleOp module) {
    nth(module, "mapped", "control.require", 1)->erase();
  });
  mutation("swap subtraction operands", [&](ModuleOp module) {
    auto sub = nth(module, "mapped", "vector.sub");
    auto left = sub->getOperand(0);
    sub->setOperand(0, sub->getOperand(1));
    sub->setOperand(1, left);
  });
  mutation("broadcast a different scalar", [&](ModuleOp module) {
    auto fill = nth(module, "mapped", "vector.fill");
    fill->setOperand(0, nth(module, "mapped", "field.add")->getResult(0));
  });
  mutation("return an intermediate", [&](ModuleOp module) {
    auto *ret = nth(module, "mapped", "local.return");
    ret->setOperand(0, nth(module, "mapped", "vector.scale")->getResult(0));
  });
  mutation("change a literal", [&](ModuleOp module) {
    nth(module, "mapped", "field.constant")
        ->setAttr("parameters",
                  ArrayAttr::get(&context, {StringAttr::get(&context, "2")}));
  });
  mutation("change the retained helper", [&](ModuleOp module) {
    module.walk([&](algebra::ConstantFieldOp op) {
      if (op->getParentOfType<func::FuncOp>().getSymName() == "formula")
        op->setAttr("value", StringAttr::get(&context, "2"));
    });
  });
  mutation("add an unused binding", [&](ModuleOp module) {
    OpBuilder builder(&module.getBody()->front().getRegion(0).front(),
                      module.getBody()->front().getRegion(0).front().begin());
    local::OperationBindingOp::create(
        builder, module.getLoc(), "extra", "vector.add",
        builder.getStrArrayAttr({"koala-bear"}), "");
  });

  auto refusal = [&](StringRef label, StringRef text, StringRef code,
                     bool realize = false) {
    cases.run(label, [&] {
      std::optional<OwningOpRef<ModuleOp>> module;
      require(named(code,
                    [&] {
                      module = parseSourceString<ModuleOp>(text, &context);
                      if (!realize)
                        return !*module;
                      return bool(*module) &&
                             failed(
                                 mathematical::expandMapRealizations(**module));
                    }),
              "missing expected refusal identifier " + code);
      if (realize) {
        ScopedDiagnosticHandler quiet(&context,
                                      [](Diagnostic &) { return success(); });
        uint64_t work = 1000000;
        auto error = mathematical::checkMapFormulas(**module, work);
        require(bool(error), "formula admission accepted the map");
        auto message = llvm::toString(std::move(error));
        require(message.find(code.str()) != std::string::npos,
                "formula admission identifier: " + message);
      }
    });
  };
  refusal("missing helper", edit(fixture, "= @formula", "= @missing"),
          "algebra-map-helper");
  refusal("no rowwise input",
          edit(fixture, "[true, true, true, false]",
               "[false, false, false, false]"),
          "algebra-map-signature");
  refusal(
      "rowwise mask and signature disagree",
      edit(fixture, "[true, true, true, false]", "[true, true, true, true]"),
      "algebra-map-signature");
  refusal("mixed fields", edit(fixture, " algebra.map_realize @mapped", R"(
 func.func private @mixed(%a:!F,%e:!algebra.field<"koala-bear.ext8-binomial3">)->!F {
   func.return %a : !F
 }
 algebra.map_realize @mixed_map = @mixed [true, false] : (!V,!algebra.field<"koala-bear.ext8-binomial3">)->!V
 algebra.map_realize @mapped)"),
          "algebra-map-signature");
  refusal("helper field differs from mapped field",
          edit(fixture, " algebra.map_realize @mapped", R"(
 func.func private @wide(%e:!algebra.field<"koala-bear.ext8-binomial3">)->!algebra.field<"koala-bear.ext8-binomial3"> {
   func.return %e : !algebra.field<"koala-bear.ext8-binomial3">
 }
 algebra.map_realize @wide_map = @wide [true] : (!V)->!V
 algebra.map_realize @mapped)"),
          "algebra-map-signature");
  refusal("unsupported unused scalar operation",
          edit(fixture, "   %dead = ",
               "   %unsupported = \"algebra.field_equal\"(%a,%b) : "
               "(!F,!F)->i1\n   %dead = "),
          "algebra-map-formula", true);
  refusal("unsupported nested helper operation",
          edit(fixture, "   %r = \"algebra.field_multiply\"(%x,%x)",
               "   %e = \"algebra.field_equal\"(%x,%x) : (!F,!F)->i1\n"
               "   %r = \"algebra.field_multiply\"(%x,%x)"),
          "algebra-map-formula", true);
  cases.run("realization requires the protocol profile", [&] {
    auto module = parseSourceString<ModuleOp>(
        "module { func.func private @empty() {func.return} }", &context);
    require(bool(module), "context fixture refused");
    require(named("algebra-map-context",
                  [&] {
                    return failed(mathematical::expandMapRealizations(*module));
                  }),
            "missing algebra-map-context refusal");
  });
  refusal("protocol call cannot bypass local application",
          edit(fixture, "callee=@work", "callee=@mapped"),
          "interactive-symbol-kind");

  // Resource-origin analysis reaches a local body because it returns an
  // affine value inside a repeat. Preparation-time declarations have no body
  // yet and only data ports, so both kinds are admitted there.
  cases.run("preparation callables inside an affine local body", [&] {
    constexpr StringLiteral body = R"(!s = !local.capability<"rng:bls12-381.fr">
!F = !algebra.field<"bls12-381.fr">
!V = tensor<?x!F>
module { "protocol.module"() ({
 func.func private @twice(%x:!F)->!F {
   %r = "algebra.field_add"(%x,%x) : (!F,!F)->!F
   func.return %r : !F
 }
 DECLARATION
 local.func @step(%s:!s,%v:VALUE) -> (!s,VALUE) attributes {logical_origin=["step",[]]} {
   %w = local.apply @doubled(%v) {site="map"} : (VALUE)->VALUE
   local.return %s, %w : !s, VALUE
 }
 "protocol.func"() ({ ^entry(%n:ui64,%s:!s,%v:VALUE):
  %done:2 = "protocol.repeat"(%n,%s,%v) ({
   ^round(%i:ui64,%state:!s,%value:VALUE):
    %next:2 = "protocol.local_call"(%state,%value) {callee=@step,role="P",site="step"} : (!s,VALUE)->(!s,VALUE)
    "protocol.yield"(%next#0,%next#1) : (!s,VALUE)->()
  }) {site="rounds",carried=2:i64,maximum=8:i64,roles=["P"],carried_roles=[["P"],["P"]]} : (ui64,!s,VALUE)->(!s,VALUE)
  "protocol.return"(%done#0,%done#1) : (!s,VALUE)->()
 }) {sym_name="main",function_type=(ui64,!s,VALUE)->(!s,VALUE),roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })";
    for (auto [declaration, type] :
         {std::pair<StringRef, StringRef>{
              "algebra.map_realize @doubled = @twice [true] : (!V)->!V", "!V"},
          {"local.realize @doubled = @twice : (!F)->!F", "!F"}}) {
      std::string text = edit(body, "DECLARATION", declaration);
      for (auto at = text.find("VALUE"); at != std::string::npos;
           at = text.find("VALUE", at))
        text.replace(at, 5, type.str());
      auto module = parseSourceString<ModuleOp>(text, &context);
      require(bool(module), "affine local body refused " + declaration);
    }
  });

  for (bool simplify : {false, true})
    cases.run(
        simplify ? "full optimized pipeline" : "full unsimplified pipeline",
        [&] {
          auto text = edit(fixture, " local.func @work", R"(
 func.func private @affine(%x:!F,%y:!F)->!F {
   %r = "algebra.field_add"(%x,%y) : (!F,!F)->!F
   func.return %r : !F
 }
 algebra.map_realize @second = @affine [false, true] : (!F,!V)->!V
 local.func @work)");
          text = edit(
              text, "   local.return %r : !V\n",
              R"(   %q = local.apply @second(%s,%r) {site="second"} : (!F,!V)->!V
   local.return %q : !V
)");
          auto module = parseSourceString<ModuleOp>(text, &context);
          require(bool(module), "two-map fixture refused");
          PassManager manager(&context);
          manager.addPass(protocol::createProjectProtocolPass(simplify));
          manager.addPass(protocol::createEliminatePolynomialsPass());
          manager.addPass(protocol::createLowerMathPass());
          manager.addPass(protocol::createSelectPhysicalPass());
          require(succeeded(manager.run(*module)),
                  "realized maps did not compile");
          bool residual = false;
          module->walk([&](Operation *op) {
            residual |=
                isa<algebra::MapRealizeOp, local::ApplyOp, func::FuncOp>(op);
          });
          require(!residual, "preparation construct escaped into execution");
        });
  return cases.result();
}
