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

  // Most edits reach the map matcher; `code` names an earlier owner that
  // already refuses the candidate during its verification.
  auto mutation = [&](StringRef label, function_ref<void(ModuleOp)> change,
                      StringRef code = "algebra-map-correspondence") {
    cases.run(label, [&] {
      auto candidate = copy(*expanded);
      change(*candidate);
      require(named(code,
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
  mutation("move a shape guard after arithmetic", [&](ModuleOp module) {
    nth(module, "mapped", "control.require")
        ->moveAfter(nth(module, "mapped", "field.constant"));
  });
  mutation("broadcast to another input's length", [&](ModuleOp module) {
    nth(module, "mapped", "vector.fill")
        ->setOperand(1,
                     nth(module, "mapped", "vector.length", 1)->getResult(0));
  });
  // Bound operand order, binding arguments and unknown attributes are also
  // checked by protocol verification before the matcher reads the body.
  mutation(
      "swap scale operands",
      [&](ModuleOp module) {
        auto *scale = nth(module, "mapped", "vector.scale");
        auto rows = scale->getOperand(0);
        scale->setOperand(0, scale->getOperand(1));
        scale->setOperand(1, rows);
      },
      "binding-operation-signature");
  auto binding = [&](ModuleOp module, StringRef contract) {
    auto ref = nth(module, "mapped", contract)
                   ->getAttrOfType<FlatSymbolRefAttr>("binding");
    return SymbolTable(&module.getBody()->front())
        .lookup<local::OperationBindingOp>(ref.getValue());
  };
  mutation(
      "bind vector arithmetic in another field",
      [&](ModuleOp module) {
        binding(module, "vector.add")
            ->setAttr("arguments",
                      ArrayAttr::get(&context, {StringAttr::get(
                                                   &context, "bls12-381.fr")}));
      },
      "binding-operation-signature");
  mutation(
      "add an attribute to a bound operation",
      [&](ModuleOp module) {
        nth(module, "mapped", "vector.add")
            ->setAttr("note", StringAttr::get(&context, "extra"));
      },
      "interactive-unknown-attribute");
  mutation(
      "add an attribute to the realized function",
      [&](ModuleOp module) {
        function(module, "mapped")
            ->setAttr("note", StringAttr::get(&context, "extra"));
      },
      "interactive-unknown-attribute");
  // An installed implementation choice and another origin are valid protocol
  // IR; only the matcher refuses them.
  mutation("select a binding implementation", [&](ModuleOp module) {
    binding(module, "vector.add")
        ->setAttr("implementation",
                  StringAttr::get(&context, "plonky3/vector.add"));
  });
  mutation("name another origin", [&](ModuleOp module) {
    function(module, "mapped")
        ->setAttr("logical_origin",
                  ArrayAttr::get(&context, {StringAttr::get(&context, "square"),
                                            ArrayAttr::get(&context, {})}));
  });
  mutation("add an unused binding", [&](ModuleOp module) {
    OpBuilder builder(&module.getBody()->front().getRegion(0).front(),
                      module.getBody()->front().getRegion(0).front().begin());
    local::OperationBindingOp::create(
        builder, module.getLoc(), "extra", "vector.add",
        builder.getStrArrayAttr({"koala-bear"}), "");
  });

  // Formation refuses while parsing. A `defended` refusal is also refused by
  // preparation's formula admission when verification is skipped.
  auto refusal = [&](StringRef label, StringRef text, StringRef code,
                     bool defended = false) {
    cases.run(label, [&] {
      require(
          named(code,
                [&] { return !parseSourceString<ModuleOp>(text, &context); }),
          "missing expected refusal identifier " + code);
      if (!defended)
        return;
      ScopedDiagnosticHandler quiet(&context,
                                    [](Diagnostic &) { return success(); });
      auto module =
          parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
      require(bool(module), "unverified fixture refused");
      uint64_t work = 1000000;
      auto error = mathematical::checkMapFormulas(*module, work);
      require(bool(error), "formula admission accepted the map");
      auto message = llvm::toString(std::move(error));
      require(namesIdentifier(message, code),
              "formula admission identifier: " + message);
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
  // Plain verification reads every operation of the helper closure, used or
  // not; preparation repeats the check on the expanded formula.
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
  // Each Ring operation is consistent in its own field, so only formation sees
  // dead work in another field.
  refusal("unused constant of another field",
          edit(fixture, "   %dead = ",
               "   %foreign = \"algebra.constant\"() {value=\"2\"} : "
               "()->!algebra.field<\"bls12-381.fr\">\n   %dead = "),
          "algebra-map-formula");
  refusal("nested helper result outside the field",
          edit(edit(fixture, " func.func private @formula", R"(
 func.func private @wide()->!algebra.field<"koala-bear.ext8-binomial3"> {
   %w = "algebra.constant"() {value="3"} : ()->!algebra.field<"koala-bear.ext8-binomial3">
   func.return %w : !algebra.field<"koala-bear.ext8-binomial3">
 }
 func.func private @formula)"),
               "   %dead = ",
               "   %wide = func.call @wide() : () -> "
               "!algebra.field<\"koala-bear.ext8-binomial3\">\n   %dead = "),
          "algebra-map-formula");
  cases.run("unused helper outside the field is not read", [&] {
    auto text = edit(fixture, " func.func private @formula", R"(
 func.func private @test(%x:!F)->i1 {
   %e = "algebra.field_equal"(%x,%x) : (!F,!F)->i1
   func.return %e : i1
 }
 func.func private @formula)");
    require(bool(parseSourceString<ModuleOp>(text, &context)),
            "a helper no map reaches was refused");
  });

  // Ring limits apply to the expanded formula during preparation. A chain of
  // operations adds one level each; subtraction adds one more on the path of
  // its right operand, so `x - acc` grows two levels per step.
  auto chain = [](unsigned steps, StringRef operation, bool deepRight,
                  unsigned calls = 1) {
    std::string text = R"(!F = !algebra.field<"koala-bear">
!V = tensor<?x!F>
module { "protocol.module"() ({
 func.func private @chain(%x:!F)->!F {
   %v0 = "algebra.field_add"(%x,%x) : (!F,!F)->!F
)";
    // %v0 = x + x has depth one; the remaining steps extend it.
    for (unsigned i = 1; i < steps; ++i) {
      auto previous = "%v" + std::to_string(i - 1);
      text += "   %v" + std::to_string(i) + " = \"" + operation.str() + "\"(" +
              (deepRight ? "%x," + previous : previous + ",%x") +
              ") : (!F,!F)->!F\n";
    }
    text += "   func.return %v" + std::to_string(steps - 1) + " : !F\n }\n";
    text += " func.func private @outer(%x:!F)->!F {\n   %c0 = func.call "
            "@chain(%x) : (!F)->!F\n";
    for (unsigned i = 1; i < calls; ++i)
      text += "   %c" + std::to_string(i) + " = func.call @chain(%c" +
              std::to_string(i - 1) + ") : (!F)->!F\n";
    text += "   func.return %c" + std::to_string(calls - 1) + " : !F\n }\n";
    text += R"( algebra.map_realize @mapped = @outer [true] : (!V)->!V
 local.func @work(%a:!V)->!V attributes {logical_origin=["work",[]]} {
   %r = local.apply @mapped(%a) {site="map"} : (!V)->!V
   local.return %r : !V
 }
 "protocol.func"() ({
 ^entry(%a:!V):
   %r = "protocol.local_call"(%a) {callee=@work,role="P",site="work"} : (!V)->!V
   "protocol.return"(%r) : (!V)->()
 }) {sym_name="main",function_type=(!V)->!V,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })";
    return text;
  };
  auto depth = [&](StringRef label, std::string text, bool admitted) {
    cases.run(label, [&] {
      auto module = parseSourceString<ModuleOp>(text, &context);
      require(bool(module), "formation refused a Ring formula");
      ScopedDiagnosticHandler quiet(&context,
                                    [](Diagnostic &) { return success(); });
      uint64_t work = 1000000;
      auto error = mathematical::checkMapFormulas(*module, work);
      if (admitted) {
        require(!error, "formula admission refused: " +
                            llvm::toString(std::move(error)));
        require(succeeded(mathematical::expandMapRealizations(*module)),
                "realization refused an admitted depth");
        return;
      }
      require(bool(error), "formula admission accepted excess depth");
      auto message = llvm::toString(std::move(error));
      require(namesIdentifier(message, "algebra-map-formula") &&
                  namesIdentifier(message, "ring-depth"),
              "depth refusal identifier: " + message);
      require(failed(mathematical::expandMapRealizations(*module)),
              "realization accepted excess depth");
    });
  };
  depth("addition chain at the Ring depth limit",
        chain(1023, "algebra.field_add", false), true);
  depth("addition chain beyond the Ring depth limit",
        chain(1024, "algebra.field_add", false), false);
  depth("subtrahend chain at the Ring depth limit",
        chain(512, "algebra.field_subtract", true), true);
  depth("subtrahend chain beyond the Ring depth limit",
        chain(513, "algebra.field_subtract", true), false);
  // Each helper is shallow; their composition is not.
  depth("expanded helper calls beyond the Ring depth limit",
        chain(600, "algebra.field_add", false, 2), false);
  // Admission charges the root helper before cloning it, operations no
  // result reaches included, and then charges only the callees it expands.
  // One work unit admits the map; every charged operation costs one more than
  // its operand and result slots. The root helper is the function (1), the
  // call (3), each dead addition (4) and the return (2); expanding @square
  // adds its multiplication (4).
  auto budgeted = [](unsigned dead) {
    std::string text = R"(!F = !algebra.field<"koala-bear">
!V = tensor<?x!F>
module { "protocol.module"() ({
 func.func private @square(%x:!F)->!F {
   %r = "algebra.field_multiply"(%x,%x) : (!F,!F)->!F
   func.return %r : !F
 }
 func.func private @outer(%x:!F)->!F {
   %s = func.call @square(%x) : (!F)->!F
)";
    for (unsigned i = 0; i < dead; ++i)
      text += "   %d" + std::to_string(i) +
              " = \"algebra.field_add\"(%x,%x) : (!F,!F)->!F\n";
    text += R"(   func.return %s : !F
 }
 algebra.map_realize @mapped = @outer [true] : (!V)->!V
 local.func @work(%a:!V)->!V attributes {logical_origin=["work",[]]} {
   %r = local.apply @mapped(%a) {site="map"} : (!V)->!V
   local.return %r : !V
 }
 "protocol.func"() ({
 ^entry(%a:!V):
   %r = "protocol.local_call"(%a) {callee=@work,role="P",site="work"} : (!V)->!V
   "protocol.return"(%r) : (!V)->()
 }) {sym_name="main",function_type=(!V)->!V,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })";
    return text;
  };
  for (unsigned dead : {0u, 3u})
    cases.run(
        "exact admission budget with " + Twine(dead) + " dead root operations",
        [&] {
          auto module = parseSourceString<ModuleOp>(budgeted(dead), &context);
          require(bool(module), "budget fixture refused");
          ScopedDiagnosticHandler quiet(&context,
                                        [](Diagnostic &) { return success(); });
          uint64_t exact = 1 + (1 + 3 + 4 * dead + 2) + 4;
          uint64_t work = exact;
          auto error = mathematical::checkMapFormulas(*module, work);
          require(!error,
                  "exact budget refused: " + llvm::toString(std::move(error)));
          require(work == 0, "exact budget left work unspent");
          work = exact - 1;
          error = mathematical::checkMapFormulas(*module, work);
          require(bool(error), "short budget admitted the formula");
          auto message = llvm::toString(std::move(error));
          require(namesIdentifier(message, "mathematical-expansion-limit"),
                  "budget refusal identifier: " + message);
        });
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

  // One helper realized as a scalar function and under two row masks. Each
  // origin names the helper; the declaration symbol and body carry the mask.
  // Origin arguments are static bindings, so they do not record a mask.
  cases.run("one helper as a scalar and under two masks", [&] {
    auto text = edit(fixture, " local.func @work", R"(
 local.realize @scalar = @formula : (!F,!F,!F,!F)->!F
 algebra.map_realize @rows = @formula [true, false, false, false] : (!V,!F,!F,!F)->!V
 local.func @work)");
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "shared helper fixture refused");
    require(succeeded(mathematical::expandMathRealizations(*module)) &&
                succeeded(mathematical::expandMapRealizations(*module)),
            "shared helper realizations failed");
    auto origin =
        ArrayAttr::get(&context, {StringAttr::get(&context, "formula"),
                                  ArrayAttr::get(&context, {})});
    for (StringRef name : {"scalar", "mapped", "rows"})
      require(function(*module, name)->getAttr("logical_origin") == origin,
              "realized origin differs for " + name);
    auto guards = [&](StringRef name) {
      return llvm::count_if(actions(*module, name), [](auto &action) {
        return action.first == "control.require";
      });
    };
    require(guards("scalar") == 0 && guards("mapped") == 2 &&
                guards("rows") == 0,
            "row masks did not select distinct bodies");
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
