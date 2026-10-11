#include "../lib/Transforms/MathematicalComparison.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Finite.h"
#include <fstream>
#include <sstream>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
const char *laneFixture = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = tensor<?x!F>
module { "protocol.module"() ({
 "local.binding"() {sym_name="add",contract="vector.add",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="mul",contract="vector.mul",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="fill",contract="vector.fill",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="div",contract="field.inverse",arguments=["bls12-381.fr"],implementation=""} : ()->()
 func.func private @formula(%x:!F,%y:!F,%c:!F)->!F {
   %a = "algebra.field_add"(%x,%y) : (!F,!F)->!F
   %b = "algebra.field_add"(%x,%y) : (!F,!F)->!F
   %square = "algebra.field_multiply"(%a,%b) : (!F,!F)->!F
   %result = "algebra.field_add"(%square,%c) : (!F,!F)->!F
   func.return %result : !F
 }
 local.func @candidate(%x:!V,%y:!V,%c:!F,%rows:ui64,%other_rows:ui64)->!V attributes {logical_origin=["candidate",[]]} {
   %sum = "algebra.exec.vector_add"(%y,%x) {binding=@add,parameters=[],site="sum"} : (!V,!V)->!V
   %square = "algebra.exec.vector_mul"(%sum,%sum) {binding=@mul,parameters=[],site="square"} : (!V,!V)->!V
   %filled = "algebra.exec.vector_fill"(%c,%rows) {binding=@fill,parameters=[],site="fill"} : (!F,ui64)->!V
   %result = "algebra.exec.vector_add"(%filled,%square) {binding=@add,parameters=[],site="result"} : (!V,!V)->!V
   local.return %result : !V
 }
 "protocol.func"() ({
   "protocol.return"() : ()->()
 }) {sym_name="main",function_type=()->(),roles=["P"],input_roles=[],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
const char *indexed = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = tensor<?x!F>
module { "protocol.module"() ({
 "local.binding"() {sym_name="get",contract="vector.get",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "local.binding"() {sym_name="mul",contract="field.mul",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "data.domain"() ({ ^entry(%xs:!V,%ys:!V):
   %x = "data.domain_indices"(%xs) {axis=0:i64} : (!V)->!data.domain<ui64>
   %y = "data.domain_indices"(%ys) {axis=0:i64} : (!V)->!data.domain<ui64>
   %d = "data.domain_zip"(%x,%y) : (!data.domain<ui64>,!data.domain<ui64>)->!data.domain<ui64,ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64,ui64>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V,!V)->!data.domain<ui64,ui64>} : ()->()
 local.func private @step(%s:!F,%i:ui64,%j:ui64,%xs:!V,%ys:!V)->!F attributes {logical_origin=["step",[]]} {
   %x = "algebra.exec.vector_get"(%xs,%i) {binding=@get,parameters=[],site="x"} : (!V,ui64)->!F
   %y = "algebra.exec.vector_get"(%ys,%i) {binding=@get,parameters=[],site="y"} : (!V,ui64)->!F
   %p = "algebra.exec.field_multiply"(%x,%y) {binding=@mul,parameters=[],site="p"} : (!F,!F)->!F
   %r = "algebra.exec.field_add"(%p,%s) {binding=@add,parameters=[],site="r"} : (!F,!F)->!F
   local.return %r : !F
 }
 "local.finite_fold"() {sym_name="fold",function_type=(!V,!V,!F)->!F,domain=@items,step=@step} : ()->()
 local.func @work(%xs:!V,%ys:!V,%seed:!F)->!F attributes {logical_origin=["work",[]]} {
   %r = local.apply @fold(%xs,%ys,%seed) {site="fold"} : (!V,!V,!F)->!F
   local.return %r : !F
 }
 "protocol.func"() ({ ^entry(%xs:!V,%ys:!V,%seed:!F):
   %r = "protocol.local_call"(%xs,%ys,%seed) {callee=@work,role="P",site="work"} : (!V,!V,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
std::string edit(std::string source, StringRef from, StringRef to) {
  auto offset = source.find(from.str());
  require(offset != std::string::npos, "missing fixture edit: " + from);
  source.replace(offset, from.size(), to.str());
  return source;
}
std::string formulaBodies(StringRef source, StringRef candidate) {
  std::string text(laneFixture);
  auto replace = [&](StringRef first, StringRef last, StringRef body) {
    auto begin = text.find(first.str()), end = text.find(last.str(), begin);
    require(begin != std::string::npos && end != std::string::npos,
            "missing formula body");
    text.replace(begin, end - begin, body.str());
  };
  replace("   %a =", "\n }\n local.func", source);
  replace("   %sum =", "\n }\n", candidate);
  return text;
}
std::string additionChain(unsigned steps, bool candidate, bool doubling,
                          bool commute = false) {
  std::string text, previous = "%x";
  for (unsigned i = 0; i < steps; ++i) {
    std::string name = "%v" + std::to_string(i);
    std::string left = previous, right = doubling && i ? previous : "%y";
    if (commute)
      std::swap(left, right);
    text += "   " + name + " = \"" +
            (candidate ? "algebra.exec.vector_add" : "algebra.field_add") +
            "\"(" + left + "," + right + ")";
    text += candidate ? " {binding=@add,parameters=[],site=\"chain_" +
                            std::to_string(i) + "\"} : (!V,!V)->!V\n"
                      : " : (!F,!F)->!F\n";
    previous = name;
  }
  return text + (candidate ? "   local.return " : "   func.return ") +
         previous + (candidate ? " : !V\n" : " : !F\n");
}
local::FuncOp function(ModuleOp module, StringRef name) {
  local::FuncOp result;
  module.walk([&](local::FuncOp op) {
    if (op.getSymName() == name)
      result = op;
  });
  require(bool(result), "missing function " + name);
  return result;
}
Operation *bound(ModuleOp module, StringRef functionName, StringRef contract) {
  SymbolTable symbols(&module.getBody()->front());
  for (Operation &op : function(module, functionName).getBody().front()) {
    auto ref = op.getAttrOfType<FlatSymbolRefAttr>("binding");
    auto binding =
        ref ? symbols.lookup<local::OperationBindingOp>(ref.getValue())
            : local::OperationBindingOp();
    if (binding && binding.getContract() == contract)
      return &op;
  }
  require(false, "missing bound operation " + contract);
  return nullptr;
}
std::string fixture(StringRef name) {
  std::ifstream stream(std::string(ZKC_FINITE_FIXTURES) + "/" + name.str() +
                       ".mlir");
  require(bool(stream), "cannot read finite fixture");
  std::ostringstream text;
  text << stream.rdbuf();
  return text.str();
}
bool compareMap(ModuleOp module, uint64_t budget = 100000, bool sum = false) {
  SymbolTable symbols(&module.getBody()->front());
  auto source = symbols.lookup<func::FuncOp>("formula");
  auto &body = function(module, "candidate").getBody().front();
  Operation *cursor = &body.front();
  Operation *originalCursor = cursor;
  llvm::DenseSet<Operation *> bindings;
  const bool rowwise[] = {true, true, false};
  auto compare =
      sum ? mathematical::compareLaneSum : mathematical::compareLaneFormula;
  auto result = compare(source.getBody().front(), rowwise,
                        body.getArguments().take_front(3), body.getArgument(3),
                        cursor, symbols, bindings, budget);
  if (failed(result)) {
    require(cursor == originalCursor && bindings.empty(),
            "failed comparison changed caller context");
    return false;
  }
  return cursor == &body.back() && body.back().getOperand(0) == *result;
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry, MLIRContext::Threading::DISABLED);
  context.loadAllAvailableDialects();
  Cases cases;
  auto map = [&](StringRef label, std::string text, bool expected) {
    cases.run(label, [&] {
      auto module = parseSourceString<ModuleOp>(text, &context);
      require(bool(module), "map comparison fixture refused");
      require(compareMap(*module) == expected,
              "unexpected semantic comparison");
    });
  };
  map("independent candidate sharing and field commutation", laneFixture, true);
  for (bool multiply : {false, true}) {
    auto text = formulaBodies(
        "   %a = \"algebra.field_add\"(%x,%y) : (!F,!F)->!F\n"
        "   %b = \"algebra.field_add\"(%a,%c) : (!F,!F)->!F\n"
        "   func.return %b : !F\n",
        "   %cvec = \"algebra.exec.vector_fill\"(%c,%rows) "
        "{binding=@fill,parameters=[],site=\"fill\"} : (!F,ui64)->!V\n"
        "   %a = \"algebra.exec.vector_add\"(%cvec,%y) "
        "{binding=@add,parameters=[],site=\"a\"} : (!V,!V)->!V\n"
        "   %b = \"algebra.exec.vector_add\"(%a,%x) "
        "{binding=@add,parameters=[],site=\"b\"} : (!V,!V)->!V\n"
        "   local.return %b : !V\n");
    if (multiply) {
      for (unsigned i = 0; i < 2; ++i) {
        text = edit(text, "algebra.field_add", "algebra.field_multiply");
        text = edit(text, "algebra.exec.vector_add", "algebra.exec.vector_mul");
        text = edit(text, "binding=@add", "binding=@mul");
      }
    }
    map(multiply ? "multiplication associativity" : "addition associativity",
        text, true);
    map(multiply ? "multiplication operand multiplicity"
                 : "addition operand multiplicity",
        edit(text, "(%a,%x)", "(%a,%y)"), false);
  }
  constexpr unsigned maximumSteps = ring::Limits::depth - 1;
  for (bool doubling : {false, true}) {
    auto source = additionChain(maximumSteps, false, doubling);
    auto candidate = additionChain(maximumSteps, true, doubling, true);
    map(doubling ? "shared DAG at the Ring depth limit"
                 : "commuted addition chain at the Ring depth limit",
        formulaBodies(source, candidate), true);
    // Leave room to normalize both unequal DAGs; doubling still requires
    // counts far wider than a machine word.
    source = additionChain(256, false, doubling);
    candidate = additionChain(256, true, doubling, true);
    map(doubling ? "shared DAG multiplicity mutation"
                 : "addition chain multiplicity mutation",
        formulaBodies(source, edit(candidate, "(%y,%x)", "(%x,%x)")), false);
  }
  map("source depth beyond the Ring limit",
      formulaBodies(additionChain(maximumSteps + 1, false, false),
                    additionChain(maximumSteps, true, false)),
      false);
  map("candidate depth beyond the Ring limit",
      formulaBodies(additionChain(maximumSteps, false, true),
                    additionChain(maximumSteps + 1, true, true)),
      false);
  for (unsigned steps : {maximumSteps, maximumSteps + 1}) {
    auto source = additionChain(steps, false, false);
    source = edit(source, "func.return %v" + std::to_string(steps - 1),
                  "func.return %x");
    map(steps == maximumSteps
            ? "unused source chain at the Ring depth limit"
            : "unused source chain beyond the Ring depth limit",
        formulaBodies(source, additionChain(0, true, false)),
        steps == maximumSteps);
  }
  // Equal raw terms take a sharing fast path, but it cannot bypass admission
  // of unused operations or refund the work charged while reading them.
  cases.run("depth-limit comparison budget refusal is transactional", [&] {
    auto text = formulaBodies(additionChain(maximumSteps, false, false),
                              additionChain(maximumSteps, true, false));
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "depth fixture refused");
    require(!compareMap(*module, 1000), "deep comparison ignored work limit");
  });
  auto wrapped =
      edit(laneFixture, " func.func private @formula",
           " func.func private @addhelper(%a:!F,%b:!F)->!F {\n"
           "   %r = \"algebra.field_add\"(%a,%b) : (!F,!F)->!F\n"
           "   func.return %r : !F\n }\n func.func private @formula");
  wrapped = edit(wrapped, "\"algebra.field_add\"(%x,%y)",
                 "func.call @addhelper(%x,%y)");
  map("actual helper body and capture assignment", wrapped, true);
  map("helper capture mutation",
      edit(wrapped, "func.call @addhelper(%x,%y)",
           "func.call @addhelper(%x,%c)"),
      false);
  auto subtract =
      edit(laneFixture, "sym_name=\"div\",contract=\"field.inverse\"",
           "sym_name=\"sub\",contract=\"vector.sub\"");
  subtract = edit(subtract, "\"algebra.field_add\"(%square,%c)",
                  "\"algebra.field_subtract\"(%square,%c)");
  subtract = edit(subtract,
                  "\"algebra.exec.vector_add\"(%filled,%square) {binding=@add",
                  "\"algebra.exec.vector_sub\"(%filled,%square) {binding=@sub");
  map("subtraction has no commutative law", subtract, false);
  map("wrong input slot",
      edit(laneFixture, "(%y,%x) {binding=@add", "(%x,%x) {binding=@add"),
      false);
  map("wrong broadcast shape witness",
      edit(laneFixture, "(%c,%rows)", "(%c,%other_rows)"), false);
  map("changed output",
      edit(laneFixture, "local.return %result", "local.return %square"), false);
  map("unused admitted source operation",
      edit(laneFixture, "   func.return",
           "   %unused = \"algebra.field_multiply\"(%x,%c) : (!F,!F)->!F\n   "
           "func.return"),
      true);
  map("unused supported candidate operation",
      edit(laneFixture, "   local.return",
           "   %unused = \"algebra.exec.vector_mul\"(%x,%y) "
           "{binding=@mul,parameters=[],site=\"unused\"} : (!V,!V)->!V\n   "
           "local.return"),
      true);
  map("unused partial candidate operation",
      edit(laneFixture, "   local.return",
           "   %unused = \"algebra.exec.field_inverse\"(%c) "
           "{binding=@div,parameters=[],site=\"unused\"} : (!F)->!F\n   "
           "local.return"),
      false);
  cases.run("unused invalid source literal is checked", [&] {
    auto module = parseSourceString<ModuleOp>(laneFixture, &context);
    require(bool(module), "fixture refused");
    auto &unit = module->getBody()->front();
    SymbolTable symbols(&unit);
    auto source = symbols.lookup<func::FuncOp>("formula");
    OpBuilder builder(&source.getBody().front().back());
    algebra::ConstantFieldOp::create(
        builder, source.getLoc(), source.getFunctionType().getResult(0), "00");
    require(!compareMap(*module),
            "unused malformed literal escaped Ring admission");
  });
  cases.run("unused uninstalled source field is checked", [&] {
    auto module = parseSourceString<ModuleOp>(laneFixture, &context);
    require(bool(module), "fixture refused");
    SymbolTable symbols(&module->getBody()->front());
    auto source = symbols.lookup<func::FuncOp>("formula");
    OpBuilder builder(&source.getBody().front().back());
    algebra::ConstantFieldOp::create(
        builder, source.getLoc(),
        algebra::FieldType::get(&context, "uninstalled.field"), "0");
    require(!compareMap(*module),
            "unused nominal field escaped Ring admission");
  });
  cases.run("unused operation outside source fragment is checked", [&] {
    auto module = parseSourceString<ModuleOp>(laneFixture, &context);
    require(bool(module), "fixture refused");
    SymbolTable symbols(&module->getBody()->front());
    auto source = symbols.lookup<func::FuncOp>("formula");
    auto &body = source.getBody().front();
    OpBuilder builder(&body.back());
    algebra::FieldEqualOp::create(builder, source.getLoc(), builder.getI1Type(),
                                  body.getArgument(0), body.getArgument(1));
    require(!compareMap(*module), "unused unsupported source was ignored");
  });
  cases.run("explicit implementation refuses law replacement", [&] {
    auto module = parseSourceString<ModuleOp>(laneFixture, &context);
    require(bool(module), "fixture refused");
    SymbolTable symbols(&module->getBody()->front());
    auto binding = symbols.lookup<local::OperationBindingOp>("mul");
    binding->setAttr("implementation", StringAttr::get(&context, "explicit"));
    require(!compareMap(*module),
            "explicit binding was rewritten by a field law");
  });
  cases.run("budget refusal preserves cursor and bindings", [&] {
    auto module = parseSourceString<ModuleOp>(laneFixture, &context);
    require(bool(module), "fixture refused");
    require(!compareMap(*module, 2), "bounded reader ignored work limit");
  });
  cases.run("nominal field mutation", [&] {
    auto module = parseSourceString<ModuleOp>(laneFixture, &context);
    require(bool(module), "fixture refused");
    SymbolTable symbols(&module->getBody()->front());
    auto binding = symbols.lookup<local::OperationBindingOp>("mul");
    binding->setAttr(
        "arguments",
        ArrayAttr::get(&context, {StringAttr::get(&context, "bn254.fr")}));
    require(!compareMap(*module),
            "nominal field mutation escaped signature reading");
  });
  cases.run("mapped sum compares actual scalar formula with dot", [&] {
    std::string text(laneFixture);
    auto begin = text.find("   %a =");
    auto end = text.find("   func.return %result");
    require(begin != std::string::npos && end != std::string::npos,
            "missing source formula");
    text.replace(
        begin, end - begin,
        "   %result = \"algebra.field_multiply\"(%x,%y) : (!F,!F)->!F\n");
    begin = text.find("   %sum =");
    end = text.find("   local.return %result");
    require(begin != std::string::npos && end != std::string::npos,
            "missing candidate formula");
    text.replace(begin, end - begin,
                 "   %result = \"algebra.exec.vector_dot\"(%y,%x) "
                 "{binding=@mul,parameters=[],site=\"dot\"} : (!V,!V)->!F\n");
    text = edit(text, "contract=\"vector.mul\"", "contract=\"vector.dot\"");
    text = edit(text, "%other_rows:ui64)->!V", "%other_rows:ui64)->!F");
    text = edit(text, "local.return %result : !V", "local.return %result : !F");
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module) && compareMap(*module, 100000, true),
            "commuted dot did not equal independently read sum of products");
    auto *dot = bound(*module, "candidate", "vector.dot");
    dot->setOperand(0, dot->getOperand(1));
    require(!compareMap(*module, 100000, true), "dot input mutation accepted");
  });
  for (unsigned steps : {maximumSteps, maximumSteps + 1})
    cases.run(
        steps == maximumSteps
            ? "mapped sum neutral chain at the Ring depth limit"
            : "mapped sum neutral chain beyond the Ring depth limit",
        [&] {
          std::string source =
              "   %zero = \"algebra.constant\"() {value=\"0\"} : ()->!F\n";
          std::string previous = "%x";
          for (unsigned i = 0; i < steps; ++i) {
            auto name = "%n" + std::to_string(i);
            source += "   " + name + " = \"algebra.field_add\"(" + previous +
                      ",%zero) : (!F,!F)->!F\n";
            previous = name;
          }
          source += "   func.return " + previous + " : !F\n";
          auto text = formulaBodies(
              source, "   %result = \"algebra.exec.vector_sum\"(%x) "
                      "{binding=@mul,parameters=[],site=\"sum\"} : (!V)->!F\n"
                      "   local.return %result : !F\n");
          text =
              edit(text, "contract=\"vector.mul\"", "contract=\"vector.sum\"");
          text = edit(text, "%other_rows:ui64)->!V", "%other_rows:ui64)->!F");
          auto module = parseSourceString<ModuleOp>(text, &context);
          require(bool(module), "neutral chain fixture refused");
          require(compareMap(*module, 100000, true) == (steps == maximumSteps),
                  "normalization changed raw Ring depth admission");
          if (steps == maximumSteps) {
            SymbolTable symbols(&module->getBody()->front());
            auto formula = symbols.lookup<func::FuncOp>("formula");
            auto &body = formula.getBody().front();
            OpBuilder builder(&body.back());
            algebra::ConstantFieldOp::create(
                builder, formula.getLoc(), body.getArgument(0).getType(), "00");
            require(!compareMap(*module, 100000, true),
                    "neutral normalization hid an unused invalid literal");
          }
        });
  cases.run("neutral normalization preserves nominal source fields", [&] {
    auto text = formulaBodies(
        "   %zero = \"algebra.constant\"() {value=\"0\"} : ()->!F\n"
        "   %r = \"algebra.field_add\"(%x,%zero) : (!F,!F)->!F\n"
        "   func.return %r : !F\n",
        "   %result = \"algebra.exec.vector_sum\"(%x) "
        "{binding=@mul,parameters=[],site=\"sum\"} : (!V)->!F\n"
        "   local.return %result : !F\n");
    text = edit(text, "contract=\"vector.mul\"", "contract=\"vector.sum\"");
    text = edit(text, "%other_rows:ui64)->!V", "%other_rows:ui64)->!F");
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module) && compareMap(*module, 100000, true),
            "neutral sum fixture refused");
    SymbolTable symbols(&module->getBody()->front());
    auto source = symbols.lookup<func::FuncOp>("formula");
    source.getBody().front().front().getResult(0).setType(
        algebra::FieldType::get(&context, "bn254.fr"));
    require(!compareMap(*module, 100000, true),
            "foreign zero was discarded before checking source fields");
  });
  cases.run("indices access is read from source SSA", [&] {
    auto before = parseSourceString<ModuleOp>(indexed, &context);
    require(bool(before), "indexed fixture refused");
    OwningOpRef<ModuleOp> after(cast<ModuleOp>((*before)->clone()));
    require(succeeded(finite::realizeLocals(*after)),
            "indexed realization failed");
    auto *dot = bound(*after, "fold", "vector.dot");
    Value left = dot->getOperand(0), right = dot->getOperand(1);
    dot->setOperands({right, left});
    require(succeeded(finite::verifyRealizations(*before, *after)),
            "independent indexed dot comparison failed");
    dot->setOperand(1, dot->getOperand(0));
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(finite::verifyRealizations(*before, *after)),
            "indexed capture mutation was accepted");
  });
  for (StringRef name :
       {"dot", "matrix-row", "matrix-column", "bilinear", "msm-direct"})
    cases.run(name + " commuted candidate independently accepted", [&] {
      auto before = parseSourceString<ModuleOp>(fixture(name), &context);
      require(bool(before), "finite fixture refused");
      OwningOpRef<ModuleOp> after(cast<ModuleOp>((*before)->clone()));
      require(succeeded(finite::realizeLocals(*after)),
              "finite realization failed");
      auto *add = bound(*after, "fold",
                        name == "msm-direct" ? "curve.add" : "field.add");
      Value left = add->getOperand(0), right = add->getOperand(1);
      add->setOperand(0, right);
      add->setOperand(1, left);
      if (name == "dot") {
        auto *dot = bound(*after, "fold", "vector.dot");
        left = dot->getOperand(0);
        right = dot->getOperand(1);
        dot->setOperand(0, right);
        dot->setOperand(1, left);
      }
      require(succeeded(finite::verifyRealizations(*before, *after)),
              "semantic reader required producer operand order");
    });
  for (StringRef mutation : {"input", "seed", "check", "helper", "output"})
    cases.run("finite mutation " + mutation, [&] {
      auto before = parseSourceString<ModuleOp>(fixture("dot"), &context);
      require(bool(before), "finite fixture refused");
      OwningOpRef<ModuleOp> after(cast<ModuleOp>((*before)->clone()));
      require(succeeded(finite::realizeLocals(*after)),
              "finite realization failed");
      auto target = function(*after, "fold");
      if (mutation == "input")
        bound(*after, "fold", "vector.dot")
            ->setOperand(1, target.getArgument(2));
      else if (mutation == "seed") {
        auto *add = bound(*after, "fold", "field.add");
        add->setOperand(0, add->getOperand(1));
      } else if (mutation == "check")
        bound(*after, "fold", "control.require")->erase();
      else if (mutation == "helper") {
        auto helper = function(*after, "step");
        helper.getBody().front().back().setOperand(0, helper.getArgument(0));
      } else
        target.getBody().front().back().setOperand(0, target.getArgument(3));
      ScopedDiagnosticHandler silence(&context,
                                      [](Diagnostic &) { return success(); });
      require(failed(finite::verifyRealizations(*before, *after)),
              "actual candidate mutation was accepted");
    });
  for (StringRef name : {"matrix-row", "matrix-column"})
    cases.run(name + " selector mutation", [&] {
      auto before = parseSourceString<ModuleOp>(fixture(name), &context);
      require(bool(before), "finite fixture refused");
      OwningOpRef<ModuleOp> after(cast<ModuleOp>((*before)->clone()));
      require(succeeded(finite::realizeLocals(*after)),
              "finite realization failed");
      auto *dot =
          bound(*after, "fold",
                name == "matrix-row" ? "matrix.row_dot" : "matrix.column_dot");
      auto *dimension = bound(*after, "fold", "matrix.dimension");
      dot->setOperand(2, dimension->getResult(0));
      ScopedDiagnosticHandler silence(&context,
                                      [](Diagnostic &) { return success(); });
      require(failed(finite::verifyRealizations(*before, *after)),
              "selected matrix index mutation was accepted");
    });
  cases.run("module reduction preserves the group seed", [&] {
    auto before = parseSourceString<ModuleOp>(fixture("msm-direct"), &context);
    require(bool(before), "module fixture refused");
    OwningOpRef<ModuleOp> after(cast<ModuleOp>((*before)->clone()));
    require(succeeded(finite::realizeLocals(*after)),
            "module realization failed");
    auto *combine = bound(*after, "fold", "curve.add");
    combine->setOperand(0, combine->getOperand(1));
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    require(failed(finite::verifyRealizations(*before, *after)),
            "module comparison discarded the source seed");
  });
  return cases.result();
}
