#include "../lib/Transforms/MathematicalComparison.h"
#include "../lib/Transforms/ScopedCandidate.h"
#include "../lib/Transforms/ScopedPreparation.h"
#include "mlir/AsmParser/AsmParser.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Finite.h"
#include <fstream>
#include <sstream>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
const char *laneFixture = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="add",contract="vector.add",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="mul",contract="vector.mul",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="fill",contract="vector.fill",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="div",contract="field.inverse",arguments=["bls12-381.fr"],implementation=""} : ()->()
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
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="get",contract="vector.get",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="mul",contract="field.mul",arguments=["bls12-381.fr"],implementation=""} : ()->()
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
    auto binding = ref ? symbols.lookup<runtime::BindingOp>(ref.getValue())
                       : runtime::BindingOp();
    if (binding && binding.getContract() == contract)
      return &op;
  }
  require(false, "missing bound operation " + contract);
  return nullptr;
}
func::FuncOp scopedFunction(ModuleOp module, StringRef name = "work") {
  auto owner = &module.getBody()->front();
  auto function = SymbolTable(owner).lookup<func::FuncOp>(name);
  require(function && protocol::isScopedExecutionFunction(function),
          "missing scoped function " + name);
  return function;
}
Operation *scopedBound(ModuleOp module, StringRef contract,
                       StringRef function = "work") {
  Operation *result = nullptr;
  scopedFunction(module, function).walk([&](exec::ApplyOp op) {
    auto declaration = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
        op, op.getBindingAttr());
    if (!result && declaration && declaration.getContract() == contract)
      result = op;
  });
  require(result, "missing scoped binding " + contract);
  return result;
}
Value payload(Operation *operation) {
  auto dispatch = dyn_cast_or_null<exec::DispatchOp>(operation->getNextNode());
  require(dispatch && dispatch.getReturned()->getNumArguments() == 1,
          "missing scoped outcome payload");
  return dispatch.getReturned()->getArgument(0);
}
void omitScoped(Operation *operation, ValueRange replacements = {}) {
  auto dispatch = cast<exec::DispatchOp>(operation->getNextNode());
  auto *next = dispatch.getReturned(), *before = operation->getBlock();
  IRRewriter rewriter(operation->getContext());
  dispatch.erase();
  operation->erase();
  rewriter.mergeBlocks(next, before, replacements);
}
exec::ReturnOp returned(func::FuncOp function) {
  exec::ReturnOp result;
  function.walk([&](exec::ReturnOp op) { result = op; });
  require(bool(result), "missing scoped return");
  return result;
}
OwningOpRef<ModuleOp> prepare(ModuleOp source,
                              MathematicalSelectionPolicy policy = {}) {
  mathematical::RealizationWork work;
  uint64_t copies = 1000000, bytes = 16 * 1024 * 1024;
  std::optional<CapacityCause> capacity;
  auto result = protocol::prepareScopedFinite(source, work, copies, bytes,
                                              capacity, policy);
  require(bool(result), "scoped finite preparation refused");
  return result;
}
bool corresponds(ModuleOp source, ModuleOp candidate) {
  mathematical::RealizationWork work;
  return succeeded(
      protocol::verifyScopedFinitePreparation(source, candidate, work));
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
  auto result =
      sum ? mathematical::compareLaneSum(source.getBody().front(), rowwise,
                                         body.getArguments().take_front(3),
                                         body.getArgument(3), cursor, symbols,
                                         bindings, budget, &body.back())
          : mathematical::compareLaneFormula(
                source.getBody().front(), rowwise,
                body.getArguments().take_front(3), body.getArgument(3), cursor,
                symbols, bindings, budget, &body.back());
  if (failed(result)) {
    require(cursor == originalCursor && bindings.empty(),
            "failed comparison changed caller context");
    return false;
  }
  return cursor == &body.back() && body.back().getOperand(0) == *result;
}
Value emitBound(ModuleOp module, OpBuilder &builder, StringRef contract,
                ValueRange inputs, Type output, StringRef site) {
  auto &unit = module.getBody()->front();
  std::string name = "test_" + site.str();
  {
    OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToStart(&unit.getRegion(0).front());
    runtime::BindingOp::create(builder, module.getLoc(), name, contract,
                               builder.getStrArrayAttr({"bls12-381.fr"}), "",
                               mlir::ArrayAttr{});
  }
  OperationState state(module.getLoc(), protocol::boundOperationName(contract));
  state.addOperands(inputs);
  state.addTypes(output);
  state.addAttribute("binding",
                     FlatSymbolRefAttr::get(builder.getContext(), name));
  state.addAttribute("parameters", builder.getArrayAttr({}));
  state.addAttribute("site", builder.getStringAttr(site));
  return builder.create(state)->getResult(0);
}
// Replace only the ordered payload; retain its exact domain-admission prefix.
void eraseOrderedPayload(local::FuncOp target) {
  auto &body = target.getBody().front();
  auto *first = bound(target->getParentOfType<ModuleOp>(), target.getSymName(),
                      "index.constant");
  body.back().setOperands(target.getArgument(target.getNumArguments() - 1));
  while (first->getNextNode() != &body.back())
    body.back().getPrevNode()->erase();
  first->erase();
}
void pruneAddedBindings(ModuleOp before, ModuleOp after) {
  SymbolTable original(&before.getBody()->front());
  auto &unit = after.getBody()->front().getRegion(0).front();
  for (auto binding :
       llvm::make_early_inc_range(unit.getOps<runtime::BindingOp>())) {
    if (original.lookup(binding.getSymName()))
      continue;
    bool used = false;
    after.walk([&](Operation *op) {
      auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding");
      used |= ref && ref.getValue() == binding.getSymName();
    });
    if (!used)
      binding.erase();
  }
}
// Rebuild a test candidate from its admitted domain prefix and a separately
// authored payload. Preserve actual guards and canonical occurrence sites.
// No producer recipe or recognition summary supplies the replacement.
template <class Build> void replaceScopedPayload(ModuleOp module, Build build) {
  auto *owner = &module.getBody()->front();
  auto view = take(mathematical::ScopedCandidate::read(owner));
  auto old = scopedFunction(module);
  OpBuilder builder(old);
  auto replacement = func::FuncOp::create(builder, old.getLoc(), "replacement",
                                          old.getFunctionType());
  replacement->setAttrs(old->getAttrs());
  replacement.setSymName("replacement");
  replacement.addEntryBlock();
  IRMapping mapping;
  mapping.map(old.getArguments(), replacement.getArguments());
  builder.setInsertionPointToEnd(&replacement.front());
  exec::ScopedExecutionBuilder control(builder, replacement);
  auto *cursor = view->first(&old.front());
  auto *boundary = scopedBound(module, "index.constant");
  unsigned ordinal = 0;
  while (cursor != boundary) {
    require(cursor && isa<exec::ApplyOp>(cursor), "nonlinear domain prefix");
    const auto *step = view->get(cursor);
    SmallVector<Value> inputs;
    for (auto value : step->inputs)
      inputs.push_back(mapping.lookup(value));
    control.setLocation(cursor->getLoc());
    auto outputs =
        control.invoke("exec.apply", ValueRange(step->outputs).getTypes(),
                       control.scoped(inputs), cursor->getAttrs());
    mapping.map(step->outputs, outputs);
    cursor = view->next(cursor);
    ++ordinal;
  }
  auto emit = [&](StringRef contract, ValueRange inputs, Type output) {
    auto site = "fold_finite_" + std::to_string(ordinal++);
    auto name = "test_" + site;
    {
      OpBuilder::InsertionGuard restore(builder);
      builder.setInsertionPointToStart(&owner->getRegion(0).front());
      runtime::BindingOp::create(builder, module.getLoc(), name, contract,
                                 builder.getStrArrayAttr({"bls12-381.fr"}), "",
                                 ArrayAttr{});
    }
    return control
        .invoke(
            "exec.apply", output, control.scoped(inputs),
            {builder.getNamedAttr(
                 "binding", FlatSymbolRefAttr::get(module.getContext(), name)),
             builder.getNamedAttr("site", builder.getStringAttr(site)),
             builder.getNamedAttr("parameters", builder.getArrayAttr({}))})
        .front();
  };
  auto result =
      build(emit, ValueRange(replacement.getArguments()).drop_front());
  control.setLocation(returned(old)->getLoc());
  control.returned(result);
  auto name = old.getSymName().str();
  old.erase();
  replacement.setSymName(name);
  // The old loop bodies were removed with this payload. Their original source
  // callbacks remain ordinary functions and are independently compared too.
  for (auto function : llvm::make_early_inc_range(
           owner->getRegion(0).front().getOps<func::FuncOp>()))
    if (function->hasAttr("runtime.region"))
      function.erase();
}
std::string largeOrderedFold(bool calls, bool total = false,
                             unsigned fanout = 16) {
  require(!calls || !total, "the total control has no executable helper calls");
  std::string text = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="mul",contract="field.mul",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "runtime.binding"() {sym_name="constant",contract="field.constant",arguments=["bls12-381.fr"],implementation=""} : ()->()
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%d) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
)mlir";
  std::string body;
  unsigned nodes = 0;
  auto scopedCall = [&](StringRef invocation, StringRef name) {
    auto tag = "block" + name.drop_front().str();
    body += "   %out" + name.drop_front().str() + " = " + invocation.str() +
            "\n   \"exec.dispatch\"(%out" + name.drop_front().str() + ")[^" +
            tag + ",^failed] : (!exec.outcome<(!F)>)->()\n ^" + tag + "(" +
            name.str() + ":!F):\n";
  };
  auto binary = [&](StringRef contract, StringRef left, StringRef right) {
    auto name = "%n" + std::to_string(nodes++);
    if (total)
      body += "   " + name + " = \"algebra.field_" +
              (contract == "mul" ? "multiply" : "add") + "\"(" + left.str() +
              "," + right.str() + ") : (!F,!F)->!F\n";
    else
      scopedCall("\"exec.apply\"(%scope," + left.str() + "," + right.str() +
                     ") {binding=@" + contract.str() +
                     ",parameters=[],site=\"n" + std::to_string(nodes) +
                     "\"} : (!runtime.scope,!F,!F)->!exec.outcome<(!F)>",
                 name);
    return name;
  };
  auto finish = [&](StringRef value) {
    if (total)
      body += "   func.return " + value.str() + " : !F\n";
    else
      body += "   %done = \"exec.returned\"(" + value.str() +
              ") : (!F)->!exec.outcome<(!F)>\n"
              "   func.return %done : !exec.outcome<(!F)>\n"
              " ^failed(%stop:!exec.stop):\n"
              "   %failure = \"exec.failed\"(%stop) : "
              "(!exec.stop)->!exec.outcome<(!F)>\n"
              "   func.return %failure : !exec.outcome<(!F)>\n";
  };
  auto function = [&](StringRef name, StringRef arguments) {
    return " func.func private @" + name.str() + "(" +
           (total ? "" : "%scope:!runtime.scope,") + arguments.str() + ")" +
           (total ? "->!F {\n"
                  : "->!exec.outcome<(!F)> attributes "
                    "{no_inline,runtime.origin=[\"" +
                        name.str() + "\",[]]} {\n");
  };
  std::vector<std::string> layer;
  for (unsigned i = 0; i < (calls ? 1024u : 2048u); ++i) {
    auto constant = "%c" + std::to_string(i);
    if (total)
      body += "   " + constant + " = \"algebra.constant\"() {value=\"" +
              std::to_string(i + 1) + "\"} : ()->!F\n";
    else
      scopedCall("\"exec.apply\"(%scope) {binding=@constant,parameters=[\"" +
                     std::to_string(i + 1) + "\"],site=\"c" +
                     std::to_string(i) +
                     "\"} : (!runtime.scope)->!exec.outcome<(!F)>",
                 constant);
    layer.push_back(binary("mul", "%item", constant));
  }
  while (layer.size() > 1) {
    std::vector<std::string> next;
    for (unsigned i = 0; i < layer.size(); i += 2)
      next.push_back(binary("add", layer[i], layer[i + 1]));
    layer = std::move(next);
  }
  auto payload = layer[0];
  if (calls) {
    finish(payload);
    text += function("payload", "%item:!F") + body + " }\n";
    body.clear();
    for (unsigned i = 0; i < fanout; ++i) {
      payload = "%call" + std::to_string(i);
      scopedCall("func.call @payload(%scope,%item) {runtime.site=\"call" +
                     std::to_string(i) +
                     "\"} : (!runtime.scope,!F)->!exec.outcome<(!F)>",
                 payload);
    }
  }
  // The carried state occurs twice in a multiplication. No supported reduction
  // law may turn this recurrence into an identity-based aggregate.
  auto squared = binary("mul", "%state", "%state");
  auto result = binary("add", squared, payload);
  finish(result);
  text += function("step", "%state:!F,%item:!F,%xs:!V") + body + " }\n";
  body.clear();
  if (total)
    body = "   %value = \"algebra.finite_fold\"(%xs,%init) "
           "{domain=@items,step=@step} : (!V,!F)->!F\n";
  else
    scopedCall("\"exec.fold\"(%scope,%xs,%init) "
               "{domain=@items,step=@step,site=\"fold\"} : "
               "(!runtime.scope,!V,!F)->!exec.outcome<(!F)>",
               "%value");
  finish("%value");
  text += function("work", "%xs:!V,%init:!F") + body + " }\n";
  text += " \"protocol.func\"() ({ ^entry(%xs:!V,%init:!F):\n   %r = ";
  text += total ? "func.call @work(%xs,%init)"
                : "\"protocol.local_call\"(%xs,%init) "
                  "{callee=@work,role=\"P\",site=\"work\"}";
  text += R"mlir( : (!V,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",origin=["main",[]],function_type=(!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
  return text;
}
// The expression realizer initially copies total scalar operations into the
// loop; the surrounding math lowering owns their later executable lowering.
FailureOr<SmallVector<Value>>
readCopiedHelper(Operation *helper, ValueRange inputs, Operation *&cursor) {
  auto &body = helper->getRegion(0).front();
  if (body.getNumArguments() != inputs.size())
    return failure();
  IRMapping values;
  for (auto [source, target] : llvm::zip(body.getArguments(), inputs))
    values.map(source, target);
  for (Operation &op : body.without_terminator()) {
    if (!cursor || cursor->getName() != op.getName() ||
        cursor->getNumRegions() ||
        cursor->getNumOperands() != op.getNumOperands() ||
        cursor->getResultTypes() != op.getResultTypes() ||
        !cursor->getAttrOfType<StringAttr>("site") ||
        cursor->getAttrs().size() != op.getAttrs().size() + 1)
      return failure();
    for (auto attr : op.getAttrs())
      if (cursor->getAttr(attr.getName()) != attr.getValue())
        return failure();
    for (auto [source, target] :
         llvm::zip(op.getOperands(), cursor->getOperands()))
      if (values.lookupOrNull(source) != target)
        return failure();
    for (auto [source, target] :
         llvm::zip(op.getResults(), cursor->getResults()))
      values.map(source, target);
    cursor = cursor->getNextNode();
  }
  SmallVector<Value> result;
  for (Value value : body.back().getOperands()) {
    Value mapped = values.lookupOrNull(value);
    if (!mapped)
      return failure();
    result.push_back(mapped);
  }
  return result;
}
const char *operationExtents = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%xs:!V):
   %d = "data.domain_indices"(%xs) {axis=0:i64} : (!V)->!data.domain<ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<ui64>} : ()->()
 func.func private @step(%state:!F,%i:ui64,%xs:!V,%ys:!V)->!F attributes {data.preconditions=[#data.index_bound<1,2,0>,#data.index_bound<1,3,0>]} {
   %x = "data.bounded_at"(%xs,%i) : (!V,ui64)->!F
   %y = "data.bounded_at"(%ys,%i) : (!V,ui64)->!F
   %p = "algebra.field_multiply"(%x,%y) : (!F,!F)->!F
   %r = "algebra.field_add"(%state,%p) : (!F,!F)->!F
   func.return %r : !F
 }
 func.func private @outer(%xs:!V,%ys:!V,%seed:!F)->!F attributes {data.preconditions=[#data.equal_extent<0,0,1,0>]} {
   %r = "algebra.finite_fold"(%xs,%seed,%ys) {domain=@items,step=@step} : (!V,!F,!V)->!F
   func.return %r : !F
 }
 "protocol.func"() ({ ^entry(%xs:!V,%seed:!F):
   %r = func.call @outer(%xs,%xs,%seed) : (!V,!V,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
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
  cases.run("empty-result helper still admits every instruction", [&] {
    auto text = edit(laneFixture, " func.func private @formula",
                     " func.func private @observe(%a:!F) {\n"
                     "   %unused = \"algebra.field_add\"(%a,%a) : (!F,!F)->!F\n"
                     "   func.return\n }\n func.func private @formula");
    text =
        edit(text, "   %a =", "   func.call @observe(%x) : (!F)->()\n   %a =");
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "empty-result helper fixture refused");
    require(compareMap(*module), "empty-result helper was refused");
    SymbolTable symbols(&module->getBody()->front());
    auto helper = symbols.lookup<func::FuncOp>("observe");
    OpBuilder builder(&helper.getBody().front().back());
    algebra::ConstantFieldOp::create(builder, helper.getLoc(),
                                     helper.getArgument(0).getType(), "00");
    require(!compareMap(*module),
            "empty-result helper hid an invalid unused instruction");
  });
  map("candidate computed from a different helper",
      edit(wrapped, "\"algebra.exec.vector_add\"(%y,%x) {binding=@add",
           "\"algebra.exec.vector_mul\"(%y,%x) {binding=@mul"),
      false);
  map("candidate computed with the wrong helper capture",
      edit(wrapped, "(%y,%x) {binding=@add", "(%y,%y) {binding=@add"), false);
  map("helper capture mutation",
      edit(wrapped, "func.call @addhelper(%x,%y)",
           "func.call @addhelper(%x,%c)"),
      false);
  cases.run("repeated helper interpretation is memoized by arguments", [&] {
    std::string calls;
    for (unsigned i = 0; i < 64; ++i)
      calls += "   %call" + std::to_string(i) +
               " = func.call @chain(%x,%y) : (!F,!F)->!F\n";
    calls += "   func.return %call63 : !F\n";
    auto text = formulaBodies(calls, additionChain(256, true, false));
    text = edit(text, " func.func private @formula",
                " func.func private @chain(%x:!F,%y:!F)->!F {\n" +
                    additionChain(256, false, false) +
                    " }\n func.func private @formula");
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "repeated helper fixture refused");
    require(compareMap(*module, 10000),
            "identical call arguments repeated helper interpretation");
    SymbolTable symbols(&module->getBody()->front());
    auto helper = symbols.lookup<func::FuncOp>("formula");
    // A different input assignment must not reuse the previous interpretation.
    auto &lastCall = *helper.getBody().front().back().getPrevNode();
    lastCall.setOperand(1, helper.getArgument(2));
    require(!compareMap(*module, 100000),
            "memoization ignored a helper capture change");
    lastCall.setOperand(1, helper.getArgument(1));
    auto &chain = symbols.lookup<func::FuncOp>("chain").getBody().front();
    OpBuilder builder(&chain.back());
    algebra::ConstantFieldOp::create(builder, module->getLoc(),
                                     chain.getArgument(0).getType(), "00");
    require(!compareMap(*module, 100000),
            "memoization hid an unused invalid helper instruction");
  });
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
  cases.run("uninstalled source field is refused at type formation", [&] {
    bool diagnosed = false;
    ScopedDiagnosticHandler expected(&context, [&](Diagnostic &d) {
      diagnosed |= d.str().find("unknown-domain") != std::string::npos;
      return success();
    });
    require(!parseType("!algebra.field<\"uninstalled.field\">", &context) &&
                diagnosed,
            "uninstalled field reached mathematical comparison");
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
    auto binding = symbols.lookup<runtime::BindingOp>("mul");
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
    auto binding = symbols.lookup<runtime::BindingOp>("mul");
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
      auto after = prepare(*before);
      auto *add =
          scopedBound(*after, name == "msm-direct" ? "curve.add" : "field.add");
      Value left = add->getOperand(1), right = add->getOperand(2);
      add->setOperand(1, right);
      add->setOperand(2, left);
      if (name == "dot") {
        auto *dot = scopedBound(*after, "vector.dot");
        left = dot->getOperand(1);
        right = dot->getOperand(2);
        dot->setOperand(1, right);
        dot->setOperand(2, left);
      }
      require(corresponds(*before, *after),
              "semantic reader required producer operand order");
    });
  for (StringRef mutation : {"input", "seed", "check", "helper", "output"})
    cases.run("finite mutation " + mutation, [&] {
      auto before = parseSourceString<ModuleOp>(fixture("dot"), &context);
      require(bool(before), "finite fixture refused");
      auto after = prepare(*before);
      auto target = scopedFunction(*after);
      if (mutation == "input")
        scopedBound(*after, "vector.dot")->setOperand(2, target.getArgument(3));
      else if (mutation == "seed") {
        auto *add = scopedBound(*after, "field.add");
        add->setOperand(1, add->getOperand(2));
      } else if (mutation == "check")
        omitScoped(scopedBound(*after, "control.require"));
      else if (mutation == "helper") {
        auto helper = scopedFunction(*after, "step");
        returned(helper)->setOperand(0, helper.getArgument(1));
      } else
        returned(target)->setOperand(0, target.getArgument(4));
      ScopedDiagnosticHandler silence(&context,
                                      [](Diagnostic &) { return success(); });
      require(!corresponds(*before, *after),
              "actual candidate mutation was accepted");
    });
  for (StringRef name : {"matrix-row", "matrix-column"})
    cases.run(name + " selector mutation", [&] {
      auto before = parseSourceString<ModuleOp>(fixture(name), &context);
      require(bool(before), "finite fixture refused");
      auto after = prepare(*before);
      auto *dot =
          scopedBound(*after, name == "matrix-row" ? "matrix.row_dot"
                                                   : "matrix.column_dot");
      auto *dimension = scopedBound(*after, "matrix.dimension");
      dot->setOperand(3, payload(dimension));
      ScopedDiagnosticHandler silence(&context,
                                      [](Diagnostic &) { return success(); });
      require(!corresponds(*before, *after),
              "selected matrix index mutation was accepted");
    });
  cases.run("expanded callback fan-out respects program body capacity", [&] {
    auto source = parseSourceString<ModuleOp>(largeOrderedFold(true), &context);
    require(source && succeeded(verify(*source)),
            "unexpanded fan-out source refused");
    // Sixteen 3071-operation callbacks exceed the program's 32768-item body
    // limit after mandatory helper expansion. The former declaration-only
    // fixture retained helper calls and never exercised this boundary.
    bool capacity = false;
    ScopedDiagnosticHandler diagnostics(&context, [&](Diagnostic &diagnostic) {
      capacity |= diagnostic.str().find("source-limit") != std::string::npos;
      return success();
    });
    mathematical::RealizationWork work;
    uint64_t copies = 1000000, bytes = 16 * 1024 * 1024;
    std::optional<CapacityCause> cause;
    auto candidate = protocol::prepareScopedFinite(*source, work, copies, bytes,
                                                   cause, {false, false});
    require(!candidate && capacity && succeeded(verify(*source)),
            "oversized expanded body was published or changed its source");
  });
  for (bool calls : {false, true})
    cases.run(
        calls ? "ordered fallback with helper call fan-out"
              : "ordered fallback with a large arithmetic step",
        [&] {
          auto before = parseSourceString<ModuleOp>(
              largeOrderedFold(calls, false, 4), &context);
          require(bool(before), "large ordered source refused");
          auto after = prepare(*before);
          auto target = scopedFunction(*after);
          Operation *cursor = scopedBound(*after, "index.constant");
          auto *saved = cursor;
          SymbolTable symbols(&after->getBody()->front());
          require(!mathematical::hasFinitePayloadContract(cursor, symbols),
                  "ordered loop entered optional semantic comparison");
          auto sourceClosure = take(protocol::readSourceExecutionClosure(
              &before->getBody()->front()));
          exec::FoldOp source;
          before->walk([&](exec::FoldOp op) { source = op; });
          finite::Computation computation;
          require(succeeded(finite::describe(source, computation)),
                  "finite description failed");
          computation.scopedSource = &sourceClosure;
          auto candidate = take(
              mathematical::ScopedCandidate::read(&after->getBody()->front()));
          llvm::DenseSet<Operation *> bindings{symbols.lookup("add")};
          auto savedBindings = bindings;
          uint64_t work = 10;
          auto result = mathematical::compareFinitePayload(
              computation, target.getArguments().drop_front(),
              payload(scopedBound(*after, "vector.length")), cursor, symbols,
              bindings, work, nullptr, nullptr, nullptr, candidate.get());
          require(failed(result) && work == 0 && cursor == saved &&
                      bindings == savedBindings,
                  "exhausted optional comparison changed caller state");
          require(
              corresponds(*before, *after),
              "ordered reader failed after an exhausted optional comparison");
        });
  cases.run(
      "large total arithmetic step retains the inline ordered fallback", [&] {
        auto module = parseSourceString<ModuleOp>(largeOrderedFold(false, true),
                                                  &context);
        require(bool(module), "large total source refused");
        algebra::FiniteFoldOp source;
        module->walk([&](algebra::FiniteFoldOp op) { source = op; });
        require(bool(source), "missing total fold");
        OpBuilder builder(
            &module->getBody()->front().getRegion(0).front(),
            module->getBody()->front().getRegion(0).front().end());
        auto signature = builder.getFunctionType(source->getOperandTypes(),
                                                 source->getResultTypes());
        auto target = local::FuncOp::create(builder, source.getLoc(),
                                            "candidate", signature);
        auto *body = target.addEntryBlock();
        builder.setInsertionPointToEnd(body);
        require(
            failed(finite::realizeExpression(source, body->getArguments(),
                                             builder)) &&
                body->empty(),
            "missing prepared occurrence site did not refuse before emission");
        source->setAttr("site", builder.getStringAttr("total_fold"));
        auto expected =
            finite::realizeExpression(source, body->getArguments(), builder);
        require(succeeded(expected), "large total ordered realization failed");
        auto ret = local::ReturnOp::create(builder, source.getLoc(), *expected);
        Operation *cursor = &body->front();
        auto actual = finite::verifyExpression(source, body->getArguments(),
                                               cursor, readCopiedHelper);
        require(succeeded(actual) && *actual == *expected && cursor == ret,
                "inline semantic comparison prevented ordered verification");
      });
  cases.run("inline identity collect leaves an arbitrary caller suffix", [&] {
    auto text =
        edit(fixture("total-collect"), "func.return %z", "func.return %x");
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "identity collect source refused");
    algebra::FiniteCollectOp source;
    module->walk([&](algebra::FiniteCollectOp op) { source = op; });
    require(bool(source), "missing total collect");
    OpBuilder builder(&module->getBody()->front().getRegion(0).front(),
                      module->getBody()->front().getRegion(0).front().end());
    auto field = source->getOperand(1).getType();
    auto suffixHelper =
        local::FuncOp::create(builder, source.getLoc(), "suffix_helper",
                              builder.getFunctionType({field}, {field}));
    auto *helperBody = suffixHelper.addEntryBlock();
    builder.setInsertionPointToEnd(helperBody);
    local::ReturnOp::create(builder, source.getLoc(),
                            helperBody->getArgument(0));
    builder.setInsertionPointAfter(suffixHelper);
    auto target = local::FuncOp::create(
        builder, source.getLoc(), "candidate",
        builder.getFunctionType(source->getOperandTypes(),
                                source->getResultTypes()));
    auto *body = target.addEntryBlock();
    builder.setInsertionPointToEnd(body);
    source->setAttr("site", builder.getStringAttr("identity_collect"));
    auto expected =
        finite::realizeExpression(source, body->getArguments(), builder);
    require(succeeded(expected) && expected->size() == 1 &&
                (*expected)[0] == body->getArgument(0),
            "identity collect emitted a nonidentity payload");
    auto suffix = local::ApplyOp::create(
        builder, source.getLoc(), TypeRange{field},
        ValueRange{body->getArgument(1)}, "suffix_helper", "suffix");
    local::ReturnOp::create(builder, source.getLoc(), *expected);
    Operation *cursor = &body->front();
    auto result = finite::verifyExpression(source, body->getArguments(), cursor,
                                           readCopiedHelper);
    require(succeeded(result) && *result == *expected && cursor == suffix,
            "identity collect consumed or refused the caller's suffix");
  });
  for (bool helperEquality : {false, true})
    cases.run(
        helperEquality ? "helper extent premise admits a dot"
                       : "operation-only extent facts retain ordered traversal",
        [&] {
          std::string text(operationExtents);
          if (helperEquality)
            text =
                edit(text, "#data.index_bound<1,3,0>]",
                     "#data.index_bound<1,3,0>,#data.equal_extent<2,0,3,0>]");
          auto module = parseSourceString<ModuleOp>(text, &context);
          require(bool(module), "operation-extent fixture refused");
          algebra::FiniteFoldOp source;
          module->walk([&](algebra::FiniteFoldOp op) { source = op; });
          require(bool(source) &&
                      source->getOperand(0) != source->getOperand(2) &&
                      finite::provesEqualExtent(source->getOperand(0), 0,
                                                source->getOperand(2), 0),
                  "fixture did not establish distinct operation-level extents");
          SymbolTable sourceSymbols(&module->getBody()->front());
          auto helper = sourceSymbols.lookup<func::FuncOp>("step");
          require(finite::provesEqualExtent(helper.getArgument(2), 0,
                                            helper.getArgument(3),
                                            0) == helperEquality,
                  "fixture did not distinguish helper from operation evidence");
          OpBuilder builder(
              &module->getBody()->front().getRegion(0).front(),
              module->getBody()->front().getRegion(0).front().end());
          auto signature = builder.getFunctionType(source->getOperandTypes(),
                                                   source->getResultTypes());
          auto target = local::FuncOp::create(builder, source.getLoc(),
                                              "candidate", signature);
          auto *body = target.addEntryBlock();
          builder.setInsertionPointToEnd(body);
          source->setAttr("site", builder.getStringAttr("extent_fold"));
          auto expected =
              finite::realizeExpression(source, body->getArguments(), builder);
          require(succeeded(expected), "extent-aware realization failed");
          auto ret =
              local::ReturnOp::create(builder, source.getLoc(), *expected);
          bool dot = false, loop = false;
          target.walk([&](Operation *op) {
            dot |= op->getName().getStringRef() == "algebra.exec.vector_dot";
            loop |= isa<local::LocalForOp>(op);
          });
          require(dot == helperEquality && loop != helperEquality,
                  "producer used extent evidence unavailable to its reader");
          Operation *cursor = &body->front();
          auto actual = finite::verifyExpression(source, body->getArguments(),
                                                 cursor, readCopiedHelper);
          require(
              succeeded(actual) && *actual == *expected && cursor == ret,
              "operation-level extent facts broke realization verification");
          if (!helperEquality) {
            // A forged dot has the right value under the operation's premise,
            // but the current bulk reader intentionally has no such evidence.
            finite::Computation computation;
            require(succeeded(finite::describe(source, computation)),
                    "finite description failed");
            eraseOrderedPayload(target);
            builder.setInsertionPoint(&body->back());
            auto args = body->getArguments();
            Value product =
                emitBound(*module, builder, "vector.dot", {args[0], args[2]},
                          args[1].getType(), "dot");
            Value result =
                emitBound(*module, builder, "field.add", {args[1], product},
                          product.getType(), "seed");
            body->back().setOperand(0, result);
            SymbolTable symbols(&module->getBody()->front());
            cursor = product.getDefiningOp();
            auto *saved = cursor;
            llvm::DenseSet<Operation *> bindings;
            uint64_t work = 100000;
            auto refused = mathematical::compareFinitePayload(
                computation, args, body->front().getResult(0), cursor, symbols,
                bindings, work, &body->back());
            require(
                failed(refused) && cursor == saved && bindings.empty(),
                "operation-only extent evidence leaked into bulk comparison");
          }
        });
  cases.run("zipped nested product is diagonal, not bilinear", [&] {
    auto before = parseSourceString<ModuleOp>(fixture("bilinear"), &context);
    require(bool(before), "bilinear source refused");
    data::DomainProductOp product;
    before->walk([&](data::DomainProductOp op) { product = op; });
    require(product && product->getNumOperands() == 2,
            "missing Cartesian domain");
    OpBuilder builder(product);
    auto right = product->getOperand(1);
    auto nested = data::DomainProductOp::create(
        builder, product.getLoc(), right.getType(), ValueRange{right});
    auto zipped = data::DomainZipOp::create(
        builder, product.getLoc(), product->getResult(0).getType(),
        ValueRange{product->getOperand(0), nested->getResult(0)});
    product->getResult(0).replaceAllUsesWith(zipped->getResult(0));
    product.erase();
    require(succeeded(verify(*before)), "diagonal domain fixture refused");
    auto after = prepare(*before, {false, false});
    require(corresponds(*before, *after),
            "ordered diagonal traversal was refused");
    // M is all ones and both vectors are [1,1]. Zip visits two cells;
    // the independently iterated Cartesian product visits four.
    unsigned diagonal = 0, bilinear = 0;
    for (unsigned i = 0; i < 2; ++i) {
      ++diagonal;
      for (unsigned j = 0; j < 2; ++j)
        ++bilinear;
    }
    require(diagonal == 2 && bilinear == 4, "counterexample collapsed");
    replaceScopedPayload(*after, [&](auto emit, ValueRange args) {
      auto product =
          emit("matrix.bilinear", args.take_front(3), args[3].getType());
      return emit("field.add", {args[3], product}, product.getType());
    });
    pruneAddedBindings(*before, *after);
    require(succeeded(verify(*after)), "bilinear mutation must be valid IR");
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    require(!corresponds(*before, *after),
            "zipped diagonal was accepted as a bilinear contraction");
  });
  for (bool row : {true, false})
    for (unsigned selectorCase : {0u, 1u, 2u})
      cases.run(
          std::string("dead ") + (row ? "row" : "column") + " contraction " +
              (selectorCase == 0   ? "without selector admission"
               : selectorCase == 1 ? "with selector admission"
                                   : "with a different admitted selector"),
          [&] {
            auto before = parseSourceString<ModuleOp>(
                fixture(row ? "matrix-row" : "matrix-column"), &context);
            require(bool(before), "dead contraction source refused");
            auto step = scopedFunction(*before, "step");
            auto *add = scopedBound(*before, "field.add", "step");
            add->setOperand(2, step.getArgument(3));
            omitScoped(scopedBound(*before, "field.mul", "step"),
                       step.getArgument(3));
            auto index = IntegerType::get(&context, 64, IntegerType::Unsigned);
            if (selectorCase == 0) {
              auto domain = SymbolTable(&before->getBody()->front())
                                .lookup<data::DomainOp>("items");
              auto &body = domain.getBody().front();
              auto *selected = &body.front();
              OpBuilder builder(selected);
              auto indices = data::DomainIndicesOp::create(
                  builder, selected->getLoc(),
                  data::DomainType::get(&context, {index}),
                  selected->getOperand(0), row ? 1 : 0);
              selected->getResult(0).replaceAllUsesWith(indices->getResult(0));
              selected->erase();
              auto *zip = body.back().getOperand(0).getDefiningOp();
              auto field = step.getArgument(3).getType();
              auto result =
                  data::DomainType::get(&context, {index, field, field});
              zip->getResult(0).setType(result);
              domain.setFunctionType(FunctionType::get(
                  &context, domain.getFunctionType().getInputs(), result));
              step.getArgument(2).setType(index);
              step.setFunctionType(
                  FunctionType::get(&context, step.front().getArgumentTypes(),
                                    step.getResultTypes()));
            }
            if (selectorCase == 2) {
              auto work = scopedFunction(*before);
              require(succeeded(work.insertArgument(work.getNumArguments(),
                                                    index, DictionaryAttr{},
                                                    work.getLoc())),
                      "extra work selector refused");
              require(succeeded(step.insertArgument(step.getNumArguments(),
                                                    index, DictionaryAttr{},
                                                    step.getLoc())),
                      "extra step selector refused");
              work.walk([&](exec::FoldOp fold) {
                fold->insertOperands(fold->getNumOperands(),
                                     work.getArguments().back());
              });
              before->walk([&](protocol_ir::MathematicalOp function) {
                auto &body = function.getBody().front();
                body.addArgument(index, function.getLoc());
                auto signature = function.getFunctionType();
                function.setFunctionType(FunctionType::get(
                    &context, body.getArgumentTypes(), signature.getResults()));
                SmallVector<Attribute> roles(
                    function.getInputRoles().getValue());
                roles.push_back(
                    ArrayAttr::get(&context, {StringAttr::get(&context, "P")}));
                function.setInputRolesAttr(ArrayAttr::get(&context, roles));
                function.walk([&](protocol_ir::LocalCallOp call) {
                  call->insertOperands(call->getNumOperands(),
                                       body.getArguments().back());
                });
              });
            }
            require(succeeded(verify(*before)),
                    "dead contraction fixture refused");
            auto after = prepare(*before, {false, false});
            replaceScopedPayload(*after, [&](auto emit, ValueRange args) {
              emit(row ? "matrix.row_dot" : "matrix.column_dot",
                   {args[0], args[1], args[selectorCase == 2 ? 5 : 3]},
                   args[4].getType());
              auto sum = emit("vector.sum", args[1], args[4].getType());
              return emit("field.add", {args[4], sum}, sum.getType());
            });
            pruneAddedBindings(*before, *after);
            require(succeeded(verify(*after)),
                    "dead contraction is invalid IR");
            ScopedDiagnosticHandler silence(
                &context, [](Diagnostic &) { return success(); });
            require(corresponds(*before, *after) == (selectorCase == 1),
                    "unused contraction selector admission was not enforced");
          });
  cases.run("module reduction preserves the group seed", [&] {
    auto before = parseSourceString<ModuleOp>(fixture("msm-direct"), &context);
    require(bool(before), "module fixture refused");
    auto after = prepare(*before);
    auto *combine = scopedBound(*after, "curve.add");
    combine->setOperand(1, combine->getOperand(2));
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    require(!corresponds(*before, *after),
            "module comparison discarded the source seed");
  });
  return cases.result();
}
