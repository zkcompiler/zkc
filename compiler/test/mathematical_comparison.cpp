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
#include "support/ComputationRecipes.h"
#include "support/NativeCases.h"
#include "support/ScopedFixture.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
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
!V = !data.field_vector<"bls12-381.fr">
!O = !exec.outcome<(!V)>
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="add",contract="vector.add",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="mul",contract="vector.mul",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !data.field_vector<"bls12-381.fr">, !data.field_vector<"bls12-381.fr">) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="fill",contract="vector.fill",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !algebra.field<"bls12-381.fr">, ui64) -> !exec.outcome<(!data.field_vector<"bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="div",contract="field.inverse",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>} : ()->()
 func.func private @formula(%x:!F,%y:!F,%c:!F)->!F {
   %a = "algebra.field_add"(%x,%y) : (!F,!F)->!F
   %b = "algebra.field_add"(%x,%y) : (!F,!F)->!F
   %square = "algebra.field_multiply"(%a,%b) : (!F,!F)->!F
   %result = "algebra.field_add"(%square,%c) : (!F,!F)->!F
   func.return %result : !F
 }
 func.func @candidate(%scope:!runtime.scope,%x:!V,%y:!V,%c:!F,%rows:ui64,%other_rows:ui64)->!O attributes {no_inline,runtime.origin=["candidate",[]]} {   %sum_attempt = "exec.apply"(%scope,%y,%x) {binding=@add,parameters=[],site="sum"} : (!runtime.scope,!V,!V)->!exec.outcome<(!V)>
   "exec.dispatch"(%sum_attempt)[^sum,^failed] : (!exec.outcome<(!V)>)->()
 ^sum(%sum:!V):
   %square_attempt = "exec.apply"(%scope,%sum,%sum) {binding=@mul,parameters=[],site="square"} : (!runtime.scope,!V,!V)->!exec.outcome<(!V)>
   "exec.dispatch"(%square_attempt)[^square,^failed] : (!exec.outcome<(!V)>)->()
 ^square(%square:!V):
   %fill_attempt = "exec.apply"(%scope,%c,%rows) {binding=@fill,parameters=[],site="fill"} : (!runtime.scope,!F,ui64)->!exec.outcome<(!V)>
   "exec.dispatch"(%fill_attempt)[^fill,^failed] : (!exec.outcome<(!V)>)->()
 ^fill(%filled:!V):
   %result_attempt = "exec.apply"(%scope,%filled,%square) {binding=@add,parameters=[],site="result"} : (!runtime.scope,!V,!V)->!exec.outcome<(!V)>
   "exec.dispatch"(%result_attempt)[^result,^failed] : (!exec.outcome<(!V)>)->()
 ^result(%result:!V):
   %done = "exec.returned"(%result) : (!V)->!O
   func.return %done : !O
 ^failed(%reason:!exec.stop):
   %failed = "exec.failed"(%reason) : (!exec.stop)->!O
   func.return %failed : !O
 }
 "protocol.func"() ({
   "protocol.return"() : ()->()
 }) {sym_name="main",function_type=()->(),roles=["P"],input_roles=[],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
std::string edit(std::string source, StringRef from, StringRef to) {
  auto offset = source.find(from.str());
  require(offset != std::string::npos, "missing fixture edit: " + from);
  source.replace(offset, from.size(), to.str());
  return source;
}
// Fixture rewrites that deliberately choose a different well-formed contract
// must supply that contract's ABI. Negative tests still mutate ports directly.
std::string withBindingSignature(std::string source, StringRef name,
                                 StringRef signature) {
  auto declaration = source.find("sym_name=\"" + name.str() + "\"");
  auto begin = source.find("function_type=", declaration);
  auto end = source.find("} : ()->()", begin);
  require(declaration != std::string::npos && begin != std::string::npos &&
              end != std::string::npos,
          "missing binding fixture signature");
  source.replace(begin, end - begin, "function_type=" + signature.str());
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
  replace("   %a =", "\n }\n func.func @candidate", source);
  replace("   %sum_attempt =", " ^failed", candidate);
  if (!candidate.contains("^failed")) {
    auto begin = text.find(" ^failed");
    text.erase(begin, text.find("\n }", begin) - begin);
  }
  return text;
}
std::string laneReturn(StringRef value, StringRef type) {
  return "   %done = \"exec.returned\"(" + value.str() + ") : (" + type.str() +
         ")->!O\n   func.return %done : !O\n";
}
std::string additionChain(unsigned steps, bool candidate, bool doubling,
                          bool commute = false) {
  std::string text, previous = "%x";
  for (unsigned i = 0; i < steps; ++i) {
    std::string name = "%v" + std::to_string(i);
    std::string left = previous, right = doubling && i ? previous : "%y";
    if (commute)
      std::swap(left, right);
    if (candidate)
      text += scopedApply("add", "chain_" + std::to_string(i),
                          left + "," + right, "!V,!V", name, "!V");
    else
      text += "   " + name + " = \"algebra.field_add\"(" + left + "," + right +
              ") : (!F,!F)->!F\n";
    previous = name;
  }
  return text + (candidate ? laneReturn(previous, "!V")
                           : "   func.return " + previous + " : !F\n");
}
Operation *bound(ModuleOp module, StringRef functionName, StringRef contract) {
  auto *owner = &module.getBody()->front();
  SymbolTable symbols(owner);
  Operation *result = nullptr;
  symbols.lookup<func::FuncOp>(functionName).walk([&](exec::ApplyOp op) {
    auto binding = symbols.lookup<runtime::BindingOp>(op.getBinding());
    if (binding && binding.getContract() == contract)
      result = op;
  });
  require(result, "missing bound operation " + contract);
  return result;
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
  auto *owner = &module.getBody()->front();
  SymbolTable symbols(owner);
  auto source = symbols.lookup<func::FuncOp>("formula");
  auto target = scopedFunction(module, "candidate");
  auto view = mathematical::ScopedCandidate::read(owner);
  if (!view) {
    llvm::consumeError(view.takeError());
    return false;
  }
  auto args = target.getArguments().drop_front();
  auto end = returned(target);
  Operation *cursor = (*view)->first(&target.front());
  Operation *originalCursor = cursor;
  llvm::DenseSet<Operation *> bindings;
  const bool rowwise[] = {true, true, false};
  auto compare =
      sum ? mathematical::compareLaneSum : mathematical::compareLaneFormula;
  auto result = compare(source.front(), rowwise, args.take_front(3), args[3],
                        cursor, symbols, bindings, budget, end, nullptr,
                        nullptr, end.getOperand(0), view->get());
  if (failed(result)) {
    require(cursor == originalCursor && bindings.empty(),
            "failed comparison changed caller context");
    return false;
  }
  return cursor == end && end.getOperand(0) == *result;
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
template <class Build>
void replaceScopedPayload(ModuleOp module, Build build,
                          StringRef functionName = "work") {
  auto *owner = &module.getBody()->front();
  auto view = take(mathematical::ScopedCandidate::read(owner));
  auto old = scopedFunction(module, functionName);
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
  auto *boundary = scopedBound(module, "index.constant", functionName);
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
                                 builder.getStrArrayAttr({"bls12-381.fr"}), "");
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
!V = !data.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="mul",contract="field.mul",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="constant",contract="field.constant",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>} : ()->()
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
      body += "   " + constant +
              " = \"algebra.constant\"() {value=#algebra.literal<!F, " +
              std::to_string(i + 1) + " : ui255>} : ()->!F\n";
    else
      scopedCall("\"exec.apply\"(%scope) "
                 "{binding=@constant,parameters=[#algebra.literal<!F, " +
                     std::to_string(i + 1) + " : ui255>],site=\"c" +
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
    body = "   %value = \"data.finite_fold\"(%xs,%init) "
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
// Test the default total numerical route. The larger required allowance lets a
// deliberately large scalar callback exercise ordered comparison rather than
// fail on the default construction quota.
OwningOpRef<ModuleOp> realizeTotal(ModuleOp source, StringRef site = "total",
                                   uint64_t copies = 1000000) {
  mathematical::RealizationWork work;
  uint64_t bytes = 16 * 1024 * 1024;
  uint64_t checking = 8 * 1024 * 1024;
  finite::VerificationLimits limits;
  limits.sharedContext = &checking;
  auto result =
      computation::realizeEntry(source, site, {}, work, copies, bytes, limits);
  require(bool(result), "total scoped realization refused");
  return result;
}
OwningOpRef<ModuleOp> totalOccurrenceSource(Operation *source) {
  auto unit = computationRecipeUnit(SymbolTable::getNearestSymbolTable(source));
  OpBuilder builder(unit->getBody(), unit->getBody()->end());
  auto entry =
      func::FuncOp::create(builder, source->getLoc(), "candidate",
                           builder.getFunctionType(source->getOperandTypes(),
                                                   source->getResultTypes()));
  builder.setInsertionPointToEnd(entry.addEntryBlock());
  IRMapping values;
  values.map(source->getOperands(), entry.getArguments());
  auto *operation = builder.clone(*source, values);
  func::ReturnOp::create(builder, source->getLoc(), operation->getResults());
  return unit;
}
const char *operationExtents = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !data.field_vector<"bls12-381.fr">
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
   %r = "data.finite_fold"(%xs,%seed,%ys) {domain=@items,step=@step} : (!V,!F,!V)->!F
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
        "   %fill_attempt = \"exec.apply\"(%scope,%c,%rows) "
        "{binding=@fill,parameters=[],site=\"fill\"} : "
        "(!runtime.scope,!F,ui64)->!exec.outcome<(!V)>\n   "
        "\"exec.dispatch\"(%fill_attempt)[^fill,^failed] : "
        "(!exec.outcome<(!V)>)->()\n ^fill(%cvec:!V):\n   %a_attempt = "
        "\"exec.apply\"(%scope,%cvec,%y) "
        "{binding=@add,parameters=[],site=\"a\"} : "
        "(!runtime.scope,!V,!V)->!exec.outcome<(!V)>\n   "
        "\"exec.dispatch\"(%a_attempt)[^a,^failed] : "
        "(!exec.outcome<(!V)>)->()\n ^a(%a:!V):\n   %b_attempt = "
        "\"exec.apply\"(%scope,%a,%x) {binding=@add,parameters=[],site=\"b\"} "
        ": (!runtime.scope,!V,!V)->!exec.outcome<(!V)>\n   "
        "\"exec.dispatch\"(%b_attempt)[^b,^failed] : "
        "(!exec.outcome<(!V)>)->()\n ^b(%b:!V):\n   %done = "
        "\"exec.returned\"(%b) : (!V)->!O\n   func.return %done : !O\n");
    if (multiply) {
      for (unsigned i = 0; i < 2; ++i) {
        text = edit(text, "algebra.field_add", "algebra.field_multiply");
        text = edit(text, "binding=@add", "binding=@mul");
      }
    }
    map(multiply ? "multiplication associativity" : "addition associativity",
        text, true);
    map(multiply ? "multiplication operand multiplicity"
                 : "addition operand multiplicity",
        edit(text, "(%scope,%a,%x)", "(%scope,%a,%y)"), false);
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
        formulaBodies(source,
                      edit(candidate, "(%scope,%y,%x)", "(%scope,%x,%x)")),
        false);
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
    algebra::ConstantFieldOp::create(
        builder, helper.getLoc(), helper.getArgument(0).getType(),
        algebra::FieldLiteralAttr::get(
            &context, cast<algebra::FieldType>(helper.getArgument(0).getType()),
            builder.getI64IntegerAttr(0)));
    require(!compareMap(*module),
            "empty-result helper hid an invalid unused instruction");
  });
  map("candidate computed from a different helper",
      edit(wrapped, "\"exec.apply\"(%scope,%y,%x) {binding=@add",
           "\"exec.apply\"(%scope,%y,%x) {binding=@mul"),
      false);
  map("candidate computed with the wrong helper capture",
      edit(wrapped, "(%scope,%y,%x) {binding=@add",
           "(%scope,%y,%y) {binding=@add"),
      false);
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
    algebra::ConstantFieldOp::create(
        builder, module->getLoc(), chain.getArgument(0).getType(),
        algebra::FieldLiteralAttr::get(
            &context, cast<algebra::FieldType>(chain.getArgument(0).getType()),
            builder.getI64IntegerAttr(0)));
    require(!compareMap(*module, 100000),
            "memoization hid an unused invalid helper instruction");
  });
  auto subtract =
      edit(laneFixture, "sym_name=\"div\",contract=\"field.inverse\"",
           "sym_name=\"sub\",contract=\"vector.sub\"");
  subtract = edit(subtract, "\"algebra.field_add\"(%square,%c)",
                  "\"algebra.field_subtract\"(%square,%c)");
  subtract =
      edit(subtract, "\"exec.apply\"(%scope,%filled,%square) {binding=@add",
           "\"exec.apply\"(%scope,%filled,%square) {binding=@sub");
  subtract = withBindingSignature(
      subtract, "sub", "(!runtime.scope,!V,!V)->!exec.outcome<(!V)>");
  map("subtraction has no commutative law", subtract, false);
  map("wrong input slot",
      edit(laneFixture, "(%scope,%y,%x) {binding=@add",
           "(%scope,%x,%x) {binding=@add"),
      false);
  map("wrong broadcast shape witness",
      edit(laneFixture, "(%scope,%c,%rows)", "(%scope,%c,%other_rows)"), false);
  map("changed output",
      edit(laneFixture, "\"exec.returned\"(%result)",
           "\"exec.returned\"(%square)"),
      false);
  map("unused admitted source operation",
      edit(laneFixture, "   func.return",
           "   %unused = \"algebra.field_multiply\"(%x,%c) : (!F,!F)->!F\n   "
           "func.return"),
      true);
  map("unused supported candidate operation",
      edit(laneFixture, "   %done = \"exec.returned\"",
           "   %unused_attempt = \"exec.apply\"(%scope,%x,%y) "
           "{binding=@mul,parameters=[],site=\"unused\"} : "
           "(!runtime.scope,!V,!V)->!exec.outcome<(!V)>\n   "
           "\"exec.dispatch\"(%unused_attempt)[^unused,^failed] : "
           "(!exec.outcome<(!V)>)->()\n ^unused(%unused:!V):\n   %done = "
           "\"exec.returned\""),
      true);
  map("unused partial candidate operation",
      edit(laneFixture, "   %done = \"exec.returned\"",
           "   %unused_attempt = \"exec.apply\"(%scope,%c) "
           "{binding=@div,parameters=[],site=\"unused\"} : "
           "(!runtime.scope,!F)->!exec.outcome<(!F)>\n   "
           "\"exec.dispatch\"(%unused_attempt)[^unused,^failed] : "
           "(!exec.outcome<(!F)>)->()\n ^unused(%unused:!F):\n   %done = "
           "\"exec.returned\""),
      false);
  cases.run("unused invalid source literal is checked", [&] {
    auto module = parseSourceString<ModuleOp>(laneFixture, &context);
    require(bool(module), "fixture refused");
    auto &unit = module->getBody()->front();
    SymbolTable symbols(&unit);
    auto source = symbols.lookup<func::FuncOp>("formula");
    OpBuilder builder(&source.getBody().front().back());
    algebra::ConstantFieldOp::create(
        builder, source.getLoc(), source.getFunctionType().getResult(0),
        algebra::FieldLiteralAttr::get(
            &context,
            cast<algebra::FieldType>(source.getFunctionType().getResult(0)),
            builder.getI64IntegerAttr(0)));
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
    begin = text.find("   %sum_attempt =");
    end = text.find("   %done = \"exec.returned\"(%result)");
    require(begin != std::string::npos && end != std::string::npos,
            "missing candidate formula");
    text.replace(begin, end - begin,
                 "   %dot_attempt = \"exec.apply\"(%scope,%y,%x) "
                 "{binding=@mul,parameters=[],site=\"dot\"} : "
                 "(!runtime.scope,!V,!V)->!exec.outcome<(!F)>\n   "
                 "\"exec.dispatch\"(%dot_attempt)[^dot,^failed] : "
                 "(!exec.outcome<(!F)>)->()\n ^dot(%result:!F):\n");
    text = edit(text, "contract=\"vector.mul\"", "contract=\"vector.dot\"");
    text = withBindingSignature(text, "mul",
                                "(!runtime.scope,!V,!V)->!exec.outcome<(!F)>");
    text = edit(text, "!O = !exec.outcome<(!V)>", "!O = !exec.outcome<(!F)>");
    text = edit(text, "\"exec.returned\"(%result) : (!V)",
                "\"exec.returned\"(%result) : (!F)");
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module) && compareMap(*module, 100000, true),
            "commuted dot did not equal independently read sum of products");
    auto *dot = bound(*module, "candidate", "vector.dot");
    dot->setOperand(1, dot->getOperand(2));
    require(!compareMap(*module, 100000, true), "dot input mutation accepted");
  });
  for (unsigned steps : {maximumSteps, maximumSteps + 1})
    cases.run(
        steps == maximumSteps
            ? "mapped sum neutral chain at the Ring depth limit"
            : "mapped sum neutral chain beyond the Ring depth limit",
        [&] {
          std::string source =
              "   %zero = \"algebra.constant\"() {value=#algebra.literal<!F, 0 "
              ": ui255>} : ()->!F\n";
          std::string previous = "%x";
          for (unsigned i = 0; i < steps; ++i) {
            auto name = "%n" + std::to_string(i);
            source += "   " + name + " = \"algebra.field_add\"(" + previous +
                      ",%zero) : (!F,!F)->!F\n";
            previous = name;
          }
          source += "   func.return " + previous + " : !F\n";
          auto text = formulaBodies(
              source, "   %sum_attempt = \"exec.apply\"(%scope,%x) "
                      "{binding=@mul,parameters=[],site=\"sum\"} : "
                      "(!runtime.scope,!V)->!exec.outcome<(!F)>\n   "
                      "\"exec.dispatch\"(%sum_attempt)[^sum,^failed] : "
                      "(!exec.outcome<(!F)>)->()\n ^sum(%result:!F):\n   %done "
                      "= \"exec.returned\"(%result) : (!F)->!O\n   func.return "
                      "%done : !O\n");
          text =
              edit(text, "contract=\"vector.mul\"", "contract=\"vector.sum\"");
          text = withBindingSignature(
              text, "mul", "(!runtime.scope,!V)->!exec.outcome<(!F)>");
          text = edit(text, "!O = !exec.outcome<(!V)>",
                      "!O = !exec.outcome<(!F)>");
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
                builder, formula.getLoc(), body.getArgument(0).getType(),
                algebra::FieldLiteralAttr::get(
                    &context,
                    cast<algebra::FieldType>(body.getArgument(0).getType()),
                    builder.getI64IntegerAttr(0)));
            require(!compareMap(*module, 100000, true),
                    "neutral normalization hid an unused invalid literal");
          }
        });
  cases.run("neutral normalization preserves nominal source fields", [&] {
    auto text = formulaBodies(
        "   %zero = \"algebra.constant\"() {value=#algebra.literal<!F, 0 : "
        "ui255>} : ()->!F\n"
        "   %r = \"algebra.field_add\"(%x,%zero) : (!F,!F)->!F\n"
        "   func.return %r : !F\n",
        "   %sum_attempt = \"exec.apply\"(%scope,%x) "
        "{binding=@mul,parameters=[],site=\"sum\"} : "
        "(!runtime.scope,!V)->!exec.outcome<(!F)>\n   "
        "\"exec.dispatch\"(%sum_attempt)[^sum,^failed] : "
        "(!exec.outcome<(!F)>)->()\n ^sum(%result:!F):\n   %done = "
        "\"exec.returned\"(%result) : (!F)->!O\n   func.return %done : !O\n");
    text = edit(text, "contract=\"vector.mul\"", "contract=\"vector.sum\"");
    text = withBindingSignature(text, "mul",
                                "(!runtime.scope,!V)->!exec.outcome<(!F)>");
    text = edit(text, "!O = !exec.outcome<(!V)>", "!O = !exec.outcome<(!F)>");
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
    auto before =
        parseSourceString<ModuleOp>(fixture("indexed-zip-dot"), &context);
    require(bool(before), "indexed fixture refused");
    auto after = prepare(*before);
    auto *dot = scopedBound(*after, "vector.dot");
    Value left = dot->getOperand(1), right = dot->getOperand(2);
    dot->setOperand(1, right);
    dot->setOperand(2, left);
    require(corresponds(*before, *after),
            "independent indexed dot comparison failed");
    dot->setOperand(2, dot->getOperand(1));
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    require(!corresponds(*before, *after),
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
  cases.run("expanded callback fan-out respects native closure capacity", [&] {
    auto source = parseSourceString<ModuleOp>(largeOrderedFold(true), &context);
    require(source && succeeded(zkc::admitStage(*source)),
            "unexpanded fan-out source refused");
    // Expanded callbacks together with retained callable bodies exceed the
    // native closure's aggregate instruction ceiling. This checks actual
    // control occurrences, independently of the byte format's body limit.
    bool capacity = false;
    std::string refusal;
    ScopedDiagnosticHandler diagnostics(&context, [&](Diagnostic &diagnostic) {
      refusal += diagnostic.str();
      capacity |= namesIdentifier(diagnostic.str(), "execution-analysis-limit");
      return success();
    });
    mathematical::RealizationWork work;
    uint64_t copies = 1000000, bytes = 16 * 1024 * 1024;
    std::optional<CapacityCause> cause;
    auto candidate = protocol::prepareScopedFinite(*source, work, copies, bytes,
                                                   cause, {false, false});
    require(!candidate && capacity && succeeded(zkc::admitStage(*source)),
            "oversized expanded body was published or changed its source; "
            "candidate=" +
                Twine(bool(candidate)) + "; diagnostics=" + refusal);
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
  cases.run("large total arithmetic step retains scoped ordered fallback", [&] {
    auto module =
        parseSourceString<ModuleOp>(largeOrderedFold(false, true), &context);
    require(bool(module), "large total source refused");
    auto numerical = computationRecipeSource(&module->getBody()->front(),
                                             "work", "candidate");
    auto actual = realizeTotal(*numerical, "total", 8 * 1024 * 1024);
    unsigned scalar = 0;
    actual->walk([&](exec::ApplyOp) { ++scalar; });
    require(scalar > 2048, "large ordered scalar callback was not retained");
    finite::VerificationLimits limits;
    uint64_t checking = 8 * 1024 * 1024;
    limits.sharedContext = &checking;
    require(succeeded(computation::verifyEntryRecipes(*numerical, *actual,
                                                      "total", {}, limits)),
            "large scoped callback lost original mathematical correspondence");
  });
  cases.run("total identity collect leaves an arbitrary scoped suffix", [&] {
    auto text =
        edit(fixture("total-collect"), "func.return %z", "func.return %x");
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "identity collect source refused");
    data::FiniteCollectOp source;
    module->walk([&](data::FiniteCollectOp op) { source = op; });
    require(bool(source), "missing total collect");
    auto numerical = totalOccurrenceSource(source);
    auto actual = realizeTotal(*numerical, "identity_collect");
    auto target = scopedFunction(*actual, "candidate");
    auto ret = returned(target);
    auto outputs = SmallVector<Value>(ret->getOperands());
    require(outputs.size() == 1 && outputs[0] == target.getArgument(1),
            "identity collect did not preserve the actual input");
    auto *block = ret->getBlock();
    ret->getNextNode()->erase();
    ret.erase();
    OpBuilder builder(block, block->end());
    exec::ScopedExecutionBuilder control(builder, target);
    auto suffix = control.invoke(
        "exec.boolean", builder.getI1Type(), control.scoped({}),
        {builder.getNamedAttr("value", builder.getBoolAttr(true)),
         builder.getNamedAttr("site", builder.getStringAttr("suffix"))},
        cast<exec::DispatchOp>(target.front().back()).getStopped());
    control.returned(outputs);
    auto *owner = &actual->getBody()->front();
    auto candidate = take(mathematical::ScopedCandidate::read(owner));
    auto *cursor = candidate->first(&target.front());
    finite::VerificationLimits limits;
    limits.candidate = candidate.get();
    finite::VerificationResult outcome{finite::VerificationStatus::Mismatch,
                                       {}};
    uint64_t work = 1000000, bytes = 16 * 1024 * 1024;
    auto result = computation::verifyComputationRecipes(
        mathematical::getComputationEntry(*numerical), owner,
        "identity_collect", target.getArguments().drop_front(), cursor, work,
        bytes, {}, limits, outcome);
    require(succeeded(result) && *result == outputs &&
                cursor == candidate->producer(suffix.front()),
            "total finite reader consumed or refused the caller suffix");
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
          data::FiniteFoldOp source;
          module->walk([&](data::FiniteFoldOp op) { source = op; });
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
          auto numerical = computationRecipeSource(&module->getBody()->front(),
                                                   "outer", "candidate");
          auto actual = realizeTotal(*numerical, "extent_fold");
          bool dot = false, loop = false;
          actual->walk([&](Operation *op) {
            if (auto apply = dyn_cast<exec::ApplyOp>(op)) {
              auto binding =
                  SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                      apply, apply.getBindingAttr());
              dot |= binding && binding.getContract() == "vector.dot";
            }
            loop |= isa<exec::RangeOp>(op);
          });
          require(dot == helperEquality && loop != helperEquality,
                  "producer used extent evidence unavailable to its reader");
          require(succeeded(computation::verifyEntryRecipes(*numerical, *actual,
                                                            "extent_fold")),
                  "extent-aware scoped recipes lost source correspondence");
          if (!helperEquality) {
            // Rebuild an independently authored dot over the actual ordered
            // admission prefix. The operation-level extent premise cannot be
            // promoted into the original helper's finite equation.
            finite::Computation computation;
            require(succeeded(finite::describe(source, computation)),
                    "finite description failed");
            replaceScopedPayload(
                *actual,
                [&](auto emit, ValueRange args) {
                  auto product =
                      emit("vector.dot", {args[0], args[1]}, args[2].getType());
                  return emit("field.add", {args[2], product},
                              product.getType());
                },
                "candidate");
            auto target = scopedFunction(*actual, "candidate");
            auto *owner = &actual->getBody()->front();
            auto candidate = take(mathematical::ScopedCandidate::read(owner));
            auto *cursor = scopedBound(*actual, "vector.dot", "candidate");
            auto *saved = cursor;
            SmallVector<Value> inputs{target.getArgument(1),
                                      target.getArgument(3),
                                      target.getArgument(2)};
            SymbolTable symbols(owner);
            llvm::DenseSet<Operation *> bindings;
            uint64_t work = 100000;
            auto refused = mathematical::compareFinitePayload(
                computation, inputs,
                payload(scopedBound(*actual, "vector.length", "candidate")),
                cursor, symbols, bindings, work, returned(target), nullptr,
                nullptr, candidate.get());
            require(failed(refused) && cursor == saved && bindings.empty(),
                    "operation-only extent evidence leaked into scoped bulk "
                    "comparison");
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
    require(succeeded(zkc::admitStage(*before)),
            "diagonal domain fixture refused");
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
            require(succeeded(zkc::admitStage(*before)),
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
