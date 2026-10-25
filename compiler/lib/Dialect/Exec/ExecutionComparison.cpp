#include "ExecutionDefinitions.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/Execution.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Program/Admission.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include <map>

using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
// Record-directed comparison of actual SSA. Do not reconstruct an expected
// program with readLocalExecution or replay the emission implementation here.
bool attrs(Operation *op, ArrayRef<StringRef> names = {}) {
  return op && llvm::all_of(op->getAttrs(), [&](NamedAttribute attribute) {
           return llvm::is_contained(names, attribute.getName().getValue());
         });
}
bool strings(ArrayAttr actual, ArrayRef<std::string> expected) {
  if (!actual || actual.size() != expected.size())
    return false;
  for (auto [a, e] : zip(actual, expected))
    if (!isa<StringAttr>(a) || cast<StringAttr>(a).getValue() != e)
      return false;
  return true;
}
bool returns(Operation *operation, Value value) {
  auto returned = dyn_cast_or_null<func::ReturnOp>(operation);
  return returned && attrs(returned) &&
         returned.getOperands() == ValueRange{value};
}
class Comparison;
class BodyComparison {
  Comparison &owner;
  func::FuncOp function;
  Value scope;
  exec::OutcomeType outcome;
  Block *current = nullptr, *failure = nullptr;
  Block::iterator position;
  llvm::DenseSet<Block *> checked;
  llvm::DenseMap<Value, std::string> names;
  bool enter(Block *block);
  Operation *take();
  bool end() const { return position == current->end(); }
  bool inputs(ValueRange, ArrayRef<std::string>) const;
  bool bind(ValueRange, ArrayRef<std::string>);
  bool stop(Block *block);
  bool dispatch(Value value, SmallVectorImpl<Value> &payload,
                Block *failed = nullptr);
  bool region(runtime::EnterScopeOp enter, StringRef kind, StringRef site,
              StringRef selection, const program::Body &body,
              ArrayRef<std::string> arguments, SmallVectorImpl<Value> &results);
  bool conditional(const program::Instruction &, const program::Conditional &);
  bool match(const program::Instruction &, const program::Match &);
  bool loop(const program::Instruction &, const program::For &);

public:
  BodyComparison(Comparison &owner, func::FuncOp function)
      : owner(owner), function(function) {}
  bool run(const program::Body &, ArrayRef<std::string> arguments);
};
class Comparison {
  Operation *module;
  bool physical, source;
  unsigned remaining = 1000000;
  llvm::DenseSet<Operation *> active, visited;
  std::map<std::string, BoundOperation> bindings;

public:
  Comparison(Operation *module, bool physical, bool source = false)
      : module(module), physical(physical), source(source) {}
  bool isSource() const { return source; }
  bool helper(func::CallOp call, const program::LocalApply &record) {
    if (!source || call.getCallee() != record.callee ||
        call.getNumResults() != 1 ||
        !isa<exec::OutcomeType>(call.getResult(0).getType()))
      return false;
    auto function = dyn_cast_or_null<func::FuncOp>(
        SymbolTable::lookupSymbolIn(module, call.getCallee()));
    return function && !function.isExternal() &&
           !function->hasAttr("runtime.region") &&
           function->hasAttr("runtime.origin");
  }
  bool charge() { return remaining && (--remaining, true); }
  bool type(Type actual, StringRef expected = {}) const {
    auto bound = encodeBoundType(actual, physical);
    if (!bound) {
      consumeError(bound.takeError());
      return false;
    }
    return expected.empty() || bound->spelling() == expected;
  }
  bool application(exec::ApplyOp call, const program::Operation &record) {
    auto found = bindings.find(record.callee);
    if (found == bindings.end())
      return false;
    const auto &expected = found->second;
    auto outputs = call.getOutcome().getType().getPayload();
    if (call.getInputs().size() != expected.inputs.size() ||
        outputs.size() != expected.outputs.size())
      return false;
    for (auto [actual, port] :
         zip(call.getInputs().getTypes(), expected.inputs))
      if (!type(actual, port.spelling()))
        return false;
    for (auto [actual, port] : zip(outputs, expected.outputs))
      if (!type(actual, port.spelling()))
        return false;
    return call.getBinding() == record.callee &&
           strings(call.getParameters(), record.attributes);
  }
  bool body(func::FuncOp function, const program::Body &expected,
            ArrayRef<std::string> arguments, bool outlined) {
    if (!function || function.isExternal() || !function.getNoInline() ||
        function.getNumArguments() != arguments.size() + 1 ||
        !isa<runtime::ScopeType>(function.getArgument(0).getType()) ||
        function.getFunctionType().getNumResults() != 1 ||
        !isa<exec::OutcomeType>(function.getResultTypes().front()) ||
        !attrs(function, {"sym_name", "sym_visibility", "function_type",
                          "no_inline", "runtime.origin", "runtime.region"}) ||
        (outlined ? !function.isPrivate() ||
                        !function->getAttrOfType<UnitAttr>("runtime.region") ||
                        function->hasAttr("runtime.origin")
                  : function->hasAttr("runtime.region")) ||
        active.size() >= 64 || !active.insert(function).second)
      return false;
    visited.insert(function);
    bool valid = succeeded(runtime::verifyScopeOwnership(function));
    for (TypeRange ports :
         {TypeRange(function.getArgumentTypes().drop_front()),
          TypeRange(cast<exec::OutcomeType>(function.getResultTypes().front())
                        .getPayload())})
      for (Type port : ports)
        valid &= type(port);
    if (valid)
      valid = BodyComparison(*this, function).run(expected, arguments);
    active.erase(function);
    return valid;
  }
  bool call(func::CallOp call, const program::Body &expected,
            ArrayRef<std::string> arguments) {
    return body(dyn_cast_or_null<func::FuncOp>(
                    SymbolTable::lookupSymbolIn(module, call.getCallee())),
                expected, arguments, true);
  }
  bool run(const program::LocalDefinitions &expected, bool mixed = false);
};
bool BodyComparison::enter(Block *block) {
  if (!block || block->getParent() != &function.getBody() ||
      !checked.insert(block).second)
    return false;
  current = block;
  position = block->begin();
  return true;
}
Operation *BodyComparison::take() {
  return owner.charge() && !end() ? &*position++ : nullptr;
}
bool BodyComparison::inputs(ValueRange actual,
                            ArrayRef<std::string> expected) const {
  if (actual.size() != expected.size())
    return false;
  for (auto [value, name] : zip(actual, expected)) {
    auto found = names.find(value);
    if (found == names.end() || found->second != name)
      return false;
  }
  return true;
}
bool BodyComparison::bind(ValueRange actual, ArrayRef<std::string> expected) {
  if (actual.size() != expected.size())
    return false;
  for (auto [value, name] : zip(actual, expected))
    if (!owner.type(value.getType()) || !names.try_emplace(value, name).second)
      return false;
  return true;
}
bool BodyComparison::stop(Block *block) {
  if (failure)
    return block == failure;
  if (!block || block->getParent() != &function.getBody() || block == current ||
      !checked.insert(block).second || block->getNumArguments() != 1 ||
      !isa<exec::StopType>(block->getArgument(0).getType()) ||
      block->getOperations().size() != 2 || !owner.charge() || !owner.charge())
    return false;
  auto stopped = dyn_cast<exec::FailureOp>(block->front());
  if (!stopped || !attrs(stopped) ||
      stopped.getStop() != block->getArgument(0) ||
      stopped.getOutcome().getType() != outcome ||
      !returns(&block->back(), stopped.getOutcome()))
    return false;
  failure = block;
  return true;
}
bool BodyComparison::dispatch(Value value, SmallVectorImpl<Value> &payload,
                              Block *failed) {
  auto edge = dyn_cast_or_null<exec::DispatchOp>(take());
  if (!edge || !attrs(edge) || edge.getOutcome() != value || !end() ||
      !(failed ? edge.getStopped() == failed : stop(edge.getStopped())) ||
      !enter(edge.getReturned()))
    return false;
  append_range(payload, current->getArguments());
  return true;
}
bool BodyComparison::region(runtime::EnterScopeOp entry, StringRef kind,
                            StringRef site, StringRef selection,
                            const program::Body &body,
                            ArrayRef<std::string> arguments,
                            SmallVectorImpl<Value> &results) {
  if (!entry || entry.getParent() != scope || entry.getKind() != kind ||
      entry.getSite() != site ||
      entry.getSelection().value_or("") != selection ||
      !attrs(entry, {"kind", "site", "selection", "operandSegmentSizes"}) ||
      !inputs(entry.getInputs(), arguments))
    return false;
  SmallVector<Value> acquired;
  if (!dispatch(entry.getOutcome(), acquired) || acquired.size() != 1)
    return false;
  auto call = dyn_cast_or_null<func::CallOp>(take());
  SmallVector<Value> operands{acquired.front()};
  append_range(operands, entry.getInputs());
  if (!call || !attrs(call, {"callee"}) || call.getOperands() != operands ||
      call.getNumResults() != 1 || !owner.call(call, body, arguments))
    return false;
  auto leave = dyn_cast_or_null<runtime::ExitScopeOp>(take());
  SmallVector<Value> held;
  if (!leave || !attrs(leave) || leave.getScope() != acquired.front() ||
      leave.getBody() != call.getResult(0) ||
      !dispatch(leave.getOutcome(), held) || held.size() != 1)
    return false;
  auto accept = dyn_cast_or_null<runtime::AcceptTransferOp>(take());
  return accept && attrs(accept) && accept.getParent() == scope &&
         accept.getTransfer() == held.front() &&
         dispatch(accept.getOutcome(), results);
}
bool BodyComparison::conditional(const program::Instruction &instruction,
                                 const program::Conditional &record) {
  auto test = dyn_cast_or_null<exec::TestOp>(take());
  SmallVector<Value> decision;
  if (!test || !attrs(test, {"site"}) || test.getScope() != scope ||
      test.getSite() != instruction.site ||
      !inputs(test.getCondition(), {record.condition}) ||
      !dispatch(test.getOutcome(), decision))
    return false;
  auto branch = dyn_cast_or_null<cf::CondBranchOp>(take());
  if (!branch || !branch->getDiscardableAttrDictionary().empty() ||
      branch.getBranchWeights() || branch.getCondition() != decision.front() ||
      !branch.getTrueDestOperands().empty() ||
      !branch.getFalseDestOperands().empty() || !end())
    return false;
  Block *join = nullptr;
  for (unsigned i = 0; i < 2; ++i) {
    if (!enter(i ? branch.getFalseDest() : branch.getTrueDest()))
      return false;
    auto entry = dyn_cast_or_null<runtime::EnterScopeOp>(take());
    SmallVector<Value> values;
    if (!region(entry, "conditional", instruction.site, i ? "else" : "then",
                i ? record.elseBody : record.thenBody, record.captures, values))
      return false;
    auto edge = dyn_cast_or_null<cf::BranchOp>(take());
    if (!edge || !attrs(edge) || edge.getDestOperands() != values || !end() ||
        (join && join != edge.getDest()))
      return false;
    join = edge.getDest();
  }
  return enter(join) && bind(current->getArguments(), record.outputs);
}
bool BodyComparison::match(const program::Instruction &instruction,
                           const program::Match &record) {
  auto match = dyn_cast_or_null<exec::MatchOp>(take());
  if (!match || !attrs(match, {"site", "alternatives"}) ||
      match.getScope() != scope || match.getSite() != instruction.site ||
      !end() || !stop(match.getStopped()) ||
      !inputs(match.getInput(), {record.input}) ||
      !inputs(match.getCaptures(), record.captures) ||
      match.getArms().size() != record.arms.size())
    return false;
  Block *join = nullptr;
  for (auto [i, recordArm] : enumerate(record.arms)) {
    auto *arm = match.getArms()[i];
    program::Names arguments = recordArm.payload;
    append_range(arguments, record.captures);
    if (cast<StringAttr>(match.getAlternatives()[i]).getValue() !=
            recordArm.alternative ||
        !enter(arm) || !bind(arm->getArguments(), arguments))
      return false;
    auto entry = dyn_cast_or_null<runtime::EnterScopeOp>(take());
    SmallVector<Value> values;
    if (!entry || entry.getInputs() != arm->getArguments() ||
        !region(entry, "match", instruction.site, recordArm.alternative,
                recordArm.body, arguments, values))
      return false;
    auto edge = dyn_cast_or_null<cf::BranchOp>(take());
    if (!edge || !attrs(edge) || edge.getDestOperands() != values || !end() ||
        (join && join != edge.getDest()))
      return false;
    join = edge.getDest();
    for (Value argument : arm->getArguments())
      names.erase(argument);
  }
  return enter(join) && bind(current->getArguments(), record.outputs);
}
bool BodyComparison::loop(const program::Instruction &instruction,
                          const program::For &record) {
  auto range = dyn_cast_or_null<exec::RangeOp>(take());
  SmallVector<Value> bounds;
  if (!range || !attrs(range, {"site"}) || range.getScope() != scope ||
      range.getSite() != instruction.site ||
      !inputs({range.getLower(), range.getUpper()},
              {record.lower, record.upper}) ||
      !dispatch(range.getOutcome(), bounds))
    return false;
  program::Names seeds, bodyArguments{record.induction};
  for (const auto &[name, seed] : record.carried) {
    seeds.push_back(seed);
    bodyArguments.push_back(name);
  }
  auto initial = dyn_cast_or_null<runtime::BorrowTransferOp>(take());
  auto initialEdge = dyn_cast_or_null<cf::BranchOp>(take());
  if (!initial || !attrs(initial) || initial.getParent() != scope ||
      !inputs(initial.getInputs(), seeds) || !initialEdge ||
      !attrs(initialEdge) ||
      initialEdge.getDestOperands() !=
          ValueRange{bounds[0], initial.getTransfer()} ||
      !end() || !enter(initialEdge.getDest()) ||
      current->getNumArguments() != 2)
    return false;
  auto *header = current;
  Value coordinate = header->getArgument(0), previous = header->getArgument(1);
  auto compare = dyn_cast_or_null<arith::CmpIOp>(take());
  auto edge = dyn_cast_or_null<cf::CondBranchOp>(take());
  if (!compare || !attrs(compare, {"predicate"}) ||
      compare.getPredicate() != arith::CmpIPredicate::ult ||
      compare.getLhs() != coordinate || compare.getRhs() != bounds[1] ||
      !edge || !edge->getDiscardableAttrDictionary().empty() ||
      edge.getBranchWeights() || edge.getCondition() != compare.getResult() ||
      !edge.getTrueDestOperands().empty() ||
      edge.getFalseDestOperands() != ValueRange{previous} || !end() ||
      !enter(edge.getTrueDest()))
    return false;
  Block *finish = edge.getFalseDest();
  auto iteration = dyn_cast_or_null<runtime::IterationOp>(take());
  if (!iteration || !attrs(iteration, {"site"}) ||
      iteration.getParent() != scope ||
      iteration.getCoordinate() != coordinate ||
      iteration.getSite() != instruction.site)
    return false;
  auto iterationEdge =
      dyn_cast_or_null<exec::DispatchOp>(end() ? nullptr : &*position);
  if (!iterationEdge)
    return false;
  Block *cleanup = iterationEdge.getStopped();
  if (!cleanup || cleanup == current ||
      cleanup->getParent() != &function.getBody() ||
      !checked.insert(cleanup).second || cleanup->getNumArguments() != 1 ||
      cleanup->getOperations().size() != 2 || !owner.charge() ||
      !owner.charge())
    return false;
  auto release = dyn_cast<runtime::ReleaseTransferOp>(cleanup->front());
  auto propagate = dyn_cast<cf::BranchOp>(cleanup->back());
  if (!release || !attrs(release) || release.getTransfer() != previous ||
      !propagate || !attrs(propagate) ||
      propagate.getDestOperands() != cleanup->getArguments() ||
      !stop(propagate.getDest()))
    return false;
  SmallVector<Value> index;
  if (!dispatch(iteration.getOutcome(), index, cleanup) ||
      !bind(index, {record.induction}) ||
      index.front().getType() != range.getLower().getType())
    return false;
  auto peek = dyn_cast_or_null<runtime::TransferValuesOp>(take());
  if (!peek || !attrs(peek) || peek.getTransfer() != previous ||
      !bind(peek.getValues(), ArrayRef(bodyArguments).drop_front()))
    return false;
  append_range(bodyArguments, record.captures);
  auto entry = dyn_cast_or_null<runtime::EnterScopeOp>(take());
  if (!entry || !attrs(entry, {"kind", "site", "operandSegmentSizes"}) ||
      entry.getParent() != scope || entry.getKind() != "iteration" ||
      entry.getCoordinate() != coordinate ||
      entry.getSite() != instruction.site ||
      !inputs(entry.getInputs(), bodyArguments))
    return false;
  // This mapping is exact even if the body does not read its induction or
  // carry.
  SmallVector<Value> prefix(index);
  append_range(prefix, peek.getValues());
  if (entry.getInputs().take_front(prefix.size()) != ValueRange(prefix))
    return false;
  SmallVector<Value> acquired;
  if (!dispatch(entry.getOutcome(), acquired, cleanup) || acquired.size() != 1)
    return false;
  SmallVector<Value> arguments{acquired.front()};
  append_range(arguments, entry.getInputs());
  auto call = dyn_cast_or_null<func::CallOp>(take());
  if (!call || !attrs(call, {"callee"}) || call.getOperands() != arguments ||
      call.getNumResults() != 1 ||
      !owner.call(call, record.body, bodyArguments))
    return false;
  auto leave = dyn_cast_or_null<runtime::ExitScopeOp>(take());
  SmallVector<Value> held;
  if (!leave || !attrs(leave) || leave.getScope() != acquired.front() ||
      leave.getBody() != call.getResult(0) ||
      !dispatch(leave.getOutcome(), held, cleanup) || held.size() != 1)
    return false;
  auto old = dyn_cast_or_null<runtime::ReleaseTransferOp>(take());
  if (!old || !attrs(old) || old.getTransfer() != previous)
    return false;
  Block *increment = nullptr;
  if (record.conditional) {
    auto test = dyn_cast_or_null<runtime::TakeConditionOp>(take());
    SmallVector<Value> selected;
    if (!test || !attrs(test) || test.getTransfer() != held.front() ||
        !dispatch(test.getOutcome(), selected))
      return false;
    auto branch = dyn_cast_or_null<cf::CondBranchOp>(take());
    if (!branch || !branch->getDiscardableAttrDictionary().empty() ||
        branch.getBranchWeights() || branch.getCondition() != selected[0] ||
        branch.getFalseDest() != finish ||
        branch.getTrueDestOperands() != ValueRange{selected[1]} ||
        branch.getFalseDestOperands() != ValueRange{selected[1]} || !end())
      return false;
    increment = branch.getTrueDest();
  } else {
    auto branch = dyn_cast_or_null<cf::BranchOp>(take());
    if (!branch || !attrs(branch) || branch.getDestOperands() != held || !end())
      return false;
    increment = branch.getDest();
  }
  if (!enter(increment) || increment->getNumArguments() != 1)
    return false;
  auto one = dyn_cast_or_null<arith::ConstantIntOp>(take());
  auto advance = dyn_cast_or_null<arith::AddIOp>(take());
  auto back = dyn_cast_or_null<cf::BranchOp>(take());
  if (!one || !attrs(one, {"value"}) || one.value() != 1 ||
      !one.getType().isSignlessInteger(64) || !advance ||
      !attrs(advance, {"overflowFlags"}) ||
      advance.getOverflowFlags() != arith::IntegerOverflowFlags::none ||
      advance.getLhs() != coordinate || advance.getRhs() != one.getResult() ||
      !back || !attrs(back) || back.getDest() != header ||
      back.getDestOperands() !=
          ValueRange{advance.getResult(), increment->getArgument(0)} ||
      !end() || !enter(finish) || finish->getNumArguments() != 1)
    return false;
  auto accept = dyn_cast_or_null<runtime::AcceptTransferOp>(take());
  SmallVector<Value> outputs;
  if (!accept || !attrs(accept) || accept.getParent() != scope ||
      accept.getTransfer() != finish->getArgument(0) ||
      !dispatch(accept.getOutcome(), outputs) || !bind(outputs, record.outputs))
    return false;
  names.erase(index.front());
  for (Value value : peek.getValues())
    names.erase(value);
  return true;
}
bool BodyComparison::run(const program::Body &expected,
                         ArrayRef<std::string> arguments) {
  outcome = cast<exec::OutcomeType>(function.getResultTypes().front());
  scope = function.getArgument(0);
  if (!enter(&function.front()) ||
      !bind(function.getArguments().drop_front(), arguments))
    return false;
  for (const auto &instruction : expected) {
    if (auto record = instruction.get<program::Conditional>()) {
      if (!conditional(instruction, *record))
        return false;
    } else if (auto record = instruction.get<program::Match>()) {
      if (!match(instruction, *record))
        return false;
    } else if (auto record = instruction.get<program::For>()) {
      if (!loop(instruction, *record))
        return false;
    } else if (auto record = instruction.get<program::Operation>()) {
      auto call = dyn_cast_or_null<exec::ApplyOp>(take());
      SmallVector<Value> outputs;
      if (!call || !attrs(call, {"binding", "parameters", "site"}) ||
          call.getScope() != scope || call.getSite() != instruction.site ||
          !inputs(call.getInputs(), record->inputs) ||
          !owner.application(call, *record) ||
          !dispatch(call.getOutcome(), outputs) ||
          !bind(outputs, record->outputs))
        return false;
    } else if (auto record = instruction.get<program::LocalApply>()) {
      auto call = dyn_cast_or_null<func::CallOp>(take());
      SmallVector<Value> outputs;
      if (!call || !attrs(call, {"callee", "runtime.site"}) ||
          !owner.helper(call, *record) ||
          call->getAttrOfType<StringAttr>("runtime.site") !=
              StringAttr::get(function.getContext(), instruction.site) ||
          call.getNumOperands() == 0 || call.getOperand(0) != scope ||
          !inputs(call.getOperands().drop_front(), record->inputs) ||
          !dispatch(call.getResult(0), outputs) ||
          !bind(outputs, record->outputs))
        return false;
    } else if (auto record = instruction.get<program::BooleanConstant>()) {
      auto value = dyn_cast_or_null<exec::BooleanOp>(take());
      SmallVector<Value> outputs;
      if (!value || !attrs(value, {"value", "site"}) ||
          value.getScope() != scope || value.getValue() != record->value ||
          value.getSite() != instruction.site ||
          !dispatch(value.getOutcome(), outputs) ||
          !bind(outputs, {record->output}))
        return false;
    } else if (auto record = instruction.get<program::VariantConstruct>()) {
      auto value = dyn_cast_or_null<exec::VariantOp>(take());
      SmallVector<Value> outputs;
      if (!value || !attrs(value, {"alternative", "site"}) ||
          value.getScope() != scope ||
          value.getAlternative() != record->alternative ||
          value.getSite() != instruction.site ||
          !inputs(value.getPayload(), record->payload) ||
          !owner.type(value.getOutcome().getType().getPayload().front(),
                      record->type) ||
          !dispatch(value.getOutcome(), outputs) ||
          !bind(outputs, {record->output}))
        return false;
    } else if (auto record = instruction.get<program::Release>()) {
      auto release = dyn_cast_or_null<runtime::ReleaseBindingsOp>(take());
      if (!release || !attrs(release) || release.getScope() != scope ||
          !inputs(release.getValues(), record->values))
        return false;
    } else if (auto record = instruction.get<program::Stop>()) {
      auto reject = dyn_cast_or_null<exec::RejectOp>(take());
      auto branch = dyn_cast_or_null<cf::BranchOp>(take());
      if (!reject || !attrs(reject, {"site", "reason"}) ||
          reject.getScope() != scope || reject.getReason() != record->reason ||
          reject.getSite() != instruction.site || !branch || !attrs(branch) ||
          branch.getDestOperands() != ValueRange{reject.getStop()} || !end() ||
          !stop(branch.getDest()))
        return false;
    } else if (instruction.get<program::Return>() ||
               instruction.get<program::Yield>()) {
      const auto &expectedValues =
          instruction.get<program::Return>()
              ? instruction.get<program::Return>()->values
              : instruction.get<program::Yield>()->values;
      if (owner.isSource() && instruction.get<program::Return>()) {
        auto returnedValue = dyn_cast_or_null<exec::ReturnOp>(take());
        if (!returnedValue || !attrs(returnedValue) ||
            !inputs(returnedValue.getValues(), expectedValues) ||
            !returns(take(), returnedValue.getOutcome()) || !end())
          return false;
      } else {
        auto complete = dyn_cast_or_null<exec::CompleteOp>(take());
        if (!complete || !attrs(complete) || complete.getScope() != scope ||
            !inputs(complete.getValues(), expectedValues) ||
            !returns(take(), complete.getOutcome()) || !end())
          return false;
      }
    } else
      return false;
  }
  return end() && checked.size() == function.getBody().getBlocks().size();
}
bool Comparison::run(const program::LocalDefinitions &expected, bool mixed) {
  for (const auto &binding : expected.bindings) {
    auto signature = resolveBinding(binding.application, physical);
    if (!signature) {
      consumeError(signature.takeError());
      return false;
    }
    bindings.emplace(binding.name, std::move(*signature));
  }
  unsigned binding = 0, root = 0, definitions = 0;
  for (Operation &op : module->getRegion(0).front()) {
    if (!charge() || ++definitions > 4096)
      return false;
    if (auto declaration = dyn_cast<runtime::BindingOp>(op)) {
      if (binding == expected.bindings.size() ||
          !attrs(declaration, {"sym_name", "contract", "arguments",
                               "implementation", "physical_arguments"}))
        return false;
      const auto &record = expected.bindings[binding++];
      const auto &application = record.application;
      if (declaration.getSymName() != record.name ||
          declaration.getContract() != application.contract ||
          declaration.getImplementation() != application.implementation ||
          !strings(declaration.getArguments(), application.arguments) ||
          (declaration.getPhysicalArgumentsAttr()
               ? !strings(declaration.getPhysicalArgumentsAttr(),
                          application.physicalArguments)
               : !application.physicalArguments.empty()))
        return false;
      continue;
    }
    auto function = dyn_cast<func::FuncOp>(op);
    if (!function) {
      if (mixed)
        continue;
      return false;
    }
    if (source && !detail::isScopedExecutionFunction(function))
      continue;
    if (function->getAttrOfType<UnitAttr>("runtime.region"))
      continue;
    if (root == expected.functions.size())
      return false;
    const auto &record = expected.functions[root++];
    auto origin = function->getAttrOfType<ArrayAttr>("runtime.origin");
    if (function.getSymName() != record.name || !record.origin || !origin ||
        origin.size() != 2 || !isa<StringAttr>(origin[0]) ||
        cast<StringAttr>(origin[0]).getValue() != record.origin->definition ||
        !isa<ArrayAttr>(origin[1]) ||
        cast<ArrayAttr>(origin[1]).size() != record.origin->arguments.size() ||
        function.getNumArguments() != record.arguments.size() + 1 ||
        function.getFunctionType().getNumResults() != 1)
      return false;
    for (auto [actual, pair] :
         zip(cast<ArrayAttr>(origin[1]), record.origin->arguments)) {
      auto row = dyn_cast<ArrayAttr>(actual);
      if (!row || !strings(row, {pair.first, pair.second}))
        return false;
    }
    auto result =
        dyn_cast<exec::OutcomeType>(function.getResultTypes().front());
    if (!result || result.getPayload().size() != record.results.size())
      return false;
    program::Names arguments;
    for (auto [actual, port] :
         zip(function.getArgumentTypes().drop_front(), record.arguments)) {
      if (!type(actual, port.type))
        return false;
      arguments.push_back(port.name);
    }
    for (auto [actual, port] : zip(result.getPayload(), record.results))
      if (!type(actual, port))
        return false;
    if (!body(function, record.body, arguments, false))
      return false;
  }
  if (binding != expected.bindings.size() || root != expected.functions.size())
    return false;
  for (auto function : module->getRegion(0).front().getOps<func::FuncOp>())
    if ((!source || detail::isScopedExecutionFunction(function)) &&
        !visited.contains(function))
      return false;
  return true;
}
} // namespace
Error verifyLocalExecution(ModuleOp module,
                           const program::LocalDefinitions &expected,
                           bool physical) {
  if (!module || failed(verify(module)) || !module->getAttrs().empty())
    return error("execution-correspondence-subject");
  program::Participants admitted;
  admitted.stage = physical ? program::Participants::Stage::Physical
                            : program::Participants::Stage::Logical;
  admitted.bindings = expected.bindings;
  admitted.functions = expected.functions;
  if (auto e = admit(admitted))
    return e;
  Comparison checker(module, physical);
  if (!checker.run(expected))
    return error("execution-correspondence");
  return Error::success();
}
Error verifyExecutionDefinitions(Operation *symbolTable,
                                 const program::LocalDefinitions &expected,
                                 bool physical) {
  if (failed(detail::verifyExecutionDefinitionScope(symbolTable)))
    return error("execution-correspondence-subject");
  program::Participants admitted;
  admitted.stage = physical ? program::Participants::Stage::Physical
                            : program::Participants::Stage::Logical;
  admitted.bindings = expected.bindings;
  admitted.functions = expected.functions;
  if (auto e = admit(admitted))
    return e;
  Comparison checker(symbolTable, physical);
  if (!checker.run(expected, /*mixed=*/true))
    return error("execution-correspondence");
  return Error::success();
}
Error verifySourceExecutionDefinitions(
    Operation *symbolTable, const program::LocalDefinitions &expected) {
  if (failed(detail::verifyExecutionDefinitionScope(symbolTable,
                                                    /*source=*/true)))
    return error("execution-correspondence-subject");
  if (auto e = admitNativeLocalDefinitions(expected))
    return e;
  Comparison checker(symbolTable, /*physical=*/false, /*source=*/true);
  if (!checker.run(expected, /*mixed=*/true))
    return error("execution-correspondence");
  return Error::success();
}
} // namespace zkc::protocol
