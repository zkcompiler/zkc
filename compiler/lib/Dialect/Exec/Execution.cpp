#include "zkc/Dialect/Exec/Execution.h"
#include "ExecutionDefinitions.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/ControlCursor.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Runtime/Execution.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Program/Admission.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/Support/TimeProfiler.h"

using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
bool isScopedExecutionFunction(func::FuncOp function) {
  if (function->hasAttr("runtime.origin") ||
      function->hasAttr("runtime.region"))
    return true;
  auto raw = function->getAttrOfType<TypeAttr>("function_type");
  auto type = raw ? dyn_cast<FunctionType>(raw.getValue()) : FunctionType();
  if (!type)
    return true;
  auto executionType = [](Type type) {
    return isa<runtime::ScopeType, runtime::TransferType, exec::OutcomeType,
               exec::StopType>(type);
  };
  return llvm::any_of(type.getInputs(), executionType) ||
         llvm::any_of(type.getResults(), executionType);
}
FunctionType scopedDataSignature(func::FuncOp function) {
  if (!function || function->hasAttr("runtime.region"))
    return {};
  auto raw = function->getAttrOfType<TypeAttr>("function_type");
  auto type = raw ? dyn_cast<FunctionType>(raw.getValue()) : FunctionType();
  auto outcome = type && type.getNumResults() == 1
                     ? dyn_cast<exec::OutcomeType>(type.getResult(0))
                     : exec::OutcomeType();
  if (!type || !type.getNumInputs() || !outcome ||
      !isa<runtime::ScopeType>(type.getInput(0)))
    return {};
  return FunctionType::get(function.getContext(), type.getInputs().drop_front(),
                           outcome.getPayload());
}

namespace {
bool attributes(Operation *op, ArrayRef<StringRef> allowed) {
  return llvm::all_of(op->getAttrs(), [&](NamedAttribute attribute) {
    return llvm::is_contained(allowed, attribute.getName().getValue());
  });
}
bool bare(Operation *op) { return op && op->getAttrs().empty(); }
bool returned(Operation *op, Value outcome) {
  auto value = dyn_cast_or_null<func::ReturnOp>(op);
  return value && bare(op) && value.getOperands() == ValueRange{outcome};
}
program::Names strings(ArrayAttr values) {
  program::Names result;
  for (auto value : values)
    result.push_back(cast<StringAttr>(value).str());
  return result;
}
class Reader;
class BodyReader {
  Reader &reader;
  func::FuncOp function;
  exec::OutcomeType outcome;
  Value scope;
  exec::ControlCursor navigation;
  llvm::DenseMap<Value, std::string> environment;
  bool regionBody;

  bool block(Block *next);
  Operation *take();
  bool atEnd() const { return navigation.atEnd(); }
  bool failedEdge(Block *block);
  bool dispatch(Value value, SmallVectorImpl<Value> &results,
                Block *expectedFailure = nullptr);
  bool names(ValueRange values, program::Names &names);
  bool results(ValueRange values, program::Names &names);
  bool invokeRegion(runtime::EnterScopeOp enter, StringRef kind, StringRef site,
                    StringRef selection, program::Body &body,
                    program::Names &captures, SmallVectorImpl<Value> &values,
                    SourceExecutionStep &step);
  bool conditional(exec::TestOp test, program::Conditional &record,
                   SourceExecutionStep &step);
  bool match(exec::MatchOp match, program::Match &record,
             SourceExecutionStep &step);
  bool loop(exec::RangeOp range, program::For &record,
            SourceExecutionStep &step);
  bool scheduledLoop(exec::RangeOp range, program::For &record,
                     SourceExecutionStep &step);

public:
  BodyReader(Reader &reader, func::FuncOp function, bool regionBody);
  bool run(ArrayRef<std::string> arguments, program::Body &body);
};
class Reader {
  Operation *module;
  bool physical, source, mathematicalCalls, scheduled;
  unsigned remaining = 1000000, next = 0;
  llvm::DenseSet<Operation *> active, visited;
  std::string problem;
  std::vector<LocalRealization> mathematicalSignatures;
  std::map<std::string, Operation *> computationOrigins;
  std::map<std::string, std::vector<SourceExecutionStep>> sourceBodies;
  llvm::DenseMap<Operation *, std::string> mathematicalNames;
  // One reader observes immutable IR. Reuse its symbol index and exact type
  // encodings, but never carry admission results across an IR transformation.
  SymbolTableCollection symbols;
  llvm::DenseMap<Type, std::string> typeSpellings;
  llvm::DenseMap<Operation *, std::pair<OperationBinding, BoundOperation>>
      applications;
  unsigned nextMathematics = 0;

public:
  Reader(Operation *module, bool physical, bool source = false,
         bool mathematicalCalls = false, bool scheduled = false)
      : module(module), physical(physical), source(source),
        mathematicalCalls(mathematicalCalls), scheduled(scheduled) {}
  bool isScheduled() const { return scheduled; }
  func::FuncOp callee(func::CallOp call) {
    return symbols.lookupSymbolIn<func::FuncOp>(module, call.getCalleeAttr());
  }
  unsigned &work() { return remaining; }
  bool isSource() const { return source; }
  std::vector<LocalRealization> takeComputations() {
    return std::move(mathematicalSignatures);
  }
  std::map<std::string, Operation *> takeComputationOrigins() {
    return std::move(computationOrigins);
  }
  auto takeBodies() { return std::move(sourceBodies); }
  void recordBody(func::FuncOp function,
                  std::vector<SourceExecutionStep> body) {
    sourceBodies.insert_or_assign(function.getSymName().str(), std::move(body));
  }
  bool computation(exec::ComputeOp call, std::string &name) {
    if (!source || !mathematicalCalls ||
        failed(finite::verifyCallPreconditions(call)))
      return fail(
          "unresolved mathematical invocation outside source admission");
    auto helper = call.resolveCallee(symbols);
    if (!helper)
      return fail("mathematical invocation has no actual definition");
    // The outer closure check has admitted every actual math definition/unit.
    // Derive only a private temporary key and signature for logical ownership
    // checking; neither is source authority or an executable declaration.
    auto found = mathematicalNames.find(helper);
    if (found != mathematicalNames.end()) {
      name = found->second;
      return true;
    }
    LocalRealization signature;
    do {
      if (!charge())
        return false;
      signature.name =
          "_mathematical_admission_" + std::to_string(nextMathematics++);
    } while (symbols.getSymbolTable(module).lookup(signature.name));
    for (bool input : {true, false}) {
      auto ports = input ? helper.getArgumentTypes() : helper.getResultTypes();
      for (Type port : ports) {
        std::string spelling;
        if (!type(port, spelling))
          return false;
        (input ? signature.inputs : signature.outputs)
            .push_back(std::move(spelling));
      }
    }
    name = signature.name;
    mathematicalNames.try_emplace(helper, name);
    computationOrigins.emplace(name, call.getOperation());
    mathematicalSignatures.push_back(std::move(signature));
    return true;
  }
  bool helper(func::CallOp call) {
    auto function = callee(call);
    return (source && !scheduled && function && !function.isExternal() &&
            function->hasAttr("runtime.origin") &&
            !function->hasAttr("runtime.region") && call.getNumOperands() &&
            call.getNumResults() == 1 &&
            isa<exec::OutcomeType>(call.getResult(0).getType())) ||
           fail("source call must select an actual ordinary scoped helper");
  }
  bool finiteInvocation(Operation *op, std::string &name) {
    finite::Computation computation;
    if (!source || !mathematicalCalls ||
        failed(finite::describe(op, computation)) || !computation.scoped)
      return fail("unresolved finite invocation outside source admission");
    // The enclosing owner has checked the domain, callback ABI, premises and
    // closure. Retain callback edges in this transient admission view: a
    // finite signature alone would hide ordered effects from control checks.
    // Complete Program admission also checks the actual callback's affine
    // state roots before accepting this source closure.
    LocalRealization signature;
    do {
      if (!charge())
        return false;
      signature.name = "_finite_admission_" + std::to_string(nextMathematics++);
    } while (symbols.getSymbolTable(module).lookup(signature.name));
    signature.kind = computation.collect ? LocalRealization::Kind::FiniteCollect
                                         : LocalRealization::Kind::FiniteFold;
    signature.domainArguments = computation.arguments;
    for (Operation *callback : {computation.helper, computation.predicate})
      if (callback)
        signature.callbacks.push_back(
            SymbolTable::getSymbolName(callback).str());
    for (bool input : {true, false})
      for (Type port : input ? computation.signature.getInputs()
                             : computation.signature.getResults()) {
        std::string spelling;
        if (!type(port, spelling))
          return false;
        (input ? signature.inputs : signature.outputs)
            .push_back(std::move(spelling));
      }
    name = signature.name;
    computationOrigins.emplace(name, op);
    mathematicalSignatures.push_back(std::move(signature));
    return true;
  }
  bool fail(StringRef reason) {
    if (problem.empty())
      problem = reason.str();
    return false;
  }
  bool charge() {
    return remaining ? (--remaining, true) : fail("analysis limit");
  }
  std::string fresh() { return "v" + std::to_string(next++); }
  bool type(Type type, std::string &spelling) {
    if (auto found = typeSpellings.find(type); found != typeSpellings.end()) {
      spelling = found->second;
      return true;
    }
    auto encoded = encodeBoundType(type, physical);
    if (!encoded) {
      consumeError(encoded.takeError());
      return fail("value outside the selected execution stage");
    }
    spelling = encoded->spelling();
    typeSpellings.try_emplace(type, spelling);
    return true;
  }
  bool ports(TypeRange actual, ArrayRef<BoundType> expected) {
    if (actual.size() != expected.size())
      return fail("binding port count");
    for (auto [a, e] : zip(actual, expected)) {
      std::string spelling;
      if (!type(a, spelling) || spelling != e.spelling())
        return fail("binding port identity");
    }
    return true;
  }
  bool application(exec::ApplyOp op) {
    auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    auto *root = SymbolTable::getNearestSymbolTable(op);
    auto *declaration =
        root && reference ? symbols.lookupSymbolIn(root, reference) : nullptr;
    if (!declaration)
      return fail("invocation binding");
    auto found = applications.find(declaration);
    if (found == applications.end()) {
      auto binding = readBinding(declaration);
      if (!binding) {
        consumeError(binding.takeError());
        return fail("invocation binding");
      }
      auto signature = resolveBinding(binding->application, physical);
      if (!signature) {
        consumeError(signature.takeError());
        return fail("binding signature");
      }
      found =
          applications
              .try_emplace(declaration, std::make_pair(std::move(*binding),
                                                       std::move(*signature)))
              .first;
    }
    const auto &[binding, signature] = found->second;
    if (!ports(op.getInputs().getTypes(), signature.inputs) ||
        !ports(op.getOutcome().getType().getPayload(), signature.outputs))
      return false;
    if (auto e =
            checkParameters(binding.application, strings(op.getParameters()))) {
      consumeError(std::move(e));
      return fail("invocation parameter formation");
    }
    return true;
  }
  bool body(func::FuncOp function, ArrayRef<std::string> names,
            program::Body &result, bool regionBody) {
    if (active.size() >= 64 || !active.insert(function).second)
      return fail("recursive or excessive region outlining");
    visited.insert(function);
    bool valid =
        !function.isExternal() && function.getNoInline() &&
        function.getNumArguments() == names.size() + 1 &&
        isa<runtime::ScopeType>(function.getArgument(0).getType()) &&
        function.getFunctionType().getNumResults() == 1 &&
        isa<exec::OutcomeType>(function.getFunctionType().getResult(0)) &&
        attributes(function, {"sym_name", "function_type", "sym_visibility",
                              "no_inline", "runtime.origin", "runtime.region",
                              "data.preconditions"}) &&
        (mathematicalCalls || !function->hasAttr("data.preconditions")) &&
        (regionBody
             ? bool(function->getAttrOfType<UnitAttr>("runtime.region")) &&
                   !function->hasAttr("runtime.origin")
             : !function->hasAttr("runtime.region")) &&
        succeeded(scheduled ? runtime::verifyScheduledScopeOwnership(function)
                            : runtime::verifyScopeOwnership(function));
    if (valid) {
      auto outcome =
          cast<exec::OutcomeType>(function.getFunctionType().getResult(0));
      for (TypeRange types :
           {TypeRange(function.getArgumentTypes().drop_front()),
            TypeRange(outcome.getPayload())})
        for (Type t : types) {
          std::string spelling;
          valid &= type(t, spelling);
        }
    }
    if (valid)
      valid = BodyReader(*this, function, regionBody).run(names, result);
    active.erase(function);
    return valid || fail("invalid scoped function body");
  }
  bool region(func::CallOp call, ArrayRef<std::string> names,
              program::Body &result) {
    auto function = callee(call);
    return (function && function.isPrivate() &&
            body(function, names, result, true)) ||
           fail("region body must be an actual private function");
  }
  Expected<program::LocalDefinitions> run(bool mixed = false);
};

BodyReader::BodyReader(Reader &reader, func::FuncOp function, bool regionBody)
    : reader(reader), function(function), navigation(function, reader.work()),
      regionBody(regionBody) {}
bool BodyReader::block(Block *next) {
  return navigation.enter(next) || reader.fail("unexpected CFG join or cycle");
}
Operation *BodyReader::take() { return navigation.take(); }
bool BodyReader::failedEdge(Block *block) {
  return navigation.failure(block) ||
         reader.fail("invalid failure continuation");
}
bool BodyReader::dispatch(Value value, SmallVectorImpl<Value> &results,
                          Block *expectedFailure) {
  return navigation.dispatch(value, results, expectedFailure) ||
         reader.fail("invocation must dispatch its exact outcome");
}
bool BodyReader::names(ValueRange values, program::Names &names) {
  for (Value value : values) {
    auto found = environment.find(value);
    if (found == environment.end())
      return reader.fail("unbound native value");
    names.push_back(found->second);
  }
  return true;
}
bool BodyReader::results(ValueRange values, program::Names &names) {
  for (Value value : values) {
    std::string spelling;
    if (!reader.type(value.getType(), spelling))
      return false;
    auto name = reader.fresh();
    if (!environment.try_emplace(value, name).second)
      return reader.fail("duplicate native result");
    names.push_back(std::move(name));
  }
  return true;
}
bool BodyReader::invokeRegion(runtime::EnterScopeOp enter, StringRef kind,
                              StringRef site, StringRef selection,
                              program::Body &body, program::Names &captures,
                              SmallVectorImpl<Value> &values,
                              SourceExecutionStep &step) {
  if (!enter || enter.getParent() != scope || enter.getKind() != kind ||
      enter.getSite() != site ||
      enter.getSelection().value_or("") != selection ||
      !attributes(enter,
                  {"operandSegmentSizes", "kind", "site", "selection"}) ||
      !names(enter.getInputs(), captures))
    return reader.fail("region entry association");
  SmallVector<Value> acquired;
  if (!dispatch(enter.getOutcome(), acquired) || acquired.size() != 1)
    return false;
  auto call = dyn_cast_or_null<func::CallOp>(take());
  SmallVector<Value> inputs{acquired.front()};
  append_range(inputs, enter.getInputs());
  if (!call || !attributes(call, {"callee"}) || call.getOperands() != inputs ||
      call.getNumResults() != 1 || !reader.region(call, captures, body))
    return reader.fail("region callee or actual captures");
  step.regions.push_back(reader.callee(call));
  auto exit = dyn_cast_or_null<runtime::ExitScopeOp>(take());
  if (!exit || !bare(exit) || exit.getScope() != acquired.front() ||
      exit.getBody() != call.getResult(0))
    return reader.fail("body must exit its exact acquired scope");
  SmallVector<Value> held;
  if (!dispatch(exit.getOutcome(), held) || held.size() != 1)
    return false;
  auto accept = dyn_cast_or_null<runtime::AcceptTransferOp>(take());
  if (!accept || !bare(accept) || accept.getParent() != scope ||
      accept.getTransfer() != held.front() ||
      !dispatch(accept.getOutcome(), values))
    return reader.fail("region result must bind into its actual parent");
  return true;
}
bool BodyReader::conditional(exec::TestOp test, program::Conditional &record,
                             SourceExecutionStep &step) {
  if (test.getScope() != scope || !attributes(test, {"site"}))
    return reader.fail("conditional admission scope");
  program::Names condition;
  if (!names(test.getCondition(), condition))
    return false;
  record.condition = condition.front();
  SmallVector<Value> decision;
  if (!dispatch(test.getOutcome(), decision))
    return false;
  auto edge = dyn_cast_or_null<cf::CondBranchOp>(take());
  if (!edge || !edge->getDiscardableAttrDictionary().empty() ||
      edge.getBranchWeights() || edge.getCondition() != decision.front() ||
      !edge.getTrueDestOperands().empty() ||
      !edge.getFalseDestOperands().empty() || !atEnd())
    return reader.fail("conditional decision edge");
  Block *join = nullptr;
  SmallVector<Value> actualCaptures;
  for (unsigned i = 0; i < 2; ++i) {
    if (!block(i ? edge.getFalseDest() : edge.getTrueDest()))
      return false;
    auto enter = dyn_cast_or_null<runtime::EnterScopeOp>(take());
    if (!enter)
      return reader.fail("conditional arm lacks scope entry");
    if (!i)
      append_range(actualCaptures, enter.getInputs());
    else if (ValueRange(actualCaptures) != enter.getInputs())
      return reader.fail("conditional arms disagree on captures");
    SmallVector<Value> values;
    program::Names captures;
    if (!invokeRegion(enter, "conditional", test.getSite(), i ? "else" : "then",
                      i ? record.elseBody : record.thenBody, captures, values,
                      step))
      return false;
    if (!i)
      record.captures = std::move(captures);
    auto branch = dyn_cast_or_null<cf::BranchOp>(take());
    if (!branch || !bare(branch) || branch.getDestOperands() != values ||
        !atEnd() || (join && join != branch.getDest()))
      return reader.fail("conditional result join");
    join = branch.getDest();
  }
  step.inputs.push_back(test.getCondition());
  append_range(step.inputs, actualCaptures);
  if (!block(join) ||
      !results(navigation.currentBlock()->getArguments(), record.outputs))
    return false;
  append_range(step.outputs, navigation.currentBlock()->getArguments());
  return true;
}
bool BodyReader::match(exec::MatchOp match, program::Match &record,
                       SourceExecutionStep &step) {
  program::Names input;
  if (match.getScope() != scope ||
      !attributes(match, {"site", "alternatives"}) || !atEnd() ||
      !failedEdge(match.getStopped()) || !names(match.getInput(), input) ||
      !names(match.getCaptures(), record.captures))
    return reader.fail("variant dispatch association");
  record.input = input.front();
  Block *join = nullptr;
  for (auto [i, armBlock] : enumerate(match.getArms())) {
    if (!block(armBlock))
      return false;
    program::MatchArm arm;
    arm.alternative = cast<StringAttr>(match.getAlternatives()[i]).str();
    unsigned payload = armBlock->getNumArguments() - record.captures.size();
    if (!results(armBlock->getArguments().take_front(payload), arm.payload))
      return false;
    for (auto [value, name] :
         zip(armBlock->getArguments().drop_front(payload), record.captures))
      environment[value] = name;
    auto enter = dyn_cast_or_null<runtime::EnterScopeOp>(take());
    program::Names arguments;
    SmallVector<Value> values;
    if (!enter || enter.getInputs() != armBlock->getArguments() ||
        !invokeRegion(enter, "match", match.getSite(), arm.alternative,
                      arm.body, arguments, values, step))
      return reader.fail(
          "variant arm must receive exact selected payload and captures");
    auto branch = dyn_cast_or_null<cf::BranchOp>(take());
    if (!branch || !bare(branch) || branch.getDestOperands() != values ||
        !atEnd() || (join && join != branch.getDest()))
      return reader.fail("variant result join");
    join = branch.getDest();
    record.arms.push_back(std::move(arm));
    for (Value value : armBlock->getArguments())
      environment.erase(value);
  }
  step.inputs.push_back(match.getInput());
  append_range(step.inputs, match.getCaptures());
  if (!block(join) ||
      !results(navigation.currentBlock()->getArguments(), record.outputs))
    return false;
  append_range(step.outputs, navigation.currentBlock()->getArguments());
  return true;
}
bool BodyReader::loop(exec::RangeOp range, program::For &record,
                      SourceExecutionStep &step) {
  if (range.getScope() != scope || !attributes(range, {"site"}))
    return reader.fail("loop admission scope");
  program::Names bounds;
  if (!names({range.getLower(), range.getUpper()}, bounds))
    return false;
  record.lower = bounds[0];
  record.upper = bounds[1];
  SmallVector<Value> counters;
  if (!dispatch(range.getOutcome(), counters))
    return false;
  auto initial = dyn_cast_or_null<runtime::BorrowTransferOp>(take());
  program::Names seeds;
  if (!initial || !bare(initial) || initial.getParent() != scope ||
      !names(initial.getInputs(), seeds))
    return reader.fail("loop must borrow its exact initial carry");
  auto initialEdge = dyn_cast_or_null<cf::BranchOp>(take());
  if (!initialEdge || !bare(initialEdge) || !atEnd() ||
      initialEdge.getDestOperands() !=
          ValueRange{counters[0], initial.getTransfer()} ||
      !block(initialEdge.getDest()))
    return reader.fail("loop initial edge");
  Block *header = navigation.currentBlock();
  if (header->getNumArguments() != 2)
    return reader.fail("loop header ports");
  Value coordinate = header->getArgument(0), previous = header->getArgument(1);
  auto compare = dyn_cast_or_null<arith::CmpIOp>(take());
  auto inside = dyn_cast_or_null<cf::CondBranchOp>(take());
  if (!compare || !attributes(compare, {"predicate"}) ||
      compare.getPredicate() != arith::CmpIPredicate::ult ||
      compare.getLhs() != coordinate || compare.getRhs() != counters[1] ||
      !inside || !inside->getDiscardableAttrDictionary().empty() ||
      inside.getBranchWeights() ||
      inside.getCondition() != compare.getResult() ||
      !inside.getTrueDestOperands().empty() ||
      inside.getFalseDestOperands() != ValueRange{previous} || !atEnd() ||
      !block(inside.getTrueDest()))
    return reader.fail(
        "loop must compare its admitted current coordinate and upper bound");
  Block *finish = inside.getFalseDest();
  auto iteration = dyn_cast_or_null<runtime::IterationOp>(take());
  if (!iteration || iteration.getParent() != scope ||
      iteration.getCoordinate() != coordinate ||
      iteration.getSite() != range.getSite() ||
      !attributes(iteration, {"site"}))
    return reader.fail("loop iteration admission association");
  // Every failure before replacement releases the still-live prior carry.
  auto iterationEdge = dyn_cast_or_null<exec::DispatchOp>(navigation.peek());
  if (!iterationEdge)
    return reader.fail("iteration admission requires an outcome edge");
  Block *releaseFailure = iterationEdge.getStopped();
  if (!releaseFailure || releaseFailure->getParent() != &function.getBody() ||
      releaseFailure == navigation.currentBlock() ||
      !navigation.inspect(releaseFailure) ||
      releaseFailure->getNumArguments() != 1 ||
      releaseFailure->getOperations().size() != 2 || !reader.charge() ||
      !reader.charge())
    return reader.fail("loop failure cleanup block");
  auto release = dyn_cast<runtime::ReleaseTransferOp>(releaseFailure->front());
  auto propagate = dyn_cast<cf::BranchOp>(releaseFailure->back());
  if (!release || !bare(release) || release.getTransfer() != previous ||
      !propagate || !bare(propagate) ||
      propagate.getDestOperands() != releaseFailure->getArguments() ||
      !failedEdge(propagate.getDest()))
    return reader.fail(
        "loop failure must release old carry and preserve its cause");
  SmallVector<Value> nativeIndex;
  if (!dispatch(iteration.getOutcome(), nativeIndex, releaseFailure))
    return false;
  record.induction = reader.fresh();
  environment[nativeIndex.front()] = record.induction;
  auto peek = dyn_cast_or_null<runtime::TransferValuesOp>(take());
  if (!peek || !bare(peek) || peek.getTransfer() != previous ||
      peek.getValues().size() != seeds.size())
    return reader.fail("iteration must read its live previous carry");
  program::Names bodyNames{record.induction};
  for (auto [value, seed] : zip(peek.getValues(), seeds)) {
    auto name = reader.fresh();
    environment[value] = name;
    record.carried.emplace_back(name, seed);
    bodyNames.push_back(std::move(name));
  }
  auto enter = dyn_cast_or_null<runtime::EnterScopeOp>(take());
  SmallVector<Value> prefix{nativeIndex.front()};
  append_range(prefix, peek.getValues());
  if (!enter || enter.getParent() != scope || enter.getKind() != "iteration" ||
      enter.getCoordinate() != coordinate ||
      enter.getSite() != range.getSite() ||
      !attributes(enter, {"operandSegmentSizes", "kind", "site"}) ||
      enter.getInputs().size() < prefix.size() ||
      enter.getInputs().take_front(prefix.size()) != ValueRange(prefix) ||
      !names(enter.getInputs().drop_front(prefix.size()), record.captures))
    return reader.fail("iteration entry/carry/capture association");
  append_range(bodyNames, record.captures);
  SmallVector<Value> acquired;
  if (!dispatch(enter.getOutcome(), acquired, releaseFailure))
    return false;
  SmallVector<Value> callInputs{acquired.front()};
  append_range(callInputs, enter.getInputs());
  auto call = dyn_cast_or_null<func::CallOp>(take());
  if (!call || !attributes(call, {"callee"}) ||
      call.getOperands() != callInputs || call.getNumResults() != 1 ||
      !reader.region(call, bodyNames, record.body))
    return reader.fail("iteration body must use actual scoped arguments");
  step.regions.push_back(reader.callee(call));
  step.inputs = {range.getLower(), range.getUpper()};
  append_range(step.inputs, initial.getInputs());
  append_range(step.inputs, enter.getInputs().drop_front(prefix.size()));
  auto exit = dyn_cast_or_null<runtime::ExitScopeOp>(take());
  if (!exit || !bare(exit) || exit.getScope() != acquired.front() ||
      exit.getBody() != call.getResult(0))
    return reader.fail("iteration must exit its exact acquired scope");
  SmallVector<Value> held;
  if (!dispatch(exit.getOutcome(), held, releaseFailure))
    return false;
  auto old = dyn_cast_or_null<runtime::ReleaseTransferOp>(take());
  if (!old || !bare(old) || old.getTransfer() != previous)
    return reader.fail(
        "old carry must be released after successful child exit");
  Operation *next = take();
  Block *increment = nullptr;
  if (auto condition = dyn_cast_or_null<runtime::TakeConditionOp>(next)) {
    record.conditional = true;
    step.conditional = true;
    if (!bare(condition) || condition.getTransfer() != held.front())
      return reader.fail(
          "conditional loop must inspect its newly returned carry");
    SmallVector<Value> decision;
    if (!dispatch(condition.getOutcome(), decision))
      return false;
    auto branch = dyn_cast_or_null<cf::CondBranchOp>(take());
    if (!branch || !branch->getDiscardableAttrDictionary().empty() ||
        branch.getBranchWeights() || branch.getCondition() != decision[0] ||
        branch.getTrueDestOperands() != ValueRange{decision[1]} ||
        branch.getFalseDestOperands() != ValueRange{decision[1]} ||
        branch.getFalseDest() != finish || !atEnd())
      return reader.fail(
          "conditional loop must preserve carry on either decision");
    increment = branch.getTrueDest();
  } else {
    auto branch = dyn_cast_or_null<cf::BranchOp>(next);
    if (!branch || !bare(branch) || branch.getDestOperands() != held ||
        !atEnd())
      return reader.fail("loop carry replacement edge");
    increment = branch.getDest();
  }
  if (!block(increment) || increment->getNumArguments() != 1)
    return reader.fail("loop increment ports");
  auto one = dyn_cast_or_null<arith::ConstantIntOp>(take());
  auto add = dyn_cast_or_null<arith::AddIOp>(take());
  auto back = dyn_cast_or_null<cf::BranchOp>(take());
  if (!one || !attributes(one, {"value"}) || one.value() != 1 ||
      !one.getType().isSignlessInteger(64) || !add ||
      !attributes(add, {"overflowFlags"}) ||
      add.getOverflowFlags() != arith::IntegerOverflowFlags::none ||
      add.getLhs() != coordinate || add.getRhs() != one.getResult() || !back ||
      !bare(back) || back.getDest() != header ||
      back.getDestOperands() !=
          ValueRange{add.getResult(), increment->getArgument(0)} ||
      !atEnd() || !block(finish) || finish->getNumArguments() != 1)
    return reader.fail("loop must advance once and retain its actual carry");
  auto accept = dyn_cast_or_null<runtime::AcceptTransferOp>(take());
  SmallVector<Value> values;
  if (!accept || !bare(accept) || accept.getParent() != scope ||
      accept.getTransfer() != finish->getArgument(0) ||
      !dispatch(accept.getOutcome(), values) ||
      !results(values, record.outputs))
    return reader.fail("loop must publish its final carry once");
  // Values borrowed inside an iteration cannot be read after its transfer has
  // been released. The reconstructed model independently checks native scopes.
  environment.erase(nativeIndex.front());
  for (Value value : peek.getValues())
    environment.erase(value);
  append_range(step.outputs, values);
  return true;
}
bool BodyReader::scheduledLoop(exec::RangeOp range, program::For &record,
                               SourceExecutionStep &step) {
  // Derive proposed data ports from a bounded prefix of the actual packet.
  // These are not accepted until ControlCursor independently checks every
  // SCF/CFG, scope, transfer and continuation edge against them below.
  for (unsigned i = 0; i < 12; ++i)
    if (!reader.charge())
      return false;
  auto first = [](Block *block) -> Operation * {
    return block && !block->empty() ? &block->front() : nullptr;
  };
  auto next = [](Operation *op) { return op ? op->getNextNode() : nullptr; };
  auto edge = dyn_cast_or_null<exec::DispatchOp>(navigation.peek());
  auto initial = dyn_cast_or_null<runtime::BorrowTransferOp>(
      edge ? first(edge.getReturned()) : nullptr);
  auto loop = dyn_cast_or_null<scf::WhileOp>(next(next(next(initial))));
  auto packet = dyn_cast_or_null<scf::ExecuteRegionOp>(
      loop && loop.getAfter().hasOneBlock() ? first(&loop.getAfter().front())
                                            : nullptr);
  auto unpack = dyn_cast_or_null<exec::DispatchOp>(
      packet && !packet.getRegion().empty() ? first(&packet.getRegion().front())
                                            : nullptr);
  auto iteration = dyn_cast_or_null<runtime::IterationOp>(
      unpack ? first(unpack.getReturned()) : nullptr);
  auto enteredIndex = dyn_cast_or_null<exec::DispatchOp>(next(iteration));
  auto values = dyn_cast_or_null<runtime::TransferValuesOp>(
      enteredIndex ? first(enteredIndex.getReturned()) : nullptr);
  auto enter = dyn_cast_or_null<runtime::EnterScopeOp>(next(values));
  auto enteredScope = dyn_cast_or_null<exec::DispatchOp>(next(enter));
  auto invocation = dyn_cast_or_null<func::CallOp>(
      enteredScope ? first(enteredScope.getReturned()) : nullptr);
  auto bodyOutcome =
      invocation && invocation.getNumResults() == 1
          ? dyn_cast<exec::OutcomeType>(invocation.getResult(0).getType())
          : exec::OutcomeType();
  if (!initial || !enter || !bodyOutcome ||
      enter.getInputs().size() < 1 + initial.getInputs().size())
    return reader.fail("missing scoped SCF iteration ports");
  auto captures = enter.getInputs().drop_front(1 + initial.getInputs().size());
  unsigned states = initial.getInputs().size();
  if (bodyOutcome.getPayload().size() != states &&
      bodyOutcome.getPayload().size() != states + 1)
    return reader.fail("scheduled iteration result arity");
  record.conditional = bodyOutcome.getPayload().size() == states + 1;
  step.conditional = record.conditional;
  program::Names bounds, seeds;
  if (!names({range.getLower(), range.getUpper()}, bounds) ||
      !names(initial.getInputs(), seeds) || !names(captures, record.captures))
    return false;
  record.lower = bounds[0];
  record.upper = bounds[1];
  record.induction = reader.fresh();
  program::Names bodyNames{record.induction};
  for (const auto &seed : seeds) {
    auto name = reader.fresh();
    record.carried.emplace_back(name, seed);
    bodyNames.push_back(std::move(name));
  }
  append_range(bodyNames, record.captures);
  SmallVector<Value> outputs;
  if (!navigation.scheduledLoop(
          range, initial.getInputs(), captures, record.conditional,
          [&](func::CallOp call, unsigned arm) {
            if (arm || call != invocation ||
                !reader.region(call, bodyNames, record.body))
              return false;
            step.regions.push_back(reader.callee(call));
            return true;
          },
          outputs) ||
      !results(outputs, record.outputs))
    return reader.fail("scoped SCF iteration differs");
  step.inputs = {range.getLower(), range.getUpper()};
  append_range(step.inputs, initial.getInputs());
  append_range(step.inputs, captures);
  step.outputs = outputs;
  return true;
}
bool BodyReader::run(ArrayRef<std::string> arguments, program::Body &body) {
  std::vector<SourceExecutionStep> sourceBody;
  auto finish = [&]() {
    if (!navigation.complete())
      return reader.fail("unchecked CFG blocks");
    reader.recordBody(function, std::move(sourceBody));
    return true;
  };
  outcome = cast<exec::OutcomeType>(function.getFunctionType().getResult(0));
  scope = function.getArgument(0);
  if (!block(&function.front()))
    return false;
  for (auto [value, name] :
       zip(function.getArguments().drop_front(), arguments))
    environment[value] = name;
  while (auto *op = take()) {
    SourceExecutionStep step;
    step.operation = op;
    if (auto apply = dyn_cast<exec::ApplyOp>(op)) {
      program::Operation record;
      if (apply.getScope() != scope ||
          !attributes(apply, {"binding", "parameters", "site"}) ||
          !reader.application(apply) ||
          !names(apply.getInputs(), record.inputs))
        return reader.fail("invalid bound instruction");
      record.callee = apply.getBinding().str();
      record.attributes = strings(apply.getParameters());
      SmallVector<Value> values;
      if (!dispatch(apply.getOutcome(), values) ||
          !results(values, record.outputs))
        return false;
      append_range(step.inputs, apply.getInputs());
      step.outputs = values;
      body.push_back({apply.getSite().str(), std::move(record)});
    } else if (auto compute = dyn_cast<exec::ComputeOp>(op)) {
      program::LocalApply record;
      if (compute.getScope() != scope ||
          !reader.computation(compute, record.callee) ||
          !names(compute.getInputs(), record.inputs))
        return reader.fail("invalid source mathematical invocation");
      SmallVector<Value> values;
      if (!dispatch(compute.getOutcome(), values) ||
          !results(values, record.outputs))
        return false;
      append_range(step.inputs, compute.getInputs());
      step.outputs = values;
      body.push_back({compute.getSite().str(), std::move(record)});
    } else if (isa<exec::FoldOp, exec::CollectOp>(op)) {
      program::LocalApply record;
      auto site = op->getAttrOfType<StringAttr>("site");
      if (!site || op->getOperand(0) != scope ||
          !reader.finiteInvocation(op, record.callee) ||
          !names(op->getOperands().drop_front(), record.inputs))
        return reader.fail("invalid source finite invocation");
      SmallVector<Value> values;
      if (!dispatch(op->getResult(0), values) ||
          !results(values, record.outputs))
        return false;
      append_range(step.inputs, op->getOperands().drop_front());
      step.outputs = values;
      body.push_back({site.str(), std::move(record)});
    } else if (auto call = dyn_cast<func::CallOp>(op)) {
      program::LocalApply record;
      auto site = call->getAttrOfType<StringAttr>("runtime.site");
      if (!reader.helper(call) || !site ||
          !attributes(call, {"callee", "runtime.site"}) ||
          call.getOperand(0) != scope ||
          !names(call.getOperands().drop_front(), record.inputs))
        return reader.fail("source helper target, scope or occurrence");
      record.callee = call.getCallee().str();
      SmallVector<Value> values;
      if (!dispatch(call.getResult(0), values) ||
          !results(values, record.outputs))
        return false;
      append_range(step.inputs, call.getOperands().drop_front());
      step.outputs = values;
      body.push_back({site.str(), std::move(record)});
    } else if (auto literal = dyn_cast<exec::BooleanOp>(op)) {
      if (literal.getScope() != scope ||
          !attributes(literal, {"value", "site"}))
        return reader.fail("Boolean instruction scope");
      SmallVector<Value> values;
      program::Names outputs;
      if (!dispatch(literal.getOutcome(), values) || !results(values, outputs))
        return false;
      step.outputs = values;
      body.push_back(
          {literal.getSite().str(),
           program::BooleanConstant{outputs.front(), literal.getValue()}});
    } else if (auto test = dyn_cast<exec::TestOp>(op)) {
      program::Conditional record;
      if (!conditional(test, record, step))
        return false;
      body.push_back({test.getSite().str(), std::move(record)});
    } else if (auto construct = dyn_cast<exec::VariantOp>(op)) {
      program::VariantConstruct record;
      if (construct.getScope() != scope ||
          !attributes(construct, {"site", "alternative"}) ||
          !names(construct.getPayload(), record.payload) ||
          !reader.type(construct.getOutcome().getType().getPayload().front(),
                       record.type))
        return reader.fail("variant construction association");
      record.alternative = construct.getAlternative().str();
      SmallVector<Value> values;
      program::Names outputs;
      if (!dispatch(construct.getOutcome(), values) ||
          !results(values, outputs))
        return false;
      append_range(step.inputs, construct.getPayload());
      step.outputs = values;
      record.output = outputs.front();
      body.push_back({construct.getSite().str(), std::move(record)});
    } else if (auto selected = dyn_cast<exec::MatchOp>(op)) {
      program::Match record;
      if (!match(selected, record, step))
        return false;
      body.push_back({selected.getSite().str(), std::move(record)});
    } else if (auto range = dyn_cast<exec::RangeOp>(op)) {
      program::For record;
      if (!(reader.isScheduled() ? scheduledLoop(range, record, step)
                                 : loop(range, record, step)))
        return false;
      body.push_back({range.getSite().str(), std::move(record)});
    } else if (auto release = dyn_cast<runtime::ReleaseBindingsOp>(op)) {
      program::Release record;
      if (release.getScope() != scope || !bare(release) ||
          !names(release.getValues(), record.values))
        return reader.fail("invalid storage release");
      append_range(step.inputs, release.getValues());
      body.push_back({"", std::move(record)});
    } else if (auto returnedValue = dyn_cast<exec::ReturnOp>(op)) {
      program::Names values;
      if (!reader.isSource() || regionBody || !bare(returnedValue) ||
          !names(returnedValue.getValues(), values) ||
          !returned(take(), returnedValue.getOutcome()) || !atEnd())
        return reader.fail("source return must package its exact payload");
      body.push_back({"", program::Return{std::move(values)}});
      append_range(step.inputs, returnedValue.getValues());
      sourceBody.push_back(std::move(step));
      return finish();
    } else if (auto complete = dyn_cast<exec::CompleteOp>(op)) {
      program::Names values;
      if ((reader.isSource() && !regionBody) || complete.getScope() != scope ||
          !bare(complete) || !names(complete.getValues(), values) ||
          !returned(take(), complete.getOutcome()) || !atEnd())
        return reader.fail("native completion must retain its outcome");
      if (regionBody)
        body.push_back({"", program::Yield{std::move(values)}});
      else
        body.push_back({"", program::Return{std::move(values)}});
      append_range(step.inputs, complete.getValues());
      sourceBody.push_back(std::move(step));
      return finish();
    } else if (auto reject = dyn_cast<exec::RejectOp>(op)) {
      auto branch = dyn_cast_or_null<cf::BranchOp>(take());
      if (reject.getScope() != scope ||
          !attributes(reject, {"site", "reason"}) || !branch || !bare(branch) ||
          branch.getDestOperands() != ValueRange{reject.getStop()} ||
          !atEnd() || !failedEdge(branch.getDest()))
        return reader.fail("native rejection must retain its cause");
      body.push_back(
          {reject.getSite().str(), program::Stop{reject.getReason().str()}});
      sourceBody.push_back(std::move(step));
      return finish();
    } else {
      return reader.fail("operation outside the canonical execution profile");
    }
    sourceBody.push_back(std::move(step));
  }
  return reader.fail("missing native completion");
}
Expected<program::LocalDefinitions> Reader::run(bool mixed) {
  llvm::TimeTraceScope timing("zkc.execution-read");
  program::LocalDefinitions result;
  unsigned definitions = 0, bindings = 0;
  for (Operation &op : module->getRegion(0).front()) {
    if (!remaining)
      return error("execution-cfg", "definition inspection limit");
    --remaining;
    if ((isa<runtime::BindingOp>(op) && ++bindings > 4096) ||
        (isa<func::FuncOp, data::DomainOp>(op) &&
         !(isa<func::FuncOp>(op) && op.hasAttr("runtime.region")) &&
         ++definitions > 4096))
      return error("execution-cfg", "definition inventory limit");
    if (auto binding = dyn_cast<runtime::BindingOp>(op)) {
      if (!attributes(binding,
                      {"sym_name", "contract", "arguments", "implementation",
                       "function_type", "arg_attrs", "res_attrs"}))
        return error("execution-cfg", "unknown binding attribute");
      auto decoded = readBinding(binding);
      if (!decoded)
        return decoded.takeError();
      if (auto e = checkBindingDeclaration(decoded->name, decoded->application,
                                           physical))
        return std::move(e);
      result.bindings.push_back(std::move(*decoded));
      continue;
    }
    auto function = dyn_cast<func::FuncOp>(op);
    if (!function) {
      if (mixed)
        continue;
      return error("execution-cfg", "unexpected execution definition");
    }
    if (source && !isScopedExecutionFunction(function))
      continue;
    if (function->getAttrOfType<UnitAttr>("runtime.region"))
      continue;
    auto origin = function->getAttrOfType<ArrayAttr>("runtime.origin");
    if (!origin || origin.size() != 2 || !isa<StringAttr>(origin[0]) ||
        !isa<ArrayAttr>(origin[1]) || function.getNumArguments() == 0)
      return error("execution-cfg", "missing callable origin");
    program::Function record;
    record.name = function.getSymName().str();
    record.origin =
        program::LogicalOrigin{cast<StringAttr>(origin[0]).str(), {}};
    for (Attribute value : cast<ArrayAttr>(origin[1])) {
      auto pair = dyn_cast<ArrayAttr>(value);
      if (!pair || pair.size() != 2 || !isa<StringAttr>(pair[0]) ||
          !isa<StringAttr>(pair[1]))
        return error("execution-cfg", "invalid origin argument");
      record.origin->arguments.emplace_back(cast<StringAttr>(pair[0]).str(),
                                            cast<StringAttr>(pair[1]).str());
    }
    program::Names arguments;
    for (Type t : function.getArgumentTypes().drop_front()) {
      std::string spelling;
      if (!type(t, spelling))
        return error("execution-cfg", problem);
      arguments.push_back(fresh());
      record.arguments.push_back({arguments.back(), std::move(spelling)});
    }
    if (!body(function, arguments, record.body, false))
      return error("execution-cfg", problem);
    auto outcome =
        cast<exec::OutcomeType>(function.getFunctionType().getResult(0));
    for (Type t : outcome.getPayload()) {
      std::string spelling;
      if (!type(t, spelling))
        return error("execution-cfg", problem);
      record.results.push_back(std::move(spelling));
    }
    result.functions.push_back(std::move(record));
  }
  for (auto function : module->getRegion(0).front().getOps<func::FuncOp>())
    if ((!source || isScopedExecutionFunction(function)) &&
        !visited.contains(function))
      return error("execution-cfg", "unchecked region definition");
  if (source) {
    if (mathematicalCalls && result.functions.empty())
      return result;
    llvm::TimeTraceScope admissionTiming("zkc.execution-native-admission");
    if (auto e = admitNativeLocalDefinitions(result, mathematicalSignatures))
      return std::move(e);
    return result;
  }
  llvm::TimeTraceScope admissionTiming("zkc.execution-native-admission");
  if (auto e = admitExecutionDefinitions(result, physical))
    return std::move(e);
  return result;
}
} // namespace
Expected<program::LocalDefinitions> readLocalExecution(ModuleOp module,
                                                       bool physical) {
  if (!module || failed(verify(module)) || !module->getAttrs().empty())
    return error("execution-cfg", "expected a verified local execution module");
  return Reader(module, physical).run();
}
Expected<program::LocalDefinitions>
readExecutionDefinitions(Operation *symbolTable, bool physical) {
  if (failed(detail::verifyExecutionDefinitionScope(symbolTable)))
    return error("execution-cfg", "invalid execution definition scope");
  return Reader(symbolTable, physical).run(/*mixed=*/true);
}
Expected<SourceExecutionClosure>
readScheduledExecutionClosure(Operation *symbolTable) {
  if (failed(detail::verifyExecutionDefinitionScope(symbolTable, true, true)))
    return error("execution-schedule", "invalid scheduled definition scope");
  for (Operation &op : symbolTable->getRegion(0).front()) {
    if (isa<runtime::BindingOp>(op))
      continue;
    auto function = dyn_cast<func::FuncOp>(op);
    if (!function || !isScopedExecutionFunction(function))
      return error("execution-schedule", "non-executable schedule declaration");
  }
  Reader reader(symbolTable, false, true, false, true);
  auto definitions = reader.run(true);
  if (!definitions)
    return error("execution-schedule", toString(definitions.takeError()));
  return SourceExecutionClosure{
      std::move(*definitions), {}, {}, reader.takeBodies()};
}
Expected<SourceExecutionClosure> readExecutionClosure(Operation *symbolTable,
                                                      bool physical) {
  if (failed(detail::verifyExecutionDefinitionScope(symbolTable)))
    return error("execution-cfg", "invalid execution definition scope");
  Reader reader(symbolTable, physical);
  auto definitions = reader.run(/*mixed=*/true);
  if (!definitions)
    return definitions.takeError();
  return SourceExecutionClosure{
      std::move(*definitions), {}, {}, reader.takeBodies()};
}
Expected<program::LocalDefinitions>
readSourceExecutionDefinitions(Operation *symbolTable) {
  if (failed(detail::verifyExecutionDefinitionScope(symbolTable,
                                                    /*source=*/true)))
    return error("execution-cfg", "invalid source execution definition scope");
  return Reader(symbolTable, /*physical=*/false, /*source=*/true)
      .run(/*mixed=*/true);
}
Expected<SourceExecutionClosure>
readSourceExecutionClosure(Operation *symbolTable) {
  llvm::TimeTraceScope timing("zkc.source-execution-closure");
  if (failed(detail::verifyExecutionDefinitionScope(symbolTable, true)))
    return error("execution-source-closure", "invalid source definition scope");
  SmallVector<Operation *> definitions;
  unsigned remaining = 1000000;
  for (Operation &op : symbolTable->getRegion(0).front()) {
    if (isa<func::FuncOp, data::DomainOp>(op))
      definitions.push_back(&op);
    if (auto unit = dyn_cast<ModuleOp>(op)) {
      if (!unit->hasAttr("exec.computation"))
        continue;
      // The enclosing source profile has not verified this nested symbol
      // table. Bound and verify its actual IR before querying typed signatures
      // or mathematical premises, including for dormant selected units.
      if (unit.walk<WalkOrder::PreOrder>([&](Operation *) {
                if (!remaining)
                  return WalkResult::interrupt();
                --remaining;
                return WalkResult::advance();
              })
              .wasInterrupted() ||
          failed(verify(unit)) ||
          failed(mathematical::verifyComputationUnit(unit)))
        return error("execution-source-closure",
                     "invalid selected computation unit");
    }
  }
  // Include scoped entry premises and actual ordinary/mathematical call sites,
  // as well as the plain mathematical definitions checked by formation.
  if (failed(finite::verifyDefinitionClosure(symbolTable, definitions)))
    return error("execution-source-closure",
                 "source data premises do not hold");
  Reader reader(symbolTable, /*physical=*/false, /*source=*/true,
                /*mathematicalCalls=*/true);
  auto admitted = reader.run(/*mixed=*/true);
  if (!admitted)
    return error("execution-source-closure", toString(admitted.takeError()));
  auto bodies = reader.takeBodies();
  // Each retained computation occurrence may require a distinct expanded
  // body. Reusing a checked helper signature must not reset or bypass the
  // shared expansion ceiling. Count actual requests, including dormant roots,
  // before liveness or numerical normalization can erase their mathematics.
  SymbolTableCollection symbols;
  llvm::DenseMap<Operation *, std::unique_ptr<mathematical::TotalClosure>>
      mathematicalClosures;
  unsigned expansion = mathematical::realizedHelperOperationLimit;
  for (const auto &body : bodies)
    for (const auto &step : body.second) {
      auto call = dyn_cast<exec::ComputeOp>(step.operation);
      if (!call)
        continue;
      auto helper = call.resolveCallee(symbols);
      if (!helper)
        return error("execution-source-closure", "missing computation body");
      auto *owner = helper->getParentOp();
      auto &closure = mathematicalClosures[owner];
      if (!closure) {
        auto unit = dyn_cast<ModuleOp>(owner);
        auto entry =
            unit ? mathematical::getComputationEntry(unit) : func::FuncOp();
        closure =
            std::make_unique<mathematical::TotalClosure>(owner, symbols, entry);
      }
      const mathematical::TotalSummary *summary;
      if (failed(closure->get(helper, summary)))
        return error("execution-source-closure", "invalid computation summary");
      if (summary->expandedOperations > expansion)
        return error("mathematical-analysis-limit",
                     "computation requests exceed the shared expansion budget");
      expansion -= summary->expandedOperations;
    }
  return SourceExecutionClosure{std::move(*admitted), reader.takeComputations(),
                                reader.takeComputationOrigins(),
                                std::move(bodies)};
}
Error verifySourceExecutionClosure(Operation *symbolTable) {
  auto admitted = readSourceExecutionClosure(symbolTable);
  return admitted ? Error::success() : admitted.takeError();
}
} // namespace zkc::protocol
