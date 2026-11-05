#include "NativeConstructionPreparation.h"
#include "NativeRequest.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Polynomial/Mathematical.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/SelectedControl.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringMap.h"
#include <algorithm>
#include <limits>
#include <map>

using namespace mlir;
using namespace llvm;
namespace zkc::detail {
struct NativeConstructionPreparation::Storage {
  ModuleOp source;
  const protocol::SourceExecutionClosure *execution;
  SmallVector<ConstructionDependency> dependencies;
  struct Request {
    std::string occurrence;
    protocol_ir::ExchangeOp exchange;
    unsigned validatorPayload, producerPayload;
  };
  SmallVector<Request> requests;
  struct RequestAssociation {
    protocol_ir::ExchangeOp original;
    protocol_ir::EmitOp validatorSend;
    protocol_ir::AwaitOp producerReceive;
    mlir::Value replica;
    bool ordinary;
  };
  SmallVector<RequestAssociation> requestAssociations;
  uint64_t used, remaining;
  bool complete = false, deferred = false, exhausted = false;
  ModuleOp realized;
  const protocol::SourceExecutionClosure *realizedExecution = nullptr;
};
NativeConstructionPreparation::NativeConstructionPreparation(
    std::unique_ptr<Storage> storage)
    : storage(std::move(storage)) {}
NativeConstructionPreparation::NativeConstructionPreparation(
    NativeConstructionPreparation &&) noexcept = default;
NativeConstructionPreparation &NativeConstructionPreparation::operator=(
    NativeConstructionPreparation &&) noexcept = default;
NativeConstructionPreparation::~NativeConstructionPreparation() = default;
ArrayRef<ConstructionDependency>
NativeConstructionPreparation::dependencies() const {
  return storage->dependencies;
}
ModuleOp NativeConstructionPreparation::source() const {
  return storage->source;
}
const protocol::SourceExecutionClosure &
NativeConstructionPreparation::execution() const {
  return *storage->execution;
}
uint64_t NativeConstructionPreparation::workUsed() const {
  return storage->used;
}

bool NativeConstructionPreparation::complete() const {
  return storage->complete;
}
bool NativeConstructionPreparation::needsRealization() const {
  return storage->deferred;
}

namespace {
namespace pir = protocol_ir;
using Kind = ConstructionDependencyKind;
using Rule = protocol::ConstructionRule;
using Id = unsigned;
constexpr Id absent = std::numeric_limits<Id>::max();
using Environment = llvm::DenseMap<Value, Id>;
struct Frame {
  Environment values;
  Id effect = absent, state = absent, record = absent, proof = absent;
  bool conditional = false;
};
// This analysis deliberately retains conservative dependence, not semantic
// equality. An edge through a formal, return or alias is never an agreement
// fact between participants. NativeRequest owns that separate judgment.
class Reader {
  ModuleOp source;
  pir::ProtocolModuleOp module;
  pir::MathematicalOp entry;
  const protocol::SourceExecutionClosure &execution;
  const NativeProofPolicy &policy;
  const protocol::ConstructionPlan *plan;
  ArrayRef<protocol::ConstructionInvocation> invocations;
  uint64_t remaining;
  StringMap<Operation *> symbols;
  SymbolTableCollection symbolTables;
  StringMap<StringRef> roles;
  llvm::DenseSet<Operation *> sourceOperations, active;
  struct QueryContinuation {
    pir::ApplyOp application;
    std::string prefix;
    const StringMap<StringRef> *roles;
    unsigned level;
  };
  SmallVector<QueryContinuation> queryContinuations;
  std::map<std::pair<Rule::Kind, std::string>, const Rule *> rules;
  llvm::DenseSet<const Rule *> usedRules;
  llvm::DenseSet<const protocol::ConstructionInvocation *> usedStarts;
  struct Request {
    pir::ExchangeOp exchange;
    Id validatorPayload = absent, producerPayload = absent;
  };
  StringMap<Request> reverseRequests;
  bool validator = false;
  bool allowLogical;
  std::string problem;

  bool refuse(StringRef diagnostic) {
    if (problem.empty())
      problem = diagnostic.str();
    return false;
  }
  bool fail(StringRef code) {
    return refuse(("native-construction-preparation-" + code).str());
  }
  bool charge(uint64_t n = 1) {
    if (n > remaining) {
      remaining = 0;
      return fail("capacity");
    }
    remaining -= n;
    return true;
  }
  bool depth(unsigned n) { return n <= 64 || fail("capacity"); }
  // Charge individual terms: never add/multiply unchecked client sizes.
  bool tree(Operation *op, unsigned level) {
    if (!depth(level) || !charge() || !charge(op->getNumOperands()) ||
        !charge(op->getNumResults()) || !charge(op->getNumRegions()) ||
        !charge(op->getAttrs().size()) || !charge())
      return false;
    if (auto name =
            op->getAttrOfType<StringAttr>(SymbolTable::getSymbolAttrName()))
      if (!charge(name.getValue().size()))
        return false;
    sourceOperations.insert(op);
    // Symbol/module wrappers consume work but not semantic body depth, as in
    // ordinary Protocol admission and the Oracle/request structural readers.
    unsigned nestedDepth =
        level + !isa<ModuleOp, func::FuncOp, pir::ProtocolModuleOp,
                     pir::MathematicalOp>(op);
    for (Region &region : op->getRegions())
      for (Block &block : region) {
        if (!charge() || !charge(block.getNumArguments()))
          return false;
        for (Operation &child : block)
          if (!tree(&child, nestedDepth))
            return false;
      }
    return true;
  }
  Id node(Kind kind, Operation *op, ArrayRef<Id> inputs = {}, Id prior = absent,
          Value value = {}, bool conditional = false,
          func::FuncOp callback = {}) {
    if (!problem.empty() || !charge() || !charge(inputs.size()) ||
        !charge(prior != absent))
      return absent;
    if (nodes.size() >= absent) {
      fail("capacity");
      return absent;
    }
    Id index = nodes.size();
    ConstructionDependency item{
        kind,
        op,
        value,
        value
            ? (isa<BlockArgument>(value) ? cast<BlockArgument>(value).getOwner()
                                         : value.getDefiningOp()->getBlock())
            : (op ? op->getBlock() : nullptr),
        callback,
        {},
        validator,
        conditional};
    for (Id input : inputs) {
      // A source operand must be available in the selected execution order.
      // The union is checked here, not by independent recipe/layout checks.
      if (input == absent || input >= index) {
        fail("order");
        return absent;
      }
      item.predecessors.push_back(input);
    }
    if (prior != absent) {
      if (prior >= index) {
        fail("order");
        return absent;
      }
      item.predecessors.push_back(prior);
    }
    item.stopped = op && isa<exec::RejectOp>(op);
    if (kind == Kind::Callback && prior != absent)
      item.stopped = nodes[prior].stopped;
    item.includesZeroTrip = kind == Kind::Iteration;
    nodes.push_back(std::move(item));
    return index;
  }
  bool bind(Environment &env, Value value, Id id) {
    if (id == absent || !charge())
      return false;
    env[value] = id;
    return true;
  }
  bool inputs(Environment &env, ValueRange values, SmallVectorImpl<Id> &out,
              bool required = true) {
    for (Value value : values) {
      if (!charge())
        return false;
      auto found = env.find(value);
      if (found == env.end())
        return required ? fail("dependency") : false;
      if (!charge())
        return false;
      out.push_back(found->second);
    }
    return true;
  }
  bool copyFrame(const Frame &from, Frame &to) {
    if (!charge(from.values.size()) || !charge(4))
      return false;
    to = from;
    return true;
  }
  func::FuncOp function(FlatSymbolRefAttr ref) {
    if (!ref || !charge(ref.getValue().size()) || !charge())
      return {};
    return dyn_cast_or_null<func::FuncOp>(symbols.lookup(ref.getValue()));
  }
  const Rule *rule(Rule::Kind kind, StringRef site) {
    if (!charge(site.size()) || !charge())
      return nullptr;
    auto found = rules.find({kind, site.str()});
    return found == rules.end() ? nullptr : found->second;
  }
  std::string occurrence(StringRef prefix, StringRef site) {
    // Bound expanded occurrence spelling and temporary strings before
    // allocation.
    for (unsigned i = 0; i < 4; ++i)
      if (!charge(prefix.size()) || !charge(site.size()))
        return {};
    return prefix.empty() ? site.str()
                          : mathematical::expandedApplicationSite(prefix, site);
  }
  StringRef mappedRole(StringRef local) {
    if (!charge(local.size()) || !charge())
      return {};
    auto found = roles.find(local);
    if (found == roles.end()) {
      fail("source");
      return {};
    }
    return found->second;
  }
  bool owns(ArrayAttr owners) {
    StringRef role =
        validator ? StringRef(policy.validator) : StringRef(policy.producer);
    for (auto item : owners) {
      if (!charge())
        return false;
      if (mappedRole(cast<StringAttr>(item).getValue()) == role)
        return true;
    }
    return false;
  }

  // All expression walks use the admitted native operations themselves. The
  // returned node summarizes dependency, not equality of result components.
  Id mathBlock(Block &body, Environment &env, Id prior, bool conditional,
               unsigned level, bool domain = false) {
    if (!depth(level) || !charge(body.getNumArguments()))
      return absent;
    Id last = prior;
    for (Operation &op : body) {
      if (!charge())
        return absent;
      SmallVector<Id> values;
      if (!inputs(env, op.getOperands(), values))
        return absent;
      if (auto call = dyn_cast<func::CallOp>(op)) {
        if (!charge(call.getCallee().size()))
          return absent;
        last = mathematics(symbolTables.lookupNearestSymbolFrom<func::FuncOp>(
                               call, call.getCalleeAttr()),
                           &op, values, last, conditional, level + 1);
      } else if (finite::isComputation(&op)) {
        last = finiteComputation(&op, op.getOperands(), values, last,
                                 conditional, level + 1);
      } else if (isa<data::BranchOp>(op)) {
        if (op.getNumRegions() > selectedRegionArmLimit || values.empty()) {
          fail("capacity");
          return absent;
        }
        Id boundary = node(Kind::Capture, &op, values, last, {}, conditional);
        SmallVector<Id> endings;
        for (Region &region : op.getRegions()) {
          if (!hasSingleElement(region)) {
            fail("profile");
            return absent;
          }
          Environment arm;
          for (BlockArgument formal : region.front().getArguments()) {
            if (!charge(region.front().getNumArguments()))
              return absent;
            Value actual = selectedCapture(formal);
            Id input = actual ? env.lookup(actual) : values.front();
            // lookup()'s default zero is not an available dependency.
            if (actual && !env.count(actual)) {
              fail("dependency");
              return absent;
            }
            if (!bind(
                    arm, formal,
                    node(Kind::Capture, &op, {input}, boundary, formal, true)))
              return absent;
          }
          Id end = mathBlock(region.front(), arm, boundary, true, level + 1);
          if (end == absent || !charge())
            return absent;
          endings.push_back(end);
        }
        last = node(Kind::Join, &op, endings, boundary, {}, conditional);
      } else if (op.getNumRegions() ||
                 (!isa<func::ReturnOp, data::YieldOp, poly::RecipeYieldOp>(
                      op) &&
                  !mathematical::isTotal(&op) &&
                  !(domain &&
                    isa<data::DomainElementsOp, data::DomainIndicesOp,
                        data::DomainRangeOp, data::DomainZipOp,
                        data::DomainProductOp, data::DomainMatrixRowOp,
                        data::DomainMatrixColumnOp,
                        data::DomainMatrixCoordinatesOp, data::DomainYieldOp>(
                        op)))) {
        fail("profile");
        return absent;
      } else {
        last = node(Kind::Source, &op, values, last, {}, conditional);
      }
      if (last == absent)
        return absent;
      for (Value output : op.getResults())
        if (!bind(env, output,
                  node(Kind::Source, &op, {last}, absent, output, conditional)))
          return absent;
    }
    return last;
  }
  Id mathematics(func::FuncOp f, Operation *anchor, ArrayRef<Id> args, Id prior,
                 bool conditional, unsigned level) {
    if (!f || !depth(level) || !charge() || !sourceOperations.contains(f) ||
        f.isExternal() || !hasSingleElement(f.getBody()) ||
        f.getNumArguments() != args.size()) {
      fail("profile");
      return absent;
    }
    if (!active.insert(f).second) {
      fail("recursion");
      return absent;
    }
    Id first = node(Kind::Callback, anchor, args, prior, {}, conditional, f);
    Environment env;
    for (auto [formal, actual] : zip(f.getArguments(), args))
      if (!bind(env, formal,
                node(Kind::Capture, f, {actual}, first, formal, conditional)))
        return absent;
    Id last =
        mathBlock(f.getBody().front(), env, first, conditional, level + 1);
    active.erase(f);
    return node(Kind::Callback, anchor, args, last, {}, conditional, f);
  }
  Id finiteComputation(Operation *op, ValueRange actuals, ArrayRef<Id> args,
                       Id prior, bool conditional, unsigned level) {
    finite::Computation computation;
    for (StringRef name : {"domain", "body", "step", "predicate"})
      if (auto reference = op->getAttrOfType<FlatSymbolRefAttr>(name))
        if (!charge(reference.getValue().size()))
          return absent;
    if (!depth(level) || !charge(op->getAttrs().size()) ||
        failed(finite::describe(op, computation, nullptr, &symbolTables)) ||
        !sourceOperations.contains(computation.domain) ||
        failed(finite::partitionEntry(computation, actuals)) ||
        actuals.size() != args.size()) {
      fail("closure");
      return absent;
    }
    computation.scopedSource = &execution;
    auto domain = computation.domain;
    if (!active.insert(domain).second) {
      fail("recursion");
      return absent;
    }
    Id first = node(Kind::Iteration, op, args, prior, {}, conditional);
    Environment env;
    for (auto [formal, actual] : zip(domain.getBody().front().getArguments(),
                                     args.take_front(computation.arguments)))
      if (!bind(env, formal,
                node(Kind::Capture, domain, {actual}, first, formal,
                     conditional)))
        return absent;
    Id domainEnd = mathBlock(domain.getBody().front(), env, first, conditional,
                             level + 1, true);
    active.erase(domain);
    if (domainEnd == absent)
      return absent;
    Id last = domainEnd;
    auto read = [&](finite::CallbackRole role) -> bool {
      auto abi = finite::readCallbackABI(computation, role);
      if (failed(abi) || !sourceOperations.contains(abi->symbol))
        return fail("closure");
      SmallVector<Id> callbackInputs;
      // A symbolic carried state includes every iteration input. Its body and
      // continuing return are retained below; no runtime trip is enumerated.
      for (Value formal : abi->formals.state) {
        if (!charge())
          return false;
        callbackInputs.push_back(
            node(Kind::Iteration, op, args, first, formal, true));
      }
      for (Value formal : abi->formals.items) {
        if (!charge())
          return false;
        callbackInputs.push_back(
            node(Kind::Capture, domain, {domainEnd}, first, formal, true));
      }
      if (!charge(computation.arguments) || !charge(computation.captures))
        return false;
      append_range(callbackInputs, args.take_front(computation.arguments));
      append_range(callbackInputs,
                   args.drop_front(computation.arguments + computation.states));
      auto function = cast<func::FuncOp>(abi->symbol);
      last = computation.scoped
                 ? callback(function, op, callbackInputs, last, true, level + 1)
                 : mathematics(function, op, callbackInputs, last, true,
                               level + 1);
      return last != absent;
    };
    if (computation.predicate && !read(finite::CallbackRole::Predicate))
      return absent;
    if (!read(computation.collect ? finite::CallbackRole::Body
                                  : finite::CallbackRole::Step))
      return absent;
    // The entry is the zero-trip/empty-domain alternative. Predicate and body
    // callbacks are conditional, preserving their reached order and stops.
    return node(Kind::Iteration, op, {first, domainEnd, last}, prior, {},
                conditional);
  }
  // Read actual closure steps, recursively retaining nested calls/regions. The
  // administrative CFG and failure transfers are owned by
  // SourceExecutionClosure. Every invocation conservatively depends on all
  // actual arguments even when its body returns a constant or stops without
  // using one of them.
  Id callback(func::FuncOp f, Operation *anchor, ArrayRef<Id> args, Id prior,
              bool conditional, unsigned level, bool region = false) {
    if (!f || !depth(level) || !charge() || f.isExternal() ||
        !sourceOperations.contains(f)) {
      fail("closure");
      return absent;
    }
    if (!active.insert(f).second) {
      fail("recursion");
      return absent;
    }
    if (!charge(f.getSymName().size()))
      return absent;
    auto body = execution.bodies.find(f.getSymName().str());
    if (body == execution.bodies.end() || f.getNumArguments() == 0 ||
        (!region && f.getNumArguments() - 1 != args.size())) {
      fail("closure");
      return absent;
    }
    Id entryNode =
        node(Kind::Callback, anchor, args, prior, {}, conditional, f);
    Environment env;
    for (auto [i, arg] : enumerate(f.getArguments().drop_front())) {
      // Closed outlined payload/carry formals have different ABIs from their
      // parent test/range. Their conservative boundary uses all actual step
      // inputs; these are dependencies, not inferred alias identities.
      Id input = region ? entryNode : args[i];
      Id formal = node(Kind::Capture, f, {input}, absent, arg, conditional);
      if (!bind(env, arg, formal))
        return absent;
    }
    Id last = entryNode;
    bool terminal = false;
    for (const auto &step : body->second) {
      if (!charge() || !charge(step.inputs.size()) ||
          !charge(step.outputs.size()) || !charge(step.regions.size()))
        return absent;
      auto *op = step.operation;
      if (!op || !sourceOperations.contains(op) ||
          op->getParentOfType<func::FuncOp>() != f) {
        fail("closure");
        return absent;
      }
      SmallVector<Id> dependencies;
      if (!inputs(env, step.inputs, dependencies))
        return absent;
      Id current = node(Kind::Source, op, dependencies, last, {}, conditional);
      if (auto call = dyn_cast<func::CallOp>(op)) {
        auto target = function(call.getCalleeAttr());
        current =
            callback(target, op, dependencies, current, conditional, level + 1);
      } else if (!step.regions.empty()) {
        if (step.regions.size() > selectedRegionArmLimit) {
          fail("capacity");
          return absent;
        }
        bool iteration = isa<exec::RangeOp>(op);
        SmallVector<Id> arms;
        // Each arm starts from current, NEVER the previous arm's effects.
        for (auto child : step.regions) {
          if (!charge())
            return absent;
          auto arm =
              callback(child, op, dependencies, current, true, level + 1, true);
          if (arm == absent)
            return absent;
          arms.push_back(arm);
        }
        if (iteration) {
          if (!charge())
            return absent;
          arms.push_back(
              current); // zero iterations preserves the initial boundary
        }
        current = node(iteration ? Kind::Iteration : Kind::Join, op, arms,
                       current, {}, conditional || step.conditional);
      } else if (auto compute = dyn_cast<exec::ComputeOp>(op)) {
        if (!charge(compute.getCalleeAttr().getNestedReferences().size()) ||
            !charge(compute.getCalleeAttr().getRootReference().size()))
          return absent;
        for (auto name : compute.getCalleeAttr().getNestedReferences())
          if (!charge(name.getValue().size()))
            return absent;
        current = mathematics(compute.resolveCallee(symbolTables), op,
                              dependencies, current, conditional, level + 1);
      } else if (isa<exec::FoldOp, exec::CollectOp>(op)) {
        current = finiteComputation(op, step.inputs, dependencies, current,
                                    conditional, level + 1);
      } else if (!isa<exec::ApplyOp, exec::BooleanOp, exec::VariantOp,
                      exec::ReturnOp, exec::CompleteOp, exec::RejectOp,
                      runtime::ReleaseBindingsOp>(op)) {
        fail("dependency");
        return absent;
      }
      for (Value output : step.outputs)
        if (!bind(
                env, output,
                node(Kind::Source, op, {current}, absent, output, conditional)))
          return absent;
      last = current;
      if (isa<exec::ReturnOp, exec::CompleteOp, exec::RejectOp>(op)) {
        terminal = true;
        // Reject has no successful successor. The node records reached work;
        // callers use it only as a conditional normal-continuation dependency.
        last = node(Kind::Completion, op, {}, last, {},
                    conditional || isa<exec::RejectOp>(op));
      }
    }
    active.erase(f);
    if (!terminal) {
      fail("closure");
      return absent;
    }
    return node(Kind::Callback, anchor, args, last, {}, conditional, f);
  }
  // A declarative realization has an actual finite-ring body, but no scoped
  // execution body yet. Retain that body and every call input as an explicit
  // obligation. Slot captures depend conservatively on the whole boundary;
  // neither a signature nor type/position coincidence supplies SSA equality.
  Id localCall(pir::LocalCallOp call, ArrayRef<Id> args, Id prior,
               bool conditional, unsigned level) {
    if (!charge(call.getCallee().size()) || !charge())
      return absent;
    Operation *target = symbols.lookup(call.getCallee());
    auto realization = dyn_cast_or_null<poly::RealizeOp>(target);
    if (!realization)
      return callback(dyn_cast_or_null<func::FuncOp>(target), call, args, prior,
                      conditional, level);
    if (!allowLogical || !depth(level) ||
        !sourceOperations.contains(realization) ||
        !charge(realization.getRecipe().size()) || !charge()) {
      fail("closure");
      return absent;
    }
    auto recipe = dyn_cast_or_null<poly::RecipeOp>(
        symbols.lookup(realization.getRecipe()));
    if (!recipe || !sourceOperations.contains(recipe) ||
        !hasSingleElement(recipe.getBody()) ||
        realization.getFunctionType().getNumInputs() != args.size()) {
      fail("closure");
      return absent;
    }
    Id boundary =
        node(Kind::Realization, realization, args, prior, {}, conditional);
    Environment env;
    for (BlockArgument formal : recipe.getBody().front().getArguments())
      if (!bind(env, formal,
                node(Kind::Capture, recipe, {boundary}, absent, formal,
                     conditional)))
        return absent;
    Id body = mathBlock(recipe.getBody().front(), env, boundary, conditional,
                        level + 1);
    return node(Kind::Realization, call, {body}, boundary, {}, conditional);
  }
  FunctionType dataSignature(func::FuncOp f) {
    if (!f)
      return {};
    auto type = f.getFunctionType();
    if (!charge(type.getNumInputs()) || !charge(type.getNumResults()))
      return {};
    for (Type output : type.getResults())
      if (auto outcome = dyn_cast<exec::OutcomeType>(output))
        if (!charge(outcome.getPayload().size()))
          return {};
    return protocol::scopedDataSignature(f);
  }
  bool signature(FlatSymbolRefAttr ref, ArrayRef<Type> in, ArrayRef<Type> out) {
    auto f = function(ref);
    if (!f || !charge(in.size()) || !charge(out.size()))
      return fail("signature");
    auto type = dataSignature(f);
    return (type && llvm::equal(type.getInputs(), in) &&
            llvm::equal(type.getResults(), out)) ||
           fail("signature");
  }
  Id invoke(FlatSymbolRefAttr ref, Kind kind, Operation *anchor,
            ArrayRef<Id> args, Frame &frame, unsigned level) {
    auto f = function(ref);
    Id body = callback(f, anchor, args, frame.effect, frame.conditional, level);
    frame.effect = node(kind, anchor, {body}, absent, {}, frame.conditional, f);
    return frame.effect;
  }
  Id invoke(const Rule *selected, Kind kind, Operation *anchor,
            ArrayRef<Id> args, Frame &frame, unsigned level) {
    if (!selected) {
      fail("coverage");
      return absent;
    }
    if (!charge())
      return absent;
    usedRules.insert(selected);
    return invoke(selected->handler, kind, anchor, args, frame, level);
  }
  bool selectedInputs(ArrayRef<unsigned> ports, Block &block, Frame &frame,
                      SmallVectorImpl<Id> &args) {
    for (unsigned index : ports) {
      if (!charge() || index >= block.getNumArguments())
        return fail("signature");
      if (!inputs(frame.values, block.getArgument(index), args))
        return false;
    }
    return true;
  }
  bool finish(Operation *op, Frame &frame, unsigned level, bool conditional) {
    if (plan && plan->codec) {
      if (!charge(plan->codec->record.size()))
        return false;
      SmallVector<Id> args(plan->codec->record.size(), frame.record);
      if (validator) {
        if (!charge())
          return false;
        args.push_back(frame.proof);
      }
      bool saved = frame.conditional;
      frame.conditional |= conditional;
      invoke(validator ? plan->codec->finish : plan->codec->write,
             Kind::Finalization, op, args, frame, level);
      frame.conditional = saved;
    }
    frame.effect =
        node(Kind::Completion, op, {}, frame.effect, {}, conditional);
    return frame.effect != absent;
  }
  // Build the full fixed-handler ABI, including a negative boundary for a
  // proposed receive(state, Record, proof). State slots are not receive ports.
  bool signatures() {
    if (!plan)
      return true;
    auto bytes = data::BytesType::get(source.getContext());
    Type index =
        IntegerType::get(source.getContext(), 64, IntegerType::Unsigned);
    if (plan->root == protocol::ConstructionPlan::Root::Local &&
        !signature(plan->initializer, {}, plan->state))
      return false;
    for (const auto &r : plan->rules) {
      if (!charge() || !charge(r.payload.size()) || !charge(r.chunks.size()) ||
          !charge(plan->state.size()) || !charge(plan->state.size()))
        return false;
      SmallVector<Type> in(plan->state), out(plan->state);
      if (r.kind == Rule::Kind::Start) {
        for (unsigned port : r.inputs) {
          if (!charge() || port >= entry.getFunctionType().getNumInputs())
            return fail("signature");
          in.push_back(entry.getFunctionType().getInput(port));
        }
      } else if (r.kind == Rule::Kind::Query) {
        append_range(out, r.payload);
        auto f = function(r.handler);
        auto t = dataSignature(f);
        if (t && t.getNumInputs() == in.size() + 1)
          in.push_back(index);
      } else if (r.kind == Rule::Kind::Message)
        append_range(in, r.payload);
      else {
        if (!plan->codec || !charge(plan->codec->record.size()) ||
            !charge(plan->codec->record.size()))
          return fail("signature");
        switch (r.kind) {
        case Rule::Kind::Encode:
          in = plan->codec->record;
          append_range(in, r.payload);
          out = plan->codec->record;
          append_range(out, r.chunks);
          break;
        case Rule::Kind::Receive:
          in = plan->codec->record;
          in.push_back(bytes);
          out = plan->codec->record;
          for (Type chunk : r.chunks) {
            if (chunk != bytes || !charge(2))
              return fail("signature");
            out.push_back(index);
            out.push_back(index);
          }
          break;
        case Rule::Kind::Decode:
          in = r.chunks;
          out = r.payload;
          break;
        case Rule::Kind::Wire:
          append_range(in, r.chunks);
          break;
        default:
          return fail("signature");
        }
      }
      if (!signature(r.handler, in, out))
        return false;
    }
    if (plan->codec) {
      const auto &codec = *plan->codec;
      SmallVector<Type> in;
      for (unsigned port : codec.inputs) {
        if (!charge() || port >= entry.getFunctionType().getNumInputs())
          return fail("signature");
        in.push_back(entry.getFunctionType().getInput(port));
      }
      if (!signature(codec.initialize, in, codec.record) ||
          !signature(codec.write, codec.record, {bytes}))
        return false;
      if (!charge(codec.record.size()) || !charge())
        return false;
      in = codec.record;
      in.push_back(bytes);
      if (!signature(codec.finish, in, {}))
        return false;
    }
    return true;
  }
  llvm::DenseSet<Id> selectedServices;
  struct QueryDelivery {
    const Rule *rule = nullptr;
    pir::QueryOp query;
    std::string queryOccurrence;
  };
  StringMap<QueryDelivery> selectedQueries;
  StringMap<const Rule *> querySelections;
  struct QueryInputs {
    pir::QueryOp operation;
    SmallVector<Id> inputs;
  };
  StringMap<QueryInputs> originalQueryInputs;
  bool stateArguments(Frame &frame, SmallVectorImpl<Id> &args) {
    size_t count = plan ? plan->state.size() : 1;
    if (!charge(count))
      return false;
    args.append(count, frame.state);
    return true;
  }
  bool pure(Operation *op, Frame &frame, unsigned level = 0) {
    if (auto restrict = dyn_cast<pir::RestrictRolesOp>(op)) {
      if (!owns(restrict.getRoles()))
        return problem.empty();
      auto found = frame.values.find(restrict.getInput());
      return found == frame.values.end()
                 ? problem.empty()
                 : bind(frame.values, restrict.getOutput(), found->second);
    }
    if (auto assembled = dyn_cast<pir::AssembleRolesOp>(op)) {
      for (auto [role, value] :
           zip(assembled.getRoles(), assembled.getInputs())) {
        if (!charge())
          return false;
        if (mappedRole(cast<StringAttr>(role).getValue()) !=
            (validator ? policy.validator : policy.producer))
          continue;
        auto found = frame.values.find(value);
        return found != frame.values.end() &&
               bind(frame.values, assembled.getOutput(), found->second);
      }
      return problem.empty();
    }
    SmallVector<Id> dependencies;
    // A pure source calculation unavailable to this role is not executed here.
    // A later REQUIRED use still refuses; this is never a missing-edge default.
    if (!inputs(frame.values, op->getOperands(), dependencies, false))
      return problem.empty();
    Id id = finite::isComputation(op)
                ? finiteComputation(op, op->getOperands(), dependencies,
                                    frame.effect, frame.conditional, level + 1)
                : node(Kind::Source, op, dependencies, frame.effect);
    for (Value output : op->getResults())
      if (!bind(frame.values, output,
                node(Kind::Source, op, {id}, absent, output)))
        return false;
    return id != absent;
  }
  bool observe(const Rule *selected, Operation *op, ArrayRef<Id> payload,
               Frame &frame, unsigned level) {
    SmallVector<Id> args;
    if (!stateArguments(frame, args) || !charge(payload.size()))
      return false;
    append_range(args, payload);
    if (!plan && policy.suite.empty()) {
      frame.effect = node(Kind::Source, op, payload, frame.effect);
      return frame.effect != absent;
    }
    if (selected)
      frame.state = invoke(selected, Kind::Observation, op, args, frame, level);
    else if (!plan || plan->nativeBase) {
      frame.state = node(Kind::Observation, op, args, frame.effect);
      frame.effect = frame.state;
    } else
      return fail("coverage");
    return frame.state != absent;
  }
  bool message(pir::ExchangeOp first, Frame &frame, StringRef prefix,
               Operation *&last, unsigned level) {
    auto site = occurrence(prefix, first.getSite());
    auto *encoded = rule(Rule::Kind::Encode, site);
    auto *observed = rule(Rule::Kind::Message, site);
    auto *group = encoded ? encoded : observed;
    SmallVector<pir::ExchangeOp> leaves;
    SmallVector<Operation *> calculations;
    if (!charge())
      return false;
    leaves.push_back(first);
    last = first;
    if (group) {
      if (group->sites.empty() || group->sites.front() != site)
        return fail("group");
      Operation *cursor = first->getNextNode();
      for (StringRef expected :
           ArrayRef<std::string>(group->sites).drop_front()) {
        while (cursor && !isa<pir::ExchangeOp>(cursor)) {
          if (!charge())
            return false;
          if ((!mathematical::isTotal(cursor) &&
               !isa<pir::RestrictRolesOp>(cursor)) ||
              cursor->getNumRegions())
            return fail(
                "order"); // preserves every prior failing/effectful prefix
          calculations.push_back(cursor);
          cursor = cursor->getNextNode();
        }
        auto leaf = dyn_cast_or_null<pir::ExchangeOp>(cursor);
        if (!leaf || occurrence(prefix, leaf.getSite()) != expected ||
            leaf.getSender() != first.getSender() ||
            leaf.getReceiver() != first.getReceiver())
          return fail("group");
        if (!charge())
          return false;
        leaves.push_back(leaf);
        last = leaf;
        cursor = cursor->getNextNode();
      }
    }
    bool writing = (validator ? policy.validator : policy.producer) ==
                   mappedRole(first.getSender());
    if (mappedRole(first.getSender()) == policy.validator &&
        mappedRole(first.getReceiver()) == policy.producer) {
      // The validator's actual SSA calculation is retained in full, including
      // every callback input and prior stop. The producer edge is an explicit
      // pending request obligation, NOT a claim that transport still exists or
      // that a same-typed public value equals the original request.
      if (leaves.size() != 1 || encoded)
        return fail("group");
      SmallVector<Id> payload;
      if (validator) {
        if (!inputs(frame.values, first.getInput(), payload) || !charge())
          return false;
        auto [found, inserted] = reverseRequests.try_emplace(
            site, Request{first, payload.front(), absent});
        if (!inserted)
          return fail("coverage");
        if (!bind(frame.values, first.getOutput(), payload.front()))
          return false;
      } else {
        auto found = reverseRequests.find(site);
        if (found == reverseRequests.end() || found->second.exchange != first)
          return fail("replica");
        Id replica =
            node(Kind::Replica, first, {found->second.validatorPayload},
                 frame.effect, first.getOutput(), frame.conditional);
        if (!bind(frame.values, first.getOutput(), replica) || !charge())
          return false;
        found->second.producerPayload = replica;
        frame.effect = replica;
        payload.push_back(replica);
      }
      return observe(observed, first, payload, frame, level);
    }
    if (mappedRole(first.getSender()) != policy.producer ||
        mappedRole(first.getReceiver()) != policy.validator)
      return fail("source");
    if (writing) {
      // Preserve availability through actual send aliases before encoding all
      // leaves. These aliases come from the Exchange operands, never types.
      auto *cursor = first.getOperation();
      while (true) {
        if (auto leaf = dyn_cast<pir::ExchangeOp>(cursor)) {
          SmallVector<Id> value;
          if (!inputs(frame.values, leaf.getInput(), value) ||
              !bind(frame.values, leaf.getOutput(), value.front()))
            return false;
        } else if (!pure(cursor, frame))
          return false;
        if (cursor == last)
          break;
        cursor = cursor->getNextNode();
      }
    }
    SmallVector<Id> payload, chunks;
    if (writing)
      for (auto leaf : leaves)
        if (!inputs(frame.values, leaf.getInput(), payload))
          return false;
    if (plan && plan->codec) {
      if (!encoded)
        return fail("coverage");
      auto *receive = rule(Rule::Kind::Receive, site);
      auto *decode = rule(Rule::Kind::Decode, site);
      auto *wire = rule(Rule::Kind::Wire, site);
      if (!receive || !decode || !charge(encoded->sites.size()) ||
          !charge(encoded->chunks.size()))
        return fail("coverage");
      if (receive->sites != encoded->sites || decode->sites != encoded->sites ||
          (wire && wire->sites != encoded->sites) ||
          receive->chunks != encoded->chunks ||
          decode->chunks != encoded->chunks)
        return fail("group");
      if (!charge(plan->codec->record.size()))
        return false;
      SmallVector<Id> args(plan->codec->record.size(), frame.record);
      if (writing) {
        if (!charge(payload.size()))
          return false;
        append_range(args, payload);
        frame.record = invoke(encoded, Kind::Encode, last, args, frame, level);
        if (!charge(encoded->chunks.size()))
          return false;
        chunks.append(encoded->chunks.size(), frame.record);
      } else {
        if (!charge())
          return false;
        args.push_back(frame.proof);
        frame.record =
            invoke(receive, Kind::Receive, first, args, frame, level);
        // Each chunk depends on BOTH endpoints returned by receive and on the
        // ORIGINAL proof. Aggregating endpoints is conservative, not equality.
        for (Type type : encoded->chunks) {
          (void)type;
          if (!charge())
            return false;
          auto range = node(Kind::Range, first, {frame.record, frame.proof},
                            frame.effect);
          frame.effect = range;
          chunks.push_back(range);
        }
      }
      if (wire) {
        args.clear();
        if (!stateArguments(frame, args) || !charge(chunks.size()))
          return false;
        append_range(args, chunks);
        frame.state =
            invoke(wire, Kind::RawObservation, first, args, frame, level);
      }
      if (!writing) {
        auto decoded =
            invoke(decode, Kind::Decode, first, chunks, frame, level);
        for (auto leaf : leaves) {
          auto output =
              node(Kind::Decode, leaf, {decoded}, absent, leaf.getOutput());
          if (!bind(frame.values, leaf.getOutput(), output) || !charge())
            return false;
          payload.push_back(output);
        }
      }
    } else if (!writing) {
      // Typed transport supplies only the actual receive result, not equality
      // with the producer's SSA component.
      for (auto leaf : leaves) {
        auto received = node(Kind::Receive, leaf, {frame.proof}, frame.effect,
                             leaf.getOutput());
        frame.effect = received;
        if (!bind(frame.values, leaf.getOutput(), received) || !charge())
          return false;
        payload.push_back(received);
      }
    }
    // Message rules may subdivide a codec group. Read every handler in the
    // selected order, requiring an exact contiguous leaf association.
    unsigned offset = 0;
    while (offset < leaves.size()) {
      auto *observer = rule(Rule::Kind::Message,
                            occurrence(prefix, leaves[offset].getSite()));
      unsigned count = observer ? observer->sites.size() : 1;
      if (!count || count > leaves.size() - offset)
        return fail("group");
      for (unsigned i = 0; i < count; ++i)
        if (observer && observer->sites[i] !=
                            occurrence(prefix, leaves[offset + i].getSite()))
          return fail("group");
      if (!observe(observer, leaves[offset + count - 1],
                   ArrayRef<Id>(payload).slice(offset, count), frame, level))
        return false;
      offset += count;
    }
    // Validator calculations crossed by the contiguous codec sequence are
    // total and now use actual decoded leaves. No opaque call/guard crosses.
    if (!writing)
      for (auto *op : calculations)
        if (!pure(op, frame))
          return false;
    return problem.empty();
  }
  bool selectedQuery(pir::QueryOp query, Frame &frame) {
    auto found = frame.values.find(query.getReference());
    if (found == frame.values.end())
      return false;
    Id id = found->second;
    while (id != absent && nodes[id].kind == Kind::Capture &&
           nodes[id].predecessors.size() == 1) {
      if (!charge())
        return false;
      id = nodes[id].predecessors.front();
    }
    return selectedServices.contains(id);
  }
  struct QueryFrontier {
    Operation *operation = nullptr;
    Value input;
    std::string site;
    StringRef sender, receiver;
  };
  // Read the first expanded event without materializing or inventing a value
  // relation. Only actual application argument/return substitutions forward
  // SSA identity; pure calculations keep their own distinct source values.
  bool queryFrontier(Operation *cursor, StringRef prefix,
                     const StringMap<StringRef> &roleMap,
                     llvm::DenseMap<Value, Value> &substitutions,
                     SmallVectorImpl<Value> &returned, QueryFrontier &frontier,
                     llvm::DenseSet<Operation *> &frontierActive,
                     unsigned level) {
    if (!depth(level))
      return false;
    auto actual = [&](Value value) {
      while (value) {
        if (!charge())
          return Value();
        auto found = substitutions.find(value);
        if (found != substitutions.end()) {
          value = found->second;
          continue;
        }
        if (auto restriction = value.getDefiningOp<pir::RestrictRolesOp>()) {
          bool available = false;
          for (auto role : restriction.getRoles()) {
            auto name = cast<StringAttr>(role).getValue();
            if (!charge(name.size()) || !charge())
              return Value();
            auto mapped = roleMap.find(name);
            available |=
                mapped != roleMap.end() && mapped->second == policy.validator;
          }
          if (!available)
            return value;
          value = restriction.getInput();
          continue;
        }
        if (auto assembly = value.getDefiningOp<pir::AssembleRolesOp>()) {
          Value component;
          for (auto [role, input] :
               zip(assembly.getRoles(), assembly.getInputs())) {
            auto name = cast<StringAttr>(role).getValue();
            if (!charge(name.size()) || !charge())
              return Value();
            auto mapped = roleMap.find(name);
            if (mapped != roleMap.end() && mapped->second == policy.validator)
              component = input;
          }
          if (!component)
            return value;
          value = component;
          continue;
        }
        return value;
      }
      return Value();
    };
    for (; cursor; cursor = cursor->getNextNode()) {
      if (!charge())
        return false;
      if (auto apply = dyn_cast<pir::ApplyOp>(cursor)) {
        if (!charge(apply.getCallee().size()) || !charge())
          return false;
        auto callee = dyn_cast_or_null<pir::MathematicalOp>(
            symbols.lookup(apply.getCallee()));
        if (!callee || !hasSingleElement(callee.getBody()) ||
            callee.getBody().front().getNumArguments() !=
                apply.getNumOperands() ||
            callee.getRoles().size() != apply.getRoles().size() ||
            !frontierActive.insert(callee).second)
          return fail("closure");
        llvm::DenseMap<Value, Value> child;
        for (auto [formal, input] :
             zip(callee.getBody().front().getArguments(), apply.getInputs())) {
          Value value = actual(input);
          if (!value || !charge())
            return false;
          child[formal] = value;
        }
        StringMap<StringRef> childRoles;
        for (auto [formal, input] : zip(callee.getRoles(), apply.getRoles())) {
          auto name = cast<StringAttr>(input).getValue();
          auto local = cast<StringAttr>(formal).getValue();
          if (!charge(name.size()) || !charge(local.size()) || !charge(2))
            return false;
          auto found = roleMap.find(name);
          if (found == roleMap.end())
            return fail("source");
          childRoles[local] = found->second;
        }
        SmallVector<Value> outputs;
        bool ok =
            queryFrontier(&callee.getBody().front().front(),
                          occurrence(prefix, apply.getSite()), childRoles,
                          child, outputs, frontier, frontierActive, level + 1);
        frontierActive.erase(callee);
        if (!ok || frontier.operation)
          return ok;
        if (outputs.size() != apply.getNumResults())
          return fail("source");
        for (auto [result, value] : zip(apply.getResults(), outputs)) {
          if (!charge())
            return false;
          substitutions[result] = value;
        }
      } else if (isa<pir::MathematicalReturnOp>(cursor)) {
        for (Value operand : cursor->getOperands()) {
          Value value = actual(operand);
          if (!value || !charge())
            return false;
          returned.push_back(value);
        }
        return problem.empty();
      } else if (isa<pir::QueryOp, pir::ExchangeOp, pir::RepeatOp,
                     pir::BranchOp, pir::ConstructionStartOp, pir::FinishIfOp>(
                     cursor)) {
        frontier.operation = cursor;
        if (auto exchange = dyn_cast<pir::ExchangeOp>(cursor)) {
          frontier.input = actual(exchange.getInput());
          frontier.site = occurrence(prefix, exchange.getSite());
          if (!charge(exchange.getSender().size()) ||
              !charge(exchange.getReceiver().size()) || !charge(2))
            return false;
          auto sender = roleMap.find(exchange.getSender());
          auto receiver = roleMap.find(exchange.getReceiver());
          if (sender == roleMap.end() || receiver == roleMap.end())
            return fail("source");
          frontier.sender = sender->second;
          frontier.receiver = receiver->second;
        }
        return problem.empty();
      }
    }
    return problem.empty();
  }
  bool query(pir::QueryOp query, Frame &frame, StringRef prefix,
             unsigned level) {
    auto site = occurrence(prefix, query.getSite());
    auto *selected = rule(Rule::Kind::Query, site);
    bool replaced =
        selected || selectedQuery(query, frame) || querySelections.count(site);
    if (replaced) {
      QueryFrontier frontier;
      llvm::DenseMap<Value, Value> substitutions;
      SmallVector<Value> returned;
      llvm::DenseSet<Operation *> frontierActive;
      for (Operation *operation : active) {
        if (!charge())
          return false;
        frontierActive.insert(operation);
      }
      if (!queryFrontier(query->getNextNode(), prefix, roles, substitutions,
                         returned, frontier, frontierActive, level))
        return false;
      Operation *boundary = query->getParentOp();
      // A selected query can return through several actual applications before
      // its delivery. Preserve those exact return substitutions and caller role
      // maps; a selected-control yield remains a separate prefix boundary.
      for (const auto &caller : reverse(queryContinuations)) {
        if (frontier.operation || !isa<pir::MathematicalOp>(boundary))
          break;
        auto apply = caller.application;
        if (returned.size() != apply.getNumResults())
          return fail("source");
        for (auto [result, value] : zip(apply.getResults(), returned)) {
          if (!charge())
            return false;
          substitutions[result] = value;
        }
        returned.clear();
        if (!charge(apply.getCallee().size()) || !charge())
          return false;
        frontierActive.erase(symbols.lookup(apply.getCallee()));
        if (!queryFrontier(apply->getNextNode(), caller.prefix, *caller.roles,
                           substitutions, returned, frontier, frontierActive,
                           caller.level))
          return false;
        boundary = apply->getParentOp();
      }
      auto *next = frontier.operation;
      if (isa_and_nonnull<pir::RepeatOp>(next))
        return refuse("native-proof-loop-prefix");
      if (isa_and_nonnull<pir::BranchOp>(next))
        return refuse("native-proof-branch-prefix");
      if (isa_and_nonnull<pir::QueryOp, pir::ConstructionStartOp,
                          pir::FinishIfOp>(next))
        return refuse("native-proof-prefix");
      if (!next)
        return refuse(isa<pir::BranchOp>(boundary)
                          ? "native-proof-branch-prefix"
                          : "native-proof-draw-selection");
      if (frontier.sender == policy.producer)
        return refuse("native-proof-prefix");
      if (query.getNumResults() != 1 || frontier.input != query.getResult(0) ||
          frontier.sender != policy.validator ||
          frontier.receiver != policy.producer)
        return refuse("native-proof-reverse-message");
      if (!charge(site.size()) || !charge())
        return false;
      selectedQueries[frontier.site] = {selected, query, site};
      querySelections[site] = selected;
      if (!validator)
        return true;
      SmallVector<Id> actualInputs;
      if (!inputs(frame.values, query.getInputs(), actualInputs) ||
          !charge(site.size()) || !charge(actualInputs.size()) || !charge())
        return false;
      originalQueryInputs[site] = {query, actualInputs};
      SmallVector<Id> args;
      if (!stateArguments(frame, args) || !charge(actualInputs.size()))
        return false;
      append_range(args, actualInputs);
      if (selected)
        frame.state = invoke(selected, Kind::Query, query, args, frame, level);
      else if (!plan || plan->nativeBase) {
        frame.state = node(Kind::Query, query, args, frame.effect);
        frame.effect = frame.state;
      } else
        return fail("coverage");
      for (Value output : query.getResults())
        if (!bind(frame.values, output,
                  node(Kind::Query, query, {frame.state}, absent, output)))
          return false;
      return true;
    }
    if (mappedRole(query.getOwner()) !=
        (validator ? policy.validator : policy.producer))
      return true;
    SmallVector<Id> args;
    if (!inputs(frame.values, query->getOperands(), args))
      return false;
    frame.effect = node(Kind::Source, query, args, frame.effect);
    for (Value result : query.getResults())
      if (!bind(frame.values, result,
                node(Kind::Source, query, {frame.effect}, absent, result)))
        return false;
    return true;
  }
  bool omitted(pir::ExchangeOp exchange, Frame &frame, StringRef prefix,
               unsigned level) {
    auto found = selectedQueries.find(occurrence(prefix, exchange.getSite()));
    if (found == selectedQueries.end() || !found->second.query)
      return fail("replica");
    auto query = found->second.query;
    auto *selected = found->second.rule;
    if (!validator) {
      SmallVector<Id> args;
      if (!stateArguments(frame, args))
        return false;
      if (!charge(found->second.queryOccurrence.size()))
        return false;
      auto sourceInputs =
          originalQueryInputs.find(found->second.queryOccurrence);
      if (sourceInputs == originalQueryInputs.end() ||
          sourceInputs->second.operation != query ||
          sourceInputs->second.inputs.size() != query.getInputs().size())
        return fail("dependency");
      for (auto [i, input] : enumerate(query.getInputs())) {
        if (!charge())
          return false;
        auto found = frame.values.find(input);
        // Native query admission independently requires the actual fixed
        // bound/count. Retain that original calculation even if source role
        // restriction omits its pure constant from the producer projection.
        args.push_back(found == frame.values.end()
                           ? sourceInputs->second.inputs[i]
                           : found->second);
      }
      if (selected)
        frame.state = invoke(selected, Kind::Query, query, args, frame, level);
      else {
        frame.state = node(Kind::Query, query, args, frame.effect);
        frame.effect = frame.state;
      }
      if (!bind(frame.values, exchange.getOutput(),
                node(Kind::Omission, exchange, {frame.state}, absent,
                     exchange.getOutput())))
        return false;
    } else {
      SmallVector<Id> value;
      if (!inputs(frame.values, exchange.getInput(), value) ||
          !bind(frame.values, exchange.getOutput(), value.front()))
        return false;
    }
    frame.effect = node(Kind::Omission, exchange, {}, frame.effect);
    SmallVector<Id> payload;
    if (!inputs(frame.values, exchange.getOutput(), payload))
      return false;
    return observe(
        rule(Rule::Kind::Message, occurrence(prefix, exchange.getSite())),
        exchange, payload, frame, level);
  }
  bool block(Block &body, Frame &frame, StringRef prefix,
             SmallVectorImpl<Id> &yielded, unsigned level, bool root = false) {
    if (!depth(level) || !charge(body.getNumArguments()))
      return false;
    for (auto cursor = body.begin(); cursor != body.end(); ++cursor) {
      Operation *op = &*cursor;
      if (!charge())
        return false;
      if (auto exchange = dyn_cast<pir::ExchangeOp>(op)) {
        if (selectedQueries.count(occurrence(prefix, exchange.getSite()))) {
          if (!omitted(exchange, frame, prefix, level + 1))
            return false;
        } else {
          Operation *last = op;
          if (!message(exchange, frame, prefix, last, level + 1))
            return false;
          cursor = last->getIterator();
        }
      } else if (auto draw = dyn_cast<pir::QueryOp>(op)) {
        if (!query(draw, frame, prefix, level + 1))
          return false;
      } else if (auto call = dyn_cast<pir::LocalCallOp>(op)) {
        if (mappedRole(call.getRole()) !=
            (validator ? policy.validator : policy.producer))
          continue;
        SmallVector<Id> args;
        if (!inputs(frame.values, call.getInputs(), args))
          return false;
        auto id = invoke(call.getCalleeAttr(), Kind::Callback, op, args, frame,
                         level + 1);
        for (Value value : call.getResults())
          if (!bind(frame.values, value,
                    node(Kind::Source, op, {id}, absent, value)))
            return false;
      } else if (auto call = dyn_cast<func::CallOp>(op)) {
        SmallVector<Id> args;
        if (!inputs(frame.values, call.getOperands(), args, false)) {
          if (!problem.empty())
            return false;
          continue;
        }
        auto id = mathematics(function(call.getCalleeAttr()), op, args,
                              frame.effect, frame.conditional, level + 1);
        for (Value output : call.getResults())
          if (!bind(frame.values, output,
                    node(Kind::Source, op, {id}, absent, output)))
            return false;
      } else if (auto guard = dyn_cast<pir::GuardOp>(op)) {
        if (mappedRole(guard.getOwner()) !=
            (validator ? policy.validator : policy.producer))
          continue;
        SmallVector<Id> args;
        if (!inputs(frame.values, guard.getCondition(), args))
          return false;
        frame.effect = node(Kind::Source, op, args, frame.effect);
      } else if (isa<pir::BranchOp, data::BranchOp, pir::RepeatOp>(op)) {
        bool loop = isa<pir::RepeatOp>(op);
        if (!loop && op->getNumRegions() > selectedRegionArmLimit)
          return fail("capacity");
        if (auto roles = op->getAttrOfType<ArrayAttr>("roles");
            roles && !owns(roles))
          continue;
        SmallVector<Id> args, available;
        for (Value operand : op->getOperands()) {
          if (!charge(2))
            return false;
          auto found = frame.values.find(operand);
          args.push_back(found == frame.values.end() ? absent : found->second);
          if (found != frame.values.end())
            available.push_back(found->second);
        }
        if (args.empty() || args.front() == absent) {
          // Total selected Math is projected only at roles that possess its
          // actual selector. Other roles may not execute this expression.
          if (isa<data::BranchOp>(op))
            continue;
          return fail("dependency");
        }
        Id boundary = node(loop ? Kind::Iteration : Kind::Capture, op,
                           available, frame.effect, {}, true);
        SmallVector<Id> endings, states, records;
        SmallVector<SmallVector<Id>> armOutputs;
        if (loop) {
          if (!charge(3) || !charge(args.size()))
            return false;
          endings.push_back(boundary);
          states.push_back(frame.state);
          if (frame.record != absent)
            records.push_back(frame.record);
          // The initial carried values are joined separately with each yield.
          // No body execution or finalizer is implied by this zero-trip edge.
        }
        for (Region &region : op->getRegions()) {
          if (!hasSingleElement(region))
            return fail("profile");
          Frame child;
          child.effect = boundary;
          child.state =
              node(Kind::Capture, op, {frame.state}, boundary, {}, true);
          child.record =
              frame.record == absent
                  ? absent
                  : node(Kind::Capture, op, {frame.record}, boundary, {}, true);
          child.proof = frame.proof;
          child.conditional = true;
          Block &arm = region.front();
          for (auto arg : arm.getArguments()) {
            Id input = boundary;
            if (loop) {
              // Protocol repeat: coordinate then actual carried/capture slots.
              if (arg.getArgNumber()) {
                if (arg.getArgNumber() >= args.size())
                  return fail("dependency");
                input = args[arg.getArgNumber()];
                if (input == absent)
                  continue; // other participant's capture
              }
            } else {
              // selectedCapture reads the selected payload shape. Its
              // temporary vector is bounded by this actual arm's formals.
              if (!charge(arm.getNumArguments()))
                return false;
              if (Value capture = selectedCapture(arg)) {
                auto found = frame.values.find(capture);
                if (found == frame.values.end())
                  continue;
                input = found->second;
              }
            }
            // Payload formals depend on the selected actual selector; they
            // never alias an arbitrary same-typed capture.
            if (!bind(child.values, arg,
                      node(Kind::Capture, op, {input}, absent, arg, true)))
              return false;
          }
          SmallVector<Id> outputs;
          if (!block(arm, child, prefix, outputs, level + 1))
            return false;
          if (!charge(3) || !charge(outputs.size()))
            return false;
          endings.push_back(child.effect);
          states.push_back(child.state);
          if (child.record != absent)
            records.push_back(child.record);
          if (!charge())
            return false;
          armOutputs.push_back(std::move(outputs));
        }
        frame.effect = node(loop ? Kind::Iteration : Kind::Join, op, endings,
                            boundary, {}, frame.conditional);
        frame.state = node(Kind::Join, op, states, frame.effect);
        if (frame.record != absent)
          frame.record = node(Kind::Join, op, records, frame.effect);
        for (auto [index, output] : enumerate(op->getResults())) {
          if (!charge())
            return false;
          auto ownership = op->getAttrOfType<ArrayAttr>(loop ? "carried_roles"
                                                             : "output_roles");
          if (ownership && !owns(cast<ArrayAttr>(ownership[index])))
            continue;
          SmallVector<Id> joined;
          bool availableOutput = true;
          if (loop) {
            if (index + 1 >= args.size())
              return fail("dependency");
            availableOutput = args[index + 1] != absent;
            if (!charge())
              return false;
            joined.push_back(args[index + 1]);
          }
          for (const auto &arm : armOutputs) {
            if (!charge())
              return false;
            if (index >= arm.size())
              return fail("dependency");
            availableOutput &= arm[index] != absent;
            joined.push_back(arm[index]);
          }
          if (availableOutput &&
              !bind(frame.values, output,
                    node(Kind::Join, op, joined, frame.effect, output)))
            return false;
        }
      } else if (auto start = dyn_cast<pir::ConstructionStartOp>(op)) {
        const protocol::ConstructionInvocation *selected = nullptr;
        auto site = occurrence(prefix, start.getSite());
        for (const auto &invocation : invocations) {
          if (!charge(invocation.site.size()))
            return false;
          if (invocation.site == site) {
            if (selected)
              return fail("coverage");
            selected = &invocation;
          }
        }
        SmallVector<Id> args;
        if (!selected || !stateArguments(frame, args) ||
            !inputs(frame.values, start.getInputs(), args))
          return fail("coverage");
        frame.state =
            invoke(selected->handler, Kind::Start, op, args, frame, level + 1);
        if (frame.state == absent || !charge())
          return false;
        usedStarts.insert(selected);
      } else if (auto apply = dyn_cast<pir::ApplyOp>(op)) {
        if (!charge(apply.getCallee().size()))
          return false;
        auto callee = dyn_cast_or_null<pir::MathematicalOp>(
            symbols.lookup(apply.getCallee()));
        if (!callee || !hasSingleElement(callee.getBody()))
          return fail("source");
        // Role names are interpreted through the actual application map.
        // This maps ownership only; it establishes no value equality.
        if (apply.getRoles().size() != callee.getRoles().size())
          return fail("source");
        StringMap<StringRef> childRoles;
        for (auto [formal, actual] : zip(callee.getRoles(), apply.getRoles())) {
          auto name = cast<StringAttr>(formal).getValue();
          if (!charge(name.size()) || !charge())
            return false;
          childRoles[name] = mappedRole(cast<StringAttr>(actual).getValue());
        }
        if (!active.insert(callee).second)
          return fail("recursion");
        Frame child;
        child.effect = frame.effect;
        child.state = frame.state;
        child.record = frame.record;
        child.proof = frame.proof;
        child.conditional = frame.conditional;
        auto &calleeBody = callee.getBody().front();
        if (calleeBody.getNumArguments() != apply.getNumOperands())
          return fail("signature");
        for (auto [formal, actual] :
             zip(calleeBody.getArguments(), apply.getInputs())) {
          if (!charge())
            return false;
          auto found = frame.values.find(actual);
          if (found != frame.values.end() &&
              !bind(child.values, formal, found->second))
            return false;
        }
        auto path = occurrence(prefix, apply.getSite());
        for (const auto &start : invocations) {
          if (!charge(start.site.size()) || !charge())
            return false;
          if (start.site != path)
            continue;
          SmallVector<Id> args;
          if (!stateArguments(child, args) ||
              !selectedInputs(start.inputs, calleeBody, child, args))
            return false;
          child.state =
              invoke(start.handler, Kind::Start, op, args, child, level + 1);
          if (!charge())
            return false;
          usedStarts.insert(&start);
        }
        SmallVector<Id> result;
        auto outerRoles = std::move(roles);
        roles = std::move(childRoles);
        if (!charge(prefix.size()) || !charge())
          return false;
        queryContinuations.push_back({apply, prefix.str(), &outerRoles, level});
        if (!block(calleeBody, child, path, result, level + 1))
          return false;
        queryContinuations.pop_back();
        roles = std::move(outerRoles);
        active.erase(callee);
        frame.effect = child.effect;
        frame.state = child.state;
        frame.record = child.record;
        // All-input conservative join does not infer role equality.
        if (result.size() != apply.getNumResults())
          return fail("dependency");
        for (auto [i, output] : enumerate(apply.getResults()))
          if (result[i] != absent &&
              !bind(frame.values, output,
                    node(Kind::Join, op, {result[i]}, frame.effect, output)))
            return false;
      } else if (auto complete = dyn_cast<pir::FinishIfOp>(op)) {
        if (mappedRole(complete.getOwner()) !=
            (validator ? policy.validator : policy.producer))
          continue;
        SmallVector<Id> args;
        if (!inputs(frame.values, complete->getOperands(), args))
          return false;
        auto boundary =
            node(Kind::Completion, op, args, frame.effect, {}, true);
        Frame completed;
        if (!copyFrame(frame, completed))
          return false;
        completed.effect = boundary;
        if (!finish(op, completed, level + 1, true))
          return false;
        // Continuing execution takes the other edge, with the original Record
        // and state. No finalizer is inserted on that edge.
        frame.effect = node(Kind::Completion, op, {boundary}, absent, {}, true);
        for (Value output : op->getResults())
          if (!bind(
                  frame.values, output,
                  node(Kind::Completion, op, args, frame.effect, output, true)))
            return false;
      } else if (isa<pir::MathematicalReturnOp, pir::ProtocolYieldOp,
                     data::YieldOp>(op)) {
        // Role-local return ports may include values absent from this role.
        // Preserve dependencies of every actual available component.
        for (Value value : op->getOperands()) {
          if (!charge())
            return false;
          auto found = frame.values.find(value);
          if (!charge())
            return false;
          yielded.push_back(found == frame.values.end() ? absent
                                                        : found->second);
        }
        SmallVector<Id> available;
        for (Id value : yielded) {
          if (!charge())
            return false;
          if (value != absent)
            available.push_back(value);
        }
        frame.effect = node(Kind::Completion, op, available, frame.effect, {},
                            frame.conditional);
        if (root && !finish(op, frame, level + 1, false))
          return false;
        return frame.effect != absent;
      } else if (isa<pir::RestrictRolesOp, pir::AssembleRolesOp>(op)) {
        if (!pure(op, frame, level))
          return false;
      } else if (isa<pir::StatementOp>(op)) {
        // Authored relation assertions are checked by Protocol admission and
        // have no participant execution. Retain their role-local actual data
        // footprint without treating another role's component as available.
        SmallVector<Id> available;
        for (Value input : op->getOperands()) {
          if (!charge())
            return false;
          auto found = frame.values.find(input);
          if (found != frame.values.end()) {
            if (!charge())
              return false;
            available.push_back(found->second);
          }
        }
        if (node(Kind::Source, op, available, frame.effect) == absent)
          return false;
      } else if (op->getNumRegions() ||
                 (!mathematical::isTotal(op) && !finite::isComputation(op))) {
        return fail("profile");
      } else if (!pure(op, frame, level))
        return false;
    }
    return fail("source");
  }

  bool hasDeferredRealization(Operation *op, unsigned level, bool &found) {
    if (!depth(level) || !charge())
      return false;
    found |= mathematical::isLogicalOracleOperation(op);
    if (auto call = dyn_cast<pir::LocalCallOp>(op)) {
      if (!charge(call.getCallee().size()) || !charge())
        return false;
      Operation *target = symbols.lookup(call.getCallee());
      if (!target || !isa<func::FuncOp, poly::RealizeOp>(target))
        return fail("closure");
      found |= isa<poly::RealizeOp>(target);
    }
    if (auto call = dyn_cast<pir::ApplyOp>(op)) {
      if (!charge(call.getCallee().size()))
        return false;
      auto *callee = symbols.lookup(call.getCallee());
      if (!callee || !active.insert(callee).second)
        return fail("recursion");
      bool ok = hasDeferredRealization(callee, level + 1, found);
      active.erase(callee);
      if (!ok)
        return false;
    }
    // Match the structural preflight's semantic body depth. Visiting a
    // definition wrapper is not another nested control body; an actual call
    // above still consumes one level.
    unsigned nestedDepth =
        level + !isa<ModuleOp, func::FuncOp, pir::ProtocolModuleOp,
                     pir::MathematicalOp>(op);
    for (Region &region : op->getRegions())
      for (Block &body : region)
        for (Operation &child : body)
          if (!hasDeferredRealization(&child, nestedDepth, found))
            return false;
    return true;
  }
  // Logical stores and declarative polynomial execution do not exist yet.
  // Retain the actual original operand/control relation and recipe bodies as
  // explicit realization obligations. PreparedProtocol independently checks
  // polynomial recipe expansion; RealizedProtocol checks the Oracle edge.
  // resolveRealization then reads the actual joint relation before emission.
  Id logicalBlock(Block &body, Environment &env, Id prior, bool conditional,
                  unsigned level) {
    if (!depth(level) || !charge(body.getNumArguments()))
      return absent;
    Id last = prior;
    for (Operation &op : body) {
      if (!charge())
        return absent;
      SmallVector<Id> args;
      if (!inputs(env, op.getOperands(), args))
        return absent;
      if (auto call = dyn_cast<pir::LocalCallOp>(op)) {
        last = localCall(call, args, last, conditional, level + 1);
      } else if (auto call = dyn_cast<func::CallOp>(op)) {
        last = mathematics(function(call.getCalleeAttr()), &op, args, last,
                           conditional, level + 1);
      } else if (finite::isComputation(&op)) {
        last = finiteComputation(&op, op.getOperands(), args, last, conditional,
                                 level + 1);
      } else if (auto apply = dyn_cast<pir::ApplyOp>(op)) {
        if (!charge(apply.getCallee().size()))
          return absent;
        auto callee = dyn_cast_or_null<pir::MathematicalOp>(
            symbols.lookup(apply.getCallee()));
        if (!callee || !hasSingleElement(callee.getBody()) ||
            callee.getBody().front().getNumArguments() != args.size() ||
            !active.insert(callee).second) {
          fail("source");
          return absent;
        }
        Environment child;
        for (auto [formal, input] :
             zip(callee.getBody().front().getArguments(), args))
          if (!bind(
                  child, formal,
                  node(Kind::Capture, &op, {input}, last, formal, conditional)))
            return absent;
        last = logicalBlock(callee.getBody().front(), child, last, conditional,
                            level + 1);
        active.erase(callee);
      } else if (isa<pir::RepeatOp, pir::BranchOp, data::BranchOp>(op)) {
        bool repeat = isa<pir::RepeatOp>(op);
        if (args.empty() || op.getNumRegions() > selectedRegionArmLimit) {
          fail("capacity");
          return absent;
        }
        Id boundary = node(repeat ? Kind::Iteration : Kind::Capture, &op, args,
                           last, {}, conditional);
        SmallVector<Id> endings;
        if (repeat) {
          if (!charge())
            return absent;
          endings.push_back(boundary);
        }
        for (Region &region : op.getRegions()) {
          if (!hasSingleElement(region)) {
            fail("source");
            return absent;
          }
          Environment child;
          for (BlockArgument formal : region.front().getArguments()) {
            Id input = boundary;
            if (repeat && formal.getArgNumber()) {
              if (formal.getArgNumber() >= args.size()) {
                fail("dependency");
                return absent;
              }
              input = args[formal.getArgNumber()];
            } else if (!repeat) {
              if (!charge(region.front().getNumArguments()))
                return absent;
              if (Value capture = selectedCapture(formal)) {
                auto found = env.find(capture);
                if (found == env.end()) {
                  fail("dependency");
                  return absent;
                }
                input = found->second;
              } else {
                input = args.front();
              }
            }
            if (!bind(
                    child, formal,
                    node(Kind::Capture, &op, {input}, boundary, formal, true)))
              return absent;
          }
          Id end =
              logicalBlock(region.front(), child, boundary, true, level + 1);
          if (end == absent || !charge())
            return absent;
          endings.push_back(end);
        }
        last = node(repeat ? Kind::Iteration : Kind::Join, &op, endings,
                    boundary, {}, conditional);
      } else if (mathematical::isLogicalOracleOperation(&op)) {
        last = node(Kind::Realization, &op, args, last, {}, conditional);
      } else if (op.getNumRegions() ||
                 (!mathematical::isTotal(&op) &&
                  !isa<pir::ExchangeOp, pir::QueryOp, pir::GuardOp,
                       pir::FinishIfOp, pir::RestrictRolesOp,
                       pir::AssembleRolesOp, pir::StatementOp,
                       pir::MathematicalReturnOp, pir::ProtocolYieldOp,
                       data::YieldOp>(op))) {
        fail("profile");
        return absent;
      } else {
        last = node(Kind::Source, &op, args, last, {}, conditional);
      }
      if (last == absent)
        return absent;
      for (Value result : op.getResults())
        if (!bind(env, result,
                  node(Kind::Source, &op, {last}, absent, result, conditional)))
          return absent;
    }
    return last;
  }

public:
  SmallVector<ConstructionDependency> nodes;
  bool deferred = false;
  Reader(ModuleOp source, pir::ProtocolModuleOp module,
         pir::MathematicalOp entry,
         const protocol::SourceExecutionClosure &execution,
         const NativeProofPolicy &policy,
         const protocol::ConstructionPlan *plan,
         ArrayRef<protocol::ConstructionInvocation> invocations,
         uint64_t budget, bool allowLogical = true)
      : source(source), module(module), entry(entry), execution(execution),
        policy(policy), plan(plan), invocations(invocations), remaining(budget),
        allowLogical(allowLogical) {}
  Error run() {
    auto result = [&]() -> bool {
      if (!charge(policy.entry.size()) || !charge(policy.producer.size()) ||
          !charge(policy.validator.size()) || !charge(policy.suite.size()))
        return false;
      if (!source || !module || module->getParentOp() != source || !entry ||
          entry->getParentOp() != module ||
          module.getProfile() != pir::Profile::Protocol ||
          !hasSingleElement(entry.getBody()) ||
          entry.getSymName() != policy.entry)
        return fail("source");
      if (!tree(source, 0))
        return false;
      for (Operation &op : module.getBody().front()) {
        if (!charge())
          return false;
        if (auto name = op.getAttrOfType<StringAttr>(
                SymbolTable::getSymbolAttrName())) {
          if (!charge(name.size()) || !charge())
            return false;
          symbols[name.getValue()] = &op;
        }
      }
      // Borrowed closure setup is included, including dormant definitions.
      // No copy or unbudgeted readSourceExecutionClosure is hidden here.
      for (const auto &[name, body] : execution.bodies) {
        if (!charge(name.size()) || !charge())
          return false;
        for (const auto &step : body) {
          if (!charge() || !charge(step.inputs.size()) ||
              !charge(step.outputs.size()) || !charge(step.regions.size()))
            return false;
          if (!sourceOperations.contains(step.operation))
            return fail("closure");
        }
      }
      for (Operation *op : execution.computations)
        if (!charge() || !sourceOperations.contains(op))
          return fail("closure");
      if (plan) {
        if (!charge(plan->suite.size()) || !charge(plan->services.size()) ||
            !charge(policy.services.size()))
          return false;
        if (!plan->target || plan->target.getValue() != policy.entry ||
            plan->suite != policy.suite ||
            !llvm::equal(plan->services, policy.services) ||
            bool(plan->codec) !=
                (policy.format == protocol::ProofFormat::RawBytes))
          return fail("source");
        for (const auto &r : plan->rules)
          for (const auto &site : r.sites) {
            if (!charge(site.size()) || !charge())
              return false;
            if (!rules.emplace(std::make_pair(r.kind, site), &r).second)
              return fail("coverage");
          }
      }
      if (!signatures())
        return false;
      for (Attribute role : entry.getRoles()) {
        auto name = cast<StringAttr>(role).getValue();
        if (!charge(name.size()) || !charge())
          return false;
        roles[name] = name;
      }
      if (!hasDeferredRealization(entry, 0, deferred))
        return false;
      if (deferred) {
        if (!allowLogical)
          return fail("profile");
        Environment env;
        Id root = node(Kind::Root, entry);
        for (BlockArgument argument : entry.getBody().front().getArguments())
          if (!bind(env, argument,
                    node(Kind::Input, entry, {}, root, argument)))
            return false;
        Id end = logicalBlock(entry.getBody().front(), env, root, false, 0);
        // This is deliberately incomplete. No handler, generated store or
        // communication is authorized until the checked realization and the
        // subsequent complete joint read discharge this boundary.
        return end != absent && charge() && problem.empty();
      }
      // Validator first also identifies actual selected SSA query/delivery
      // pairs for the producer, whose original ingress omits that service.
      for (bool role : {true, false}) {
        validator = role;
        Frame frame;
        Block &body = entry.getBody().front();
        for (auto arg : body.getArguments()) {
          if (!charge())
            return false;
          if (!owns(cast<ArrayAttr>(entry.getInputRoles()[arg.getArgNumber()])))
            continue;
          auto id = node(Kind::Input, entry, {}, absent, arg);
          if (!bind(frame.values, arg, id))
            return false;
          for (unsigned port : policy.services) {
            if (!charge())
              return false;
            if (port == arg.getArgNumber())
              selectedServices.insert(id);
          }
        }
        frame.effect = node(Kind::Root, entry);
        frame.state = frame.effect;
        if (validator)
          frame.proof = node(Kind::Input, entry);
        if (plan) {
          if (plan->root == protocol::ConstructionPlan::Root::Local)
            frame.state =
                invoke(plan->initializer, Kind::Root, entry, {}, frame, 0);
          for (const auto &r : plan->rules) {
            if (!charge())
              return false;
            if (r.kind != Rule::Kind::Start)
              continue;
            SmallVector<Id> args;
            if (!stateArguments(frame, args) ||
                !selectedInputs(r.inputs, body, frame, args))
              return false;
            frame.state = invoke(&r, Kind::Start, entry, args, frame, 0);
          }
          if (plan->codec) {
            SmallVector<Id> args;
            if (!selectedInputs(plan->codec->inputs, body, frame, args))
              return false;
            frame.record =
                invoke(plan->codec->initialize, Kind::RecordInitialization,
                       entry, args, frame, 0);
          }
        }
        SmallVector<Id> returned;
        if (!block(body, frame, {}, returned, 0, true))
          return false;
      }
      if (plan)
        for (const auto &r : plan->rules) {
          if (!charge())
            return false;
          if (!usedRules.contains(&r))
            return fail("coverage");
        }
      for (const auto &start : invocations) {
        if (!charge())
          return false;
        if (!usedStarts.contains(&start))
          return fail("coverage");
      }
      // The common relation is checked AGAIN as a complete result. These ranks
      // are static selected-order constraints, not a claim that dormant arms,
      // zero-trip bodies, stopped successors or untaken finalizers execute.
      for (auto [i, dependency] : enumerate(nodes)) {
        if (!charge())
          return false;
        for (Id predecessor : dependency.predecessors)
          if (!charge() || predecessor >= i)
            return fail("order");
      }
      for (const auto &item : reverseRequests)
        if (!charge() || !charge(item.getKey().size()) ||
            item.second.producerPayload == absent)
          return fail("replica");
      return charge() && problem.empty(); // allocation of the returned owner
    };
    if (!result())
      return error(problem.empty()
                       ? "native-construction-preparation-dependency"
                       : problem);
    return Error::success();
  }
  uint64_t workRemaining() const { return remaining; }
  bool exhausted() const {
    return problem == "native-construction-preparation-capacity";
  }
  const auto &requests() const { return reverseRequests; }
};
} // namespace

Error NativeConstructionPreparation::resolveRealization(
    ModuleOp realized, pir::MathematicalOp entry,
    const protocol::SourceExecutionClosure &execution,
    const NativeProofPolicy &policy, const protocol::ConstructionPlan *plan,
    ArrayRef<protocol::ConstructionInvocation> invocations) {
  if (storage->exhausted)
    return error("native-construction-preparation-capacity");
  if (!storage->deferred || !realized || realized == storage->source || !entry)
    return error("native-construction-preparation-source");
  auto module =
      realized.getBody()->empty()
          ? pir::ProtocolModuleOp()
          : dyn_cast<pir::ProtocolModuleOp>(realized.getBody()->front());
  Reader reader(realized, module, entry, execution, policy, plan, invocations,
                storage->remaining, false);
  auto result = reader.run();
  storage->used += storage->remaining - reader.workRemaining();
  storage->remaining = reader.workRemaining();
  storage->exhausted = reader.exhausted();
  if (result)
    return result;
  // Moving the rows is cheap, but reindexing and output growth still use the
  // same allowance. All references continue to borrow their actual owners.
  auto charge = [&](uint64_t count) {
    if (count > storage->remaining) {
      storage->exhausted = true;
      storage->used += storage->remaining;
      storage->remaining = 0;
      return false;
    }
    storage->remaining -= count;
    storage->used += count;
    return true;
  };
  for (const auto &node : reader.nodes)
    if (!charge(1) || !charge(node.predecessors.size()))
      return error("native-construction-preparation-capacity");
  for (const auto &item : reader.requests())
    if (!charge(1) || !charge(item.getKey().size()))
      return error("native-construction-preparation-capacity");
  if (reader.nodes.size() >= absent - storage->dependencies.size()) {
    storage->exhausted = true;
    return error("native-construction-preparation-capacity");
  }
  unsigned offset = storage->dependencies.size();
  for (auto &node : reader.nodes) {
    for (unsigned &predecessor : node.predecessors)
      predecessor += offset;
    storage->dependencies.push_back(std::move(node));
  }
  for (const auto &item : reader.requests())
    storage->requests.push_back({item.getKey().str(), item.second.exchange,
                                 offset + item.second.validatorPayload,
                                 offset + item.second.producerPayload});
  storage->realized = realized;
  storage->realizedExecution = &execution;
  storage->deferred = false;
  storage->complete = storage->requests.empty();
  return Error::success();
}

Error NativeConstructionPreparation::dischargeRequests(
    const NativeRequestPlan &requests) {
  storage->complete = false;
  if (storage->exhausted)
    return error("native-construction-preparation-capacity");
  bool capacity = false;
  auto charge = [&](uint64_t count = 1) {
    if (count > storage->remaining) {
      capacity = storage->exhausted = true;
      storage->used += storage->remaining;
      storage->remaining = 0;
      return false;
    }
    storage->remaining -= count;
    storage->used += count;
    return true;
  };
  if (storage->deferred)
    return error("native-construction-preparation-closure");
  auto producer = requests.producer;
  auto validator = requests.validator;
  if (!requests.root || !producer || !validator ||
      producer->getParentOp() != validator->getParentOp() ||
      !hasSingleElement(producer.getBody()) ||
      !hasSingleElement(validator.getBody()) ||
      requests.root->producer != &producer.getBody().front() ||
      requests.root->validator != &validator.getBody().front())
    return error("native-construction-preparation-replica");
  // Successful planning has already consumed each actual send input and proved
  // its relation, including count, capture, all-arm and recurrence obligations.
  // Read those actual associations, not a generated helper's name or type.
  struct ActualRequest {
    pir::EmitOp send;
    pir::AwaitOp receive;
    NativeRequestValue value;
  };
  StringMap<ActualRequest> actual;
  auto read = [&](auto &&self, const NativeRequestFrame &frame,
                  unsigned level) -> bool {
    if (level > 64) {
      capacity = storage->exhausted = true;
      return false;
    }
    if (!frame.producer || !frame.validator || !frame.finished || !charge())
      return false;
    for (Operation &op : *frame.producer) {
      if (!charge())
        return false;
      auto request = frame.requests.find(&op);
      if (request != frame.requests.end()) {
        auto receive = dyn_cast<pir::AwaitOp>(op);
        pir::EmitOp send;
        for (Operation &other : *frame.validator) {
          if (!charge())
            return false;
          auto candidate = dyn_cast<pir::EmitOp>(other);
          if (candidate && receive &&
              (!charge(candidate.getSite().size()) ||
               !charge(receive.getSite().size())))
            return false;
          if (candidate && receive &&
              candidate.getSite() == receive.getSite()) {
            if (send)
              return false;
            send = candidate;
          }
        }
        if (!send || receive.getPeer() != validator.getRole() ||
            send.getPeer() != producer.getRole() || !request->second.source ||
            !charge(receive.getSite().size()))
          return false;
        auto relation = frame.relations.find(send.getInput());
        if (relation == frame.relations.end() ||
            relation->second.source != request->second.source ||
            relation->second.ordinary != request->second.ordinary ||
            !actual
                 .try_emplace(receive.getSite(),
                              ActualRequest{send, receive, request->second})
                 .second)
          return false;
      }
      auto loop = frame.loops.find(&op);
      if (loop != frame.loops.end() &&
          !self(self, *loop->second->body, level + 1))
        return false;
      auto branch = frame.branches.find(&op);
      if (branch != frame.branches.end())
        for (const auto &arm : branch->second->arms)
          if (!self(self, *arm, level + 1))
            return false;
    }
    return true;
  };
  if (!read(read, *requests.root, 0))
    return error(capacity ? "native-construction-preparation-capacity"
                          : "native-construction-preparation-replica");
  if (actual.size() != storage->requests.size())
    return error("native-construction-preparation-coverage");
  SmallVector<Storage::RequestAssociation> associations;
  for (const auto &request : storage->requests) {
    if (!charge(2) || !charge(request.occurrence.size()))
      return error("native-construction-preparation-capacity");
    auto found = actual.find(request.occurrence);
    if (found == actual.end() || !request.exchange ||
        request.producerPayload >= storage->dependencies.size() ||
        request.validatorPayload >= request.producerPayload)
      return error("native-construction-preparation-replica");
    // The node already points to the FULL actual original computation. The
    // checked source/projection edge and this exact send-input relation close
    // its replica obligation. Neither an empty dependency nor a fabricated
    // operation tree is substituted for that computation.
    const auto &dependency = storage->dependencies[request.producerPayload];
    if (dependency.source != request.exchange ||
        dependency.kind != Kind::Replica || dependency.predecessors.empty() ||
        dependency.predecessors.front() != request.validatorPayload)
      return error("native-construction-preparation-replica");
    const auto &checked = found->second;
    associations.push_back({request.exchange, checked.send, checked.receive,
                            checked.value.source, checked.value.ordinary});
  }
  storage->requestAssociations = std::move(associations);
  storage->complete = true;
  return Error::success();
}

Expected<NativeConstructionPreparation> prepareNativeConstruction(
    ModuleOp source, pir::MathematicalOp entry,
    const protocol::SourceExecutionClosure &execution,
    const NativeProofPolicy &policy, const protocol::ConstructionPlan *plan,
    ArrayRef<protocol::ConstructionInvocation> invocations,
    uint64_t workBudget) {
  if (workBudget > 1000000)
    workBudget = 1000000;
  pir::ProtocolModuleOp module;
  if (source && !source.getBody()->empty())
    module = dyn_cast<pir::ProtocolModuleOp>(source.getBody()->front());
  Reader reader(source, module, entry, execution, policy, plan, invocations,
                workBudget);
  if (auto e = reader.run())
    return std::move(e);
  auto result = std::make_unique<NativeConstructionPreparation::Storage>();
  result->source = source;
  result->execution = &execution;
  result->dependencies = std::move(reader.nodes);
  for (const auto &item : reader.requests())
    result->requests.push_back({item.getKey().str(), item.second.exchange,
                                item.second.validatorPayload,
                                item.second.producerPayload});
  result->used = workBudget - reader.workRemaining();
  result->remaining = reader.workRemaining();
  result->deferred = reader.deferred;
  result->complete = !result->deferred && result->requests.empty();
  return NativeConstructionPreparation(std::move(result));
}
} // namespace zkc::detail
