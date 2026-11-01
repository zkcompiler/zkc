#include "zkc/Analysis/ProtocolObservations.h"
#include "zkc/Analysis/Interactions.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/ScopeExit.h"
#include <map>
#include <set>

using namespace mlir;
using namespace llvm;
namespace zkc {
namespace {
namespace pir = protocol_ir;
using Summary = ProtocolObservationSummary;
using Action = ProtocolObservationAction;
using Atom = ProtocolObservationAtom;
using Origin = ProtocolValueOrigin;
using Pending = ProtocolPendingTransfer;
using Dependencies = SmallVector<BitVector>;
constexpr unsigned maxPorts = 1024, maxDepth = 64, maxActions = 2048;
constexpr unsigned maxAtoms = 65536, maxQueries = 64;
struct ValueInfo {
  BitVector dependencies;
  Origin origin;
};
bool owns(ArrayAttr roles, StringRef role) {
  return any_of(roles, [&](Attribute a) {
    return cast<StringAttr>(a).getValue() == role;
  });
}
Origin formal(unsigned port) { return {Origin::Kind::Formal, port, {}}; }
Origin query(Operation *op) { return {Origin::Kind::Query, 0, {op}}; }
} // namespace

struct ProtocolObservationAnalysis::Impl {
  Operation *owner;
  InteractionAnalysis interactions;
  ExecutionObservationAnalysis numerical;
  SymbolTableCollection symbols;
  using Key = std::pair<Block *, std::string>;
  std::map<Key, Summary> summaries;
  std::set<Key> active;
  std::map<Operation *, mathematical::Availability> availability;
  std::set<Operation *> dataExchanges;
  unsigned actionCount = 0;
  std::string failureCode, failureDetail;

  explicit Impl(Operation *owner)
      : owner(owner), interactions(owner), numerical(owner) {}
  Impl(Operation *owner, ArrayRef<Operation *> selected) : Impl(owner) {
    for (Operation *op : selected)
      if (!op || !isa<pir::ExchangeOp>(op) ||
          op->getParentOfType<ModuleOp>() != owner ||
          !dataExchanges.insert(op).second)
        fail("protocol-observation-owner", "invalid data exchange selection");
  }
  bool fail(StringRef code, const Twine &detail) {
    if (failureCode.empty()) {
      failureCode = code.str();
      failureDetail = detail.str();
    }
    return false;
  }
  bool unsupported(const Twine &detail) {
    return fail("protocol-observation-unsupported", detail);
  }
  bool capacity(facts::Work &work, StringRef detail) {
    work.exhaust();
    return fail("protocol-observation-capacity", detail);
  }
  bool charge(facts::Work &work, uint64_t count = 1) {
    return work.charge(count) || capacity(work, "observation work exhausted");
  }
  bool capture(Error failure, facts::Work &work) {
    auto detail = toString(std::move(failure));
    return work.exhausted() ? capacity(work, detail) : unsupported(detail);
  }
  Error failure() { return error(failureCode, failureDetail); }
  bool unite(BitVector &to, const BitVector &from, facts::Work &work) {
    if (to.size() != from.size())
      return unsupported("inconsistent observation dependency width");
    if (!charge(work, 1 + (to.size() + 63) / 64))
      return false;
    to |= from;
    return true;
  }
  bool available(const mathematical::Availability &facts, Value value,
                 unsigned observer) {
    auto it = facts.values.find(value);
    return it != facts.values.end() && it->second.test(observer);
  }
  bool instantiate(const Origin &source, ArrayRef<Origin> arguments,
                   Operation *call, Origin &result, facts::Work &work) {
    if (!charge(work, source.path.size() + 1))
      return false;
    result = source;
    if (source.kind == Origin::Kind::Formal) {
      if (source.port >= arguments.size())
        return unsupported("origin formal is outside the call signature");
      if (!charge(work, arguments[source.port].path.size()))
        return false;
      result = arguments[source.port];
    } else if (source.kind == Origin::Kind::Query) {
      if (source.path.size() >= maxDepth)
        return capacity(work, "query occurrence depth exceeded");
      result.path.insert(result.path.begin(), call);
    }
    return true;
  }
  // Substitute only formal positions. Nonformal child observations retain a
  // reference to the actual child result/stop transfer through one local atom.
  bool substitute(const BitVector &source, unsigned formals,
                  ArrayRef<BitVector> arguments, unsigned childAtom,
                  BitVector &result, facts::Work &work) {
    if (arguments.size() != formals || source.size() < formals)
      return unsupported("observation call signature differs");
    if (!charge(work, 1 + source.size()))
      return false;
    for (int bit : source.set_bits()) {
      if (unsigned(bit) < formals) {
        if (arguments[bit].empty() || !unite(result, arguments[bit], work))
          return unsupported(
              "verifier dependency is unavailable at the caller");
      } else {
        result.set(childAtom);
      }
    }
    return true;
  }

  struct Transfer {
    Impl &analysis;
    Summary &summary;
    facts::Work &work;
    const mathematical::Availability &availability;
    unsigned observer;
    llvm::DenseMap<Value, ValueInfo> values;
    std::map<Operation *, unsigned> atoms;
    BitVector control;
    // Preserved denotes the symbolic incoming pending value, not emptiness.
    Pending::Output pending = Pending::Output::Preserved;
    Origin pendingQuery;

    Transfer(Impl &analysis, Summary &summary, facts::Work &work,
             const mathematical::Availability &availability, unsigned observer)
        : analysis(analysis), summary(summary), work(work),
          availability(availability), observer(observer) {}

    bool empty() {
      if (pending == Pending::Output::Preserved) {
        summary.pending.input = Pending::Input::Empty;
        pending = Pending::Output::Empty;
      }
      return pending == Pending::Output::Empty ||
             analysis.unsupported(
                 "challenge must be delivered before this observation");
    }
    bool consume(const Origin &origin) {
      if (pending == Pending::Output::Preserved) {
        if (origin.kind != Origin::Kind::Formal)
          return analysis.unsupported(
              "incoming challenge delivery is not an exact formal");
        summary.pending.input = Pending::Input::Formal;
        summary.pending.port = origin.port;
      } else if (pending != Pending::Output::Query ||
                 origin.kind != Origin::Kind::Query || origin != pendingQuery) {
        return analysis.unsupported(
            "delivery is not the exact pending challenge");
      }
      pending = Pending::Output::Empty;
      pendingQuery = {};
      return true;
    }
    bool pendingCall(const Summary &child, Action &action) {
      auto &transfer = child.pending;
      if (transfer.input == Pending::Input::Empty && !empty())
        return false;
      if (transfer.input == Pending::Input::Formal) {
        if (transfer.port >= action.inputOrigins.size() ||
            !consume(action.inputOrigins[transfer.port]))
          return false;
      }
      if (transfer.output == Pending::Output::Empty) {
        pending = Pending::Output::Empty;
        pendingQuery = {};
      } else if (transfer.output == Pending::Output::Query) {
        pending = Pending::Output::Query;
        if (!analysis.instantiate(transfer.query, action.inputOrigins,
                                  action.operation, pendingQuery, work))
          return false;
      }
      return true;
    }
    bool set(Value value, BitVector deps, Origin origin = {}) {
      if (!analysis.unite(deps, control, work))
        return false;
      values[value] = {std::move(deps), std::move(origin)};
      return true;
    }
    bool observed(Value value) const {
      return analysis.available(availability, value, observer);
    }
    bool inputs(Action &action) {
      for (Value value : action.operation->getOperands()) {
        auto found = values.find(value);
        if (found == values.end()) {
          if (observed(value))
            return analysis.unsupported("missing verifier SSA association");
          action.inputs.emplace_back();
          action.inputOrigins.emplace_back();
        } else {
          if (!analysis.charge(work, 1 + (control.size() + 63) / 64 +
                                         found->second.origin.path.size()))
            return false;
          action.inputs.push_back(found->second.dependencies);
          action.inputOrigins.push_back(found->second.origin);
        }
      }
      return true;
    }
    bool unionInputs(BitVector &result, ArrayRef<unsigned> ports,
                     const Action &action) {
      for (unsigned port : ports) {
        if (port >= action.inputs.size() || action.inputs[port].empty())
          return analysis.unsupported("verifier operand is not observed");
        if (!analysis.unite(result, action.inputs[port], work))
          return false;
      }
      return true;
    }
    bool stops(Action &action) {
      if (!action.mayStop)
        return true;
      summary.mayStop = true;
      return analysis.unite(action.stops, control, work) &&
             analysis.unite(summary.stops, action.stops, work) &&
             analysis.unite(control, action.stops, work);
    }
    bool services(const Summary &child, const Action &action) {
      for (int port : child.services.set_bits()) {
        const auto &origin = action.inputOrigins[port];
        if (origin.kind != Origin::Kind::Formal)
          return analysis.unsupported(
              "service reference has no exact formal association");
        summary.services.set(origin.port);
      }
      if (child.queryFamilies > maxQueries - summary.queryFamilies)
        return analysis.capacity(work, "challenge family count exceeded");
      summary.queryFamilies += child.queryFamilies;
      summary.depth = std::max(summary.depth, child.depth + 1);
      return true;
    }
    bool protocolCall(Action &action, pir::ApplyOp call, unsigned level) {
      auto function =
          analysis.symbols.lookupNearestSymbolFrom<pir::MathematicalOp>(
              call, call.getCalleeAttr());
      if (!function)
        return analysis.unsupported("protocol call has no actual declaration");
      std::optional<StringRef> role;
      for (auto [index, mapped] : enumerate(call.getRoles()))
        if (cast<StringAttr>(mapped).getValue() == summary.observer)
          role = cast<StringAttr>(function.getRoles()[index]).getValue();
      if (!role)
        return true;
      auto *child = analysis.get(function, *role, work, level + 1);
      if (!child)
        return false;
      action.callee = child;
      if (!pendingCall(*child, action) || !services(*child, action))
        return false;
      for (auto [index, result] : enumerate(call.getOutputs())) {
        if (!observed(result))
          continue;
        BitVector deps(control.size());
        Origin origin;
        if (child->results[index].empty() ||
            !analysis.substitute(child->results[index], child->formals,
                                 action.inputs, atoms[call] + index, deps,
                                 work) ||
            !analysis.instantiate(child->resultOrigins[index],
                                  action.inputOrigins, call, origin, work) ||
            !set(result, std::move(deps), std::move(origin)))
          return false;
      }
      action.mayStop = child->mayStop;
      return analysis.substitute(child->stops, child->formals, action.inputs,
                                 atoms[call] + call.getNumResults(),
                                 action.stops, work);
    }
    bool repeat(Action &action, pir::RepeatOp loop,
                const InteractionDeclaration &view, unsigned sequence,
                unsigned level) {
      if (!owns(loop.getRoles(), summary.observer))
        return true;
      auto *child =
          analysis.sequence(summary.declaration, summary.observer, availability,
                            observer, view, sequence, work, level + 1);
      if (!child)
        return false;
      action.callee = child;
      // A preserved incoming state or a closed round is an invariant. A body
      // that consumes an incoming formal only once is not repeatable.
      auto transfer = child->pending;
      if (transfer.input == Pending::Input::Any &&
          transfer.output == Pending::Output::Preserved) {
      } else if (transfer.input == Pending::Input::Empty &&
                 transfer.output == Pending::Output::Empty) {
        if (!empty())
          return false;
      } else {
        return analysis.unsupported(
            "repeat has no invariant pending-challenge transfer");
      }
      if (!services(*child, action))
        return false;
      Dependencies arguments = action.inputs, carry;
      for (unsigned i = 0; i < loop.getCarried(); ++i)
        carry.push_back(arguments[i + 1]);
      bool changed;
      do {
        changed = false;
        for (unsigned i = 0; i < carry.size(); ++i) {
          if (!observed(loop.getResult(i)))
            continue;
          BitVector next = carry[i];
          if (child->results[i].empty() || arguments[0].empty() ||
              !analysis.substitute(child->results[i], child->formals, arguments,
                                   atoms[loop] + i, next, work) ||
              !analysis.unite(next, arguments[0], work))
            return false;
          if (next != carry[i]) {
            carry[i] = std::move(next);
            changed = true;
          }
        }
        for (unsigned i = 0; i < carry.size(); ++i)
          arguments[i + 1] = carry[i];
      } while (changed);
      for (auto [i, result] : enumerate(loop.getOutputs())) {
        if (!observed(result))
          continue;
        Origin origin;
        auto returned = child->resultOrigins[i];
        // Include the zero-trip path. A last-iteration query is not a single
        // exact identity and cannot escape as the repeated family's challenge.
        if (returned.kind == Origin::Kind::Formal &&
            action.inputOrigins[returned.port] == action.inputOrigins[i + 1])
          origin = action.inputOrigins[i + 1];
        if (!set(result, std::move(carry[i]), std::move(origin)))
          return false;
      }
      // The observer checks the logical count/maximum even when the body is
      // total or the actual count is zero. Host resource failures are separate.
      if (owns(loop.getRoles(), summary.observer)) {
        action.mayStop = true;
        if (arguments[0].empty() ||
            !analysis.unite(action.stops, arguments[0], work))
          return false;
      }
      action.mayStop |= child->mayStop;
      return analysis.substitute(child->stops, child->formals, arguments,
                                 atoms[loop] + loop.getNumResults(),
                                 action.stops, work);
    }
    bool numericalCall(Action &action, func::FuncOp function) {
      auto checked = analysis.numerical.get(function, work);
      if (!checked)
        return analysis.capture(checked.takeError(), work);
      action.numerical = *checked;
      auto &child = **checked;
      if (child.results.size() != action.operation->getNumResults())
        return analysis.unsupported("numerical result signature differs");
      for (auto [i, result] : enumerate(action.operation->getResults())) {
        if (!observed(result))
          continue;
        BitVector deps(control.size());
        // Numerical summaries contain only formal data dependencies.
        if (!analysis.substitute(child.results[i], action.inputs.size(),
                                 action.inputs, 0, deps, work) ||
            !set(result, std::move(deps)))
          return false;
      }
      action.mayStop = child.mayStop;
      return analysis.substitute(child.stops, action.inputs.size(),
                                 action.inputs, 0, action.stops, work);
    }
    bool operation(Action &action, const InteractionDeclaration &view,
                   const InteractionAction &structure, unsigned level) {
      Operation *op = action.operation;
      if (auto call = dyn_cast<pir::ApplyOp>(op))
        return protocolCall(action, call, level);
      if (auto loop = dyn_cast<pir::RepeatOp>(op))
        return repeat(action, loop, view, *structure.getRepeatBody(), level);
      if (auto call = dyn_cast<pir::LocalCallOp>(op)) {
        if (call.getRole() != summary.observer)
          return true;
        return numericalCall(
            action, cast<func::FuncOp>(structure.getReferencedSymbol()));
      }
      if (isa<func::CallOp>(op)) {
        if (none_of(op->getResults(), [&](Value v) { return observed(v); }))
          return true;
        return numericalCall(
            action, cast<func::FuncOp>(structure.getReferencedSymbol()));
      }
      if (auto request = dyn_cast<pir::QueryOp>(op)) {
        if (request.getOwner() != summary.observer)
          return true;
        auto service =
            cast<pir::ServiceReferenceType>(request.getReference().getType());
        auto origin = action.inputOrigins.front();
        if (origin.kind != Origin::Kind::Formal ||
            !protocol::serviceMethod(service.getContract(),
                                     request.getMethod()) ||
            request.getNumResults() != 1)
          return analysis.unsupported(
              "query is not an admitted formal random service request");
        if (!empty())
          return false;
        if (summary.queryFamilies == maxQueries)
          return analysis.capacity(work, "challenge family count exceeded");
        ++summary.queryFamilies;
        action.service = origin.port;
        summary.services.set(origin.port);
        BitVector deps(control.size());
        deps.set(atoms[op]);
        for (const auto &argument : ArrayRef(action.inputs).drop_front())
          if (argument.empty() || !analysis.unite(deps, argument, work))
            return false;
        pending = Pending::Output::Query;
        pendingQuery = query(op);
        return set(request.getResult(0), std::move(deps), pendingQuery);
      }
      if (auto exchange = dyn_cast<pir::ExchangeOp>(op)) {
        if (exchange.getReceiver() == summary.observer) {
          if (!empty())
            return false;
          BitVector deps(control.size());
          deps.set(atoms[op]);
          return set(exchange.getOutput(), std::move(deps));
        }
        if (exchange.getSender() == summary.observer) {
          if (analysis.dataExchanges.count(op)) {
            if (!empty() || action.inputs.front().empty())
              return false;
            action.dataExchange = true;
            return !observed(exchange.getOutput()) ||
                   set(exchange.getOutput(), action.inputs.front(),
                       action.inputOrigins.front());
          }
          action.delivered = action.inputOrigins.front();
          if (!consume(action.delivered))
            return false;
          // Admission may retain the sender's component on the result too.
          if (observed(exchange.getOutput()))
            return set(exchange.getOutput(), action.inputs.front(),
                       action.delivered);
        }
        return true;
      }
      if (auto guard = dyn_cast<pir::GuardOp>(op)) {
        if (guard.getOwner() != summary.observer)
          return true;
        action.mayStop = true;
        return unionInputs(action.stops, {0}, action);
      }
      if (auto restricted = dyn_cast<pir::RestrictRolesOp>(op)) {
        return !observed(restricted.getOutput()) ||
               (!action.inputs.front().empty() &&
                set(restricted.getOutput(), action.inputs.front(),
                    action.inputOrigins.front()));
      }
      if (auto assembled = dyn_cast<pir::AssembleRolesOp>(op)) {
        if (!observed(assembled.getOutput()))
          return true;
        Value component = assembled.getComponent(summary.observer);
        auto found = values.find(component);
        if (found == values.end())
          return analysis.unsupported(
              "role assembly lacks the observed component");
        return set(assembled.getOutput(), found->second.dependencies,
                   found->second.origin);
      }
      if (isa<pir::StatementOp, pir::MathematicalReturnOp,
              pir::ProtocolYieldOp>(op))
        return true;
      auto semantics = mathematical::classify(op);
      if (!semantics || semantics->category != mathematical::Category::Total)
        return analysis.unsupported(
            Twine("unsupported observation operation ") +
            op->getName().getStringRef());
      for (auto result : op->getResults()) {
        if (!observed(result))
          continue;
        auto operands =
            mathematical::operandDependencies(op, result.getResultNumber());
        BitVector deps(control.size());
        if (failed(operands) || !unionInputs(deps, *operands, action) ||
            !set(result, std::move(deps)))
          return false;
      }
      return true;
    }
  };

  const Summary *sequence(pir::MathematicalOp declaration, StringRef observer,
                          const mathematical::Availability &available,
                          unsigned role, const InteractionDeclaration &view,
                          unsigned sequenceIndex, facts::Work &work,
                          unsigned level) {
    Block *block = view.getSequence(sequenceIndex).getBlock();
    Key key{block, observer.str()};
    if (!charge(work))
      return nullptr;
    if (!level || level > maxDepth) {
      capacity(work, "observation call/repeat depth exceeded");
      return nullptr;
    }
    if (auto found = summaries.find(key); found != summaries.end()) {
      const auto &summary = found->second;
      if (summary.depth > maxDepth - level + 1) {
        capacity(work, "observation call/repeat depth exceeded");
        return nullptr;
      }
      if (!charge(work, (summary.results.size() + 1) *
                            (1 + (summary.atoms.size() + 63) / 64)))
        return nullptr;
      return &summary;
    }
    if (!active.insert(key).second) {
      unsupported("cyclic protocol observation closure");
      return nullptr;
    }
    auto leave = scope_exit([&] { active.erase(key); });
    Summary summary;
    summary.declaration = declaration;
    summary.block = block;
    summary.observer = observer.str();
    summary.formals = block->getNumArguments();
    if (summary.formals > maxPorts ||
        block->back().getNumOperands() > maxPorts) {
      capacity(work, "protocol observation port limit exceeded");
      return nullptr;
    }
    summary.services.resize(summary.formals);
    Transfer transfer(*this, summary, work, available, role);
    for (unsigned i = 0; i < summary.formals; ++i)
      summary.atoms.push_back({Atom::Kind::Formal, nullptr, i});
    for (unsigned index : view.getSequence(sequenceIndex).getActions()) {
      const auto &action = view.getActions()[index];
      Operation *op = action.getOperation();
      if (!charge(work, op->getNumOperands() + op->getNumResults() + 1))
        return nullptr;
      if (op->hasAttr("site") && ++actionCount > maxActions) {
        capacity(work, "protocol observation action limit exceeded");
        return nullptr;
      }
      transfer.atoms.emplace(op, summary.atoms.size());
      auto query = dyn_cast<pir::QueryOp>(op);
      auto exchange = dyn_cast<pir::ExchangeOp>(op);
      bool observedQuery = query && query.getOwner() == observer;
      bool received = exchange && exchange.getReceiver() == observer;
      unsigned added = observedQuery || received ? 1
                       : isa<pir::ApplyOp, pir::RepeatOp>(op)
                           ? op->getNumResults() + 1
                           : 0;
      if (added > maxAtoms - summary.atoms.size()) {
        capacity(work, "protocol observation atom limit exceeded");
        return nullptr;
      }
      if (observedQuery)
        summary.atoms.push_back({Atom::Kind::Query, op, 0});
      else if (received)
        summary.atoms.push_back({Atom::Kind::Receive, op, 0});
      else if (isa<pir::ApplyOp, pir::RepeatOp>(op)) {
        bool repeat = isa<pir::RepeatOp>(op);
        for (unsigned i = 0; i < op->getNumResults(); ++i)
          summary.atoms.push_back(
              {repeat ? Atom::Kind::RepeatResult : Atom::Kind::CallResult, op,
               i});
        summary.atoms.push_back(
            {repeat ? Atom::Kind::RepeatStop : Atom::Kind::CallStop, op, 0});
      }
    }
    // Width zero is reserved for an unavailable value. A definition with no
    // atoms has one unused padding bit, which no transfer may set.
    unsigned width = std::max(1u, unsigned(summary.atoms.size()));
    if (width > maxAtoms) {
      capacity(work, "protocol observation atom limit exceeded");
      return nullptr;
    }
    transfer.control.resize(width);
    summary.stops.resize(width);
    for (auto argument : block->getArguments()) {
      if (!transfer.observed(argument))
        continue;
      BitVector deps(width);
      deps.set(argument.getArgNumber());
      transfer.values[argument] = {std::move(deps),
                                   formal(argument.getArgNumber())};
    }
    for (unsigned index : view.getSequence(sequenceIndex).getActions()) {
      const auto &structure = view.getActions()[index];
      Action action;
      action.operation = structure.getOperation();
      action.stops.resize(width);
      if (!charge(work) || !transfer.inputs(action) ||
          !transfer.operation(action, view, structure, level) ||
          !transfer.stops(action)) {
        if (failureCode.empty())
          unsupported("protocol observation transfer failed");
        return nullptr;
      }
      for (Value result : action.operation->getResults()) {
        auto it = transfer.values.find(result);
        action.results.push_back(it == transfer.values.end()
                                     ? BitVector()
                                     : it->second.dependencies);
      }
      summary.actions.push_back(std::move(action));
    }
    for (Value returned : block->back().getOperands()) {
      auto it = transfer.values.find(returned);
      BitVector deps =
          it == transfer.values.end() ? BitVector() : it->second.dependencies;
      if (!deps.empty() && !unite(deps, transfer.control, work))
        return nullptr;
      summary.results.push_back(std::move(deps));
      summary.resultOrigins.push_back(
          it == transfer.values.end() ? Origin() : it->second.origin);
    }
    summary.pending.output = transfer.pending;
    summary.pending.query = transfer.pendingQuery;
    return &summaries.emplace(std::move(key), std::move(summary)).first->second;
  }

  const Summary *get(pir::MathematicalOp function, StringRef observer,
                     facts::Work &work, unsigned level = 1) {
    if (!failureCode.empty())
      return nullptr;
    if (!owner || !isa<ModuleOp>(owner) || !function ||
        function->getParentOfType<ModuleOp>() != owner) {
      fail("protocol-observation-owner",
           "foreign protocol observation subject");
      return nullptr;
    }
    if (!owns(function.getRoles(), observer)) {
      unsupported("observer is not a declaration role");
      return nullptr;
    }
    auto structure = interactions.get(function, work);
    if (!structure) {
      capture(structure.takeError(), work);
      return nullptr;
    }
    auto found = availability.find(function);
    if (found == availability.end()) {
      mathematical::Availability facts;
      // Formation/availability have their own admission bounds. Debit every
      // retained association here as well before retaining this query's facts.
      if (!charge(work, (*structure)->getActions().size()) ||
          failed(mathematical::analyze(function, facts, symbols))) {
        unsupported("protocol availability is not admitted");
        return nullptr;
      }
      found = availability.emplace(function, std::move(facts)).first;
    }
    unsigned role = 0;
    for (auto name : function.getRoles()) {
      if (cast<StringAttr>(name).getValue() == observer)
        break;
      ++role;
    }
    return sequence(function, observer, found->second, role, **structure, 0,
                    work, level);
  }
};

ProtocolObservationAnalysis::ProtocolObservationAnalysis(Operation *module)
    : impl_(std::make_unique<Impl>(module)) {}
ProtocolObservationAnalysis::ProtocolObservationAnalysis(
    Operation *module, ArrayRef<Operation *> dataExchanges)
    : impl_(std::make_unique<Impl>(module, dataExchanges)) {}
ProtocolObservationAnalysis::ProtocolObservationAnalysis(Operation *module,
                                                         AnalysisManager &)
    : ProtocolObservationAnalysis(module) {}
ProtocolObservationAnalysis::~ProtocolObservationAnalysis() = default;
bool ProtocolObservationAnalysis::isInvalidated(
    const AnalysisManager::PreservedAnalyses &preserved) {
  return !preserved.isPreserved<ProtocolObservationAnalysis>();
}
void ProtocolObservationAnalysis::clear() {
  impl_ = std::make_unique<Impl>(impl_->owner);
}
Operation *ProtocolObservationAnalysis::getOwner() const {
  return impl_->owner;
}
Expected<const Summary *>
ProtocolObservationAnalysis::get(pir::MathematicalOp function,
                                 StringRef observer, facts::Work &work) {
  auto *summary = impl_->get(function, observer, work);
  if (!summary)
    return impl_->failure();
  return summary;
}
Expected<const ExecutionObservationSummary *>
ProtocolObservationAnalysis::numerical(func::FuncOp function,
                                       facts::Work &work) {
  if (!impl_->failureCode.empty())
    return impl_->failure();
  auto result = impl_->numerical.get(function, work);
  if (!result) {
    impl_->capture(result.takeError(), work);
    return impl_->failure();
  }
  return *result;
}
} // namespace zkc
