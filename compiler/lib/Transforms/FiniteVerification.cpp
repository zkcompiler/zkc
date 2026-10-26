#include "FiniteVerification.h"
#include "CollectFold.h"
#include "CollectionInterpretation.h"
#include "Kernel/Schedule.h"
#include "MathematicalComparison.h"
#include "RealizationSubject.h"
#include "ScopedCandidate.h"
#include "ScopedNestedContraction.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/ComputationMeaning.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Finite.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ScopeExit.h"
using namespace mlir;
using namespace llvm;
namespace zkc::finite {
namespace {
// Consumes actual candidate instructions. This reader does not allocate IR,
// invoke the producer, or trust a recorded recognition/formation summary.
class Reader {
  Computation c;
  SymbolTable &symbols;
  mathematical::CandidatePorts ports;
  llvm::DenseMap<Operation *, unsigned> regionReturns;
  llvm::DenseSet<Operation *> &bindings;
  Operation *cursor = nullptr;
  Type index, boolean;
  llvm::DenseMap<Value, Value> actual, cardinalities, offsets;
  bool valid = true, inlineMode = false;
  bool stoppedCallback = false;
  bool allowBulk;
  unsigned occurrence = 0;
  std::optional<Location> admissionLocation;
  std::optional<protocol::Assignments> admissionPath;
  unsigned admissionOccurrence = 0;
  std::string nextSite() {
    auto suffix = std::to_string(occurrence++);
    auto size =
        limits.finiteSite.size() + StringRef("_finite_").size() + suffix.size();
    if (size > 128 && ports.isScoped()) {
      uint64_t standaloneBytes = 16 * 1024 * 1024;
      auto &bytes =
          limits.sharedSiteBytes ? *limits.sharedSiteBytes : standaloneBytes;
      auto encoded = protocol::algorithmSite(
          {}, (limits.finiteSite + "_finite_" + suffix).str(), bytes);
      if (!encoded) {
        llvm::consumeError(encoded.takeError());
        result = {VerificationStatus::RequiredCapacity, "finite site bytes",
                  CapacityCause{WorkOwner::AlgorithmOriginBytes}};
        fail();
        return {};
      }
      return std::move(*encoded);
    }
    if (!limits.finiteSite.empty() && limits.sharedSiteBytes) {
      if (size > *limits.sharedSiteBytes) {
        result = {VerificationStatus::RequiredCapacity, "finite site bytes",
                  CapacityCause{WorkOwner::AlgorithmOriginBytes, size,
                                *limits.sharedSiteBytes}};
        fail();
        return {};
      }
      *limits.sharedSiteBytes -= size;
    }
    return (limits.finiteSite + "_finite_" + suffix).str();
  }
  bool site(Operation *op, StringRef contract = {}) {
    if (limits.finiteSite.empty())
      return true;
    std::string expected;
    if (admissionPath && contract == "control.require") {
      ++occurrence;
      uint64_t standaloneBytes = 16 * 1024 * 1024;
      auto &bytes =
          limits.sharedSiteBytes ? *limits.sharedSiteBytes : standaloneBytes;
      auto encoded = protocol::algorithmSite(
          *admissionPath, "finite_" + std::to_string(admissionOccurrence),
          bytes);
      if (!encoded) {
        llvm::consumeError(encoded.takeError());
        result = {VerificationStatus::RequiredCapacity, "finite site bytes",
                  CapacityCause{WorkOwner::AlgorithmOriginBytes}};
        fail();
        return false;
      }
      expected = std::move(*encoded);
    } else
      expected = nextSite();
    if (admissionPath)
      ++admissionOccurrence;
    auto actual = op->getAttrOfType<StringAttr>("site");
    return valid && actual && actual.getValue() == expected;
  }

  HelperReader helperReader;
  const CollectFold *composition = nullptr;
  ComposedHelperReader composedHelper;
  SmallVector<Value> consumerInputs, consumerEnvironment;
  SmallVector<Value> expressionResults;
  uint64_t remaining;
  VerificationLimits limits;
  VerificationResult result{VerificationStatus::Mismatch,
                            "finite recipe differs from its domain/helper"};
  void fail() { valid = false; }
  uint64_t availableWork() const {
    return limits.sharedReader ? std::min(remaining, *limits.sharedReader)
                               : remaining;
  }
  bool charge(uint64_t amount = 1) {
    auto available = availableWork();
    if (amount > available) {
      result = {
          VerificationStatus::RequiredCapacity, "finite reader work",
          CapacityCause{WorkOwner::RequiredFiniteReader, amount, available},
          mathematical::realizationSubject(c.operation)};
      fail();
      return false;
    }
    // A callback can enter another reader before this one finishes. Leave
    // unspent shared work available and retain this reader's own local cap.
    remaining -= amount;
    if (limits.sharedReader)
      *limits.sharedReader -= amount;
    return true;
  }
  SmallVector<Value> arguments(Block *block) {
    return ports.isScoped() ? SmallVector<Value>(ports.arguments(block))
                            : zkc::kernel::traversalArguments(block);
  }
  Operation *consume(StringRef name) {
    if (ports.isScoped()) {
      if (name == "local.for")
        name = "exec.range";
      else if (name == "local.if")
        name = "exec.test";
      else if (name == "local.yield" || name == "local.condition")
        name = "exec.complete";
      else if (name == "local.return")
        name = "exec.returned";
    }
    if (!valid || !ports.contains(cursor) ||
        cursor->getName().getStringRef() != name) {
      fail();
      return nullptr;
    }
    if (!charge())
      return nullptr;
    auto *op = cursor;
    cursor = ports.next(cursor);
    return op;
  }
  Value kernel(StringRef contract, ValueRange operands, Type result,
               ArrayRef<std::string> arguments = {},
               ArrayRef<std::string> parameters = {}) {
    auto *op =
        consume(ports.isScoped() ? exec::ApplyOp::getOperationName()
                                 : protocol::boundOperationName(contract));
    if (!op)
      return {};
    auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    auto binding = ref ? symbols.lookup<runtime::BindingOp>(ref.getValue())
                       : runtime::BindingOp();
    auto params = op->getAttrOfType<ArrayAttr>("parameters");
    auto site = op->getAttrOfType<StringAttr>("site");
    if (!binding || !params || !site || !this->site(op, contract) ||
        op->getAttrs().size() != 3 || ports.bodies(op) ||
        ports.inputs(op) != operands ||
        ports.outputs(op).size() != unsigned(bool(result)) ||
        (result && ports.outputs(op)[0].getType() != result) ||
        (admissionLocation && contract == "control.require" &&
         op->getLoc() != *admissionLocation) ||
        binding.getContract() != contract ||
        !binding.getImplementation().empty() ||
        binding.getArguments().size() != arguments.size() ||
        params.size() != parameters.size()) {
      fail();
      return {};
    }
    for (auto [a, b] : zip(binding.getArguments(), arguments))
      if (a != StringAttr::get(op->getContext(), b))
        fail();
    for (auto [a, b] : zip(params, parameters))
      if (a != StringAttr::get(op->getContext(), b))
        fail();
    bindings.insert(binding);
    return result ? ports.outputs(op)[0] : Value();
  }
  Value natural(uint64_t n) {
    return kernel("index.constant", {}, index, {}, {std::to_string(n)});
  }
  void require(Value condition) {
    if (!condition) {
      fail();
      return;
    }
    kernel("control.require", condition, {});
  }
  Value extent(Value container, unsigned selected = 0) {
    if (!container) {
      fail();
      return {};
    }
    auto col = mathematical::interpretCollection(container.getType());
    if (col.staticExtent.has_value())
      return natural(
          cast<algebra::FieldArrayType>(container.getType()).getLength());
    return kernel(col.length, container, index, col.arguments,
                  col.matrix ? ArrayRef<std::string>{std::to_string(selected)}
                             : ArrayRef<std::string>{});
  }
  Operation *control(StringRef name, ValueRange operands, TypeRange results,
                     unsigned regions) {
    if (name == "local.for" && !ports.isScoped()) {
      auto *at = cursor;
      auto available = availableWork();
      auto scheduleWork = available;
      auto parsed = zkc::kernel::readScheduledLoop(at, scheduleWork);
      // Schema inspection spends required work even if no packet matches or
      // inspection exhausts its allowance. Settle its actual debit once.
      if (!charge(available - scheduleWork))
        return nullptr;
      if (failed(parsed)) {
        result = {
            VerificationStatus::RequiredCapacity, "finite reader work",
            CapacityCause{WorkOwner::RequiredFiniteReader, {}, availableWork()},
            mathematical::realizationSubject(c.operation)};
        fail();
        return nullptr;
      }
      auto &scheduled = *parsed;
      if (scheduled) {
        if (!charge())
          return nullptr;
        if (ValueRange(scheduled->inputs) != operands ||
            scheduled->states != results.size() ||
            !llvm::equal(scheduled->loop.getResults()
                             .take_front(results.size())
                             .getTypes(),
                         results)) {
          fail();
          return nullptr;
        }
        cursor = at;
        return scheduled->loop;
      }
    }
    auto *op = consume(name);
    if (!op)
      return nullptr;
    if (ports.inputs(op) != operands ||
        ports.outputs(op).getTypes() != results ||
        ports.bodies(op) != regions || !op->getAttrOfType<StringAttr>("site") ||
        op->getAttrs().size() != 1 || !site(op)) {
      fail();
      return nullptr;
    }
    return op;
  }
  Block *enter(Operation *op, unsigned region, TypeRange types) {
    auto *block = ports.body(op, region);
    if (!block) {
      fail();
      return nullptr;
    }
    auto values = arguments(block);
    if (!llvm::equal(ValueRange(values).getTypes(), types) ||
        !ports.first(block)) {
      fail();
      return nullptr;
    }
    if (ports.isScoped())
      regionReturns[block->getParentOp()] = ports.outputs(op).size();
    if (ports.isScoped() && !limits.finiteSite.empty()) {
      auto function = cast<func::FuncOp>(block->getParentOp());
      NamedAttrList expected;
      expected.set("sym_name", function.getSymNameAttr());
      expected.set("function_type", function->getAttr("function_type"));
      expected.set("sym_visibility",
                   StringAttr::get(op->getContext(), "private"));
      expected.set("no_inline", UnitAttr::get(op->getContext()));
      expected.set("runtime.region", UnitAttr::get(op->getContext()));
      if (expected.getDictionary(op->getContext()) !=
          function->getAttrDictionary()) {
        fail();
        return nullptr;
      }
    }
    cursor = ports.first(block);
    if (isa<scf::ForOp>(op))
      cursor =
          cursor->getNextNode(); // Exact induction bridge checked by schema.
    return block;
  }
  void end(StringRef name, ValueRange inputs) {
    if (stoppedCallback) {
      if (cursor)
        fail();
      return;
    }
    if (cursor && isa<scf::ForOp>(cursor->getParentOp()) &&
        name == "local.yield")
      name = "scf.yield";
    auto *op = consume(name);
    if (!op)
      return;
    if (ports.isScoped() && isa<exec::CompleteOp>(op)) {
      auto found = regionReturns.find(op->getParentOp());
      if (found == regionReturns.end() || inputs.size() < found->second) {
        fail();
        return;
      }
      inputs = inputs.take_front(found->second);
    }
    if (ports.inputs(op) != inputs || !ports.outputs(op).empty() ||
        ports.bodies(op) || !op->getAttrs().empty() || cursor)
      fail();
  }
  void bound(Value value) {
    auto *loop = control("local.for", {value, value}, {}, 1);
    Operation *after = cursor;
    if (enter(loop, 0, {index}))
      end("local.yield", {});
    cursor = after;
  }
  Value range(Value lower, Value upper) {
    Value condition = kernel("index.less", {lower, upper}, boolean);
    SmallVector<Value> inputs{condition, lower};
    if (upper != lower)
      inputs.push_back(upper);
    SmallVector<Type> types(inputs.size() - 1, index);
    auto *branch = control("local.if", inputs, {index}, 2);
    auto *after = cursor;
    if (auto *yes = enter(branch, 0, types)) {
      Value size = kernel(
          "index.sub",
          {arguments(yes)[upper == lower ? 0 : 1], arguments(yes)[0]}, index);
      end("local.yield", size ? ValueRange{size} : ValueRange{});
    }
    if (enter(branch, 1, types)) {
      Value zero = natural(0);
      end("local.yield", zero ? ValueRange{zero} : ValueRange{});
    }
    cursor = after;
    return branch ? ports.outputs(branch)[0] : Value();
  }
  bool nestedContraction(const nested::ScopedSource &source, ValueRange entry,
                         Value size) {
    auto output = c.signature.getResult(0);
    auto field = cast<algebra::FieldVectorType>(output).getElementType();
    SmallVector<std::string> parameters{
        cast<algebra::FieldType>(field).getDomain().str()};
    Value zero = natural(0);
    Value nonempty = kernel("index.less", {zero, size}, boolean);
    SmallVector<Value> inputs{nonempty};
    append_range(inputs, entry);
    inputs.push_back(size);
    inputs.push_back(zero);
    auto *branch = control("local.if", inputs, output, 2);
    if (!branch)
      return false;
    auto *after = cursor;
    auto captureTypes = ValueRange(inputs).drop_front().getTypes();
    for (unsigned arm = 0; arm < 2 && valid; ++arm) {
      auto *block = enter(branch, arm, captureTypes);
      if (!block)
        return false;
      auto captures = arguments(block);
      if (arm) {
        Value empty = kernel("vector.empty", {}, output, parameters);
        end("local.yield", empty ? ValueRange{empty} : ValueRange{});
        continue;
      }
      auto &domain = source.inner.domain->getRegion(0).front();
      auto mapped = [&](Value formal) {
        auto position = cast<BlockArgument>(formal).getArgNumber();
        auto input = source.inputMap[position];
        return input ? captures[input - 1] : captures.back();
      };
      llvm::DenseMap<Value, Value> extents;
      admissionLocation = source.inner.operation->getLoc();
      admissionPath = protocol::Assignments{
          {limits.finiteSite.str(), SymbolTable::getSymbolName(c.helper).str()},
          {source.call->getAttrOfType<StringAttr>("site").str(),
           SymbolTable::getSymbolName(source.inner.helper).str()}};
      admissionOccurrence = 0;
      for (auto &op : domain.without_terminator()) {
        if (!valid)
          return false;
        Value size;
        if (isa<data::DomainElementsOp>(op))
          size = extent(mapped(op.getOperand(0)));
        else if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(op)) {
          Value matrix = mapped(op.getOperand(0));
          Value bound = extent(matrix, source.axis);
          require(
              kernel("index.less", {mapped(op.getOperand(1)), bound}, boolean));
          size = extent(matrix, 1 - source.axis);
        } else {
          size = extents.lookup(op.getOperand(0));
          for (Value child : op.getOperands().drop_front())
            require(
                kernel("index.equal", {size, extents.lookup(child)}, boolean));
        }
        extents[op.getResult(0)] = size;
      }
      admissionLocation.reset();
      admissionPath.reset();
      Value seed = source.seed.input
                       ? captures[*source.seed.input]
                       : kernel("field.constant", {}, field, parameters,
                                {source.seed.constant});
      Value result = kernel(source.axis ? "matrix.transpose_mul_vector"
                                        : "matrix.mul_vector",
                            {captures[source.matrix], captures[source.vector]},
                            output, parameters);
      Value initial = kernel("vector.fill", {seed, captures[entry.size()]},
                             output, parameters);
      Value value = kernel("vector.add", {initial, result}, output, parameters);
      end("local.yield", value ? ValueRange{value} : ValueRange{});
    }
    cursor = after;
    if (valid)
      finish(ports.outputs(branch));
    return valid;
  }
  Value product(Value left, Value right) {
    bound(left);
    bound(right);
    Value result = kernel("index.mul", {left, right}, index);
    bound(result);
    return result;
  }
  void admission() {
    for (auto &op : c.domain.getBody().front().without_terminator()) {
      if (!valid)
        return;
      Value size;
      if (isa<data::DomainElementsOp>(op))
        size = extent(actual.lookup(op.getOperand(0)));
      else if (auto indices = dyn_cast<data::DomainIndicesOp>(op))
        size = extent(actual.lookup(op.getOperand(0)), indices.getAxis());
      else if (isa<data::DomainRangeOp>(op)) {
        Value lower = actual.lookup(op.getOperand(0)),
              upper = actual.lookup(op.getOperand(1));
        bound(lower);
        bound(upper);
        size = range(lower, upper);
        offsets[op.getResult(0)] = lower;
      } else if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(op)) {
        bool row = isa<data::DomainMatrixRowOp>(op);
        Value matrix = actual.lookup(op.getOperand(0));
        Value selected = actual.lookup(op.getOperand(1)),
              limit = extent(matrix, row ? 0 : 1);
        require(kernel("index.less", {selected, limit}, boolean));
        size = extent(matrix, row ? 1 : 0);
      } else if (isa<data::DomainZipOp>(op)) {
        size = cardinalities.lookup(op.getOperand(0));
        for (Value v : op.getOperands().drop_front())
          require(
              kernel("index.equal", {size, cardinalities.lookup(v)}, boolean));
      } else if (isa<data::DomainProductOp>(op)) {
        size = cardinalities.lookup(op.getOperand(0));
        for (Value v : op.getOperands().drop_front())
          size = product(size, cardinalities.lookup(v));
      } else if (auto coordinates =
                     dyn_cast<data::DomainMatrixCoordinatesOp>(op)) {
        Value matrix = actual.lookup(op.getOperand(0));
        Value rows = extent(matrix, 0), cols = extent(matrix, 1);
        size = product(rows, cols);
        offsets[op.getResult(0)] =
            coordinates.getOrder() == "row_major" ? cols : rows;
      } else
        fail();
      if (!size)
        fail();
      cardinalities[op.getResult(0)] = size;
    }
  }
  SmallVector<Value> enumerate(Value domain, Value position,
                               const llvm::DenseMap<Value, Value> &captures) {
    if (!valid)
      return {};
    auto *op = domain.getDefiningOp();
    if (isa<data::DomainZipOp>(op)) {
      SmallVector<Value> result;
      for (Value v : op->getOperands())
        append_range(result, enumerate(v, position, captures));
      return result;
    }
    if (isa<data::DomainProductOp>(op)) {
      SmallVector<SmallVector<Value>> backwards;
      Value q = position;
      for (Value v : reverse(op->getOperands())) {
        Value divisor = captures.lookup(cardinalities.lookup(v));
        Value r = kernel("index.mod", {q, divisor}, index);
        backwards.push_back(enumerate(v, r, captures));
        q = kernel("index.div", {q, divisor}, index);
      }
      SmallVector<Value> result;
      for (auto &part : reverse(backwards))
        append_range(result, part);
      return result;
    }
    if (isa<data::DomainIndicesOp>(op))
      return {position};
    if (isa<data::DomainRangeOp>(op))
      return {kernel("index.add",
                     {captures.lookup(offsets.lookup(domain)), position},
                     index)};
    if (auto coordinates = dyn_cast<data::DomainMatrixCoordinatesOp>(op)) {
      Value radix = captures.lookup(offsets.lookup(domain));
      Value major = kernel("index.div", {position, radix}, index),
            minor = kernel("index.mod", {position, radix}, index);
      return coordinates.getOrder() == "row_major"
                 ? SmallVector<Value>{major, minor}
                 : SmallVector<Value>{minor, major};
    }
    Value container = captures.lookup(actual.lookup(op->getOperand(0)));
    if (!container) {
      fail();
      return {};
    }
    auto col = mathematical::interpretCollection(container.getType());
    if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(op)) {
      Value selector = captures.lookup(actual.lookup(op->getOperand(1)));
      bool row = isa<data::DomainMatrixRowOp>(op);
      return {kernel(
          "matrix.get",
          {container, row ? selector : position, row ? position : selector},
          col.element, col.arguments)};
    }
    return {
        kernel(col.access, {container, position}, col.element, col.arguments)};
  }
  SmallVector<Value> invoke(CallbackRole role, CallbackValues actuals) {
    // Reconstruct from this reader's immutable source and actual candidate
    // values. No selected producer environment participates in correspondence.
    auto callback = readCallbackABI(c, role);
    if (failed(callback)) {
      fail();
      return {};
    }
    Value scope;
    if (c.scoped && cursor && ports.isScoped())
      scope = cast<func::FuncOp>(cursor->getParentOp()).getArgument(0);
    auto environment = bindCallback(*callback, actuals, scope);
    if (failed(environment)) {
      fail();
      return {};
    }
    auto *helper = callback->symbol;
    ValueRange args = environment->actuals;
    if (c.scoped) {
      if (!limits.callback) {
        fail();
        return {};
      }
      auto callSite = nextSite();
      if (!valid)
        return {};
      auto result = limits.callback(cast<func::FuncOp>(helper),
                                    args.drop_front(), callSite, cursor);
      if (failed(result)) {
        fail();
        return {};
      }
      stoppedCallback = result->stopped;
      if ((stoppedCallback && !result->values.empty()) ||
          (!stoppedCallback &&
           !llvm::equal(
               ValueRange(result->values).getTypes(),
               cast<exec::OutcomeType>(callback->signature.getResult(0))
                   .getPayload()))) {
        fail();
        return {};
      }
      return result->values;
    }
    if (c.total) {
      auto result = helperReader(helper, args, cursor);
      if (failed(result)) {
        fail();
        return {};
      }
      return *result;
    }
    auto *op = consume("local.apply");
    if (!op)
      return {};
    auto type = callback->signature;
    auto ref = op->getAttrOfType<FlatSymbolRefAttr>("callee");
    if (!ref ||
        ref.getValue() != SymbolTable::getSymbolName(helper).getValue() ||
        op->getOperands() != args ||
        op->getResultTypes() != type.getResults() ||
        op->getAttrs().size() != 2 || !op->getAttrOfType<StringAttr>("site"))
      fail();
    return SmallVector<Value>(op->getResults());
  }
  SmallVector<Value> transition(ValueRange state, ValueRange items,
                                ValueRange env, Value position = {}) {
    if (composition) {
      auto producerEnv = env.take_front(c.arguments + c.captures);
      auto element =
          invoke(CallbackRole::Body, {{},
                                      items,
                                      producerEnv.take_front(c.arguments),
                                      producerEnv.drop_front(c.arguments)});
      if (!valid || element.size() != 1) {
        fail();
        return {};
      }
      auto rest = env.drop_front(c.arguments + c.captures);
      SmallVector<Value> consumerEnv;
      unsigned next = 0;
      for (Value value : consumerEnvironment)
        consumerEnv.push_back(value == composition->collected ? value
                                                              : rest[next++]);
      auto &consumer = composition->consumer;
      auto callback = readCallbackABI(consumer, CallbackRole::Step);
      if (failed(callback)) {
        fail();
        return {};
      }
      SmallVector<Value> item{composition->indexed ? position : element[0]};
      auto environment = bindCallback(
          *callback,
          {state, item, ValueRange(consumerEnv).take_front(consumer.arguments),
           ValueRange(consumerEnv).drop_front(consumer.arguments)});
      if (failed(environment)) {
        fail();
        return {};
      }
      auto results =
          composedHelper(callback->symbol, environment->actuals, cursor,
                         composition->collected, position, element[0]);
      if (failed(results)) {
        fail();
        return {};
      }
      return *results;
    }
    auto next =
        invoke(c.collect ? CallbackRole::Body : CallbackRole::Step,
               {c.collect ? ValueRange{} : state, items,
                env.take_front(c.arguments), env.drop_front(c.arguments)});
    if (!valid || stoppedCallback || !c.collect)
      return next;
    auto col = mathematical::interpretCollection(state[0].getType());
    return {kernel(col.append, {state[0], next[0]}, state[0].getType(),
                   col.arguments)};
  }

public:
  static uint64_t reserve(uint64_t limit, uint64_t *shared) {
    if (!shared)
      return limit;
    auto allowance = std::min(limit, *shared);
    *shared -= allowance;
    return allowance;
  }
  Reader(Computation computation, SymbolTable &symbols,
         llvm::DenseSet<Operation *> &bindings, VerificationLimits limits = {},
         bool allowBulk = true)
      : c(computation), symbols(symbols), ports(limits.candidate),
        bindings(bindings), index(IntegerType::get(c.operation->getContext(),
                                                   64, IntegerType::Unsigned)),
        boolean(IntegerType::get(c.operation->getContext(), 1)),
        allowBulk(allowBulk), remaining(limits.reader), limits(limits) {}
  void compose(const CollectFold &pair, ValueRange inputs,
               ComposedHelperReader helper) {
    composition = &pair;
    consumerInputs.assign(inputs.begin(), inputs.end());
    composedHelper = helper;
    allowBulk = false;
  }
  VerificationResult outcome() const { return result; }
  bool check(local::FuncOp target) {
    if (!target || target.getFunctionType() != c.signature ||
        !target.getBody().hasOneBlock() || target->getAttrs().size() != 3)
      return false;
    auto origin = target->getAttrOfType<ArrayAttr>("logical_origin");
    if (!origin || origin.size() != 2 ||
        origin[0] != SymbolTable::getSymbolName(c.operation) ||
        origin[1] != ArrayAttr::get(target.getContext(), {}))
      return false;
    auto &entry = target.getBody().front();
    return checkBody(entry.getArguments(), &entry.front());
  }
  void finish(ValueRange values) {
    if (inlineMode)
      expressionResults.assign(values.begin(), values.end());
    else
      end("local.return", values);
  }
  FailureOr<SmallVector<Value>> checkInline(ValueRange inputs, Operation *&at,
                                            HelperReader helper) {
    inlineMode = true;
    helperReader = helper;
    if (!checkBody(inputs, at))
      return failure();
    at = cursor;
    return expressionResults;
  }
  bool checkBody(ValueRange entry, Operation *begin) {
    cursor = begin;
    auto partitions = partitionEntry(c, entry);
    if (failed(partitions))
      return false;
    for (auto [a, b] :
         zip(c.domain.getBody().front().getArguments(), partitions->domain))
      actual[a] = b;
    admission();
    if (!valid)
      return false;
    Value rootDomain = c.domain.getBody().front().back().getOperand(0);
    auto binding = cursor ? cursor->getAttrOfType<FlatSymbolRefAttr>("binding")
                          : FlatSymbolRefAttr();
    auto declaration =
        binding ? symbols.lookup<runtime::BindingOp>(binding.getValue())
                : runtime::BindingOp();
    if (allowBulk && ports.isScoped() && c.collect && declaration &&
        declaration.getContract() == "index.constant") {
      // The optional source interpreter has its own comparison allowance. It
      // consumes actual scoped instructions, never the producer's selection.
      uint64_t comparisonWork =
          reserve(std::min(availableWork(), limits.comparison),
                  limits.sharedComparison);
      auto settle = llvm::scope_exit([&] {
        if (limits.sharedComparison)
          *limits.sharedComparison += comparisonWork;
      });
      bool exhausted = false;
      auto nested = nested::readScopedSource(c, comparisonWork, exhausted);
      if (exhausted) {
        result = {VerificationStatus::OptionalCapacity,
                  "nested contraction source work",
                  CapacityCause{WorkOwner::OptionalComparison, {}, {}},
                  mathematical::realizationSubject(c.operation)};
        return false;
      }
      if (nested)
        return nestedContraction(*nested, entry,
                                 cardinalities.lookup(rootDomain));
    }
    bool startsEmpty =
        declaration && declaration.getContract() == "vector.empty";
    if (allowBulk &&
        (mathematical::hasFinitePayloadContract(cursor, symbols) ||
         // An identity collect may return an existing vector without payload.
         (c.collect && cursor &&
          isa<algebra::FieldVectorType>(c.signature.getResult(0)) &&
          !startsEmpty))) {
      // Semantic comparison is optional. Its bounded interpretation and
      // normalization cannot spend the ordered reader's admission budget.
      uint64_t comparisonWork =
          reserve(std::min(availableWork(), limits.comparison),
                  limits.sharedComparison);
      auto settleComparison = llvm::scope_exit([&] {
        if (limits.sharedComparison)
          *limits.sharedComparison += comparisonWork;
      });
      mathematical::ComparisonCapacity capacity;
      std::optional<CapacityCause> debit;
      auto *payload = cursor;
      if (auto compared = mathematical::compareFinitePayload(
              c, entry, cardinalities.lookup(rootDomain), cursor, symbols,
              bindings, comparisonWork,
              inlineMode ? nullptr : &begin->getBlock()->back(), &capacity,
              &debit, limits.candidate);
          succeeded(compared)) {
        // Mathematical equality does not authorize changing the actual
        // occurrence identities. Account and check the complete consumed
        // payload, including unused arithmetic admitted by the comparison.
        for (auto *op = payload; op != cursor; op = ports.next(op))
          if (!op || !charge() || !site(op)) {
            fail();
            return false;
          }
        finish(ValueRange{*compared});
        return valid;
      }
      if (capacity != mathematical::ComparisonCapacity::None) {
        result = {VerificationStatus::OptionalCapacity,
                  mathematical::comparisonCapacityName(capacity),
                  debit.value_or(
                      CapacityCause{WorkOwner::OptionalComparison, {}, {}}),
                  mathematical::realizationSubject(c.operation)};
        return false;
      }
    }
    SmallVector<Value> state, env;
    append_range(env, partitions->domain);
    append_range(env, partitions->captures);
    if (composition) {
      auto consumer = partitionEntry(composition->consumer, consumerInputs);
      if (failed(consumer))
        return false;
      append_range(state, consumer->initialState);
      append_range(consumerEnvironment, consumer->domain);
      append_range(consumerEnvironment, consumer->captures);
      for (Value value : consumerEnvironment)
        if (value != composition->collected)
          env.push_back(value);
    } else if (c.collect) {
      auto result = c.signature.getResult(0);
      auto col = mathematical::interpretCollection(result);
      if (col.staticExtent.has_value()) {
        result = algebra::FieldVectorType::get(
            col.element.getContext(),
            cast<algebra::FieldType>(col.element).getDomain());
        col = mathematical::interpretCollection(result);
      }
      state.push_back(kernel(col.empty, {}, result, col.arguments));
    } else
      append_range(state, partitions->initialState);
    Value zero = natural(0),
          root = c.domain.getBody().front().back().getOperand(0);
    SmallVector<Value> captures(env);
    for (auto &op : c.domain.getBody().front().without_terminator()) {
      captures.push_back(cardinalities.lookup(op.getResult(0)));
      if (Value v = offsets.lookup(op.getResult(0)))
        captures.push_back(v);
    }
    if (!valid)
      return false;
    SmallVector<Value> unique;
    for (Value value : captures)
      if (!is_contained(unique, value))
        unique.push_back(value);
    captures = std::move(unique);
    SmallVector<Value> inputs{zero, cardinalities.lookup(root)};
    append_range(inputs, state);
    append_range(inputs, captures);
    SmallVector<Type> types;
    for (Value v : state)
      types.push_back(v.getType());
    auto *loop = control("local.for", inputs, types, 1);
    auto *after = cursor;
    SmallVector<Type> bt{index};
    append_range(bt, types);
    for (Value v : captures)
      bt.push_back(v.getType());
    auto *body = enter(loop, 0, bt);
    if (!body)
      return false;
    auto bodyArguments = arguments(body);
    auto current = ValueRange(bodyArguments).slice(1, state.size()),
         captured = ValueRange(bodyArguments).drop_front(1 + state.size());
    llvm::DenseMap<Value, Value> mapping;
    for (auto [a, b] : zip(captures, captured))
      mapping[a] = b;
    auto item = enumerate(root, bodyArguments[0], mapping);
    SmallVector<Value> environment;
    for (Value v : env)
      environment.push_back(mapping.lookup(v));
    if (!valid)
      return false;
    SmallVector<Value> next;
    if (c.predicate) {
      auto pred = invoke(CallbackRole::Predicate,
                         {{},
                          item,
                          ValueRange(environment).take_front(c.arguments),
                          ValueRange(environment).drop_front(c.arguments)});
      if (!valid || (!stoppedCallback && pred.size() != 1))
        return false;
      if (!stoppedCallback) {
        SmallVector<Value> capturedValues;
        for (ValueRange operands :
             {ValueRange(current), ValueRange(item), ValueRange(environment)})
          for (Value value : operands)
            if (!is_contained(capturedValues, value))
              capturedValues.push_back(value);
        SmallVector<Value> bi{pred[0]};
        append_range(bi, capturedValues);
        auto *branch = control("local.if", bi, types, 2);
        auto *following = cursor;
        SmallVector<Type> branchTypes;
        for (Value v : capturedValues)
          branchTypes.push_back(v.getType());
        auto remap = [&](Block *block, ValueRange operands) {
          SmallVector<Value> result;
          for (Value value : operands) {
            auto position =
                llvm::find(capturedValues, value) - capturedValues.begin();
            result.push_back(arguments(block)[position]);
          }
          return result;
        };
        if (auto *yes = enter(branch, 0, branchTypes)) {
          auto result = transition(remap(yes, current), remap(yes, item),
                                   remap(yes, environment));
          end("local.yield", result);
        }
        stoppedCallback = false;
        if (auto *no = enter(branch, 1, branchTypes))
          end("local.yield", remap(no, current));
        cursor = following;
        if (!valid)
          return false;
        append_range(next, ports.outputs(branch));
      }
    } else
      next = transition(current, item, environment, bodyArguments[0]);
    append_range(next, captured);
    end("local.yield", next);
    stoppedCallback = false;
    cursor = after;
    if (!valid)
      return false;
    SmallVector<Value> results(ports.outputs(loop).take_front(state.size()));
    if (!composition && c.collect &&
        results[0].getType() != c.signature.getResult(0)) {
      auto col = mathematical::interpretCollection(c.signature.getResult(0));
      results[0] = kernel("field_array.from_vector", results,
                          c.signature.getResult(0), col.arguments);
    }
    finish(results);
    return valid;
  }
};
} // namespace
FailureOr<SmallVector<Value>>
verifyExpression(Operation *source, ValueRange inputs, Operation *&cursor,
                 HelperReader helper, Operation *symbolRoot) {
  VerificationResult outcome{VerificationStatus::Mismatch, {}};
  auto result =
      verifyExpression(source, inputs, cursor, helper, symbolRoot, {}, outcome);
  if (outcome.status == VerificationStatus::OptionalCapacity ||
      outcome.status == VerificationStatus::RequiredCapacity)
    diagnostics::emit(source->emitError(), "finite-verification-capacity",
                      outcome.detail);
  return result;
}

FailureOr<SmallVector<Value>>
verifyExpression(Operation *source, ValueRange inputs, Operation *&cursor,
                 HelperReader helper, Operation *symbolRoot,
                 VerificationLimits limits, VerificationResult &outcome,
                 MathematicalSelectionPolicy policy) {
  outcome = {VerificationStatus::Mismatch,
             "finite expression differs from its domain/helper"};
  if (!cursor)
    return failure();
  auto *unit = SymbolTable::getNearestSymbolTable(cursor);
  if (!unit || unit->getNumRegions() != 1 || !unit->getRegion(0).hasOneBlock())
    return failure();
  SymbolTable symbols(unit);
  llvm::DenseSet<Operation *> bindings;
  Computation c;
  SymbolTableCollection sourceSymbols;
  if (failed(describe(source, c, symbolRoot, &sourceSymbols)))
    return failure();
  c.scopedSource = limits.sourceClosure;
  c.fixedBindings = limits.fixedBindings;
  Reader reader(c, symbols, bindings, limits, policy.finiteBulk);
  auto result = reader.checkInline(inputs, cursor, helper);
  outcome = succeeded(result)
                ? VerificationResult{VerificationStatus::Verified, {}}
                : reader.outcome();
  return result;
}

FailureOr<SmallVector<Value>>
verifyCollectFold(const CollectFold &pair, ValueRange producerInputs,
                  ValueRange consumerInputs, Operation *&cursor,
                  HelperReader helper, ComposedHelperReader composed,
                  VerificationLimits limits, VerificationResult &outcome) {
  outcome = {VerificationStatus::Mismatch,
             "collect-fold recipe differs from its domain/helpers"};
  if (!cursor)
    return failure();
  auto *unit = SymbolTable::getNearestSymbolTable(cursor);
  if (!unit || unit->getNumRegions() != 1 || !unit->getRegion(0).hasOneBlock())
    return failure();
  SymbolTable symbols(unit);
  llvm::DenseSet<Operation *> bindings;
  Reader reader(pair.producer, symbols, bindings, limits, false);
  reader.compose(pair, consumerInputs, composed);
  auto result = reader.checkInline(producerInputs, cursor, helper);
  outcome = succeeded(result)
                ? VerificationResult{VerificationStatus::Verified, {}}
                : reader.outcome();
  return result;
}

VerificationResult checkRealizations(ModuleOp original, ModuleOp candidate,
                                     VerificationLimits limits) {
  if (failed(mlir::verify(original)) || failed(mlir::verify(candidate)))
    return {VerificationStatus::Mismatch, "module verification"};
  auto refuse = [&](StringRef detail) {
    return VerificationResult{VerificationStatus::Mismatch, detail};
  };
  if (!hasSingleElement(*original.getBody()) ||
      !hasSingleElement(*candidate.getBody()) ||
      original->getAttrDictionary() != candidate->getAttrDictionary())
    return refuse("module shape");
  auto before =
      dyn_cast<protocol_ir::ProtocolModuleOp>(original.getBody()->front());
  auto after =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!before || !after ||
      before->getAttrDictionary() != after->getAttrDictionary())
    return refuse("unit profile");
  SymbolTable symbols(after);
  SymbolTableCollection sourceSymbols;
  llvm::DenseSet<Operation *> retained, usedBindings;
  for (auto &op : before.getBody().front()) {
    auto name = SymbolTable::getSymbolName(&op);
    Operation *replacement = name ? symbols.lookup(name) : nullptr;
    if (!replacement)
      return refuse("missing declaration");
    retained.insert(replacement);
    if (isDeclaration(&op)) {
      Computation c;
      if (failed(describe(&op, c, before, &sourceSymbols)))
        return refuse("finite recipe differs from its domain/helper");
      Reader reader(c, symbols, usedBindings, limits);
      if (!reader.check(dyn_cast<local::FuncOp>(replacement)))
        return reader.outcome();
    } else if (!OperationEquivalence::isEquivalentTo(
                   &op, replacement, OperationEquivalence::IgnoreLocations))
      return refuse("changed retained definition or helper body");
  }
  for (auto &op : after.getBody().front())
    if (!retained.contains(&op) && !usedBindings.contains(&op))
      return refuse("unexpected declaration");
  return {VerificationStatus::Verified, {}};
}

LogicalResult VerificationResult::diagnose(ModuleOp candidate) const {
  if (status == VerificationStatus::Verified)
    return success();
  return diagnostics::emit(candidate.emitError(),
                           status == VerificationStatus::Mismatch
                               ? "finite-correspondence"
                               : "finite-verification-capacity",
                           detail);
}

LogicalResult verifyRealizations(ModuleOp original, ModuleOp candidate) {
  return checkRealizations(original, candidate).diagnose(candidate);
}
} // namespace zkc::finite
