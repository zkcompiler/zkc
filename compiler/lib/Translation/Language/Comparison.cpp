#include "DataPreconditions.h"
#include "Finite.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Exec/ControlCursor.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialTypes.h"
#include "zkc/Dialect/Protocol/Construction.h"
#include "zkc/Dialect/Protocol/IR/ProtocolAttrs.h"
#include "zkc/Dialect/Protocol/IR/ProtocolTypes.h"
#include "zkc/Dialect/Protocol/Origins.h"
#include "zkc/Dialect/Relation/Formula.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#include "zkc/Interfaces/Mathematical.h"
#include "zkc/Language/Builtins.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/Layout.h"
#include "zkc/Language/Names.h"
#include "zkc/Language/SourceTerms.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Translation/Entry.h"
#include "zkc/Translation/Language.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <limits>
#include <set>
using namespace llvm;
namespace zkc::language {
namespace {
using Values = SmallVector<mlir::Value>;
bool attributes(mlir::Operation &op, ArrayRef<StringRef> names) {
  return op.getAttrs().size() == names.size() &&
         llvm::all_of(names, [&](auto name) { return bool(op.getAttr(name)); });
}
bool string(mlir::Operation &op, StringRef name, StringRef expected) {
  auto value = op.getAttrOfType<mlir::StringAttr>(name);
  return value && value.getValue() == expected;
}
bool strings(mlir::Attribute attr, ArrayRef<std::string> expected) {
  auto values = mlir::dyn_cast_if_present<mlir::ArrayAttr>(attr);
  if (!values || values.size() != expected.size())
    return false;
  for (unsigned i = 0; i < expected.size(); ++i) {
    auto value = mlir::dyn_cast<mlir::StringAttr>(values[i]);
    if (!value || value.getValue() != expected[i])
      return false;
  }
  return true;
}
bool roleSet(mlir::Attribute value, ArrayRef<unsigned> indices) {
  std::vector<std::string> expected;
  for (auto i : indices)
    expected.push_back(nativeRoleName(i));
  return strings(value, expected);
}
class Comparator {
  const ClosedEntry &project;
  ArrayRef<Declaration> declared;
  mlir::ModuleOp module;
  const Limits &limits;
  Layouts layouts;
  std::map<std::string, mlir::Operation *> outlined, maps;
  std::set<mlir::Operation *> usedOutlined, usedMaps;
  exec::ControlCursor *scoped = nullptr;
  unsigned accounted = 0;
  std::map<std::string, mlir::Operation *> finiteDefinitions;
  std::set<mlir::Operation *> usedFiniteDefinitions;
  Error failure = Error::success();
  Correspondence report;
  uint64_t remaining;
  uint64_t siteOrdinal = 0;
  std::map<std::string, mlir::Operation *> bindings;
  std::set<std::string> usedBindings;
  template <class T> std::optional<T> take(Expected<T> value) {
    if (!value) {
      failure = value.takeError();
      return {};
    }
    return std::move(*value);
  }
  Error takeFailure() {
    if (failure)
      return std::move(failure);
    return error("source.correspondence",
                 "comparison refused without a diagnostic");
  }
  bool fail(StringRef message) {
    if (!failure)
      failure = scoped && scoped->exhausted()
                    ? error("source.limit", "scoped comparison limit exceeded")
                    : error("source.correspondence", message);
    return false;
  }
  bool contractSelector(mlir::Attribute attr,
                        const SpecificationSelector &expected, unsigned port) {
    auto row = mlir::dyn_cast<mlir::ArrayAttr>(attr);
    if (!charge(1) || !row || row.size() != 3)
      return fail("contract selector shape differs");
    auto direction =
        mlir::dyn_cast<mlir::StringAttr>(row[expected.anchor ? 1 : 0]);
    auto index =
        mlir::dyn_cast<mlir::IntegerAttr>(row[expected.anchor ? 2 : 1]);
    auto role = mlir::dyn_cast<mlir::StringAttr>(row[expected.anchor ? 0 : 2]);
    return (direction &&
            direction.getValue() == (expected.output ? "output" : "input") &&
            index && index.getType().isSignlessInteger(64) &&
            index.getInt() == port && role &&
            role.getValue() ==
                (expected.anchor ? "anchor" : nativeRoleName(expected.role))) ||
           fail("contract selector differs from source layout");
  }
  bool contractApplication(const Declaration &owner, mlir::Attribute attr,
                           const RelationApplication &expected) {
    auto row = mlir::dyn_cast<mlir::ArrayAttr>(attr);
    if (!row || row.size() != 2)
      return fail("contract application shape differs");
    auto relation = mlir::dyn_cast<mlir::FlatSymbolRefAttr>(row[0]);
    auto operands = mlir::dyn_cast<mlir::ArrayAttr>(row[1]);
    if (!relation ||
        relation.getValue() !=
            project.declarations()[expected.relation.index].symbol ||
        !operands)
      return fail("contract relation differs");
    unsigned at = 0;
    for (const auto &operand : expected.operands) {
      auto slice = take(layouts.select(owner, operand));
      if (!slice)
        return false;
      for (unsigned i = 0; i < slice->layout->leaves.size(); ++i)
        if (at >= operands.size() ||
            !contractSelector(operands[at++], operand, slice->offset + i))
          return fail("contract application native layout differs");
    }
    return at == operands.size() || fail("extra contract operands");
  }
  bool contracts(const Declaration &owner, mlir::Operation &function) {
    auto clauses = function.getAttrOfType<mlir::ArrayAttr>("contracts");
    if (!clauses || clauses.size() != owner.specifications.size())
      return fail("contract inventory differs");
    for (auto [attr, expected] : zip(clauses, owner.specifications)) {
      if (!charge(1))
        return false;
      auto row = mlir::dyn_cast<mlir::ArrayAttr>(attr);
      if (!row || row.size() != 5)
        return fail("contract clause shape differs");
      using K = SpecificationClause::Kind;
      StringRef kind = expected.kind == K::Target   ? "target"
                       : expected.kind == K::Input  ? "input"
                       : expected.kind == K::Output ? "output"
                                                    : "continuation";
      auto actualKind = mlir::dyn_cast<mlir::StringAttr>(row[0]);
      auto name = mlir::dyn_cast<mlir::StringAttr>(row[1]);
      if (!actualKind || actualKind.getValue() != kind || !name ||
          name.getValue() != expected.name ||
          !contractApplication(owner, row[2], expected.subject))
        return fail("contract clause differs");
      if (expected.residual
              ? !contractApplication(owner, row[3], *expected.residual)
              : !mlir::isa<mlir::UnitAttr>(row[3]))
        return fail("contract residual differs");
      if (expected.decision) {
        auto slice = take(layouts.select(owner, *expected.decision));
        if (!slice ||
            !contractSelector(row[4], *expected.decision, slice->offset))
          return fail("contract decision differs");
      } else if (!mlir::isa<mlir::UnitAttr>(row[4]))
        return fail("unexpected contract decision");
    }
    return true;
  }
  bool charge(uint64_t n) {
    if (n > remaining) {
      failure = error("source.limit", "comparison work limit exceeded");
      return false;
    }
    remaining -= n;
    return true;
  }
  unsigned allowance() const {
    return unsigned(std::min<uint64_t>(
        std::numeric_limits<unsigned>::max(),
        std::min(remaining, limits.operations - std::min(report.operations,
                                                         limits.operations))));
  }
  bool account() {
    unsigned count = scoped->consumed() - accounted;
    if (report.operations > limits.operations ||
        count > limits.operations - report.operations) {
      failure =
          error("source.limit", "scoped comparison operation limit exceeded");
      return false;
    }
    if (!charge(count))
      return false;
    accounted = scoped->consumed();
    report.operations += count;
    return true;
  }
  std::optional<std::string> alternative(const Layout &layout, StringRef name) {
    for (unsigned i = 0; i < layout.alternatives.size(); ++i) {
      if (!charge(layout.alternatives[i].name.size() + 1))
        return {};
      if (layout.alternatives[i].name == name)
        return nativeAlternativeName(i);
    }
    fail("unknown source variant alternative");
    return {};
  }
  bool record(mlir::Operation &op, Span source) {
    if (auto loc = mlir::dyn_cast<mlir::FileLineColLoc>(op.getLoc())) {
      if (report.locations.size() >=
          limits.locationBytes / (5 * sizeof(uint64_t))) {
        failure = error("source.limit", "source location map limit exceeded");
        return false;
      }
      report.locations.push_back({loc.getLine(), loc.getColumn(), source});
    }
    return true;
  }
  bool types(mlir::TypeRange actual, ArrayRef<LayoutLeaf> expected) {
    if (actual.size() != expected.size())
      return fail("native layout arity differs");
    for (unsigned i = 0; i < actual.size(); ++i) {
      if (!charge(expected[i].cost()))
        return false;
      if (const auto *quotient = expected[i].quotient()) {
        auto type = mlir::dyn_cast<poly::QuotientType>(actual[i]);
        if (!type || type.getModulus() != quotient->modulus ||
            type.getDegree() != quotient->degree)
          return fail("formal quotient layout differs");
        continue;
      }
      if (const auto *polynomial = expected[i].polynomial()) {
        auto type = mlir::dyn_cast<poly::PolynomialType>(actual[i]);
        if (!type || type.getDomain() != polynomial->field ||
            type.getArity() != polynomial->arity)
          return fail("formal polynomial layout differs");
        continue;
      }
      if (const auto *oracle = expected[i].oracle()) {
        protocol_ir::OracleKindAttr kind;
        if (oracle->maximum) {
          auto sequence =
              mlir::dyn_cast<protocol_ir::OracleSequenceType>(actual[i]);
          if (!sequence || sequence.getMaximum() != *oracle->maximum)
            return fail("oracle sequence maximum differs");
          kind = sequence.getKind();
        } else {
          auto handle =
              mlir::dyn_cast<protocol_ir::OracleHandleType>(actual[i]);
          if (!handle)
            return fail("oracle handle layout differs");
          kind = handle.getKind();
        }
        if (kind.getIdentity() != oracle->kind.identity ||
            kind.getArguments().size() != oracle->kind.arguments.size())
          return fail("oracle kind layout differs");
        for (unsigned j = 0; j < oracle->kind.arguments.size(); ++j) {
          const auto &argument = oracle->kind.arguments[j];
          if (argument.kind == protocol::TypeArgument::Kind::Nat) {
            auto number =
                mlir::dyn_cast<mlir::IntegerAttr>(kind.getArguments()[j]);
            if (!number || !number.getType().isUnsignedInteger(64) ||
                number.getValue().getZExtValue() != argument.natural)
              return fail("oracle static cardinality differs");
          } else {
            auto row = mlir::dyn_cast<mlir::TypeAttr>(kind.getArguments()[j]);
            if (!row || !argument.type)
              return fail("oracle row layout differs");
            auto logical =
                take(protocol::encodeBoundType(row.getValue(), false));
            if (!logical || !(*logical == *argument.type))
              return fail("oracle row layout differs");
          }
        }
        continue;
      }
      auto type = take(protocol::encodeBoundType(actual[i], false));
      if (!type)
        return false;
      if (type->spelling() != *expected[i].data())
        return fail("native layout type differs");
    }
    return true;
  }
  mlir::Operation *next(mlir::Block &block, mlir::Block::iterator &cursor,
                        Span span, StringRef name, mlir::ValueRange operands,
                        unsigned results, unsigned regions = 0) {
    if (scoped ? scoped->atEnd() : cursor == block.end()) {
      fail("original omitted an operation");
      return nullptr;
    }
    auto *operation = scoped ? scoped->take() : &*cursor++;
    if (!operation || (scoped && !account())) {
      fail("scoped operation is unavailable");
      return nullptr;
    }
    auto &op = *operation;
    if (!scoped && ++report.operations > limits.operations) {
      failure = error("source.limit", "comparison operation limit exceeded");
      return nullptr;
    }
    if (!charge((scoped ? 0 : 1) + operands.size()) || !record(op, span))
      return nullptr;
    if ((!name.empty() && op.getName().getStringRef() != name) ||
        op.getNumResults() != results || op.getNumRegions() != regions ||
        op.getNumSuccessors() || op.getOperands() != operands) {
      fail("operation identity, operands or region structure differs");
      return nullptr;
    }
    return &op;
  }
  mlir::Operation *invoke(mlir::Block &block, mlir::Block::iterator &cursor,
                          Span span, StringRef name, mlir::ValueRange inputs,
                          ArrayRef<LayoutLeaf> outputs, Values &result) {
    Values arguments{scoped->getScope()};
    llvm::append_range(arguments, inputs);
    auto *operation = next(block, cursor, span, name, arguments, 1);
    auto outcome = operation ? mlir::dyn_cast<exec::OutcomeType>(
                                   operation->getResult(0).getType())
                             : exec::OutcomeType();
    if (!outcome || !types(outcome.getPayload(), outputs) ||
        !scoped->dispatch(operation->getResult(0), result) || !account()) {
      fail("scoped outcome or dispatch differs");
      return nullptr;
    }
    return operation;
  }
  mlir::func::FuncOp region(mlir::func::CallOp call, Span span) {
    if (!account())
      return {};
    auto found = outlined.find(call.getCallee().str());
    auto function = found == outlined.end()
                        ? mlir::func::FuncOp()
                        : mlir::dyn_cast<mlir::func::FuncOp>(found->second);
    if (!function || !usedOutlined.insert(function).second ||
        !attributes(*function, {"sym_name", "sym_visibility", "function_type",
                                "no_inline", "runtime.region"}) ||
        !string(*function, "sym_visibility", "private") ||
        !function->getAttrOfType<mlir::UnitAttr>("no_inline") ||
        !function->getAttrOfType<mlir::UnitAttr>("runtime.region") ||
        mlir::TypeRange(function.getArgumentTypes()) !=
            call.getOperandTypes() ||
        mlir::TypeRange(function.getResultTypes()) != call.getResultTypes() ||
        function.empty() || !record(*function, span) || !charge(1)) {
      fail("outlined control identity or signature differs");
      return {};
    }
    if (++report.operations > limits.operations) {
      failure = error("source.limit", "outlined definition limit exceeded");
      return {};
    }
    return function;
  }
  bool finish(mlir::Block &block, mlir::Block::iterator &cursor, Span span,
              mlir::ValueRange values, bool charged) {
    Values arguments;
    if (charged)
      arguments.push_back(scoped->getScope());
    llvm::append_range(arguments, values);
    auto *result =
        next(block, cursor, span, charged ? "exec.complete" : "exec.returned",
             arguments, 1);
    auto outcome =
        result
            ? mlir::dyn_cast<exec::OutcomeType>(result->getResult(0).getType())
            : exec::OutcomeType();
    if (!result || !attributes(*result, {}) || !outcome ||
        mlir::TypeRange(outcome.getPayload()) != values.getTypes())
      return fail("scoped return packaging differs");
    auto *ret =
        next(block, cursor, span, "func.return", result->getResults(), 0);
    return (ret && attributes(*ret, {}) && scoped->complete()) ||
           fail("scoped function has extra control or a changed return");
  }
  bool stop(Span span, StringRef reason, StringRef site) {
    auto reject = mlir::dyn_cast_or_null<exec::RejectOp>(scoped->take());
    auto edge = mlir::dyn_cast_or_null<mlir::cf::BranchOp>(scoped->take());
    if (!reject || !attributes(*reject, {"site", "reason"}) ||
        reject.getScope() != scoped->getScope() ||
        reject.getReason() != reason || reject.getSite() != site || !edge ||
        !attributes(*edge, {}) ||
        edge.getDestOperands() != mlir::ValueRange{reject.getStop()} ||
        !scoped->atEnd() || !scoped->failure(edge.getDest()) ||
        !scoped->complete() || !account() || !record(*reject, span) ||
        !record(*edge, span))
      return fail("scoped rejection or propagation differs");
    return true;
  }
  bool withScoped(mlir::func::FuncOp function,
                  llvm::function_ref<bool()> check) {
    auto signature = function.getFunctionType();
    if (function.empty() || signature.getNumInputs() == 0 ||
        !mlir::isa<runtime::ScopeType>(signature.getInput(0)) ||
        signature.getNumResults() != 1 ||
        !mlir::isa<exec::OutcomeType>(signature.getResult(0)) ||
        function.front().getArgumentTypes() != signature.getInputs())
      return fail("scoped function interface differs");
    unsigned work = allowance();
    exec::ControlCursor control(function, work);
    auto *parent = scoped;
    unsigned parentAccounted = accounted;
    scoped = &control;
    accounted = 0;
    llvm::scope_exit restore([&] {
      scoped = parent;
      accounted = parentAccounted;
    });
    if (!control.enter(&function.front()) || !check() || !account())
      return false;
    return control.complete() ||
           fail("scoped function has uninspected control");
  }
  std::optional<Values> variant(mlir::Block &block,
                                mlir::Block::iterator &cursor, Span span,
                                mlir::ValueRange inputs,
                                const LayoutLeaf &output, StringRef alternative,
                                StringRef site) {
    if (!scoped) {
      fail("variant construction requires scoped execution");
      return {};
    }
    Values result;
    auto *actual =
        invoke(block, cursor, span, "exec.variant", inputs, {output}, result);
    if (!actual || !attributes(*actual, {"alternative", "site"}) ||
        !string(*actual, "alternative", alternative) ||
        !string(*actual, "site", site)) {
      fail("variant alternative or occurrence differs");
      return {};
    }
    return result;
  }
  std::optional<Values> unpackMathematical(mlir::Block &block,
                                           mlir::Block::iterator &cursor,
                                           mlir::Value value,
                                           ArrayRef<LayoutLeaf> outputs,
                                           Span span) {
    Values result;
    for (unsigned i = 0; i < outputs.size(); ++i) {
      auto *project = next(block, cursor, span, "data.get", value, 1);
      if (!project || !attributes(*project, {"index"}) ||
          !types(project->getResultTypes(), {outputs[i]})) {
        fail("total payload projection differs");
        return {};
      }
      auto index = project->getAttrOfType<mlir::IntegerAttr>("index");
      if (!index || !index.getType().isSignlessInteger(64) ||
          index.getInt() != i) {
        fail("total payload projection index differs");
        return {};
      }
      result.push_back(project->getResult(0));
    }
    return result;
  }
  std::optional<Values> unpack(mlir::Value value, ArrayRef<LayoutLeaf> outputs,
                               StringRef alternative, Span span,
                               StringRef site) {
    if (!scoped) {
      fail("ordered payload unpacking requires scoped execution");
      return {};
    }
    Values result;
    auto check = [&](mlir::func::CallOp call, unsigned) {
      auto function = region(call, span);
      if (!function ||
          !types(function.getArgumentTypes().drop_front(), outputs))
        return false;
      return withScoped(function, [&] {
        auto cursor = function.front().begin();
        return finish(function.front(), cursor, span,
                      function.getArguments().drop_front(), true);
      });
    };
    if (!scoped->match(value, {}, {alternative.str()}, site, check, result) ||
        !account() || !types(mlir::ValueRange(result).getTypes(), outputs)) {
      fail("sequence payload unpacking or transfer differs");
      return {};
    }
    return result;
  }
  std::optional<Values>
  map(const Declaration &helper, const BulkApplication &source,
      mlir::ValueRange inputs, ArrayRef<LayoutLeaf> outputs, mlir::Block &block,
      mlir::Block::iterator &cursor, Span span, StringRef site) {
    if (!scoped || source.mapped.size() != inputs.size()) {
      fail("mapped application requires scoped execution and exact ports");
      return {};
    }
    Values vectors, captures;
    for (auto [input, mapped] : llvm::zip(inputs, source.mapped))
      (mapped ? vectors : captures).push_back(input);
    std::string identity =
        "zkc.source.map:" + std::to_string(helper.symbol.size()) + ":" +
        helper.symbol + ":";
    for (bool row : source.mapped)
      identity += row ? '1' : '0';
    if (!charge(identity.size()))
      return {};
    auto digest = SHA256::hash(arrayRefFromStringRef(identity));
    std::string name = "zkl_map_" + toHex(ArrayRef<uint8_t>(digest), true);
    auto domain = maps.find(name + "_domain"),
         callback = maps.find(name + "_body");
    auto layout = take(layouts.get(helper.outputs.front().type));
    if (!layout || vectors.empty() || domain == maps.end() ||
        callback == maps.end() || (*layout)->leaves.size() != 1 ||
        !(*layout)->leaves.front().data()) {
      fail("mapped auxiliary definition or scalar layout differs");
      return {};
    }
    auto bound = take(
        protocol::parseBoundType(*(*layout)->leaves.front().data(), false));
    if (!bound)
      return {};
    auto scalar = protocol::decodeBoundType(module.getContext(), *bound);
    if (!scalar) {
      fail("mapped scalar type is unavailable");
      return {};
    }
    auto *domainOp = domain->second, *callbackOp = callback->second;
    if (!usedMaps.count(domainOp)) {
      SmallVector<mlir::Type> items(vectors.size(), scalar);
      auto domainType = data::DomainType::get(module.getContext(), items);
      SmallVector<mlir::Type> arguments{
          runtime::ScopeType::get(module.getContext())};
      llvm::append_range(arguments, items);
      llvm::append_range(arguments, mlir::ValueRange(vectors).getTypes());
      llvm::append_range(arguments, mlir::ValueRange(captures).getTypes());
      auto outcome = exec::OutcomeType::get(module.getContext(), {scalar});
      auto definition = [&](mlir::Operation *op, StringRef kind,
                            mlir::TypeRange inputs, mlir::TypeRange outputs,
                            ArrayRef<StringRef> attrs, bool single) {
        auto type = op->getAttrOfType<mlir::TypeAttr>("function_type");
        auto signature =
            type ? mlir::dyn_cast<mlir::FunctionType>(type.getValue())
                 : mlir::FunctionType();
        if (!charge(1) || ++report.operations > limits.operations) {
          if (!failure)
            failure = error("source.limit", "mapped definition limit exceeded");
          return false;
        }
        return (op->getName().getStringRef() == kind &&
                attributes(*op, attrs) &&
                string(*op, "sym_visibility", "private") &&
                !op->getNumOperands() && !op->getNumResults() &&
                op->getNumRegions() == 1 && !op->getRegion(0).empty() &&
                (!single || llvm::hasSingleElement(op->getRegion(0))) &&
                signature && mlir::TypeRange(signature.getInputs()) == inputs &&
                mlir::TypeRange(signature.getResults()) == outputs &&
                op->getRegion(0).front().getArgumentTypes() == inputs &&
                record(*op, span)) ||
               fail("mapped definition structure or signature differs");
      };
      if (!definition(domainOp, "data.domain",
                      mlir::ValueRange(vectors).getTypes(), {domainType},
                      {"sym_name", "sym_visibility", "function_type"}, true) ||
          !definition(callbackOp, "func.func", arguments, {outcome},
                      {"sym_name", "sym_visibility", "function_type",
                       "no_inline", "runtime.origin"},
                      false))
        return {};
      usedMaps.insert(domainOp);
      usedMaps.insert(callbackOp);
      {
        auto *parent = scoped;
        scoped = nullptr;
        llvm::scope_exit restore([&] { scoped = parent; });
        auto &entry = domainOp->getRegion(0).front();
        auto cursor = entry.begin();
        mlir::Value root;
        SmallVector<mlir::Type> admittedItems;
        for (auto input : entry.getArguments()) {
          auto *elements =
              next(entry, cursor, span, "data.domain_elements", input, 1);
          if (!elements || !attributes(*elements, {}) ||
              elements->getResult(0).getType() !=
                  data::DomainType::get(module.getContext(), {scalar})) {
            fail("mapped element domain differs");
            return {};
          }
          admittedItems.push_back(scalar);
          if (!root) {
            root = elements->getResult(0);
            continue;
          }
          auto *zip = next(entry, cursor, span, "data.domain_zip",
                           {root, elements->getResult(0)}, 1);
          if (!zip || !attributes(*zip, {}) ||
              zip->getResult(0).getType() !=
                  data::DomainType::get(module.getContext(), admittedItems)) {
            fail("mapped zip domain or row admission order differs");
            return {};
          }
          root = zip->getResult(0);
        }
        auto *yield = next(entry, cursor, span, "data.domain_yield", root, 0);
        if (!yield || !attributes(*yield, {}) || cursor != entry.end()) {
          fail("mapped domain returns a different value or has extra work");
          return {};
        }
      }
      auto origin =
          callbackOp->getAttrOfType<mlir::ArrayAttr>("runtime.origin");
      auto label = origin && origin.size() == 2
                       ? mlir::dyn_cast<mlir::StringAttr>(origin[0])
                       : mlir::StringAttr();
      if (!callbackOp->getAttrOfType<mlir::UnitAttr>("no_inline") || !label ||
          label.getValue() != name + "_body" || !strings(origin[1], {})) {
        fail("mapped callback origin differs");
        return {};
      }
      auto function = mlir::cast<mlir::func::FuncOp>(callbackOp);
      if (!withScoped(function, [&] {
            auto &entry = function.front();
            auto cursor = entry.begin();
            Values actual, result;
            unsigned item = 1, capture = 1 + items.size() + vectors.size();
            for (bool mapped : source.mapped)
              actual.push_back(entry.getArgument(mapped ? item++ : capture++));
            auto *call = invoke(entry, cursor, span, "exec.compute", actual,
                                (*layout)->leaves, result);
            auto callee =
                call ? call->getAttrOfType<mlir::FlatSymbolRefAttr>("callee")
                     : mlir::FlatSymbolRefAttr();
            return (call && attributes(*call, {"callee", "site"}) && callee &&
                    callee.getValue() == helper.symbol &&
                    string(*call, "site", "body") &&
                    finish(entry, cursor, span, result, false)) ||
                   fail("mapped scalar callback differs");
          }))
        return {};
    }
    Values arguments = vectors, result;
    llvm::append_range(arguments, captures);
    auto *actual =
        invoke(block, cursor, span, "exec.collect", arguments, outputs, result);
    auto selectedDomain =
        actual ? actual->getAttrOfType<mlir::FlatSymbolRefAttr>("domain")
               : mlir::FlatSymbolRefAttr();
    auto selectedBody =
        actual ? actual->getAttrOfType<mlir::FlatSymbolRefAttr>("body")
               : mlir::FlatSymbolRefAttr();
    if (!actual || !attributes(*actual, {"domain", "body", "site"}) ||
        !selectedDomain || !selectedBody ||
        selectedDomain.getValue() != name + "_domain" ||
        selectedBody.getValue() != name + "_body" ||
        !string(*actual, "site", site)) {
      fail("mapped occurrence, domain or callback differs");
      return {};
    }
    return result;
  }
  std::optional<Values>
  primitive(mlir::Block &block, mlir::Block::iterator &cursor,
            const LocalPrimitive &expected, mlir::ValueRange operands,
            ArrayRef<LayoutLeaf> outputs, Span span, StringRef site) {
    if (!scoped) {
      fail("ordered primitives require scoped execution");
      return {};
    }
    if (!expected.bindingArguments && expected.contract == "bool.constant") {
      Values result;
      auto *actual =
          invoke(block, cursor, span, "exec.boolean", {}, outputs, result);
      if (!actual)
        return {};
      auto value = actual->getAttrOfType<mlir::BoolAttr>("value");
      if (!attributes(*actual, {"value", "site"}) || !value ||
          value.getValue() != (expected.parameters.front() == "true") ||
          !string(*actual, "site", site)) {
        if (!failure)
          fail("local Boolean literal differs");
        return {};
      }
      return result;
    }
    if (!expected.bindingArguments && expected.contract == "bool.equal") {
      auto invoke = [&](StringRef contract, mlir::ValueRange ins,
                        StringRef suffix) {
        return primitive(block, cursor, LocalPrimitive{contract.str(), {}, {}},
                         ins, outputs, span, site.str() + suffix.str());
      };
      auto both = invoke("bool.and", operands, "_both");
      if (!both)
        return {};
      auto left = invoke("bool.not", operands[0], "_left");
      if (!left)
        return {};
      auto right = invoke("bool.not", operands[1], "_right");
      if (!right)
        return {};
      Values neg{left->front(), right->front()};
      auto neither = invoke("bool.and", neg, "_neither");
      if (!neither)
        return {};
      Values either{both->front(), neither->front()};
      return invoke("bool.or", either, "");
    }
    Values result;
    auto *actual =
        invoke(block, cursor, span, "exec.apply", operands, outputs, result);
    if (!actual)
      return {};
    if (!attributes(*actual, {"binding", "parameters", "site"}) ||
        !string(*actual, "site", site) ||
        !strings(actual->getAttr("parameters"), expected.parameters)) {
      if (!failure)
        fail("ordered operation contract, parameters or site differ");
      return {};
    }
    auto ref = actual->getAttrOfType<mlir::FlatSymbolRefAttr>("binding");
    auto found = ref ? bindings.find(ref.getValue().str()) : bindings.end();
    if (found == bindings.end()) {
      fail("ordered binding is absent");
      return {};
    }
    auto &binding = *found->second;
    usedBindings.insert(found->first);
    std::vector<std::string> args;
    if (expected.bindingArguments) {
      auto roots = take(layouts.kernelArguments(expected.contract,
                                                *expected.bindingArguments));
      if (!roots)
        return {};
      args = std::move(*roots);
    } else if (StringRef(expected.contract).starts_with("field.") ||
               StringRef(expected.contract).starts_with("curve.") ||
               StringRef(expected.contract).starts_with("resource_unit.")) {
      auto type = take(protocol::encodeBoundType(
          operands.empty() ? result.front().getType() : operands[0].getType(),
          false));
      if (!type)
        return {};
      args.push_back(type->identity);
    }
    if (!protocol::bindingMatches(mlir::dyn_cast<runtime::BindingOp>(binding),
                                  {found->first, {expected.contract, args, {}}},
                                  false)) {
      fail("ordered binding selection differs");
      return {};
    }
    protocol::BindingApplication application{expected.contract, args, {}};
    auto selected = take(protocol::resolveBinding(application, false));
    if (!selected)
      return {};
    if (auto err =
            protocol::checkParameters(application, expected.parameters)) {
      failure = std::move(err);
      return {};
    }
    auto agree = [&](mlir::TypeRange actualTypes,
                     ArrayRef<protocol::BoundType> signature) {
      if (actualTypes.size() != signature.size())
        return fail("ordered binding port count differs");
      for (unsigned i = 0; i < signature.size(); ++i) {
        auto logical = take(protocol::encodeBoundType(actualTypes[i], false));
        if (!logical || !(*logical == signature[i]))
          return fail("ordered binding port type differs");
      }
      return true;
    };
    if (!agree(operands.getTypes(), selected->inputs) ||
        !agree(mlir::ValueRange(result).getTypes(), selected->outputs))
      return {};
    return result;
  }
  bool retire(mlir::Block &block, mlir::Block::iterator &cursor,
              mlir::Value value, Span span, StringRef site) {
    return bool(primitive(block, cursor,
                          LocalPrimitive{"resource_unit.consume", {}, {}},
                          value, {}, span, site));
  }
  std::vector<unsigned> oracleReceivers(const Port &port,
                                        ArrayRef<unsigned> mapping = {}) {
    std::vector<unsigned> result;
    for (auto role : port.roles)
      if (role != port.oracle->holder)
        result.push_back(mapping.empty() ? role : mapping[role]);
    llvm::sort(result);
    return result;
  }
  bool oracleShapeBounds(mlir::Operation &operation,
                         std::optional<uint64_t> maximum) {
    auto bounds = operation.getAttrOfType<mlir::DictionaryAttr>("shape_bounds");
    if (!bounds || bounds.size() != unsigned(maximum.has_value()))
      return fail("oracle shape bounds differ");
    if (maximum) {
      auto bound = bounds.getAs<mlir::IntegerAttr>("rows");
      if (!bound || !bound.getType().isUnsignedInteger(64) ||
          bound.getValue().getZExtValue() != *maximum)
        return fail("oracle row maximum differs");
    }
    return true;
  }
  bool oraclePortAttributes(mlir::Operation &operation, const Port &port,
                            ArrayRef<unsigned> mapping, bool binding) {
    unsigned holder = port.oracle->holder;
    if (!mapping.empty())
      holder = mapping[holder];
    if (!(binding
              ? attributes(operation, {"holder", "receivers", "shape_bounds"})
              : attributes(operation, {"holder", "receivers"})) ||
        !string(operation, "holder", nativeRoleName(holder)) ||
        !roleSet(operation.getAttr("receivers"),
                 oracleReceivers(port, mapping)))
      return fail("oracle port role family differs");
    return !binding ||
           oracleShapeBounds(
               operation,
               port.oracle->maximumRows
                   ? std::optional<uint64_t>(
                         port.oracle->maximumRows->dimension.closedValue())
                   : std::nullopt);
  }
  mlir::Operation *oracleComponents(mlir::Block &block,
                                    mlir::Block::iterator &cursor, Span span,
                                    mlir::Value value, const Port &port,
                                    ArrayRef<unsigned> mapping = {}) {
    auto *operation =
        next(block, cursor, span, "protocol.oracle_components", value, 2);
    auto handle =
        mlir::dyn_cast<protocol_ir::OracleHandleType>(value.getType());
    if (!operation || !handle ||
        !oraclePortAttributes(*operation, port, mapping, false) ||
        operation->getResult(0).getType() != handle.getKind().getDataType() ||
        operation->getResult(1).getType() != handle)
      return fail("oracle component view differs"), nullptr;
    return operation;
  }
  mlir::Operation *bindOracle(mlir::Block &block, mlir::Block::iterator &cursor,
                              Span span, mlir::ValueRange pair,
                              const Port &port,
                              ArrayRef<unsigned> mapping = {}) {
    auto *operation =
        next(block, cursor, span, "protocol.oracle_input", pair, 1);
    auto handle =
        mlir::dyn_cast<protocol_ir::OracleHandleType>(pair[1].getType());
    if (!operation || !handle ||
        pair[0].getType() != handle.getKind().getDataType() ||
        operation->getResult(0).getType() != handle ||
        !oraclePortAttributes(*operation, port, mapping, true))
      return fail("oracle input binding differs"), nullptr;
    return operation;
  }
  bool body(const Declaration &decl, const Body &source, mlir::Block &block,
            const mathematical::Availability *availability, bool region = false,
            unsigned forwarded = 0) {
    auto check = [&] {
      return contents(decl, source, block, availability, region, forwarded);
    };
    if (source.mode == Body::Mode::Local) {
      auto function = mlir::dyn_cast<mlir::func::FuncOp>(block.getParentOp());
      return (function && withScoped(function, check)) ||
             fail("expected scoped source function");
    }
    return check();
  }
  bool contents(const Declaration &decl, const Body &source, mlir::Block &block,
                const mathematical::Availability *availability, bool region,
                unsigned forwarded) {
    auto cursor = block.begin();
    std::vector<Values> values(source.values.size());
    unsigned argument = scoped ? 1 : 0;
    auto bind = [&](unsigned i, Values native, bool exact = true) -> bool {
      auto layout = take(layouts.get(source.values[i].type));
      if (!layout ||
          !types(mlir::ValueRange(native).getTypes(), (**layout).leaves))
        return false;
      if (availability)
        for (auto value : native) {
          auto found = availability->values.find(value);
          if (found == availability->values.end() ||
              (exact &&
               found->second.count() != source.values[i].components.size()))
            return fail("participant availability differs");
          for (auto role : source.values[i].components)
            if (role >= found->second.size() || !found->second[role])
              return fail("participant availability differs");
        }
      values[i] = std::move(native);
      return true;
    };
    for (unsigned i = 0; i < source.inputs; ++i) {
      if (!region && source.mode == Body::Mode::Protocol &&
          decl.inputs[i].oracle) {
        if (argument > block.getNumArguments() ||
            block.getNumArguments() - argument < 2)
          return fail("oracle input pair is incomplete");
        auto *joined =
            bindOracle(block, cursor, decl.inputs[i].span,
                       block.getArguments().slice(argument, 2), decl.inputs[i]);
        if (!joined || !bind(i, Values(joined->getResults())))
          return false;
        argument += 2;
        continue;
      }
      auto layout = take(layouts.get(source.values[i].type));
      if (!layout)
        return false;
      Values input;
      for (unsigned j = 0; j < (**layout).leaves.size(); ++j) {
        if (argument >= block.getNumArguments())
          return fail("block input layout is incomplete");
        input.push_back(block.getArgument(argument++));
      }
      if (!bind(i, std::move(input)))
        return false;
    }
    Values services;
    for (const auto &port : source.services) {
      if (argument >= block.getNumArguments())
        return fail("missing managed service argument");
      auto value = block.getArgument(argument++);
      auto type =
          mlir::dyn_cast<protocol_ir::ServiceReferenceType>(value.getType());
      if (!type || type.getContract() != port.contract)
        return fail("managed service contract differs");
      if (!availability)
        return fail("managed service outside protocol body");
      auto found = availability->values.find(value);
      if (found == availability->values.end() || found->second.count() != 1 ||
          port.owner >= found->second.size() || !found->second[port.owner])
        return fail("managed service owner differs");
      services.push_back(value);
    }
    if (argument != block.getNumArguments())
      return fail("block has extra arguments");
    const auto &proof = project.entry().proof();
    if (!region && proof && decl.id.index == project.protocol().id.index &&
        proof->target) {
      const auto &clause = decl.specifications[*proof->target];
      const auto &relation =
          project.declarations()[clause.subject.relation.index];
      Values operands;
      std::vector<std::string> selectors;
      for (const auto &operand : clause.subject.operands) {
        auto slice = take(layouts.select(decl, operand));
        if (!slice)
          return false;
        for (unsigned i = 0; i < slice->layout->leaves.size(); ++i) {
          if (slice->offset + i >= block.getNumArguments())
            return fail("statement operand is outside the entry signature");
          operands.push_back(block.getArgument(slice->offset + i));
          selectors.push_back(operand.anchor ? "anchor"
                                             : nativeRoleName(operand.role));
        }
      }
      auto acceptance = take(layouts.select(decl, proof->acceptance));
      if (!acceptance)
        return false;
      auto *actual =
          next(block, cursor, clause.span, "protocol.statement", operands, 0);
      if (!actual)
        return false;
      if (!attributes(*actual,
                      {"relation", "selectors", "acceptance", "target"}))
        return fail("selected Entry statement attributes differ");
      auto symbol = actual->getAttrOfType<mlir::FlatSymbolRefAttr>("relation");
      auto output = actual->getAttrOfType<mlir::IntegerAttr>("acceptance");
      if (!symbol || symbol.getValue() != relation.symbol || !output ||
          output.getInt() != acceptance->offset ||
          !string(*actual, "target", clause.name) ||
          !strings(actual->getAttr("selectors"), selectors))
        return fail("selected Entry statement differs");
    }
    auto flatten = [&](ArrayRef<ValueId> ids) {
      Values result;
      for (auto id : ids)
        llvm::append_range(result, values[id.index]);
      return result;
    };
    for (auto &op : source.operations) {
      std::vector<std::shared_ptr<const Layout>> resultLayouts;
      std::vector<LayoutLeaf> leaves;
      for (auto id : op.results) {
        auto layout = take(layouts.get(source.values[id.index].type));
        if (!layout)
          return false;
        llvm::append_range(leaves, (**layout).leaves);
        resultLayouts.push_back(*layout);
      }
      Values result;
      auto site = nativeSiteName(op.site.value_or(""), siteOrdinal++);
      if (auto *projection = std::get_if<Projection>(&op.action)) {
        auto selected =
            take(layouts.get(source.values[projection->input.index].type));
        if (!selected)
          return false;
        unsigned offset = 0;
        for (auto field : projection->path) {
          offset += (**selected).fields[field].offset;
          selected = (**selected).fields[field].layout;
        }
        auto &input = values[projection->input.index];
        result.append(input.begin() + offset,
                      input.begin() + offset + (**selected).leaves.size());
      } else if (auto *construct = std::get_if<Construct>(&op.action)) {
        auto input = flatten(construct->operands);
        if (construct->kind == Construct::Kind::Unpack) {
          auto origin = take(layouts.get(
              source.values[construct->operands.front().index].type));
          if (!origin)
            return false;
          if ((**origin).custody) {
            if (!retire(block, cursor, input.front(), op.span,
                        site + "_unpack"))
              return false;
            input.erase(input.begin());
          }
          result = std::move(input);
        } else {
          if (resultLayouts.front()->custody) {
            auto created = primitive(
                block, cursor, LocalPrimitive{"resource_unit.create", {}, {}},
                {}, ArrayRef<LayoutLeaf>(leaves).take_front(), op.span,
                site + "_create");
            if (!created)
              return false;
            llvm::append_range(result, *created);
          }
          if (source.values[op.results.front().index].type.kind ==
              Type::Kind::Variant) {
            auto label =
                alternative(*resultLayouts.front(), construct->alternative);
            if (!label)
              return false;
            auto injected = variant(block, cursor, op.span, input,
                                    leaves.back(), *label, site);
            if (!injected)
              return false;
            result.push_back(injected->front());
          } else
            llvm::append_range(result, input);
        }
      } else if (auto *consume = std::get_if<Consume>(&op.action)) {
        auto input =
            take(layouts.get(source.values[consume->input.index].type));
        if (!input)
          return false;
        for (unsigned i = 0; i < (**input).leaves.size(); ++i)
          if ((**input).leaves[i].data() &&
              StringRef(*(**input).leaves[i].data())
                  .starts_with("resource_unit:") &&
              !retire(block, cursor, values[consume->input.index][i], op.span,
                      site + "_" + std::to_string(i)))
            return false;
      } else if (auto *math = std::get_if<MathValue>(&op.action)) {
        auto operands = flatten(math->operands);
        std::optional<PackedLayout> packed;
        if (math->identity == MathematicalIdentity::ContainerAt &&
            source.values[math->operands.front().index].type.domain ==
                "sequence") {
          packed = take(
              layouts.packed(source.values[op.results.front().index].type));
          if (!packed)
            return false;
        }
        auto *actual = next(block, cursor, op.span, "", operands,
                            packed ? 1 : leaves.size());
        if (!actual)
          return false;
        auto interface = mlir::dyn_cast<MathematicalOpInterface>(actual);
        if (!interface || interface.getMathematicalIdentity() != math->identity)
          return fail("mathematical operation identity differs");
        auto dependencies = interface.getOperandDependencies(0);
        if (dependencies.size() != operands.size())
          return fail("mathematical dependency arity differs");
        for (unsigned i = 0; i < dependencies.size(); ++i)
          if (dependencies[i] != i)
            return fail("mathematical dependency order differs");
        if (math->identity == MathematicalIdentity::VectorLength) {
          auto axis = actual->getAttrOfType<mlir::IntegerAttr>("axis");
          if (!attributes(*actual, {"axis"}) || !axis ||
              !axis.getType().isSignlessInteger(64) || axis.getInt() != 0)
            return fail("vector length axis differs");
        } else if (math->identity == MathematicalIdentity::IndexConstant) {
          auto literal =
              math->literal.empty()
                  ? std::to_string(
                        math->staticArguments.front().dimension.closedValue())
                  : math->literal;
          if (!attributes(*actual, {"value"}) ||
              !string(*actual, "value", literal))
            return fail("index literal differs");
        } else if (math->identity == MathematicalIdentity::FieldConstant) {
          if (!attributes(*actual, {"value"}) ||
              !string(*actual, "value", math->literal))
            return fail("field literal differs");
        } else if (math->identity == MathematicalIdentity::BooleanConstant) {
          auto value = actual->getAttrOfType<mlir::IntegerAttr>("value");
          if (!attributes(*actual, {"value"}) || !value ||
              value.getValue().getBoolValue() != (math->literal == "true"))
            return fail("Boolean literal differs");
        } else if (math->identity == MathematicalIdentity::BooleanEqual) {
          auto cmp = mlir::dyn_cast<mlir::arith::CmpIOp>(actual);
          if (!attributes(*actual, {"predicate"}) || !cmp ||
              cmp.getPredicate() != mlir::arith::CmpIPredicate::eq)
            return fail("Boolean comparison differs");
        } else if (math->identity == MathematicalIdentity::ArrayAt ||
                   math->identity == MathematicalIdentity::PolynomialSum) {
          StringRef key = math->identity == MathematicalIdentity::ArrayAt
                              ? "index"
                              : "count";
          auto value = actual->getAttrOfType<mlir::IntegerAttr>(key);
          if (!attributes(*actual, {key}) || !value ||
              !value.getType().isSignlessInteger(64) ||
              value.getValue().getZExtValue() !=
                  math->staticArguments[2].dimension.closedValue())
            return fail("mathematical static coordinate differs");
        } else if (math->identity ==
                       MathematicalIdentity::PolynomialEvaluateDomain ||
                   math->identity ==
                       MathematicalIdentity::PolynomialInterpolate) {
          if (!attributes(*actual, {"points"}) ||
              !strings(actual->getAttr("points"), math->parameters))
            return fail("polynomial domain differs");
        } else if (!attributes(*actual, {}))
          return fail("extra mathematical attributes");
        result = Values(actual->getResults());
        if (packed &&
            !types(actual->getResultTypes(), {packed->carrier.spelling()}))
          return fail("total sequence result carrier differs");
        if (packed && packed->product) {
          auto flat = unpackMathematical(block, cursor, result.front(), leaves,
                                         op.span);
          if (!flat)
            return false;
          result = std::move(*flat);
        }
      } else if (auto *local = std::get_if<LocalPrimitive>(&op.action)) {
        auto operands = flatten(local->operands);
        auto outputs = leaves;
        std::optional<PackedLayout> packed;
        if (isSequenceKernel(local->contract)) {
          if (!local->bindingArguments || local->bindingArguments->size() != 1)
            return fail("sequence binding requires its element type");
          packed = take(layouts.packed(local->bindingArguments->front()));
          if (!packed)
            return false;
          if (local->contract == "sequence.append" && packed->product) {
            const auto &fields = values[local->operands[1].index];
            auto packedValue = variant(block, cursor, op.span, fields,
                                       packed->carrier.spelling(),
                                       packed->alternative, site + "_pack");
            if (!packedValue)
              return false;
            operands = values[local->operands[0].index];
            operands.push_back(packedValue->front());
          }
          if (local->contract == "sequence.at")
            outputs = {packed->carrier.spelling()};
        }
        auto checked =
            primitive(block, cursor, *local, operands, outputs, op.span, site);
        if (!checked)
          return false;
        result = std::move(*checked);
        if (packed && packed->product && local->contract == "sequence.at") {
          auto flat = unpack(result.front(), leaves, packed->alternative,
                             op.span, site + "_unpack");
          if (!flat)
            return false;
          result = std::move(*flat);
        }
      } else if (auto *call = std::get_if<HelperCall>(&op.action)) {
        auto &target = project.declarations()[call->callee.index];
        bool owned = target.kind == Declaration::Kind::Local &&
                     source.mode == Body::Mode::Protocol;
        bool math = target.kind == Declaration::Kind::Math;
        auto input = flatten(call->operands);
        auto *actual = scoped
                           ? invoke(block, cursor, op.span,
                                    math ? "exec.compute" : "func.call", input,
                                    leaves, result)
                           : next(block, cursor, op.span,
                                  owned ? "protocol.local_call" : "func.call",
                                  input, leaves.size());
        if (!actual)
          return false;
        auto callee = actual->getAttrOfType<mlir::FlatSymbolRefAttr>("callee");
        SmallVector<StringRef> attrs{"callee"};
        if (owned)
          attrs.append({"site", "role"});
        else if (scoped)
          attrs.push_back(math ? "site" : "runtime.site");
        if (!callee || callee.getValue() != target.symbol ||
            !attributes(*actual, attrs) ||
            ((owned || scoped) &&
             !string(*actual, scoped && !math ? "runtime.site" : "site",
                     site)) ||
            (owned && (!call->owner ||
                       !string(*actual, "role", nativeRoleName(*call->owner)))))
          return fail("call target, mode, owner or site differs");
        if (!scoped)
          result = Values(actual->getResults());
      } else if (auto *finite = std::get_if<FiniteComputation>(&op.action)) {
        if (scoped ? scoped->atEnd() : cursor == block.end())
          return fail("omitted finite computation");
        auto *occurrence = scoped ? scoped->peek() : &*cursor;
        if (scoped && !account())
          return false;
        auto first = cursor;
        auto compared = take(compareFinite(
            project, source, *finite,
            source.values[op.results.front().index].type, values, block, cursor,
            finiteDefinitions, usedFiniteDefinitions, layouts,
            "finite_" + decl.symbol + "_" + site, site, limits,
            report.operations, remaining, scoped));
        if (!compared)
          return false;
        if (scoped) {
          accounted = scoped->consumed();
          if (!record(*occurrence, op.span))
            return false;
        } else
          for (auto emitted = first; emitted != cursor; ++emitted)
            if (!record(*emitted, op.span))
              return false;
        result = std::move(*compared);
      } else if (auto *bulk = std::get_if<BulkApplication>(&op.action)) {
        auto &target = project.declarations()[bulk->callee.index];
        if (source.mode != Body::Mode::Local ||
            target.kind != Declaration::Kind::Math)
          return fail("map mode or helper kind differs");
        auto compared = map(target, *bulk, flatten(bulk->operands), leaves,
                            block, cursor, op.span, site);
        if (!compared)
          return false;
        result = std::move(*compared);
      } else if (auto *query = std::get_if<ServiceQuery>(&op.action)) {
        const auto &port = source.services[query->service.index];
        SmallVector<mlir::Value> operands{services[query->service.index]};
        if (query->bound) {
          if (!query->bound->isClosed())
            return fail("index domain is not closed");
          auto *bound = next(block, cursor, op.span, "data.index", {}, 1);
          if (!bound)
            return false;
          if (!attributes(*bound, {"value"}) ||
              !string(*bound, "value",
                      std::to_string(query->bound->closedValue())) ||
              !types(bound->getResultTypes(), leaves))
            return fail("index query domain differs");
          operands.push_back(bound->getResult(0));
        }
        auto *actual =
            next(block, cursor, op.span, "protocol.query", operands, 1);
        if (!actual)
          return false;
        if (!attributes(*actual, {"method", "owner", "site"}) ||
            !string(*actual, "method", query->bound ? "index" : "draw") ||
            !string(*actual, "owner", nativeRoleName(port.owner)) ||
            !string(*actual, "site", site))
          return fail("managed query method, owner or occurrence differs");
        result = Values(actual->getResults());
      } else if (auto *completion =
                     std::get_if<ProtocolCompletion>(&op.action)) {
        auto input = values[completion->condition.index];
        llvm::append_range(input, flatten(completion->values));
        mathematical::NativeTypePolicies policies(module);
        SmallVector<mlir::Type> successors;
        SmallVector<unsigned> positions;
        for (unsigned i = 1; i < input.size(); ++i) {
          auto policy = policies.get(input[i].getType());
          if (!policy)
            return fail("completion leaf has no native policy");
          if (policy->affine) {
            positions.push_back(i);
            successors.push_back(input[i].getType());
          }
        }
        auto *actual = next(block, cursor, op.span, "protocol.finish_if", input,
                            successors.size());
        if (!actual)
          return false;
        if (!attributes(*actual, {"owner", "site"}) ||
            !string(*actual, "owner", nativeRoleName(completion->owner)) ||
            !string(*actual, "site", site) ||
            actual->getResultTypes() != mlir::TypeRange(successors))
          return fail("completion owner, site or affine successors differ");
        for (unsigned i = 0; i < positions.size(); ++i)
          input[positions[i]] = actual->getResult(i);
        result.append(input.begin() + 1, input.end());
      } else if (auto *check = std::get_if<Require>(&op.action)) {
        const bool protocol = source.mode == Body::Mode::Protocol;
        if (source.mode == Body::Mode::Math ||
            protocol != check->owner.has_value())
          return fail("require owner does not match its body mode");
        if (protocol) {
          auto *actual = next(block, cursor, op.span, "protocol.guard",
                              values[check->condition.index], 0);
          if (!actual || !attributes(*actual, {"owner", "site"}) ||
              !string(*actual, "owner", nativeRoleName(*check->owner)) ||
              !string(*actual, "site", site))
            return fail("require owner or occurrence differs");
        } else {
          Values outputs;
          auto arm = [&](mlir::func::CallOp call, unsigned index) {
            auto function = this->region(call, op.span);
            if (!function || function.getNumArguments() != 1 ||
                !mlir::cast<exec::OutcomeType>(
                     function.getResultTypes().front())
                     .getPayload()
                     .empty())
              return fail("require branch signature differs");
            return withScoped(function, [&] {
              auto cursor = function.front().begin();
              return index
                         ? stop(op.span, "reject", site + "_reject")
                         : finish(function.front(), cursor, op.span, {}, true);
            });
          };
          if (!scoped->conditional(values[check->condition.index].front(), {},
                                   site, arm, outputs) ||
              !outputs.empty() || !account())
            return fail("require control or outcome differs");
        }
      } else if (auto *application =
                     std::get_if<ProtocolApplication>(&op.action)) {
        const auto &target = project.declarations()[application->callee.index];
        Values operands;
        for (unsigned i = 0; i < application->operands.size(); ++i) {
          const auto &input = values[application->operands[i].index];
          if (target.inputs[i].oracle) {
            auto *parts =
                oracleComponents(block, cursor, op.span, input.front(),
                                 target.inputs[i], application->roles);
            if (!parts)
              return false;
            llvm::append_range(operands, parts->getResults());
          } else
            llvm::append_range(operands, input);
        }
        for (auto service : application->services)
          operands.push_back(services[service.index]);
        unsigned count = leaves.size();
        for (const auto &port : target.outputs)
          count += port.oracle.has_value();
        auto *actual =
            next(block, cursor, op.span, "protocol.apply", operands, count);
        if (!actual)
          return false;
        auto callee = actual->getAttrOfType<mlir::FlatSymbolRefAttr>("callee");
        std::vector<std::string> mapped;
        for (auto role : application->roles)
          mapped.push_back(nativeRoleName(role));
        if (!attributes(*actual, {"callee", "site", "roles"}) || !callee ||
            callee.getValue() != target.symbol ||
            !string(*actual, "site", site) ||
            !strings(actual->getAttr("roles"), mapped))
          return fail(
              "protocol application target, role substitution or site differs");
        unsigned offset = 0;
        for (unsigned i = 0; i < target.outputs.size(); ++i) {
          const auto &port = target.outputs[i];
          unsigned count = port.oracle ? 2 : resultLayouts[i]->leaves.size();
          auto output = actual->getResults().slice(offset, count);
          if (port.oracle) {
            auto *joined = bindOracle(block, cursor, op.span, output, port,
                                      application->roles);
            if (!joined)
              return false;
            result.push_back(joined->getResult(0));
          } else
            llvm::append_range(result, output);
          offset += count;
        }
      } else if (std::holds_alternative<OracleSequenceEmpty>(op.action)) {
        auto *actual = next(block, cursor, op.span,
                            "protocol.oracle_sequence_empty", {}, 1);
        if (!actual || !attributes(*actual, {}))
          return fail("empty oracle sequence differs");
        result = Values(actual->getResults());
      } else if (auto *append = std::get_if<OracleSequenceAppend>(&op.action)) {
        auto *actual =
            next(block, cursor, op.span, "protocol.oracle_sequence_append",
                 flatten({append->prefix, append->element}), 1);
        if (!actual || !attributes(*actual, {"roles", "site"}) ||
            !roleSet(actual->getAttr("roles"), append->roles) ||
            !string(*actual, "site", site))
          return fail("oracle sequence append family or occurrence differs");
        result = Values(actual->getResults());
      } else if (auto *at = std::get_if<OracleSequenceAt>(&op.action)) {
        auto *actual =
            next(block, cursor, op.span, "protocol.oracle_sequence_at",
                 flatten({at->input, at->position}), 1);
        if (!actual || !attributes(*actual, {"roles", "site"}) ||
            !roleSet(actual->getAttr("roles"), at->roles) ||
            !string(*actual, "site", site))
          return fail("oracle sequence selection family or occurrence differs");
        result = Values(actual->getResults());
      } else if (auto *length = std::get_if<OracleSequenceLength>(&op.action)) {
        auto *actual =
            next(block, cursor, op.span, "protocol.oracle_sequence_length",
                 values[length->input.index], 1);
        if (!actual || !attributes(*actual, {}))
          return fail("oracle sequence length differs");
        result = Values(actual->getResults());
      } else if (auto *send = std::get_if<OracleSend>(&op.action)) {
        auto *actual = next(block, cursor, op.span, "protocol.oracle_send",
                            flatten({send->data, send->rows}), 1);
        if (!actual)
          return false;
        if (!attributes(*actual, {"sender", "receivers", "site", "shape_names",
                                  "shape_bounds"}) ||
            !string(*actual, "sender", nativeRoleName(send->holder)) ||
            !roleSet(actual->getAttr("receivers"), send->receivers) ||
            !string(*actual, "site", site))
          return fail("oracle send roles or occurrence differ");
        auto dimensions = actual->getAttrOfType<mlir::ArrayAttr>("shape_names");
        if (!dimensions || dimensions.size() != 1 ||
            dimensions[0] !=
                mlir::StringAttr::get(actual->getContext(), "rows") ||
            !oracleShapeBounds(*actual, send->maximum
                                            ? std::optional<uint64_t>(
                                                  send->maximum->closedValue())
                                            : std::nullopt))
          return fail("oracle send named shape differs");
        result = Values(actual->getResults());
      } else if (auto *query = std::get_if<OracleQuery>(&op.action)) {
        auto packed =
            take(layouts.packed(source.values[op.results.front().index].type));
        if (!packed)
          return false;
        auto *actual = next(block, cursor, op.span, "protocol.oracle_query",
                            flatten({query->handle, query->position}), 1);
        if (!actual)
          return false;
        if (!attributes(*actual, {"owner", "site"}) ||
            !string(*actual, "owner", nativeRoleName(query->owner)) ||
            !string(*actual, "site", site))
          return fail("oracle query owner or occurrence differs");
        auto answer =
            protocol::decodeBoundType(actual->getContext(), packed->carrier);
        if (!answer || actual->getResult(0).getType() != answer)
          return fail("oracle answer carrier differs");
        result = Values(actual->getResults());
        if (packed->product) {
          auto flat = unpackMathematical(block, cursor, result.front(), leaves,
                                         op.span);
          if (!flat)
            return false;
          result = std::move(*flat);
        }
      } else if (auto *contents = std::get_if<OracleContents>(&op.action)) {
        auto *actual = next(block, cursor, op.span, "protocol.oracle_contents",
                            values[contents->input.index], 1);
        if (!actual || !attributes(*actual, {"owner"}) ||
            !string(*actual, "owner", nativeRoleName(contents->owner)))
          return fail("oracle data owner differs");
        result = Values(actual->getResults());
      } else if (auto *rows = std::get_if<OracleRows>(&op.action)) {
        auto *actual = next(block, cursor, op.span, "protocol.oracle_shape",
                            values[rows->input.index], 1);
        if (!actual || !attributes(*actual, {"dimension"}) ||
            !string(*actual, "dimension", "rows"))
          return fail("oracle row view differs");
        result = Values(actual->getResults());
      } else if (auto *forget = std::get_if<OracleForgetRows>(&op.action)) {
        auto *actual =
            next(block, cursor, op.span, "protocol.oracle_forget_shape",
                 values[forget->input.index], 1);
        if (!actual || !attributes(*actual, {}))
          return fail("oracle shape refinement differs");
        result = Values(actual->getResults());
      } else if (auto *exchange = std::get_if<Exchange>(&op.action)) {
        auto &input = values[exchange->payload.index];
        if (leaves.empty() || input.size() != leaves.size())
          return fail(
              "message has no native occurrence or its payload layout differs");
        for (unsigned i = 0; i < leaves.size(); ++i) {
          auto *sent =
              next(block, cursor, op.span, "protocol.exchange", input[i], 1);
          if (!sent)
            return false;
          if (!attributes(*sent, {"sender", "receiver", "site"}) ||
              !string(*sent, "sender", nativeRoleName(exchange->sender)) ||
              !string(*sent, "receiver", nativeRoleName(exchange->receiver)) ||
              !string(*sent, "site", site + "_" + std::to_string(i)))
            return fail("message occurrence differs");
          auto *received =
              next(block, cursor, op.span, "protocol.restrict_roles",
                   sent->getResult(0), 1);
          if (!received)
            return false;
          if (!attributes(*received, {"roles"}) ||
              !roleSet(received->getAttr("roles"), {exchange->receiver}))
            return fail("message receiver restriction differs");
          result.push_back(received->getResult(0));
        }
      } else if (auto *assembly = std::get_if<RoleAssembly>(&op.action)) {
        for (unsigned i = 0; i < leaves.size(); ++i) {
          Values components;
          for (auto operand : assembly->operands)
            components.push_back(values[operand.index][i]);
          auto *actual = next(block, cursor, op.span, "protocol.assemble_roles",
                              components, 1);
          if (!actual)
            return false;
          if (!attributes(*actual, {"roles"}) ||
              !roleSet(actual->getAttr("roles"), assembly->roles))
            return fail("role component assembly differs");
          result.push_back(actual->getResult(0));
        }
      } else if (auto *restriction = std::get_if<Restriction>(&op.action)) {
        for (auto input : values[restriction->input.index]) {
          auto *actual =
              next(block, cursor, op.span, "protocol.restrict_roles", input, 1);
          if (!actual)
            return false;
          if (!attributes(*actual, {"roles"}) ||
              !roleSet(actual->getAttr("roles"), restriction->roles))
            return fail("role restriction differs");
          result.push_back(actual->getResult(0));
        }
      } else if (auto *repeat = std::get_if<ProtocolRepeat>(&op.action)) {
        auto input = values[repeat->count.index];
        llvm::append_range(input, flatten(repeat->carried));
        llvm::append_range(input, flatten(repeat->captures));
        for (auto service : repeat->services)
          input.push_back(services[service.index]);
        auto *actual = next(block, cursor, op.span, "protocol.repeat", input,
                            leaves.size(), 1);
        if (!actual)
          return false;
        auto maximum = actual->getAttrOfType<mlir::IntegerAttr>("maximum");
        auto carried = actual->getAttrOfType<mlir::IntegerAttr>("carried");
        auto carriedRoles =
            actual->getAttrOfType<mlir::ArrayAttr>("carried_roles");
        if (!attributes(*actual, {"site", "carried", "maximum", "roles",
                                  "carried_roles"}) ||
            !string(*actual, "site", site) || !maximum ||
            !maximum.getType().isSignlessInteger(64) ||
            maximum.getValue().getZExtValue() !=
                repeat->maximum.closedValue() ||
            !carried || !carried.getType().isSignlessInteger(64) ||
            carried.getValue().getZExtValue() != leaves.size() ||
            !roleSet(actual->getAttr("roles"), repeat->roles) ||
            !carriedRoles || carriedRoles.size() != leaves.size())
          return fail(
              "repeat site, maximum, roles or carried interface differs");
        unsigned flat = 0;
        for (unsigned i = 0; i < op.results.size(); ++i)
          for (unsigned j = 0; j < resultLayouts[i]->leaves.size(); ++j)
            if (!roleSet(carriedRoles[flat++],
                         source.values[op.results[i].index].components))
              return fail("repeat carried roles differ");
        if (!llvm::hasSingleElement(actual->getRegion(0)) ||
            !body(decl, *repeat->region, actual->getRegion(0).front(),
                  availability, true))
          return false;
        result = Values(actual->getResults());
      } else if (auto *control = std::get_if<LocalControl>(&op.action)) {
        auto input = flatten(control->operands);
        bool match = control->kind == LocalControl::Kind::Match;
        std::vector<std::string> labels;
        if (match) {
          auto subject = take(
              layouts.get(source.values[control->operands.front().index].type));
          if (!subject)
            return false;
          for (const auto &name : control->alternatives) {
            auto label = alternative(**subject, name);
            if (!label)
              return false;
            labels.push_back(std::move(*label));
          }
          if ((**subject).custody) {
            if (!retire(block, cursor, input.front(), op.span, site + "_match"))
              return false;
            input.erase(input.begin());
          }
        }
        bool loop = control->kind == LocalControl::Kind::For;
        if (loop && input.size() < 2 + leaves.size())
          return fail("loop state interface is incomplete");
        unsigned forwarded = loop ? input.size() - 2 - leaves.size() : 0;
        auto arm = [&](mlir::func::CallOp call, unsigned index) {
          auto function = this->region(call, op.span);
          if (!function || index >= control->regions.size() ||
              !types(mlir::cast<exec::OutcomeType>(
                         function.getResultTypes().front())
                         .getPayload(),
                     leaves))
            return fail("control region result signature differs");
          return body(decl, *control->regions[index], function.front(), nullptr,
                      true, forwarded);
        };
        bool agrees =
            match  ? scoped->match(input.front(),
                                   mlir::ValueRange(input).drop_front(), labels,
                                   site, arm, result)
            : loop ? scoped->loop(
                         input[0], input[1],
                         mlir::ValueRange(input).slice(2, leaves.size()),
                         mlir::ValueRange(input).drop_front(2 + leaves.size()),
                         false, site, arm, result)
                   : scoped->conditional(input.front(),
                                         mlir::ValueRange(input).drop_front(),
                                         site, arm, result);
        if (!agrees || !account())
          return fail("control occurrence, transfer or state differs");
      } else
        return fail("source operation has no comparison rule");
      if (result.size() != leaves.size())
        return fail("operation result layout differs");
      // Logical products and abstract helper dependencies may conservatively
      // narrow their leaves. Exact operation/operand matching already fixes
      // derived native availability; it must contain the source guarantee.
      bool derived = std::holds_alternative<OracleSequenceEmpty>(op.action) ||
                     std::holds_alternative<OracleSequenceLength>(op.action) ||
                     std::holds_alternative<MathValue>(op.action) ||
                     std::holds_alternative<Construct>(op.action) ||
                     std::holds_alternative<Projection>(op.action) ||
                     std::holds_alternative<ProtocolCompletion>(op.action);
      if (auto *call = std::get_if<HelperCall>(&op.action))
        derived = !call->owner;
      unsigned offset = 0;
      for (unsigned i = 0; i < op.results.size(); ++i) {
        const auto count = resultLayouts[i]->leaves.size();
        if (!bind(op.results[i].index,
                  Values(result.begin() + offset,
                         result.begin() + offset + count),
                  !derived))
          return false;
        offset += count;
      }
    }
    if (scoped) {
      if (source.stopped)
        return stop(decl.span, source.stopReason,
                    "stop" + std::to_string(siteOrdinal++));
      auto results = flatten(source.results);
      if (forwarded > results.size() ||
          forwarded > block.getNumArguments() - 1 ||
          mlir::ValueRange(results).take_back(forwarded) !=
              block.getArguments().take_back(forwarded))
        return fail("loop invariant forwarding differs");
      results.resize(results.size() - forwarded);
      return finish(block, cursor, decl.span, results, region);
    }
    if (source.stopped)
      return fail("stopped body requires scoped execution");
    Values returned;
    for (unsigned i = 0; i < source.results.size(); ++i) {
      const auto &value = values[source.results[i].index];
      if (!region && source.mode == Body::Mode::Protocol &&
          decl.outputs[i].oracle) {
        auto *parts = oracleComponents(block, cursor, decl.outputs[i].span,
                                       value.front(), decl.outputs[i]);
        if (!parts)
          return false;
        llvm::append_range(returned, parts->getResults());
      } else
        llvm::append_range(returned, value);
    }
    auto *ret =
        next(block, cursor, decl.span,
             region && source.mode == Body::Mode::Protocol ? "protocol.yield"
             : source.mode == Body::Mode::Protocol         ? "protocol.return"
                                                           : "func.return",
             returned, 0);
    return (ret && attributes(*ret, {}) && cursor == block.end()) ||
           fail("extra return attributes or operations after source body");
  }

  bool construction(const Declaration &definition,
                    protocol_ir::ConstructionOp record) {
    if (!record)
      return fail("missing construction selection");
    mlir::SymbolTableCollection symbols;
    auto plan = take(protocol::readConstructionPlan(record, symbols));
    if (!plan)
      return false;
    const auto &source = *definition.construction;
    const auto &target = project.declarations()[definition.target->index];
    if (plan->symbol.getValue() != definition.symbol ||
        plan->target.getValue() != target.symbol ||
        plan->provider != typeIdentity(*source.provider) ||
        plan->suite != source.suite || plan->nativeBase != source.nativeBase ||
        plan->rootOnly !=
            (definition.proofFormat.has_value() || source.nativeBase) ||
        (plan->root == protocol::ConstructionPlan::Root::Local) !=
            (source.root == ConstructionDefinition::Root::Local) ||
        plan->rules.size() != source.rules.size() ||
        plan->applications.size() != source.applications.size())
      return fail("construction identity or root differs");
    for (auto [expected, actual] :
         zip(source.applications, plan->applications)) {
      std::string site;
      for (const auto &part : expected.path) {
        auto label = nativeSiteName(part, 0);
        site = site.empty()
                   ? label
                   : mathematical::expandedApplicationSite(site, label);
      }
      if (!charge(site.size() + 1) || actual.site != site ||
          actual.construction.getValue() !=
              project.declarations()[expected.construction.index].symbol)
        return fail("construction application differs");
    }
    if (bool(plan->initializer) != bool(source.initializer) ||
        (source.initializer &&
         plan->initializer.getValue() !=
             project.declarations()[source.initializer->declaration.index]
                 .symbol))
      return fail("construction initializer differs");
    auto state = take(layouts.get(*source.state));
    if (!state || !types(plan->state, (*state)->leaves))
      return false;
    std::vector<unsigned> offsets{0};
    for (const auto &port : target.inputs) {
      auto layout = take(layouts.get(port.type));
      if (!layout)
        return false;
      offsets.push_back(offsets.back() + (*layout)->leaves.size());
    }
    SmallVector<unsigned> replaced;
    for (auto port : source.services)
      replaced.push_back(offsets.back() + port);
    if (plan->services != replaced)
      return fail("construction replacement authority differs");
    if (bool(plan->codec) != bool(source.codec))
      return fail("construction record format differs");
    if (source.codec) {
      const auto &expected = *source.codec;
      const auto &actual = *plan->codec;
      auto record = take(layouts.get(expected.record));
      if (!record || !types(actual.record, (*record)->leaves))
        return false;
      SmallVector<unsigned> inputs;
      for (unsigned port : expected.inputs)
        for (unsigned i = offsets[port]; i < offsets[port + 1]; ++i)
          inputs.push_back(i);
      if (actual.provider != typeIdentity(expected.provider) ||
          actual.inputs != inputs)
        return fail("construction codec or layout inputs differ");
      for (auto [method, reference] :
           {std::pair{&expected.initialize, actual.initialize},
            std::pair{&expected.write, actual.write},
            std::pair{&expected.finish, actual.finish}})
        if (reference.getValue() !=
            project.declarations()[method->target.declaration.index].symbol)
          return fail("construction codec method differs");
    }
    for (auto [expected, actual] : zip(source.rules, plan->rules)) {
      if (!charge(expected.path.size() + expected.inputs.size() + 1))
        return false;
      const auto &handler = project.declarations()[expected.handler.index];
      if (actual.kind != expected.kind ||
          actual.handler.getValue() != handler.symbol)
        return fail("construction handler selection differs");
      if (expected.kind == ConstructionRule::Kind::Start) {
        SmallVector<unsigned> ports;
        for (auto port : expected.inputs)
          for (unsigned i = offsets[port]; i < offsets[port + 1]; ++i)
            ports.push_back(i);
        if (ports != actual.inputs)
          return fail("construction start inputs differ");
        continue;
      }
      auto layout = take(layouts.get(*expected.payload));
      if (!layout || !types(actual.payload, (*layout)->leaves))
        return false;
      if (expected.chunks) {
        auto chunks = take(layouts.get(*expected.chunks));
        if (!chunks || !types(actual.chunks, (*chunks)->leaves))
          return false;
      } else if (!actual.chunks.empty())
        return fail("unexpected codec byte shape");
      for (auto [i, site] : enumerate(actual.sites)) {
        std::string prefix;
        for (const auto &part : ArrayRef(expected.path).drop_back()) {
          auto label = nativeSiteName(part, 0);
          prefix = prefix.empty()
                       ? label
                       : mathematical::expandedApplicationSite(prefix, label);
        }
        auto label = nativeSiteName(expected.path.back(), 0);
        if (expected.kind != ConstructionRule::Kind::Query)
          label += "_" + std::to_string(i);
        auto name = prefix.empty()
                        ? label
                        : mathematical::expandedApplicationSite(prefix, label);
        if (!charge(name.size()) || site != name)
          return fail("construction occurrence selector differs");
      }
    }
    return true;
  }

public:
  Comparator(const ClosedEntry &project, mlir::ModuleOp module,
             const Limits &limits, ArrayRef<Declaration> selected = {})
      : project(project),
        declared(selected.empty() ? project.declarations() : selected),
        module(module), limits(limits), layouts(project, limits),
        remaining(limits.work) {
    (void)!!failure;
  }
  Expected<Correspondence> run() {
    if (!module->getAttrs().empty() ||
        !llvm::hasSingleElement(*module.getBody()))
      return error("source.correspondence",
                   "expected one unadorned protocol module");
    auto native = mlir::dyn_cast<protocol_ir::ProtocolModuleOp>(
        module.getBody()->front());
    if (!native ||
        !(native->hasAttr("source_declarations")
              ? attributes(*native, {"profile", "source_declarations"})
              : attributes(*native, {"profile"})) ||
        native.getProfile() != protocol_ir::Profile::Protocol ||
        !llvm::hasSingleElement(native.getBody()))
      return error("source.correspondence", "unexpected original module");
    auto retained = inspectComponentDeclarations(project, limits);
    if (!retained)
      return retained.takeError();
    auto declarations =
        native->getAttrOfType<mlir::StringAttr>("source_declarations");
    if ((*retained == "[[],[]]" && declarations) ||
        (*retained != "[[],[]]" &&
         (!declarations || declarations.getValue() != *retained)))
      return error("source.correspondence", "source declarations differ");
    SmallVector<mlir::Operation *> functions;
    std::map<std::string, protocol_ir::ConstructionOp> constructions;
    std::map<std::string, relation::DeclareOp> relations;
    for (auto &op : native.getBody().front()) {
      auto name = op.getAttrOfType<mlir::StringAttr>("sym_name");
      if (name && name.getValue().starts_with("finite_")) {
        if (!finiteDefinitions.emplace(name.getValue().str(), &op).second)
          return error("source.correspondence",
                       "duplicate finite auxiliary symbol");
        continue;
      }
      if (auto record = mlir::dyn_cast<protocol_ir::ConstructionOp>(op)) {
        if (!constructions.emplace(record.getSymName().str(), record).second)
          return error("source.correspondence",
                       "duplicate construction selection");
      } else if (auto declaration = mlir::dyn_cast<relation::DeclareOp>(op)) {
        if (!relations.emplace(declaration.getSymName().str(), declaration)
                 .second)
          return error("source.correspondence", "duplicate relation symbol");
      } else if (op.getName().getStringRef() == "runtime.binding") {
        auto name = op.getAttrOfType<mlir::StringAttr>("sym_name");
        if (!attributes(op, {"sym_name", "contract", "arguments",
                             "implementation", "function_type"}) ||
            !name || !bindings.emplace(name.getValue().str(), &op).second)
          return error("source.correspondence", "invalid or duplicate binding");
      } else if (op.hasAttr("runtime.region")) {
        if (!name || !outlined.emplace(name.getValue().str(), &op).second)
          return error("source.correspondence", "duplicate outlined control");
      } else if (name && name.getValue().starts_with("zkl_map_")) {
        if (!maps.emplace(name.getValue().str(), &op).second)
          return error("source.correspondence", "duplicate mapped adapter");
      } else
        functions.push_back(&op);
    }
    SmallVector<DeclarationId> pendingConstructions;
    if (const auto *proof = project.entry().proof();
        proof && proof->construction == ProofEntry::Construction::Derived)
      pendingConstructions.push_back(*proof->selectedConstruction);
    std::set<unsigned> checkedConstructions;
    while (!pendingConstructions.empty()) {
      auto selected = pendingConstructions.pop_back_val();
      if (!checkedConstructions.insert(selected.index).second)
        continue;
      const auto &definition = project.declarations()[selected.index];
      auto found = constructions.find(definition.symbol);
      if (found == constructions.end())
        return error("source.correspondence", "missing construction selection");
      if (!construction(definition, found->second))
        return takeFailure();
      for (const auto &application : definition.construction->applications)
        pendingConstructions.push_back(application.construction);
    }
    if (checkedConstructions.size() != constructions.size())
      return error("source.correspondence",
                   "unexpected construction selection");
    unsigned index = 0;
    mlir::SymbolTableCollection symbols;
    relation::FormulaIdentities formulas(remaining, limits.irBytes);
    LayoutIdentities schemaIdentities(remaining);
    for (auto &decl : declared) {
      if (!decl.body || !decl.parameters.empty())
        continue;
      if (++report.declarations > limits.declarations)
        return error("source.limit", "comparison declaration limit");
      if (index >= functions.size())
        return error("source.correspondence", "omitted definition");
      auto &function = *functions[index++];
      bool protocol = decl.kind == Declaration::Kind::Protocol,
           local = decl.kind == Declaration::Kind::Local;
      if (function.getName().getStringRef() !=
              (protocol ? "protocol.func" : "func.func") ||
          !string(function, "sym_name",
                  decl.relation ? formulaSymbol(decl) : decl.symbol) ||
          function.getNumRegions() != 1 ||
          (local ? function.getRegion(0).empty()
                 : !llvm::hasSingleElement(function.getRegion(0))))
        return error("source.correspondence",
                     "definition identity or structure differs");
      SmallVector<StringRef> names =
          protocol ? std::initializer_list<StringRef>{"sym_name",
                                                      "function_type",
                                                      "roles",
                                                      "input_roles",
                                                      "output_roles",
                                                      "contracts",
                                                      "origin"}
          : local
              ? std::initializer_list<StringRef>{"sym_name", "function_type",
                                                 "runtime.origin", "no_inline",
                                                 "sym_visibility"}
              : std::initializer_list<StringRef>{"sym_name", "function_type",
                                                 "sym_visibility"};
      auto conditions = take(flattenDataPreconditions(decl, layouts));
      if (!conditions)
        return std::move(failure);
      if (local)
        for (auto &condition : *conditions) {
          ++condition.left;
          ++condition.right;
        }
      if (!conditions->empty())
        names.push_back("data.preconditions");
      if (!compareDataPreconditions(function, *conditions))
        return error("source.correspondence",
                     "helper data preconditions differ");
      if (!attributes(function, names) ||
          (!protocol && !string(function, "sym_visibility", "private")) ||
          (local && !function.getAttrOfType<mlir::UnitAttr>("no_inline")))
        return error("source.correspondence", "definition attributes differ");
      if (protocol) {
        auto origin = take(encodeProtocolOrigin(project, decl));
        if (!origin)
          return std::move(failure);
        if (function.getAttr("origin") !=
            protocol_ir::protocolOriginAttr(function.getContext(), *origin))
          return error("source.correspondence", "protocol origin differs");
      }
      if (local) {
        auto origin = function.getAttrOfType<mlir::ArrayAttr>("runtime.origin");
        if (!origin || origin.size() != 2 || !strings(origin[1], {}) ||
            !mlir::isa<mlir::StringAttr>(origin[0]) ||
            mlir::cast<mlir::StringAttr>(origin[0]).getValue() !=
                logicalOrigin(project, decl))
          return error("source.correspondence", "local origin differs");
      }
      auto type = function.getAttrOfType<mlir::TypeAttr>("function_type");
      auto signature = type
                           ? mlir::dyn_cast<mlir::FunctionType>(type.getValue())
                           : mlir::FunctionType();
      if (!signature)
        return error("source.correspondence", "missing definition signature");
      if (local && (!signature.getNumInputs() ||
                    !mlir::isa<runtime::ScopeType>(signature.getInput(0)) ||
                    signature.getNumResults() != 1 ||
                    !mlir::isa<exec::OutcomeType>(signature.getResult(0))))
        return error("source.correspondence",
                     "scoped definition signature differs");
      for (bool input : {true, false}) {
        std::vector<LayoutLeaf> leaves;
        auto roles = function.getAttrOfType<mlir::ArrayAttr>(
            input ? "input_roles" : "output_roles");
        unsigned flat = 0;
        for (auto &port : input ? decl.inputs : decl.outputs) {
          auto layout = take(layouts.get(port.type));
          if (!layout)
            return takeFailure();
          if (port.oracle) {
            const auto *oracle = (**layout).leaves.front().oracle();
            if (!oracle || oracle->maximum)
              return error("source.correspondence",
                           "oracle port layout differs");
            leaves.emplace_back(oracle->kind.signature.data.spelling());
            if (!roles || flat >= roles.size() ||
                !roleSet(roles[flat++], {port.oracle->holder}))
              return error("source.correspondence",
                           "oracle holder role differs");
          }
          llvm::append_range(leaves, (**layout).leaves);
          for (unsigned i = 0; i < (**layout).leaves.size(); ++i)
            if (protocol &&
                (!roles || flat >= roles.size() ||
                 !roleSet(roles[flat++],
                          port.oracle ? oracleReceivers(port) : port.roles)))
              return error("source.correspondence",
                           "flattened port roles differ");
        }
        auto nativeTypes =
            input ? signature.getInputs() : signature.getResults();
        if (local)
          nativeTypes =
              input ? nativeTypes.drop_front()
                    : mlir::cast<exec::OutcomeType>(signature.getResult(0))
                          .getPayload();
        auto serviceCount = input ? decl.services.size() : 0;
        if (nativeTypes.size() != leaves.size() + serviceCount)
          return error("source.correspondence",
                       "signature argument count differs");
        if (!types(nativeTypes.take_front(leaves.size()), leaves))
          return takeFailure();
        for (unsigned i = 0; i < serviceCount; ++i) {
          const auto &port = decl.services[i];
          auto type = mlir::dyn_cast<protocol_ir::ServiceReferenceType>(
              nativeTypes[leaves.size() + i]);
          if (!type || type.getContract() != port.contract || !roles ||
              flat >= roles.size() || !roleSet(roles[flat++], {port.owner}))
            return error("source.correspondence",
                         "managed port signature differs");
        }
        if (protocol && flat != roles.size())
          return error("source.correspondence", "extra port roles");
      }
      mathematical::Availability availability;
      if (protocol) {
        if (!contracts(decl, function))
          return takeFailure();
        std::vector<std::string> roster;
        for (unsigned i = 0; i < decl.roles.size(); ++i)
          roster.push_back(nativeRoleName(i));
        if (!strings(function.getAttr("roles"), roster))
          return error("source.correspondence", "participant roster differs");
        if (mlir::failed(mathematical::analyze(
                mlir::cast<protocol_ir::MathematicalOp>(function), availability,
                symbols)))
          return error("source.correspondence", "participant analysis failed");
      }
      siteOrdinal = 0;
      if (!record(function, decl.span) ||
          !body(decl, *decl.body, function.getRegion(0).front(),
                protocol ? &availability : nullptr))
        return takeFailure();
    }
    for (const auto &decl : declared) {
      if (!decl.relation || !decl.origin)
        continue;
      if (++report.declarations > limits.declarations)
        return error("source.limit", "comparison declaration limit");
      auto found = relations.find(decl.symbol);
      if (found == relations.end())
        return error("source.correspondence", "omitted relation declaration");
      auto declaration = found->second;
      relations.erase(found);
      SmallVector<StringRef> attributesExpected{
          "sym_name",         "kind",      "key",     "revision",
          "static_arguments", "signature", "purposes"};
      if (decl.relation->kind == RelationDefinition::Kind::Formula)
        attributesExpected.push_back("formula");
      if (!attributes(*declaration, attributesExpected) ||
          declaration->getNumRegions() || declaration->getNumOperands() ||
          declaration->getNumResults())
        return error("source.correspondence",
                     "relation declaration structure differs");
      const auto &definition = *decl.relation;
      std::vector<LayoutLeaf> leaves;
      std::vector<std::string> purposes, logicalTypes, logicalPurposes;
      for (unsigned i = 0; i < decl.inputs.size(); ++i) {
        auto layout = take(layouts.get(decl.inputs[i].type));
        if (!layout)
          return takeFailure();
        llvm::append_range(leaves, (**layout).leaves);
        std::string purpose;
        switch (definition.purposes[i]) {
        case RelationPurpose::Parameter:
          purpose = "parameter";
          break;
        case RelationPurpose::Statement:
          purpose = "statement";
          break;
        case RelationPurpose::Witness:
          purpose = "witness";
          break;
        }
        purposes.insert(purposes.end(), (**layout).leaves.size(), purpose);
        logicalPurposes.push_back(purpose);
        auto schema = take(schemaIdentities.get(**layout));
        if (!schema)
          return takeFailure();
        logicalTypes.push_back(std::move(*schema));
      }
      if (!types(declaration.getSignature().getInputs(), leaves))
        return takeFailure();
      if (!strings(declaration.getPurposes(), purposes))
        return error("source.correspondence", "relation input purposes differ");
      std::string kind, key, revision;
      switch (definition.kind) {
      case RelationDefinition::Kind::Formula: {
        if (!declaration.getFormulaAttr() ||
            declaration.getFormulaAttr().getValue() != formulaSymbol(decl))
          return error("source.correspondence", "formula helper link differs");
        kind = "zkc.language.formula/0";
        key = decl.symbol;
        auto helper = symbols.getSymbolTable(native).lookup<mlir::func::FuncOp>(
            formulaSymbol(decl));
        auto identity =
            take(formulas.get(helper, logicalTypes, logicalPurposes));
        if (!identity)
          return takeFailure();
        revision = std::move(*identity);
        break;
      }
      case RelationDefinition::Kind::Opaque:
        kind = definition.externalKind;
        key = definition.key;
        revision = definition.revision;
        break;
      case RelationDefinition::Kind::R1CS:
      case RelationDefinition::Kind::AIR:
      case RelationDefinition::Kind::Bundle:
        kind = definition.kind == RelationDefinition::Kind::R1CS
                   ? "zkc.relation.r1cs/0"
               : definition.kind == RelationDefinition::Kind::AIR
                   ? "zkc.relation.air/0"
                   : "zkc.relation.bundle/0";
        key = project.project().assets()[*definition.asset].identity().str();
        revision = "0";
        break;
      }
      json::Array staticArguments;
      if (definition.kind == RelationDefinition::Kind::Opaque)
        for (const auto &argument : decl.staticArguments) {
          auto encoded = take(encodeStaticTerm(argument));
          if (!encoded)
            return takeFailure();
          staticArguments.push_back(std::move(*encoded));
        }
      if (declaration.getStaticArguments() !=
          protocol_ir::protocolOriginAttr(
              declaration.getContext(),
              json::Value(std::move(staticArguments))))
        return error("source.correspondence",
                     "relation static arguments differ");
      if (!string(*declaration, "kind", kind) ||
          !string(*declaration, "key", key) ||
          !string(*declaration, "revision", revision))
        return error("source.correspondence", "relation identity differs");
      if (!record(*declaration, decl.span))
        return takeFailure();
    }
    if (!relations.empty())
      return error("source.correspondence", "extra relation declaration");
    if (index != functions.size() || usedBindings.size() != bindings.size() ||
        usedOutlined.size() != outlined.size() ||
        usedMaps.size() != maps.size() ||
        usedFiniteDefinitions.size() != finiteDefinitions.size())
      return error("source.correspondence",
                   "extra definition or unused binding");
    llvm::sort(report.locations, [](auto &a, auto &b) {
      return std::tie(a.line, a.column) < std::tie(b.line, b.column);
    });
    return std::move(report);
  }
};
} // namespace
Expected<Correspondence> compareOriginal(const ClosedEntry &project,
                                         mlir::ModuleOp module,
                                         const Limits &limits) {
  if (auto e = checkLimits(limits))
    return e;
  if (auto e = checkScopedElaboration(project.project(), limits))
    return e;
  if (auto e = checkScopedSpecialization(project, limits))
    return e;
  if (project.project().installationIdentity() != installedCatalogIdentity())
    return error("source.environment",
                 "source was checked against another installed catalog");
  if (!module || mlir::failed(mlir::verify(module)))
    return error("target.admission",
                 "original failed mathematical IR admission");
  if (project.entry().kind == Declaration::Kind::EntryFunction)
    return compareHostOriginal(project, module, limits);
  return Comparator(project, module, limits).run();
}
Expected<Correspondence> compareNumericalOriginal(const ClosedEntry &project,
                                                  const Declaration &fragment,
                                                  mlir::ModuleOp module,
                                                  const Limits &limits) {
  auto definitions = numericalDefinitions(project, fragment);
  if (!definitions)
    return definitions.takeError();
  if (!module || mlir::failed(mlir::verify(module)))
    return error("target.admission", "numerical original failed admission");
  return Comparator(project, module, limits, *definitions).run();
}
} // namespace zkc::language
