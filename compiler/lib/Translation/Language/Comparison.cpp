#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialTypes.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "zkc/Dialect/Relation/Formula.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include "zkc/Interfaces/Mathematical.h"
#include "zkc/Language/Builtins.h"
#include "zkc/Language/Layout.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Translation/Language.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <set>
using namespace llvm;
namespace zkc::language {
namespace {
using Values = SmallVector<mlir::Value>;
bool attributes(mlir::Operation &op, std::initializer_list<StringRef> names) {
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
bool roleSet(mlir::Attribute value, const Declaration &decl,
             ArrayRef<unsigned> indices) {
  std::vector<std::string> expected;
  for (auto i : indices)
    expected.push_back(decl.roles[i]);
  return strings(value, expected);
}
class Comparator {
  const ClosedEntry &project;
  mlir::ModuleOp module;
  const Limits &limits;
  Layouts layouts;
  std::map<std::string, mlir::Operation *> realizations;
  std::set<mlir::Operation *> usedRealizations;
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
      failure = error("source.correspondence", message);
    return false;
  }
  bool charge(uint64_t n) {
    if (n > remaining) {
      failure = error("source.limit", "comparison work limit exceeded");
      return false;
    }
    remaining -= n;
    return true;
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
      if (const auto *polynomial = expected[i].polynomial()) {
        auto type = mlir::dyn_cast<poly::PolynomialType>(actual[i]);
        if (!type || type.getDomain() != polynomial->field ||
            type.getArity() != polynomial->arity)
          return fail("formal polynomial layout differs");
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
    if (cursor == block.end()) {
      fail("original omitted an operation");
      return nullptr;
    }
    auto &op = *cursor++;
    if (++report.operations > limits.operations) {
      failure = error("source.limit", "comparison operation limit exceeded");
      return nullptr;
    }
    if (!charge(1 + operands.size()) || !record(op, span))
      return nullptr;
    if ((!name.empty() && op.getName().getStringRef() != name) ||
        op.getNumResults() != results || op.getNumRegions() != regions ||
        op.getNumSuccessors() || op.getOperands() != operands) {
      fail("operation identity, operands or region structure differs");
      return nullptr;
    }
    return &op;
  }
  std::optional<Values>
  primitive(mlir::Block &block, mlir::Block::iterator &cursor,
            const LocalPrimitive &expected, mlir::ValueRange operands,
            ArrayRef<LayoutLeaf> outputs, Span span, StringRef site) {
    if (!expected.bindingArguments && expected.contract == "bool.constant") {
      auto *actual = next(block, cursor, span, "local.bool_constant", {}, 1);
      if (!actual)
        return {};
      auto value = actual->getAttrOfType<mlir::BoolAttr>("value");
      if (!attributes(*actual, {"value", "site"}) || !value ||
          value.getValue() != (expected.parameters.front() == "true") ||
          !string(*actual, "site", site) ||
          !types(actual->getResultTypes(), outputs)) {
        if (!failure)
          fail("local Boolean literal differs");
        return {};
      }
      return Values(actual->getResults());
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
    auto *actual = next(block, cursor, span, "", operands, outputs.size());
    if (!actual)
      return {};
    if (!attributes(*actual, {"binding", "parameters", "site"}) ||
        !string(*actual, "site", site) ||
        !strings(actual->getAttr("parameters"), expected.parameters) ||
        !protocol::operationSupportsContract(actual->getName().getStringRef(),
                                             expected.contract) ||
        !types(actual->getResultTypes(), outputs)) {
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
      auto roots =
          take(kernelArguments(expected.contract, *expected.bindingArguments));
      if (!roots)
        return {};
      args = std::move(*roots);
    } else if (StringRef(expected.contract).starts_with("field.") ||
               StringRef(expected.contract).starts_with("curve.") ||
               StringRef(expected.contract).starts_with("resource_unit.")) {
      auto type = take(protocol::encodeBoundType(
          operands.empty() ? actual->getResult(0).getType()
                           : operands[0].getType(),
          false));
      if (!type)
        return {};
      args.push_back(type->identity);
    }
    if (!string(binding, "contract", expected.contract) ||
        !strings(binding.getAttr("arguments"), args) ||
        !string(binding, "implementation", "")) {
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
    if (!agree(actual->getOperandTypes(), selected->inputs) ||
        !agree(actual->getResultTypes(), selected->outputs))
      return {};
    return Values(actual->getResults());
  }
  bool retire(mlir::Block &block, mlir::Block::iterator &cursor,
              mlir::Value value, Span span, StringRef site) {
    return bool(primitive(block, cursor,
                          LocalPrimitive{"resource_unit.consume", {}, {}},
                          value, {}, span, site));
  }
  bool body(const Declaration &decl, const Body &source, mlir::Block &block,
            const mathematical::Availability *availability,
            bool region = false) {
    auto cursor = block.begin();
    std::vector<Values> values(source.values.size());
    unsigned argument = 0;
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
    const auto &proof = project.entry().proof;
    if (!region && decl.id.index == project.protocol().id.index && proof &&
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
          selectors.push_back(decl.roles[operand.role]);
        }
      }
      auto acceptance = take(layouts.select(decl, proof->acceptance));
      if (!acceptance)
        return false;
      auto *actual =
          next(block, cursor, clause.span, "protocol.statement", operands, 0);
      if (!actual)
        return false;
      if (!attributes(*actual, {"relation", "selectors", "acceptance"}))
        return fail("selected Entry statement attributes differ");
      auto symbol = actual->getAttrOfType<mlir::FlatSymbolRefAttr>("relation");
      auto output = actual->getAttrOfType<mlir::IntegerAttr>("acceptance");
      if (!symbol || symbol.getValue() != relation.symbol || !output ||
          output.getInt() != acceptance->offset ||
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
      auto site = "s" + std::to_string(siteOrdinal++);
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
            auto *actual =
                next(block, cursor, op.span, "local.variant_inject", input, 1);
            if (!actual)
              return false;
            if (!attributes(*actual, {"alternative", "site"}) ||
                !string(*actual, "alternative", construct->alternative) ||
                !string(*actual, "site", site))
              return fail("variant alternative differs");
            result.push_back(actual->getResult(0));
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
        auto *actual =
            next(block, cursor, op.span, "", operands, leaves.size());
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
        if (math->identity == MathematicalIdentity::FieldConstant) {
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
      } else if (auto *local = std::get_if<LocalPrimitive>(&op.action)) {
        auto checked =
            primitive(block, cursor, *local, flatten(local->operands), leaves,
                      op.span, site);
        if (!checked)
          return false;
        result = std::move(*checked);
      } else if (auto *call = std::get_if<HelperCall>(&op.action)) {
        auto &target = project.declarations()[call->callee.index];
        bool local = target.kind == Declaration::Kind::Local ||
                     source.mode == Body::Mode::Local,
             owned = local && source.mode == Body::Mode::Protocol,
             realized = source.mode == Body::Mode::Local &&
                        target.kind == Declaration::Kind::Math;
        auto *actual = next(block, cursor, op.span,
                            owned   ? "protocol.local_call"
                            : local ? "local.apply"
                                    : "func.call",
                            flatten(call->operands), leaves.size());
        if (!actual)
          return false;
        auto callee = actual->getAttrOfType<mlir::FlatSymbolRefAttr>("callee");
        if (realized) {
          auto found = callee ? realizations.find(callee.getValue().str())
                              : realizations.end();
          if (found == realizations.end())
            return fail("missing mathematical realization");
          auto *definition = found->second;
          auto helper =
              definition->getAttrOfType<mlir::FlatSymbolRefAttr>("helper");
          auto type =
              definition->getAttrOfType<mlir::TypeAttr>("function_type");
          auto signature =
              type ? mlir::dyn_cast<mlir::FunctionType>(type.getValue())
                   : mlir::FunctionType();
          if (!helper || helper.getValue() != target.symbol || !signature ||
              actual->getOperandTypes() != signature.getInputs() ||
              actual->getResultTypes() != signature.getResults())
            return fail("mathematical realization target or signature differs");
          usedRealizations.insert(definition);
        }
        if (!callee || (!realized && callee.getValue() != target.symbol) ||
            !attributes(
                *actual,
                owned
                    ? std::initializer_list<StringRef>{"callee", "site", "role"}
                : local ? std::initializer_list<StringRef>{"callee", "site"}
                        : std::initializer_list<StringRef>{"callee"}) ||
            (local && !string(*actual, "site", site)) ||
            (owned && (!call->owner ||
                       !string(*actual, "role", decl.roles[*call->owner]))))
          return fail("call target, mode, owner or site differs");
        result = Values(actual->getResults());
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
            !string(*actual, "owner", decl.roles[port.owner]) ||
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
            !string(*actual, "owner", decl.roles[completion->owner]) ||
            !string(*actual, "site", site) ||
            actual->getResultTypes() != mlir::TypeRange(successors))
          return fail("completion owner, site or affine successors differ");
        for (unsigned i = 0; i < positions.size(); ++i)
          input[positions[i]] = actual->getResult(i);
        unsigned offset = 1;
        for (unsigned port = 0; port < completion->values.size(); ++port) {
          unsigned width = values[completion->values[port].index].size();
          if (llvm::is_contained(completion->continuations, port))
            result.append(input.begin() + offset,
                          input.begin() + offset + width);
          offset += width;
        }
      } else if (auto *guard = std::get_if<ProtocolGuard>(&op.action)) {
        auto *actual = next(block, cursor, op.span, "protocol.guard",
                            values[guard->condition.index], 0);
        if (!actual)
          return false;
        if (!attributes(*actual, {"owner", "site"}) ||
            !string(*actual, "owner", decl.roles[guard->owner]) ||
            !string(*actual, "site", site))
          return fail("guard owner or occurrence differs");
      } else if (auto *application =
                     std::get_if<ProtocolApplication>(&op.action)) {
        const auto &target = project.declarations()[application->callee.index];
        auto operands = flatten(application->operands);
        for (auto service : application->services)
          operands.push_back(services[service.index]);
        auto *actual = next(block, cursor, op.span, "protocol.apply", operands,
                            leaves.size());
        if (!actual)
          return false;
        auto callee = actual->getAttrOfType<mlir::FlatSymbolRefAttr>("callee");
        std::vector<std::string> mapped;
        for (auto role : application->roles)
          mapped.push_back(decl.roles[role]);
        if (!attributes(*actual, {"callee", "site", "roles"}) || !callee ||
            callee.getValue() != target.symbol ||
            !string(*actual, "site", site) ||
            !strings(actual->getAttr("roles"), mapped))
          return fail(
              "protocol application target, role substitution or site differs");
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
              !string(*sent, "sender", decl.roles[exchange->sender]) ||
              !string(*sent, "receiver", decl.roles[exchange->receiver]) ||
              !string(*sent, "site", site + "_" + std::to_string(i)))
            return fail("message occurrence differs");
          auto *received =
              next(block, cursor, op.span, "protocol.restrict_roles",
                   sent->getResult(0), 1);
          if (!received)
            return false;
          if (!attributes(*received, {"roles"}) ||
              !roleSet(received->getAttr("roles"), decl, {exchange->receiver}))
            return fail("message receiver restriction differs");
          result.push_back(received->getResult(0));
        }
      } else if (auto *restriction = std::get_if<Restriction>(&op.action)) {
        for (auto input : values[restriction->input.index]) {
          auto *actual =
              next(block, cursor, op.span, "protocol.restrict_roles", input, 1);
          if (!actual)
            return false;
          if (!attributes(*actual, {"roles"}) ||
              !roleSet(actual->getAttr("roles"), decl, restriction->roles))
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
            !roleSet(actual->getAttr("roles"), decl, repeat->roles) ||
            !carriedRoles || carriedRoles.size() != leaves.size())
          return fail(
              "repeat site, maximum, roles or carried interface differs");
        unsigned flat = 0;
        for (unsigned i = 0; i < op.results.size(); ++i)
          for (unsigned j = 0; j < resultLayouts[i]->leaves.size(); ++j)
            if (!roleSet(carriedRoles[flat++], decl,
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
        if (match) {
          auto subject = take(
              layouts.get(source.values[control->operands.front().index].type));
          if (!subject)
            return false;
          if ((**subject).custody) {
            if (!retire(block, cursor, input.front(), op.span, site + "_match"))
              return false;
            input.erase(input.begin());
          }
        }
        auto *actual =
            next(block, cursor, op.span,
                 match                                      ? "local.match"
                 : control->kind == LocalControl::Kind::For ? "local.for"
                                                            : "local.if",
                 input, leaves.size(), control->regions.size());
        if (!actual)
          return false;
        if (!attributes(
                *actual,
                match ? std::initializer_list<StringRef>{"site", "alternatives"}
                      : std::initializer_list<StringRef>{"site"}) ||
            !string(*actual, "site", site) ||
            (match &&
             !strings(actual->getAttr("alternatives"), control->alternatives)))
          return fail("control site or alternative order differs");
        for (unsigned i = 0; i < control->regions.size(); ++i)
          if (!llvm::hasSingleElement(actual->getRegion(i)) ||
              !body(decl, *control->regions[i], actual->getRegion(i).front(),
                    nullptr, true))
            return false;
        result = Values(actual->getResults());
      } else
        return fail("source operation has no comparison rule");
      if (result.size() != leaves.size())
        return fail("operation result layout differs");
      // Logical products and abstract helper dependencies may conservatively
      // narrow their leaves. Exact operation/operand matching already fixes
      // derived native availability; it must contain the source guarantee.
      bool derived = std::holds_alternative<MathValue>(op.action) ||
                     std::holds_alternative<Construct>(op.action) ||
                     std::holds_alternative<Projection>(op.action);
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
    if (source.stopped) {
      auto *stop = next(block, cursor, decl.span, "local.stop", {}, 0);
      if (!stop)
        return false;
      if (!attributes(*stop, {"site", "reason"}) ||
          !string(*stop, "site", "stop" + std::to_string(siteOrdinal++)) ||
          !string(*stop, "reason", source.stopReason))
        return fail("stop reason or site differs");
    } else {
      auto *ret =
          next(block, cursor, decl.span,
               region && source.mode == Body::Mode::Protocol ? "protocol.yield"
               : region                                      ? "local.yield"
               : source.mode == Body::Mode::Protocol         ? "protocol.return"
               : source.mode == Body::Mode::Local            ? "local.return"
                                                             : "func.return",
               flatten(source.results), 0);
      if (!ret)
        return false;
      if (!attributes(*ret, {}))
        return fail("extra return attributes");
    }
    return cursor == block.end() || fail("extra operations after source body");
  }

public:
  Comparator(const ClosedEntry &project, mlir::ModuleOp module,
             const Limits &limits)
      : project(project), module(module), limits(limits),
        layouts(project, limits), remaining(limits.work) {
    (void)!!failure;
  }
  Expected<Correspondence> run() {
    if (!module->getAttrs().empty() ||
        !llvm::hasSingleElement(*module.getBody()))
      return error("source.correspondence",
                   "expected one unadorned protocol module");
    auto native = mlir::dyn_cast<protocol_ir::ProtocolModuleOp>(
        module.getBody()->front());
    if (!native || !attributes(*native, {"profile"}) ||
        native.getProfile() != protocol_ir::Profile::Protocol ||
        !llvm::hasSingleElement(native.getBody()))
      return error("source.correspondence", "unexpected original module");
    SmallVector<mlir::Operation *> functions;
    std::map<std::string, relation::DeclareOp> relations;
    std::set<std::string> realizedHelpers;
    for (auto &op : native.getBody().front()) {
      if (auto declaration = mlir::dyn_cast<relation::DeclareOp>(op)) {
        if (!relations.emplace(declaration.getSymName().str(), declaration)
                 .second)
          return error("source.correspondence", "duplicate relation symbol");
      } else if (op.getName().getStringRef() == "local.binding") {
        auto name = op.getAttrOfType<mlir::StringAttr>("sym_name");
        if (!attributes(
                op, {"sym_name", "contract", "arguments", "implementation"}) ||
            !name || !bindings.emplace(name.getValue().str(), &op).second)
          return error("source.correspondence", "invalid or duplicate binding");
      } else if (op.getName().getStringRef() == "local.realize") {
        auto name = op.getAttrOfType<mlir::StringAttr>("sym_name");
        auto helper = op.getAttrOfType<mlir::FlatSymbolRefAttr>("helper");
        if (!name || !helper ||
            !realizedHelpers.insert(helper.getValue().str()).second ||
            !attributes(op, {"sym_name", "helper", "function_type"}) ||
            op.getNumOperands() || op.getNumResults() || op.getNumRegions() ||
            !realizations.emplace(name.getValue().str(), &op).second)
          return error("source.correspondence",
                       "invalid or duplicate realization");
      } else
        functions.push_back(&op);
    }
    unsigned index = 0;
    mlir::SymbolTableCollection symbols;
    relation::FormulaIdentities formulas(remaining, limits.irBytes);
    LayoutIdentities schemaIdentities(remaining);
    for (auto &decl : project.declarations()) {
      if (!decl.body || !decl.parameters.empty())
        continue;
      if (++report.declarations > limits.declarations)
        return error("source.limit", "comparison declaration limit");
      if (index >= functions.size())
        return error("source.correspondence", "omitted definition");
      auto &function = *functions[index++];
      bool protocol = decl.kind == Declaration::Kind::Protocol,
           local = decl.kind == Declaration::Kind::Local;
      if (function.getName().getStringRef() != (protocol ? "protocol.func"
                                                : local  ? "local.func"
                                                         : "func.func") ||
          !string(function, "sym_name",
                  decl.relation ? formulaSymbol(decl) : decl.symbol) ||
          function.getNumRegions() != 1 ||
          !llvm::hasSingleElement(function.getRegion(0)))
        return error("source.correspondence",
                     "definition identity or structure differs");
      auto names =
          protocol
              ? std::initializer_list<StringRef>{"sym_name", "function_type",
                                                 "roles", "input_roles",
                                                 "output_roles"}
          : local
              ? std::initializer_list<StringRef>{"sym_name", "function_type",
                                                 "logical_origin"}
              : std::initializer_list<StringRef>{"sym_name", "function_type",
                                                 "sym_visibility"};
      if (!attributes(function, names) ||
          (!protocol && !local &&
           !string(function, "sym_visibility", "private")))
        return error("source.correspondence", "definition attributes differ");
      if (local) {
        auto origin = function.getAttrOfType<mlir::ArrayAttr>("logical_origin");
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
      for (bool input : {true, false}) {
        std::vector<LayoutLeaf> leaves;
        auto roles = function.getAttrOfType<mlir::ArrayAttr>(
            input ? "input_roles" : "output_roles");
        unsigned flat = 0;
        for (auto &port : input ? decl.inputs : decl.outputs) {
          auto layout = take(layouts.get(port.type));
          if (!layout)
            return takeFailure();
          llvm::append_range(leaves, (**layout).leaves);
          for (unsigned i = 0; i < (**layout).leaves.size(); ++i)
            if (protocol && (!roles || flat >= roles.size() ||
                             !roleSet(roles[flat++], decl, port.roles)))
              return error("source.correspondence",
                           "flattened port roles differ");
        }
        auto nativeTypes =
            input ? signature.getInputs() : signature.getResults();
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
              flat >= roles.size() ||
              !roleSet(roles[flat++], decl, {port.owner}))
            return error("source.correspondence",
                         "managed port signature differs");
        }
        if (protocol && flat != roles.size())
          return error("source.correspondence", "extra port roles");
      }
      mathematical::Availability availability;
      if (protocol) {
        if (!strings(function.getAttr("roles"), decl.roles))
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
    for (const auto &decl : project.declarations()) {
      if (!decl.relation || !decl.origin)
        continue;
      if (++report.declarations > limits.declarations)
        return error("source.limit", "comparison declaration limit");
      auto found = relations.find(decl.symbol);
      if (found == relations.end())
        return error("source.correspondence", "omitted relation declaration");
      auto declaration = found->second;
      relations.erase(found);
      if (!attributes(*declaration, {"sym_name", "kind", "key", "revision",
                                     "signature", "purposes"}) ||
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
        kind = definition.kind == RelationDefinition::Kind::R1CS
                   ? "zkc.relation.r1cs/0"
                   : "zkc.relation.air/0";
        key = project.project().assets()[*definition.asset].identity().str();
        revision = "0";
        break;
      }
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
        usedRealizations.size() != realizations.size())
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
  if (project.project().installationIdentity() != installedCatalogIdentity())
    return error("source.environment",
                 "source was checked against another installed catalog");
  if (!module || mlir::failed(mlir::verify(module)))
    return error("target.admission",
                 "original failed mathematical IR admission");
  return Comparator(project, module, limits).run();
}
} // namespace zkc::language
