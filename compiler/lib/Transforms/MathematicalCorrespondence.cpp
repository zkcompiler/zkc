#include "MathematicalValues.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "llvm/ADT/StringMap.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
using Environment = ValueCorrespondence::Environment;
using Term = ValueCorrespondence::Term;
bool expression(Operation *op) {
  return isTotal(op) || isa<func::CallOp, protocol_ir::RestrictRolesOp>(op);
}
Operation *nextAction(Operation *op) {
  while (op && expression(op))
    op = op->getNextNode();
  return op;
}
class Correspondence {
  ValueCorrespondence terms;
  StringMap<Term> services;
  SymbolTableCollection symbols;
  struct Substitution {
    StringMap<Attribute> roles;
    std::string prefix;
    Attribute role(Attribute value) const {
      auto found = roles.find(cast<StringAttr>(value).getValue());
      return found == roles.end() ? value : found->second;
    }
    ArrayAttr set(ArrayAttr values) const {
      SmallVector<Attribute> result;
      for (auto value : values)
        result.push_back(role(value));
      return ArrayAttr::get(values.getContext(), result);
    }
    DictionaryAttr attributes(Operation *op) const {
      NamedAttrList result(op->getAttrDictionary());
      for (StringRef key : {"owner", "sender", "receiver", "role"})
        if (auto attr = op->getAttrOfType<StringAttr>(key))
          result.set(key, role(attr));
      if (auto attr = op->getAttrOfType<ArrayAttr>("roles"))
        result.set("roles", set(attr));
      if (auto attr = op->getAttrOfType<ArrayAttr>("carried_roles")) {
        SmallVector<Attribute> sets;
        for (auto value : attr)
          sets.push_back(set(cast<ArrayAttr>(value)));
        result.set("carried_roles", ArrayAttr::get(op->getContext(), sets));
      }
      if (!prefix.empty())
        if (auto site = op->getAttrOfType<StringAttr>("site"))
          result.set("site", StringAttr::get(op->getContext(),
                                             expandedApplicationSite(
                                                 prefix, site.getValue())));
      return result.getDictionary(op->getContext());
    }
    void bindRoles(ValueCorrespondence &terms, Environment env,
                   MLIRContext *context) const {
      SmallVector<Attribute> from, to;
      for (const auto &item : roles) {
        from.push_back(StringAttr::get(context, item.first()));
        to.push_back(item.second);
      }
      terms.roleMap(env, ArrayAttr::get(context, from),
                    ArrayAttr::get(context, to));
    }
  };
  bool operands(Environment left, ValueRange a, Environment right,
                ValueRange b) {
    if (a.size() != b.size())
      return false;
    for (auto [x, y] : zip(a, b))
      if (!terms.compare(left, x, right, y))
        return false;
    return true;
  }
  bool results(Environment left, Operation *a, Environment right,
               Operation *b) {
    if (a->getResultTypes() != b->getResultTypes())
      return false;
    for (auto [x, y] : zip(a->getResults(), b->getResults())) {
      Term value = terms.anchor(x.getType());
      if (!value)
        return false;
      terms.bind(left, x, value);
      terms.bind(right, y, value);
    }
    return true;
  }
  LogicalResult fail(StringRef detail) { return terms.refuse(detail); }

  LogicalResult sameBlock(Block &source, Operation *&cursor, Environment left,
                          Environment right, const Substitution &substitution,
                          unsigned depth, bool inlined = false) {
    if (depth > 64 || !terms.charge())
      return fail("region or application comparison exceeds its bound");
    substitution.bindRoles(terms, left, source.getParentOp()->getContext());
    for (auto &op : source) {
      if (!terms.charge())
        return fail("operation comparison exceeds its bound");
      if (expression(&op))
        continue;
      if (auto application = dyn_cast<protocol_ir::ApplyOp>(op)) {
        auto callee =
            symbols.lookupNearestSymbolFrom<protocol_ir::MathematicalOp>(
                application, application.getCalleeAttr());
        if (!callee)
          return fail("missing application definition");
        NativeTypePolicies policies(
            callee->getParentOfType<protocol_ir::ProtocolModuleOp>());
        Substitution nested;
        for (auto [formal, actual] :
             zip(callee.getRoles(), application.getRoles()))
          nested.roles[cast<StringAttr>(formal).getValue()] =
              substitution.role(actual);
        nested.prefix = substitution.prefix.empty()
                            ? application.getSite().str()
                            : expandedApplicationSite(substitution.prefix,
                                                      application.getSite());
        if (nested.prefix.size() > 4096 || !terms.charge(nested.prefix.size()))
          return fail("application occurrence exceeds its bound");
        Environment arguments = terms.environment();
        auto restrict = [&](Term value, Type type, ArrayAttr owners) {
          auto policy = policies.get(type);
          return policy && policy->shared &&
                         !isa<protocol_ir::ServiceReferenceType>(type)
                     ? terms.restrictRoles(value, type, nested.set(owners))
                     : value;
        };
        for (auto [argument, input, owners] :
             zip(callee.getBody().front().getArguments(),
                 application.getInputs(), callee.getInputRoles()))
          terms.bind(arguments, argument,
                     restrict(terms.value(left, input), input.getType(),
                              cast<ArrayAttr>(owners)));
        if (failed(sameBlock(callee.getBody().front(), cursor, arguments, right,
                             nested, depth + 1, true)))
          return failure();
        for (auto [output, returned, owners] :
             zip(application.getOutputs(),
                 callee.getBody().front().back().getOperands(),
                 callee.getOutputRoles()))
          terms.bind(left, output,
                     restrict(terms.value(arguments, returned),
                              output.getType(), cast<ArrayAttr>(owners)));
        continue;
      }
      if (inlined && isa<protocol_ir::MathematicalReturnOp>(op))
        return success();
      if (!cursor || op.getName() != cursor->getName() ||
          substitution.attributes(&op) != cursor->getAttrDictionary() ||
          !operands(left, op.getOperands(), right, cursor->getOperands()))
        return fail(
            "ordered operation or operand correspondence is unsupported");
      if (isa<protocol_ir::RepeatOp, protocol_ir::ProtocolLoopOp>(op)) {
        auto &a = op.getRegion(0).front();
        auto &b = cursor->getRegion(0).front();
        if (a.getArgumentTypes() != b.getArgumentTypes())
          return fail("loop ports differ");
        Environment innerLeft = terms.environment(),
                    innerRight = terms.environment();
        unsigned carried = op.getNumResults();
        unsigned offset =
            isa<protocol_ir::RepeatOp>(op) || op.hasAttr("maximum") ? 1 : 0;
        for (auto [i, x, y] : enumerate(a.getArguments(), b.getArguments())) {
          Term value = i < carried + offset
                           ? terms.anchor(x.getType())
                           : terms.value(left, op.getOperand(i));
          terms.bind(innerLeft, x, value);
          terms.bind(innerRight, y, value);
        }
        Operation *inner = nextAction(&b.front());
        if (failed(sameBlock(a, inner, innerLeft, innerRight, substitution,
                             depth + 1)))
          return failure();
      } else if (op.getNumRegions() || cursor->getNumRegions())
        return fail("unsupported action region");
      if (!results(left, &op, right, cursor))
        return fail("action result correspondence differs");
      cursor = nextAction(cursor->getNextNode());
    }
    return cursor ? fail("candidate added an ordered operation") : success();
  }

  LogicalResult projectedBlock(Block &source, Block &target, Environment left,
                               Environment right, StringAttr role,
                               ArrayRef<Value> outputs, unsigned depth) {
    if (depth > 64 || !terms.charge())
      return fail("projection comparison exceeds its bound");
    terms.roleComponent(left, role);
    Operation *cursor = nextAction(&target.front());
    for (auto &op : source) {
      if (!terms.charge())
        return fail("projection comparison exceeds its bound");
      if (expression(&op) || isa<protocol_ir::StatementOp>(op))
        continue;
      if (isa<protocol_ir::MathematicalReturnOp, protocol_ir::ProtocolYieldOp>(
              op)) {
        bool kind = isa<protocol_ir::MathematicalReturnOp>(op)
                        ? isa_and_nonnull<protocol_ir::FinishOp>(cursor)
                        : isa_and_nonnull<protocol_ir::ProtocolYieldOp>(cursor);
        if (!kind || !operands(left, outputs, right, cursor->getOperands()))
          return fail(
              "projected return or yield correspondence is unsupported");
        cursor = cursor->getNextNode();
        continue;
      }
      if (auto repeat = dyn_cast<protocol_ir::RepeatOp>(op)) {
        if (!is_contained(repeat.getRoles(), role))
          continue;
        auto loop = dyn_cast_if_present<protocol_ir::ProtocolLoopOp>(cursor);
        if (!loop || repeat.getSite() != loop.getSite() ||
            repeat.getMaximumAttr() != loop.getMaximumAttr() ||
            loop.getParameter() || !loop.getCount().empty() ||
            !terms.compare(left, repeat.getInputs()[0], right,
                           loop.getInputs()[0]))
          return fail("projected loop count or control differs");
        SmallVector<unsigned> carried;
        for (auto [i, owners] : enumerate(repeat.getCarriedRoles()))
          if (is_contained(cast<ArrayAttr>(owners), role))
            carried.push_back(i);
        if (carried.size() != loop.getNumResults())
          return fail("projected loop result ports differ");
        Environment innerLeft = terms.environment(),
                    innerRight = terms.environment();
        auto &a = repeat.getBody().front();
        auto &b = loop.getBody().front();
        Term induction = terms.anchor(a.getArgument(0).getType());
        terms.bind(innerLeft, a.getArgument(0), induction);
        terms.bind(innerRight, b.getArgument(0), induction);
        SmallVector<Value> yielded;
        for (auto [port, index] : enumerate(carried)) {
          if (!terms.compare(left, repeat.getInputs()[index + 1], right,
                             loop.getInputs()[port + 1]) ||
              a.getArgument(index + 1).getType() !=
                  b.getArgument(port + 1).getType())
            return fail(
                "projected carried input correspondence is unsupported");
          Term state = terms.anchor(a.getArgument(index + 1).getType());
          terms.bind(innerLeft, a.getArgument(index + 1), state);
          terms.bind(innerRight, b.getArgument(port + 1), state);
          yielded.push_back(a.back().getOperand(index));
        }
        // Immutable captures mean their actual outer values, including the
        // values from which a candidate rebuilds a captured expression.
        for (unsigned i = repeat.getNumResults() + 1; i < a.getNumArguments();
             ++i)
          terms.bind(innerLeft, a.getArgument(i),
                     terms.value(left, repeat.getInputs()[i]));
        for (unsigned i = loop.getNumResults() + 1; i < b.getNumArguments();
             ++i)
          terms.bind(innerRight, b.getArgument(i),
                     terms.value(right, loop.getInputs()[i]));
        if (failed(projectedBlock(a, b, innerLeft, innerRight, role, yielded,
                                  depth + 1)))
          return failure();
        for (auto [port, index] : enumerate(carried)) {
          auto x = repeat.getResult(index), y = loop.getResult(port);
          if (x.getType() != y.getType())
            return fail("projected loop result type differs");
          Term value = terms.anchor(x.getType());
          terms.bind(left, x, value);
          terms.bind(right, y, value);
        }
      } else if (auto exchange = dyn_cast<protocol_ir::ExchangeOp>(op)) {
        if (exchange.getSenderAttr() == role) {
          auto send = dyn_cast_if_present<protocol_ir::EmitOp>(cursor);
          if (!send || send.getSite() != exchange.getSite() ||
              send.getSchema() != exchange.getSite() ||
              send.getPeer() != exchange.getReceiver() ||
              !terms.compare(left, exchange.getInput(), right, send.getInput()))
            return fail("projected send operand or occurrence differs");
          terms.bind(left, exchange.getOutput(),
                     terms.value(left, exchange.getInput()));
        } else if (exchange.getReceiverAttr() == role) {
          auto receive = dyn_cast_if_present<protocol_ir::AwaitOp>(cursor);
          if (!receive || receive.getSite() != exchange.getSite() ||
              receive.getSchema() != exchange.getSite() ||
              receive.getPeer() != exchange.getSender() ||
              !results(left, &op, right, cursor))
            return fail("projected receive occurrence differs");
        } else
          continue;
      } else if (auto query = dyn_cast<protocol_ir::QueryOp>(op)) {
        if (query.getOwnerAttr() != role)
          continue;
        auto call =
            dyn_cast_if_present<protocol_ir::ParticipantQueryOp>(cursor);
        if (!call || call.getMethod() != query.getMethod() ||
            call.getSite() != query.getSite() ||
            !terms.equal(terms.value(left, query.getReference()),
                         services.lookup(call.getPort())) ||
            !operands(left, query.getInputs(), right, call.getInputs()) ||
            !results(left, &op, right, cursor))
          return fail("projected service root or query operand differs");
      } else if (auto call = dyn_cast<protocol_ir::LocalCallOp>(op)) {
        if (call.getRoleAttr() != role)
          continue;
        auto invocation = dyn_cast_if_present<local::CallOp>(cursor);
        if (!invocation || invocation.getCalleeAttr() != call.getCalleeAttr() ||
            invocation.getSite() != call.getSite() ||
            !operands(left, call.getInputs(), right, invocation.getInputs()) ||
            !results(left, &op, right, cursor))
          return fail("projected local call correspondence differs");
      } else if (auto guard = dyn_cast<protocol_ir::GuardOp>(op)) {
        if (guard.getOwnerAttr() != role)
          continue;
        auto check = dyn_cast_if_present<local::GuardOp>(cursor);
        if (!check || check.getSite() != guard.getSite() ||
            !terms.compare(left, guard.getCondition(), right,
                           check.getCondition()))
          return fail("projected guard operand differs");
      } else if (auto finish = dyn_cast<protocol_ir::FinishIfOp>(op)) {
        if (finish.getOwnerAttr() != role)
          continue;
        if (!isa_and_nonnull<protocol_ir::FinishIfOp>(cursor) ||
            op.getAttrDictionary() != cursor->getAttrDictionary() ||
            !operands(left, op.getOperands(), right, cursor->getOperands()) ||
            !results(left, &op, right, cursor))
          return fail("projected completion correspondence differs");
      } else
        return fail("unsupported prepared operation");
      cursor = nextAction(cursor->getNextNode());
    }
    return cursor ? fail("projection added an ordered operation") : success();
  }

public:
  explicit Correspondence(Operation *diagnostic, bool roleComponents = false)
      : terms(diagnostic, roleComponents) {}
  LogicalResult same(Operation *source, Operation *target) {
    auto &a = source->getRegion(0).front();
    auto &b = target->getRegion(0).front();
    if (source->getAttrDictionary() != target->getAttrDictionary() ||
        a.getArgumentTypes() != b.getArgumentTypes())
      return fail("definition interface differs");
    Environment left = terms.environment(), right = terms.environment();
    for (auto [x, y] : zip(a.getArguments(), b.getArguments())) {
      Term input = terms.anchor(x.getType());
      terms.bind(left, x, input);
      terms.bind(right, y, input);
    }
    Operation *cursor = nextAction(&b.front());
    return sameBlock(a, cursor, left, right, Substitution{}, 0);
  }
  LogicalResult project(protocol_ir::MathematicalOp source,
                        protocol_ir::ParticipantOp target) {
    auto role = target.getRoleAttr();
    auto &a = source.getBody().front();
    auto &b = target.getBody().front();
    Environment left = terms.environment(), right = terms.environment();
    services.clear();
    SmallVector<Value> outputs;
    unsigned input = 0, abi = 0;
    auto servicePorts = target->getAttrOfType<ArrayAttr>("service_ports");
    unsigned serviceCount = 0;
    for (auto [x, owners] : zip(a.getArguments(), source.getInputRoles())) {
      if (!is_contained(cast<ArrayAttr>(owners), role))
        continue;
      Term value = terms.anchor(x.getType());
      terms.bind(left, x, value);
      if (auto reference =
              dyn_cast<protocol_ir::ServiceReferenceType>(x.getType())) {
        bool found = false;
        if (servicePorts)
          for (auto item : servicePorts) {
            auto port = cast<ArrayAttr>(item);
            if (cast<IntegerAttr>(port[2]).getInt() != abi)
              continue;
            if (cast<StringAttr>(port[1]).getValue() != reference.getContract())
              return fail("projected service contract differs");
            services[cast<StringAttr>(port[0]).getValue()] = value;
            found = true;
          }
        if (!found)
          return fail("projected service input coordinate differs");
        ++serviceCount;
      } else {
        if (input == b.getNumArguments() ||
            x.getType() != b.getArgument(input).getType())
          return fail("projected entry input type or count differs");
        terms.bind(right, b.getArgument(input++), value);
      }
      ++abi;
    }
    if (input != b.getNumArguments() ||
        serviceCount != (servicePorts ? servicePorts.size() : 0))
      return fail("projected entry input count differs");
    for (auto [value, owners] :
         zip(a.back().getOperands(), source.getOutputRoles()))
      if (is_contained(cast<ArrayAttr>(owners), role))
        outputs.push_back(value);
    return projectedBlock(a, b, left, right, role, outputs, 0);
  }
};
template <typename Definition>
LogicalResult definitions(protocol_ir::ProtocolModuleOp before,
                          protocol_ir::ProtocolModuleOp after) {
  Correspondence compare(after);
  SymbolTable symbols(after);
  auto originals = before.getBody().front().getOps<Definition>();
  auto candidates = after.getBody().front().getOps<Definition>();
  if (range_size(originals) != range_size(candidates))
    return ValueCorrespondence(after).refuse("definition count differs");
  for (auto source : originals) {
    auto target =
        dyn_cast_or_null<Definition>(symbols.lookup(source.getSymName()));
    if (!target)
      return ValueCorrespondence(after).refuse("definition was lost");
    if (failed(compare.same(source, target)))
      return failure();
  }
  return success();
}
} // namespace
LogicalResult verifyPreparedValues(protocol_ir::ProtocolModuleOp before,
                                   protocol_ir::ProtocolModuleOp after) {
  return definitions<protocol_ir::MathematicalOp>(before, after);
}
LogicalResult verifyParticipantValues(protocol_ir::ProtocolModuleOp before,
                                      protocol_ir::ProtocolModuleOp after) {
  return definitions<protocol_ir::ParticipantOp>(before, after);
}
LogicalResult verifyProjectedValues(protocol_ir::ProtocolModuleOp before,
                                    protocol_ir::ProtocolModuleOp after) {
  Correspondence compare(after, true);
  SymbolTable originals(before);
  for (auto target :
       after.getBody().front().getOps<protocol_ir::ParticipantOp>()) {
    auto source = dyn_cast_or_null<protocol_ir::MathematicalOp>(
        originals.lookup(target.getInstance()));
    if (!source)
      return ValueCorrespondence(after).refuse(
          "projected source definition is missing");
    if (failed(compare.project(source, target)))
      return failure();
  }
  return success();
}
} // namespace zkc::mathematical
