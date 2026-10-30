#include "Native.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringSet.h"
using namespace llvm;
namespace zkc::language::entry_detail {
namespace {
class Reader {
  const Limits &limits;
  uint64_t work, metadata, operations = 0;
  unsigned next = 0;
  mlir::Region *region = nullptr;
  mlir::Region::iterator nextBlock;
  mlir::Block *failure = nullptr;
  exec::OutcomeType outcome;
  using Environment = DenseMap<mlir::Value, unsigned>;
  Error fail(StringRef detail) {
    return error("source.correspondence", detail);
  }
  bool charge(uint64_t amount = 1) {
    if (amount > work)
      return false;
    work -= amount;
    return true;
  }
  bool bytes(uint64_t amount) {
    if (amount > metadata)
      return false;
    metadata -= amount;
    return true;
  }
  static bool bare(mlir::Operation *op) {
    return op && op->getDiscardableAttrDictionary().empty();
  }
  static bool attributes(mlir::Operation *op, ArrayRef<StringRef> allowed) {
    return op && all_of(op->getAttrs(), [&](mlir::NamedAttribute attr) {
             return is_contained(allowed, attr.getName().getValue());
           });
  }
  Expected<json::Value> schema(data::LayoutAttr layout, unsigned depth = 0) {
    if (!layout || depth > limits.typeDepth || !charge())
      return fail("Host layout exceeds bounded structural export");
    auto fields =
        [&](ArrayRef<data::LayoutFieldAttr> fields) -> Expected<json::Array> {
      json::Array result;
      for (auto field : fields) {
        if (!charge() || !bytes(field.getName().getValue().size()))
          return fail("Host layout fields exceed export limits");
        auto nested = schema(field.getLayout(), depth + 1);
        if (!nested)
          return nested.takeError();
        result.push_back(
            json::Object{{"name", field.getName().getValue().str()},
                         {"offset", field.getOffset()},
                         {"schema", std::move(*nested)}});
      }
      return result;
    };
    auto members = fields(layout.getFields());
    if (!members)
      return members.takeError();
    json::Array alternatives, permissions, leaves;
    for (auto arm : layout.getAlternatives()) {
      if (!charge() || !bytes(arm.getName().getValue().size()))
        return fail("Host layout alternatives exceed export limits");
      auto payload = fields(arm.getFields());
      if (!payload)
        return payload.takeError();
      alternatives.push_back(
          json::Object{{"name", arm.getName().getValue().str()},
                       {"fields", std::move(*payload)}});
    }
    for (auto leaf : layout.getLeaves()) {
      if (!charge())
        return fail("Host native leaves exceed export work");
      auto value = protocol::encodeBoundType(leaf, false);
      if (!value)
        return value.takeError();
      auto spelling = value->spelling();
      if (!bytes(spelling.size()))
        return fail("Host native leaves exceed export bytes");
      leaves.push_back(std::move(spelling));
    }
    if (!bytes(layout.getKind().getValue().size() +
               layout.getIdentity().getValue().size() +
               layout.getDisplayType().getValue().size()))
      return fail("Host layout exceeds metadata allowance");
    if (layout.getCopy())
      permissions.push_back("Copy");
    if (layout.getDrop())
      permissions.push_back("Drop");
    return json::Object{{"kind", layout.getKind().getValue().str()},
                        {"identity", layout.getIdentity().getValue().str()},
                        {"type", layout.getDisplayType().getValue().str()},
                        {"custody", layout.getCustody()},
                        {"constructible", layout.getConstructible()},
                        {"permissions", std::move(permissions)},
                        {"fields", std::move(*members)},
                        {"alternatives", std::move(alternatives)},
                        {"leaves", std::move(leaves)}};
  }
  Expected<json::Value> schema(mlir::Type type) {
    if (auto native = mlir::dyn_cast<data::ValueType>(type))
      return schema(native.getLayout());
    // These two source scalar types have no nominal parameters. Their canonical
    // source identities are fixed independently of function annotations.
    if (!type.isSignlessInteger(1) && !type.isSignlessInteger(64))
      return fail("Host value has no admitted native schema");
    if (!charge() || !bytes(128))
      return fail("Host scalar schemas exceed export allowance");
    Layout layout;
    layout.type = Type(type.isSignlessInteger(1) ? Type::Kind::Boolean
                                                 : Type::Kind::Index);
    layout.permissions = {true, true};
    layout.constructible = true;
    layout.leaves = {type.isSignlessInteger(1) ? "bool" : "index"};
    return encodeEntrySchema(layout);
  }
  Expected<json::Array> definitions(mlir::ValueRange values, Environment &env) {
    json::Array result;
    for (auto value : values) {
      auto type = schema(value.getType());
      if (!type)
        return type.takeError();
      if (!env.try_emplace(value, next).second)
        return fail("Host value was defined twice");
      result.push_back(
          json::Object{{"id", next++}, {"schema", std::move(*type)}});
    }
    return result;
  }
  Expected<json::Array> uses(mlir::ValueRange values, const Environment &env) {
    json::Array result;
    for (auto value : values) {
      auto found = env.find(value);
      if (!charge() || found == env.end())
        return fail("Host operand is outside its explicit region scope");
      result.push_back(found->second);
    }
    return result;
  }
  mlir::Block *takeBlock() {
    return charge() && nextBlock != region->end() ? &*nextBlock++ : nullptr;
  }
  static bool branch(mlir::Operation *op, mlir::Block *target,
                     mlir::ValueRange values) {
    auto edge = mlir::dyn_cast_or_null<mlir::cf::BranchOp>(op);
    return edge && bare(edge) && edge.getDest() == target &&
           edge.getDestOperands() == values;
  }
  Expected<json::Value> body(mlir::Block *start, mlir::Block *continuation,
                             unsigned depth = 0) {
    if (!start || depth > limits.callDepth)
      return fail("Host control exceeds nesting limits");
    Environment env;
    auto arguments = definitions(start->getArguments(), env);
    if (!arguments)
      return arguments.takeError();
    json::Array steps;
    auto finish = [&](json::Array returns) -> json::Value {
      return json::Object{{"arguments", std::move(*arguments)},
                          {"operations", std::move(steps)},
                          {"returns", std::move(returns)}};
    };
    auto *current = start;
    auto cursor = current->begin();
    auto take = [&]() -> mlir::Operation * {
      return charge() && cursor != current->end() ? &*cursor++ : nullptr;
    };
    auto advance = [&](mlir::Block *block) {
      current = block;
      cursor = current->begin();
    };
    while (auto *raw = take()) {
      if (auto edge = mlir::dyn_cast<mlir::cf::BranchOp>(raw);
          edge && continuation && edge.getDest() == continuation) {
        if (!bare(edge) || cursor != current->end())
          return fail("Host continuation is not an exact terminal edge");
        auto returns = uses(edge.getDestOperands(), env);
        if (!returns)
          return returns.takeError();
        return finish(std::move(*returns));
      }
      if (auto returned = mlir::dyn_cast<exec::ReturnOp>(raw)) {
        auto ret = mlir::dyn_cast_or_null<mlir::func::ReturnOp>(take());
        if (continuation || !bare(returned) || !ret || !bare(ret) ||
            returned.getOutcome().getType() != outcome ||
            ret.getOperands() != returned->getResults() ||
            cursor != current->end())
          return fail("Host return differs from its explicit outcome");
        auto returns = uses(returned.getValues(), env);
        if (!returns)
          return returns.takeError();
        return finish(std::move(*returns));
      }
      if (++operations > limits.operations)
        return fail("Host operation inventory exceeds limits");
      if (auto stop = mlir::dyn_cast<exec::StopOp>(raw)) {
        if (!attributes(stop, {"reason"}) || !bytes(stop.getReason().size()) ||
            !branch(take(), failure, stop->getResults()) ||
            cursor != current->end())
          return fail("Host stop does not propagate terminal failure");
        steps.push_back(json::Object{{"op", "stop"},
                                     {"reason", stop.getReason().str()},
                                     {"operands", json::Array{}},
                                     {"results", json::Array{}}});
        return finish({});
      }
      json::Object operation;
      SmallVector<mlir::Value> inputs, outputs;
      if (auto conditional = mlir::dyn_cast<mlir::cf::CondBranchOp>(raw)) {
        auto *next = takeBlock(), *yes = takeBlock(), *no = takeBlock();
        if (!next || !yes || !no || !bare(conditional) ||
            conditional.getBranchWeights() ||
            conditional.getTrueDest() != yes ||
            conditional.getFalseDest() != no ||
            conditional.getTrueDestOperands() !=
                conditional.getFalseDestOperands() ||
            cursor != current->end())
          return fail("Host conditional capture or successor edges differ");
        operation["op"] = "if";
        inputs.push_back(conditional.getCondition());
        append_range(inputs, conditional.getTrueDestOperands());
        json::Array regions;
        for (auto *arm : {yes, no}) {
          auto nested = body(arm, next, depth + 1);
          if (!nested)
            return nested.takeError();
          regions.push_back(std::move(*nested));
        }
        operation["regions"] = std::move(regions);
        advance(next);
        append_range(outputs, next->getArguments());
      } else if (auto initial = mlir::dyn_cast<mlir::cf::BranchOp>(raw)) {
        auto *next = takeBlock(), *header = takeBlock(),
             *iteration = takeBlock(), *latch = takeBlock();
        if (!next || !header || !iteration || !latch || !bare(initial) ||
            initial.getDest() != header || cursor != current->end() ||
            header->getOperations().size() != 2 ||
            header->getNumArguments() != next->getNumArguments() + 1 ||
            !header->getArgument(0).getType().isSignlessInteger(64) ||
            mlir::TypeRange(header->getArgumentTypes()).drop_front() !=
                next->getArgumentTypes() ||
            latch->getArgumentTypes() != next->getArgumentTypes() ||
            latch->getOperations().size() != 3 || !charge(5))
          return fail("Host loop has an invalid control signature");
        auto compare = mlir::dyn_cast<mlir::arith::CmpIOp>(header->front());
        auto edge = mlir::dyn_cast<mlir::cf::CondBranchOp>(header->back());
        if (!compare || !bare(compare) ||
            compare.getPredicate() != mlir::arith::CmpIPredicate::ult ||
            compare.getLhs() != header->getArgument(0) || !edge ||
            !bare(edge) || edge.getBranchWeights() ||
            edge.getCondition() != compare.getResult() ||
            edge.getTrueDest() != iteration || edge.getFalseDest() != next ||
            edge.getFalseDestOperands() !=
                header->getArguments().drop_front() ||
            edge.getTrueDestOperands().size() < header->getNumArguments() ||
            edge.getTrueDestOperands().take_front(header->getNumArguments()) !=
                header->getArguments())
          return fail("Host loop bounds, carried values or captures differ");
        auto one = mlir::dyn_cast<mlir::arith::ConstantIntOp>(latch->front());
        auto add =
            mlir::dyn_cast<mlir::arith::AddIOp>(*std::next(latch->begin()));
        if (!one || !bare(one) || one.value() != 1 ||
            !one.getType().isSignlessInteger(64) || !add || !bare(add) ||
            add.getOverflowFlags() != mlir::arith::IntegerOverflowFlags::none ||
            add.getLhs() != header->getArgument(0) ||
            add.getRhs() != one.getResult())
          return fail("Host loop does not advance by one unsigned index");
        SmallVector<mlir::Value> advanced{add.getResult()};
        append_range(advanced, latch->getArguments());
        if (!branch(&latch->back(), header, advanced))
          return fail("Host loop successor values differ");
        operation["op"] = "for";
        operation["carried"] = next->getNumArguments();
        inputs.push_back(initial.getDestOperands().front());
        inputs.push_back(compare.getRhs());
        append_range(inputs, initial.getDestOperands().drop_front());
        append_range(inputs, edge.getTrueDestOperands().drop_front(
                                 header->getNumArguments()));
        auto nested = body(iteration, latch, depth + 1);
        if (!nested)
          return nested.takeError();
        operation["regions"] = json::Array{std::move(*nested)};
        advance(next);
        append_range(outputs, next->getArguments());
      } else if (auto match = mlir::dyn_cast<data::MatchOp>(raw)) {
        auto *next = takeBlock();
        if (!next || !attributes(match, {"alternatives"}) ||
            cursor != current->end())
          return fail("Host match has invalid control metadata");
        SmallVector<mlir::Block *> arms;
        for (auto target : match.getArms()) {
          auto *arm = takeBlock();
          if (!arm || arm != target)
            return fail("Host match successor inventory differs");
          arms.push_back(arm);
        }
        json::Array names, regions;
        for (auto label : match.getAlternatives()) {
          auto name = mlir::cast<mlir::StringAttr>(label).getValue();
          if (!charge() || !bytes(name.size()))
            return fail("Host match alternatives exceed export limits");
          names.push_back(name.str());
        }
        for (auto *arm : arms) {
          auto nested = body(arm, next, depth + 1);
          if (!nested)
            return nested.takeError();
          regions.push_back(std::move(*nested));
        }
        operation["op"] = "match";
        operation["alternatives"] = std::move(names);
        operation["regions"] = std::move(regions);
        append_range(inputs, match->getOperands());
        advance(next);
        append_range(outputs, next->getArguments());
      } else {
        StringRef name = raw->getName().getStringRef();
        StringRef attribute;
        bool total = false;
        if (name == "data.construct") {
          operation["op"] = "construct";
          attribute = "alternative";
          total = true;
        } else if (name == "data.unpack") {
          operation["op"] = "unpack";
          total = true;
        } else if (name == "data.project") {
          operation["op"] = "project";
          attribute = "path";
          total = true;
        } else if (name == "func.call") {
          operation["op"] = "call";
          attribute = "callee";
        } else if (name == "exec.numeric") {
          operation["op"] = "numeric";
          attribute = "calculation";
        } else if (name == "exec.invoke") {
          operation["op"] = "invoke";
          attribute = "deployment";
        } else if (name == "exec.require")
          operation["op"] = "require";
        else if (name == "exec.drop")
          operation["op"] = "drop";
        else
          return fail("Host original contains an unsupported operation");
        if (!attributes(raw, attribute.empty()
                                 ? ArrayRef<StringRef>{}
                                 : ArrayRef<StringRef>{attribute}))
          return fail("Host operation has unexpected metadata");
        if (attribute == "path") {
          auto path = raw->getAttrOfType<mlir::DenseI64ArrayAttr>(attribute);
          if (!path)
            return fail("Host projection has no typed path");
          json::Array indices;
          for (auto index : path.asArrayRef()) {
            if (!charge())
              return fail("Host projection exceeds export work");
            indices.push_back(index);
          }
          operation[attribute] = std::move(indices);
        } else if (attribute == "callee") {
          auto callee = raw->getAttrOfType<mlir::FlatSymbolRefAttr>(attribute);
          if (!callee || !bytes(callee.getValue().size()))
            return fail("Host call has no local symbol reference");
          operation[attribute] = callee.getValue().str();
        } else if (!attribute.empty()) {
          auto value = raw->getAttrOfType<mlir::StringAttr>(attribute);
          if (!value || !bytes(value.getValue().size()))
            return fail("Host operation has invalid named metadata");
          operation[attribute] = value.getValue().str();
        }
        append_range(inputs, raw->getOperands());
        if (total)
          append_range(outputs, raw->getResults());
        else {
          auto dispatch = mlir::dyn_cast_or_null<exec::DispatchOp>(take());
          auto *next = takeBlock();
          if (!dispatch || !next || raw->getNumResults() != 1 ||
              !bare(dispatch) || dispatch.getOutcome() != raw->getResult(0) ||
              dispatch.getReturned() != next ||
              dispatch.getStopped() != failure || cursor != current->end())
            return fail("Host call did not dispatch its exact outcome");
          advance(next);
          append_range(outputs, next->getArguments());
        }
      }
      auto operands = uses(inputs, env);
      if (!operands)
        return operands.takeError();
      auto results = definitions(outputs, env);
      if (!results)
        return results.takeError();
      operation["operands"] = std::move(*operands);
      operation["results"] = std::move(*results);
      steps.push_back(std::move(operation));
    }
    return fail(
        "Host body is missing a terminal outcome or exhausted its allowance");
  }

public:
  Reader(const Limits &limits)
      : limits(limits), work(limits.work), metadata(limits.irBytes) {}
  Expected<json::Array> run(mlir::ModuleOp module) {
    json::Array functions;
    for (auto function : module.getOps<mlir::func::FuncOp>()) {
      auto names = function->getAttrOfType<mlir::ArrayAttr>("entry.parameters");
      if (!names || !charge() || !bytes(function.getSymName().size()) ||
          function->getAttrs().size() != 3 || function.getBody().empty() ||
          names.size() != function.getNumArguments() ||
          function.getFunctionType().getNumResults() != 1 ||
          functions.size() >= limits.instances)
        return fail("invalid native Host function or parameter inventory");
      outcome =
          mlir::dyn_cast<exec::OutcomeType>(function.getResultTypes().front());
      if (!outcome || outcome.getPayload().size() != 1)
        return fail("Host function must return one logical outcome payload");
      json::Array parameters;
      StringSet<> unique;
      for (auto [name, input] : zip(names, function.getArgumentTypes())) {
        auto text = mlir::dyn_cast<mlir::StringAttr>(name);
        if (!text || !charge() || !bytes(text.getValue().size()) ||
            text.getValue().empty() ||
            text.getValue().size() > limits.identifierBytes ||
            !json::isUTF8(text.getValue()) ||
            !unique.insert(text.getValue()).second)
          return fail("invalid Host parameter name");
        auto type = schema(input);
        if (!type)
          return type.takeError();
        parameters.push_back(json::Object{{"name", text.getValue().str()},
                                          {"schema", std::move(*type)}});
      }
      auto result = schema(outcome.getPayload().front());
      if (!result)
        return result.takeError();
      region = &function.getBody();
      nextBlock = std::next(region->begin());
      failure = takeBlock();
      if (!failure || failure->getNumArguments() != 1 ||
          !mlir::isa<exec::StopType>(failure->getArgument(0).getType()) ||
          failure->getOperations().size() != 2 || !charge(2))
        return fail("Host function has no terminal failure block");
      auto stopped = mlir::dyn_cast<exec::FailureOp>(failure->front());
      auto ret = mlir::dyn_cast<mlir::func::ReturnOp>(failure->back());
      if (!stopped || !ret || !bare(stopped) || !bare(ret) ||
          stopped.getStop() != failure->getArgument(0) ||
          stopped.getOutcome().getType() != outcome ||
          ret.getOperands() != stopped->getResults())
        return fail("Host terminal failure was not propagated");
      next = 0;
      auto actual = body(&region->front(), nullptr);
      if (!actual)
        return actual.takeError();
      if (nextBlock != region->end())
        return fail("Host original has uninspected control blocks");
      functions.push_back(json::Object{
          {"signature", json::Object{{"symbol", function.getSymName().str()},
                                     {"parameters", std::move(parameters)},
                                     {"result", std::move(*result)}}},
          {"body", std::move(*actual)}});
    }
    if (functions.empty())
      return fail("Host original contains no functions");
    return functions;
  }
};
} // namespace
Expected<json::Array> reconstructNativeHost(mlir::ModuleOp module,
                                            const Limits &limits) {
  return Reader(limits).run(module);
}
} // namespace zkc::language::entry_detail
