#include "OracleMerkle.h"
#include "RealizationEmission.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Support/Refusal.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
using Values = SmallVector<Value>;
using Types = SmallVector<Type>;
using Control = exec::ScopedExecutionBuilder;
struct Emitter {
  protocol_ir::ProtocolModuleOp unit;
  OpBuilder builder;
  mathematical::RealizationEmitter bindings;
  Type index, boolean;
  unsigned next = 0;
  explicit Emitter(protocol_ir::ProtocolModuleOp unit)
      : unit(unit), builder(unit.getContext()),
        bindings(unit, "_oracle_merkle_binding_"),
        index(IntegerType::get(unit.getContext(), 64, IntegerType::Unsigned)),
        boolean(builder.getI1Type()) {}
  func::FuncOp function(StringRef label, TypeRange inputs, TypeRange outputs,
                        bool region,
                        llvm::function_ref<void(Control &, ValueRange)> emit) {
    OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToEnd(&unit.getBody().front());
    std::string name;
    do {
      name = "_oracle_merkle_" + label.str() + "_" + std::to_string(next++);
    } while (SymbolTable::lookupSymbolIn(unit, name));
    Types formals{runtime::ScopeType::get(unit.getContext())};
    append_range(formals, inputs);
    auto outcome = exec::OutcomeType::get(unit.getContext(), Types(outputs));
    auto helper =
        func::FuncOp::create(builder, unit.getLoc(), name,
                             builder.getFunctionType(formals, outcome));
    helper.setPrivate();
    helper.setNoInline(true);
    if (region)
      helper->setAttr("runtime.region", builder.getUnitAttr());
    else
      helper->setAttr("runtime.origin",
                      builder.getArrayAttr({builder.getStringAttr(name),
                                            builder.getArrayAttr({})}));
    builder.setInsertionPointToEnd(helper.addEntryBlock());
    Control control(builder, helper);
    emit(control, helper.getArguments().drop_front());
    return helper;
  }
  Values apply(Control &c, StringRef contract, TypeRange outputs,
               ValueRange inputs, StringRef site,
               ArrayRef<Attribute> statics = {},
               ArrayRef<Attribute> parameters = {}) {
    auto binding =
        bindings.binding(builder, unit.getLoc(),
                         {contract.str(), SmallVector<Attribute>(statics), ""});
    return c.invoke(
        "exec.apply", outputs, c.scoped(inputs),
        {builder.getNamedAttr("binding", binding),
         builder.getNamedAttr("parameters", builder.getArrayAttr(parameters)),
         builder.getNamedAttr("site", builder.getStringAttr(site))});
  }
  Value number(Control &c, uint64_t n, StringRef site) {
    return apply(c, "index.constant", index, {}, site, {},
                 {builder.getIntegerAttr(index, n)})[0];
  }
  Value binary(Control &c, StringRef contract, Value a, Value b,
               StringRef site) {
    return apply(c, contract,
                 contract == "index.less" || contract == "index.equal" ? boolean
                                                                       : index,
                 {a, b}, site)[0];
  }
  void require(Control &c, Value predicate, StringRef site) {
    apply(c, "control.require", {}, predicate, site);
  }
  Values call(Control &c, func::FuncOp callee, ValueRange inputs,
              StringRef site) {
    auto outputs =
        cast<exec::OutcomeType>(callee.getResultTypes()[0]).getPayload();
    return c.invoke(
        "func.call", outputs, c.scoped(inputs),
        {builder.getNamedAttr("callee", FlatSymbolRefAttr::get(callee)),
         builder.getNamedAttr("runtime.site", builder.getStringAttr(site))});
  }
  func::FuncOp position(OracleLeafGrouping grouping, OracleLeafOrder order) {
    bool paired = grouping == OracleLeafGrouping::AntipodalPairs;
    bool reversed = order == OracleLeafOrder::BitReversed;
    return function(
        "position", {index, index}, {index, index, index}, false,
        [&](Control &c, ValueRange a) {
          auto zero = number(c, 0, "zero");
          auto one = number(c, 1, "one");
          auto width = number(c, paired ? 2 : 1, "width");
          require(c, binary(c, "index.less", zero, a[0], "nonempty"),
                  "admit_rows");
          require(c, binary(c, "index.less", a[1], a[0], "in_domain"),
                  "admit_query");
          if (paired) {
            auto remainder =
                binary(c, "index.mod", a[0], width, "pair_remainder");
            require(c, binary(c, "index.equal", remainder, zero, "paired"),
                    "admit_pairs");
          }
          auto height = binary(c, "index.div", a[0], width, "height");
          auto leaf = binary(c, "index.mod", a[1], height, "logical_leaf");
          auto slot = binary(c, "index.div", a[1], height, "slot");
          Types stateTypes{index};
          Values seeds{height};
          if (reversed) {
            append_range(stateTypes, Types{index, index});
            append_range(seeds, Values{leaf, zero});
          }
          // Native admission checks a range's declared bound before execution.
          // Clamp it to 64 even though early completion already visits <=63
          // bits. The lower bound of one keeps the singleton loop empty.
          auto limit = number(c, 64, "bit_limit");
          auto small = binary(c, "index.less", height, limit, "small_height");
          auto upper = c.conditional(
              small, {height, limit}, index, "bit_bound", [&](unsigned branch) {
                return function("bit_bound", {index, index}, index, true,
                                [&](Control &body, ValueRange inputs) {
                                  body.complete(inputs[branch]);
                                });
              })[0];
          auto state = c.loop(
              one, upper, seeds, {}, stateTypes, true, "layout_bits",
              [&](unsigned) {
                Types inputs{index};
                append_range(inputs, stateTypes);
                Types outputs{boolean};
                append_range(outputs, stateTypes);
                return function(
                    "layout_bit", inputs, outputs, true,
                    [&](Control &body, ValueRange b) {
                      auto zero = number(body, 0, "bit_zero");
                      auto one = number(body, 1, "bit_one");
                      auto two = number(body, 2, "bit_two");
                      auto remainder = binary(body, "index.mod", b[1], two,
                                              "span_remainder");
                      require(body,
                              binary(body, "index.equal", remainder, zero,
                                     "even_span"),
                              "admit_span");
                      auto span =
                          binary(body, "index.div", b[1], two, "next_span");
                      Values next{span};
                      if (reversed) {
                        auto bit =
                            binary(body, "index.mod", b[2], two, "low_bit");
                        auto rest = binary(body, "index.div", b[2], two,
                                           "remaining_bits");
                        auto shifted = binary(body, "index.mul", b[3], two,
                                              "shift_reversed");
                        auto value = binary(body, "index.add", shifted, bit,
                                            "append_bit");
                        append_range(next, Values{rest, value});
                      }
                      Values yielded{
                          binary(body, "index.less", one, span, "more_bits")};
                      append_range(yielded, next);
                      body.complete(yielded);
                    });
              });
          c.returned({height, reversed ? state[2] : leaf, slot});
        });
  }
};
} // namespace
Expected<OracleMerkleFunctions>
emitOracleMerkle(ModuleOp candidate, protocol_ir::OracleKindAttr kind,
                 StringRef scheme, OracleLeafGrouping grouping,
                 OracleLeafOrder order) {
  auto layout = OracleTableLayout::create(2, grouping, order);
  if (!layout) {
    consumeError(layout.takeError());
    return error("oracle-merkle");
  }
  if (!candidate || !hasSingleElement(candidate.getBody()->getOperations()) ||
      !kind || kind.getContext() != candidate.getContext() ||
      kind.getIdentity() != "table" ||
      failed(protocol_ir::OracleKindAttr::verify(
          [&]() { return emitError(candidate.getLoc()); }, kind.getIdentity(),
          kind.getArguments())))
    return error("oracle-merkle");
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol)
    return error("oracle-merkle");
  auto *context = candidate.getContext();
  auto signature = resolveLogicalSignature(
      [&] { return emitError(candidate.getLoc()); }, context, "oracle.commit",
      {StringAttr::get(context, scheme)});
  auto opening = resolveLogicalSignature(
      [&] { return emitError(candidate.getLoc()); }, context, "oracle.open",
      {StringAttr::get(context, scheme)});
  auto answer = dyn_cast<algebra::FieldType>(kind.getAnswerType());
  if (!answer || !signature || !opening || signature.getNumInputs() != 2 ||
      signature.getNumResults() != 2 || opening.getNumInputs() != 2 ||
      opening.getNumResults() != 2 ||
      signature.getInput(0) != kind.getDataType() ||
      opening.getInput(0) != signature.getResult(1) ||
      opening.getResult(0) != kind.getDataType())
    return error("oracle-merkle");
  Type root = signature.getResult(0);
  Type state = signature.getResult(1);
  Type proof = opening.getResult(1);
  Emitter e(unit);
  auto index = e.index;
  OracleMerkleFunctions result;
  result.position = e.position(grouping, order);
  result.commit = e.function(
      "commit", {kind.getDataType(), index}, {root, state}, false,
      [&](Control &c, ValueRange a) {
        auto zero = e.number(c, 0, "first_query");
        auto position = e.call(c, result.position, {a[1], zero}, "layout");
        auto count = e.apply(c, "vector.length", index, a[0], "actual_rows",
                             {StringAttr::get(context, answer.getDomain())})[0];
        e.require(c, e.binary(c, "index.equal", count, a[1], "exact_rows"),
                  "admit_data");
        auto width = e.number(c, layout->width(), "width");
        Value values = a[0];
        if (grouping == OracleLeafGrouping::AntipodalPairs)
          values = e.apply(c, "vector.transpose", kind.getDataType(),
                           {values, width, position[0]}, "group_rows",
                           {StringAttr::get(context, answer.getDomain())})[0];
        if (order == OracleLeafOrder::BitReversed)
          values = e.apply(c, "vector.bit_reverse_rows", kind.getDataType(),
                           {values, width}, "permute_leaves",
                           {StringAttr::get(context, answer.getDomain())})[0];
        c.returned(e.apply(c, "oracle.commit", {root, state}, {values, width},
                           "commit", {StringAttr::get(context, scheme)}));
      });
  result.open = e.function(
      "open", {state, index, index}, {kind.getDataType(), proof}, false,
      [&](Control &c, ValueRange a) {
        auto position = e.call(c, result.position, {a[1], a[2]}, "layout");
        c.returned(e.apply(c, "oracle.open", {kind.getDataType(), proof},
                           {a[0], position[1]}, "open",
                           {StringAttr::get(context, scheme)}));
      });
  result.authenticate = e.function(
      "authenticate", {root, index, index, kind.getDataType(), proof},
      kind.getAnswerType(), false, [&](Control &c, ValueRange a) {
        auto position = e.call(c, result.position, {a[1], a[2]}, "layout");
        auto width = e.number(c, layout->width(), "width");
        auto valid =
            e.apply(c, "oracle.check", e.boolean,
                    {a[0], width, position[0], position[1], a[3], a[4]},
                    "authenticate", {StringAttr::get(context, scheme)})[0];
        e.require(c, valid, "admit_opening");
        c.returned(e.apply(c, "vector.get", kind.getAnswerType(),
                           {a[3], position[2]}, "answer",
                           {StringAttr::get(context, answer.getDomain())}));
      });
  return result;
}
} // namespace zkc::protocol
