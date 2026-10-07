#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/AsmState.h"
#include "mlir/IR/Builders.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Translation/Language.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>

using namespace llvm;
namespace zkc::language {
Expected<std::string> emitOriginal(const CheckedProject &project,
                                   mlir::MLIRContext &context,
                                   const Limits &limits) {
  if (auto error = checkLimits(limits))
    return std::move(error);
  if (project.checkedWork() > limits.work ||
      project.declarations().size() > limits.declarations)
    return error("source.limit",
                 "checked project exceeds requested emission limits");
  if (!hasProtocolDialects(context))
    return error("source.dialects",
                 "native dialects must be loaded before source emission");
  mlir::OpBuilder builder(&context);
  auto location = builder.getUnknownLoc();
  mlir::OwningOpRef<mlir::ModuleOp> module(mlir::ModuleOp::create(location));
  auto type = [&](const Type &source) -> mlir::Type {
    return source.kind == Type::Kind::Boolean
               ? mlir::Type(builder.getI1Type())
               : algebra::FieldType::get(&context, source.domain);
  };
  auto make =
      [&](StringRef name, mlir::TypeRange results, mlir::ValueRange operands,
          ArrayRef<mlir::NamedAttribute> attributes, bool region = false) {
        mlir::OperationState state(location, name);
        state.addOperands(operands);
        state.addTypes(results);
        state.addAttributes(attributes);
        if (region)
          state.addRegion()->push_back(new mlir::Block());
        return builder.create(state);
      };
  auto named = [&](StringRef name, mlir::Attribute value) {
    return builder.getNamedAttr(name, value);
  };
  builder.setInsertionPointToEnd(module->getBody());
  auto *protocolModule =
      make("protocol.module", {}, {},
           {named("profile", protocol_ir::ProfileAttr::get(
                                 &context, protocol_ir::Profile::Protocol))},
           true);
  uint64_t count = 0;
  for (const auto &decl : project.declarations()) {
    if (!decl.body)
      continue;
    builder.setInsertionPointToEnd(&protocolModule->getRegion(0).front());
    SmallVector<mlir::Type> inputs, outputs;
    for (const auto &port : decl.inputs)
      inputs.push_back(type(port.type));
    for (const auto &port : decl.outputs)
      outputs.push_back(type(port.type));
    bool protocol = decl.kind == Declaration::Kind::Protocol;
    auto roleSet = [&](ArrayRef<unsigned> indices) {
      SmallVector<mlir::Attribute> attrs;
      for (unsigned index : indices)
        attrs.push_back(builder.getStringAttr(decl.roles[index]));
      return builder.getArrayAttr(attrs);
    };
    SmallVector<mlir::NamedAttribute> attrs{
        named("sym_name", builder.getStringAttr(decl.symbol)),
        named("function_type",
              mlir::TypeAttr::get(builder.getFunctionType(inputs, outputs)))};
    if (protocol) {
      SmallVector<mlir::Attribute> roster, ins, outs;
      for (const auto &role : decl.roles)
        roster.push_back(builder.getStringAttr(role));
      for (const auto &port : decl.inputs)
        ins.push_back(roleSet(port.roles));
      for (const auto &port : decl.outputs)
        outs.push_back(roleSet(port.roles));
      attrs.append({named("roles", builder.getArrayAttr(roster)),
                    named("input_roles", builder.getArrayAttr(ins)),
                    named("output_roles", builder.getArrayAttr(outs))});
    } else
      attrs.push_back(
          named("sym_visibility", builder.getStringAttr("private")));
    auto *function =
        make(protocol ? "protocol.func" : "func.func", {}, {}, attrs, true);
    auto &block = function->getRegion(0).front();
    SmallVector<mlir::Value> values;
    for (auto input : inputs)
      values.push_back(block.addArgument(input, location));
    builder.setInsertionPointToEnd(&block);
    for (const auto &op : decl.body->operations) {
      if (++count > limits.operations)
        return error("source.limit", "emitted operation count limit exceeded");
      mlir::Operation *actual = nullptr;
      auto resultType = type(decl.body->values[op.result.index].type);
      if (const auto *math = std::get_if<MathValue>(&op.action)) {
        SmallVector<mlir::Value> operands;
        for (auto id : math->operands)
          operands.push_back(values[id.index]);
        switch (math->identity) {
        case MathematicalIdentity::BooleanConstant:
          actual = mlir::arith::ConstantIntOp::create(
              builder, location, math->literal == "true", 1);
          break;
        case MathematicalIdentity::BooleanEqual:
          actual = mlir::arith::CmpIOp::create(builder, location,
                                               mlir::arith::CmpIPredicate::eq,
                                               operands[0], operands[1]);
          break;
        case MathematicalIdentity::FieldConstant:
          actual = make("algebra.constant", resultType, {},
                        {named("value", builder.getStringAttr(math->literal))});
          break;
        case MathematicalIdentity::FieldAdd:
          actual = make("algebra.field_add", resultType, operands, {});
          break;
        case MathematicalIdentity::FieldSubtract:
          actual = make("algebra.field_subtract", resultType, operands, {});
          break;
        case MathematicalIdentity::FieldMultiply:
          actual = make("algebra.field_multiply", resultType, operands, {});
          break;
        case MathematicalIdentity::FieldEqual:
          actual = make("algebra.field_equal", resultType, operands, {});
          break;
        default:
          return error("source.emission",
                       "unsupported checked mathematical identity");
        }
      } else if (const auto *call = std::get_if<HelperCall>(&op.action)) {
        SmallVector<mlir::Value> operands;
        for (auto id : call->operands)
          operands.push_back(values[id.index]);
        actual = make(
            "func.call", resultType, operands,
            {named("callee",
                   mlir::FlatSymbolRefAttr::get(
                       &context,
                       project.declarations()[call->callee.index].symbol))});
      } else if (const auto *exchange = std::get_if<Exchange>(&op.action)) {
        actual = make(
            "protocol.exchange", resultType, values[exchange->payload.index],
            {named("sender",
                   builder.getStringAttr(decl.roles[exchange->sender])),
             named("receiver",
                   builder.getStringAttr(decl.roles[exchange->receiver])),
             named("site",
                   builder.getStringAttr("s" + std::to_string(op.statement)))});
      } else {
        const auto &restriction = std::get<Restriction>(op.action);
        actual = make("protocol.restrict_roles", resultType,
                      values[restriction.input.index],
                      {named("roles", roleSet(restriction.roles))});
      }
      if (const auto *exchange = std::get_if<Exchange>(&op.action)) {
        if (++count > limits.operations)
          return error("source.limit",
                       "emitted operation count limit exceeded");
        actual =
            make("protocol.restrict_roles", resultType, actual->getResult(0),
                 {named("roles", roleSet({exchange->receiver}))});
      }
      values.push_back(actual->getResult(0));
    }
    SmallVector<mlir::Value> results;
    for (auto id : decl.body->results)
      results.push_back(values[id.index]);
    make(protocol ? "protocol.return" : "func.return", {}, results, {});
  }
  std::string result;
  // Host processes can register MLIR printer flags. Identity bytes use our
  // fixed scalar printing policy, independently of those global preferences.
  mlir::OpPrintingFlags flags;
  flags.printGenericOpForm(true)
      .enableDebugInfo(false)
      .skipRegions(false)
      .assumeVerified(false)
      .useLocalScope(false)
      .printValueUsers(false)
      .printUniqueSSAIDs(false)
      .printNameLocAsPrefix(false);
  mlir::AsmState state(*module, flags);
  BoundedStream stream(result, limits.irBytes);
  module->print(stream, state);
  stream << '\n';
  if (stream.overflow())
    return error("source.limit", "emitted MLIR byte limit exceeded");
  return result;
}
} // namespace zkc::language
