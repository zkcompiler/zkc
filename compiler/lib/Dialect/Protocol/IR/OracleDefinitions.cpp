#include "OracleAnalysis.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Analysis/TotalClosure.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSet.h"
using namespace mlir;
namespace zkc::protocol_ir {
unsigned OracleDefinitionOp::getNumSources() {
  unsigned sources = 0;
  for (Type input : getFunctionType().getInputs()) {
    if (!isa<OracleHandleType>(input))
      break;
    ++sources;
  }
  return sources;
}
LogicalResult OracleDefinitionOp::verifyRegions() {
  auto signature = getFunctionType();
  auto kind = getKind();
  if (signature.getNumInputs() == 0 || signature.getNumInputs() > 1024 ||
      signature.getNumResults() != 1 ||
      signature.getInput(signature.getNumInputs() - 1) != kind.getQueryType() ||
      signature.getResult(0) != kind.getAnswerType())
    return emitOpError(
        "signature must end with its kind's position and answer");
  if (!llvm::hasSingleElement(getBody()) || getBody().front().empty() ||
      getBody().front().getArgumentTypes() != signature.getInputs())
    return emitOpError("requires one query body with the declared arguments");
  auto yield = dyn_cast<OracleYieldOp>(getBody().front().back());
  if (!yield || yield.getAnswer().getType() != kind.getAnswerType())
    return emitOpError("query body must yield the kind's answer");
  if (kind.getStaticRows()) {
    if (getShapeArgument() || getMaximumRows())
      return emitOpError("a sized virtual kind has no dynamic shape metadata");
  } else if (!getShapeArgument() || !getMaximumRows() ||
             *getShapeArgument() < getNumSources() ||
             *getShapeArgument() >= signature.getNumInputs() - 1 ||
             !signature.getInput(*getShapeArgument()).isUnsignedInteger(64))
    return emitOpError(
        "a dynamic virtual shape requires an index parameter and maximum");
  return success();
}
LogicalResult
OracleDefinitionOp::verifySymbolUses(SymbolTableCollection &tables) {
  auto predicate = tables.lookupNearestSymbolFrom<relation::DeclareOp>(
      *this, getAdmissibilityAttr());
  if (!predicate)
    return emitOpError(
        "admissibility must name a retained relation declaration");
  if (!getFunctionType().getNumInputs())
    return emitOpError("admissibility requires a nonempty query signature");
  SmallVector<Type> inputs;
  for (Type input : getFunctionType().getInputs().drop_back())
    inputs.push_back(isa<OracleHandleType>(input)
                         ? cast<OracleHandleType>(input).getKind().getDataType()
                         : input);
  if (predicate.getSignature().getInputs() != ArrayRef<Type>(inputs) ||
      predicate.getSignature().getNumResults() != 1 ||
      !predicate.getSignature().getResult(0).isSignlessInteger(1))
    return emitOpError(
        "admissibility must read source data and ordinary parameters");
  return success();
}
LogicalResult OracleVirtualOp::verifySymbolUses(SymbolTableCollection &tables) {
  auto declaration = tables.lookupNearestSymbolFrom<OracleDefinitionOp>(
      *this, getCalleeAttr());
  if (!declaration || !declaration.getFunctionType().getNumInputs() ||
      getInputs().getTypes() !=
          declaration.getFunctionType().getInputs().drop_back() ||
      getHandle().getType().getKind() != declaration.getKind())
    return emitOpError(
        "virtual construction must match its closed declaration");
  return success();
}
} // namespace zkc::protocol_ir
namespace zkc::mathematical {
LogicalResult verifyOracleDefinitions(protocol_ir::ProtocolModuleOp module,
                                      TotalClosure &helpers,
                                      NativeTypePolicies &types,
                                      unsigned &remaining) {
  auto refuse = [](Operation *op, llvm::StringRef detail) {
    return diagnostics::emit(op->emitOpError(), "mathematical-formation",
                             detail);
  };
  auto charge = [&](Operation *op, uint64_t amount) -> LogicalResult {
    if (amount > remaining)
      return diagnostics::emit(op->emitOpError(), "mathematical-analysis-limit",
                               "virtual query analysis budget exhausted");
    remaining -= amount;
    return success();
  };
  for (auto declaration :
       module.getBody().front().getOps<protocol_ir::OracleDefinitionOp>()) {
    if (failed(declaration->getName().verifyInvariants(declaration)) ||
        failed(declaration.verifyRegions()))
      return failure();
    for (auto attr : declaration->getAttrs())
      if (!llvm::is_contained(declaration.getAttributeNames(),
                              attr.getName().getValue()))
        return refuse(declaration, "unexpected virtual declaration attribute");
    unsigned sources = declaration.getNumSources();
    auto &body = declaration.getBody().front();
    if (failed(charge(declaration, body.getNumArguments() + 1)))
      return failure();
    llvm::DenseMap<Value, bool> answers;
    for (auto [index, argument] : llvm::enumerate(body.getArguments())) {
      if (index >= sources) {
        auto policy = types.get(argument.getType());
        if (!policy || !policy->total)
          return refuse(declaration,
                        "virtual parameters require ordinary total data");
      }
      answers[argument] = false;
    }
    llvm::StringSet<> sites;
    for (auto &operation : body) {
      auto *op = &operation;
      if (failed(charge(op, 1 + op->getNumOperands() + op->getNumResults())) ||
          failed(op->getName().verifyInvariants(op)))
        return failure();
      if (op->getNumRegions())
        return refuse(
            op,
            "virtual query bodies cannot contain control or execution regions");
      for (Value input : op->getOperands())
        if (!answers.count(input))
          return refuse(op,
                        "virtual query operand is outside its admitted body");
      if (auto query = dyn_cast<protocol_ir::OracleQueryOp>(op)) {
        for (auto attr : op->getAttrs())
          if (!llvm::is_contained(query.getAttributeNames(),
                                  attr.getName().getValue()))
            return refuse(op, "unexpected virtual query attribute");
        auto source = dyn_cast<BlockArgument>(query.getHandle());
        if (!source || source.getOwner() != &body ||
            source.getArgNumber() >= sources)
          return refuse(op,
                        "virtual queries must use a declared source handle");
        if (answers.lookup(query.getPosition()))
          return refuse(
              op, "virtual query positions cannot depend on earlier answers");
        auto site = query.getSite();
        if (site.empty() ||
            !(llvm::isAlpha(site.front()) || site.front() == '_') ||
            !llvm::all_of(
                site, [](char c) { return llvm::isAlnum(c) || c == '_'; }) ||
            !sites.insert(site).second)
          return refuse(op, "virtual query sites must be distinct identifiers");
        answers[query.getAnswer()] = true;
      } else if (isa<protocol_ir::OracleYieldOp>(op)) {
        if (&body.back() != op || !op->getAttrs().empty())
          return refuse(op, "invalid virtual query terminator");
      } else if (auto call = dyn_cast<func::CallOp>(op)) {
        if (failed(verifyOperation(op, Context::Helper)))
          return failure();
        const TotalSummary *summary;
        if (failed(helpers.get(call, summary)) ||
            failed(charge(op, uint64_t(summary->expandedOperations) +
                                  summary->replayIndices)))
          return failure();
        for (auto [output, dependencies] :
             llvm::zip(call.getResults(), summary->results)) {
          bool depends = false;
          for (int index = dependencies.find_first(); index >= 0;
               index = dependencies.find_next(index))
            depends |= answers.lookup(call.getOperand(index));
          answers[output] = depends;
        }
      } else if (isTotal(op)) {
        if (failed(verifyOperation(op, Context::Helper)) ||
            failed(verifyTotalTypes(op, types)))
          return failure();
        finite::Summary finiteSummary;
        if (finite::isComputation(op) &&
            failed(finite::summarize(op, finiteSummary)))
          return failure();
        for (auto [index, output] : llvm::enumerate(op->getResults())) {
          auto inputs = operandDependencies(op, index);
          if (failed(inputs) || failed(charge(op, inputs->size())))
            return failure();
          bool depends = false;
          for (unsigned input : *inputs)
            depends |= answers.lookup(op->getOperand(input));
          answers[output] = depends;
        }
      } else
        return refuse(
            op,
            "virtual bodies contain only source queries and total mathematics");
    }
    if (failed(helpers.verifyObservations(body)))
      return failure();
  }
  return success();
}
} // namespace zkc::mathematical
