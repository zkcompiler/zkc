#include "zkc/Dialect/IR.h"
#include "Internal.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Protocol/Bindings.h"
#include "zkc/Protocol/Kernels.h"
#include "zkc/Target/Json.h"

using namespace llvm;
using namespace mlir;
namespace zkc::claims {
namespace {
Expected<OwningOpRef<ModuleOp>> build(const Contract &contract,
                                      const Certificate &certificate,
                                      const Checked &checked,
                                      MLIRContext &ctx) {
  ctx.loadDialect<ClaimDialect, PIRDialect, AlgebraDialect, PolynomialDialect,
                  PCSDialect, PlanDialect>();
  OpBuilder b(&ctx);
  OwningOpRef<ModuleOp> module(ModuleOp::create(b.getUnknownLoc()));
  (*module)->setAttr("claim.source", b.getStringAttr(checked.source.digest));
  (*module)->setAttr("claim.contract", b.getStringAttr(checked.contractDigest));
  (*module)->setAttr("claim.entry", b.getStringAttr(contract.entry));
  (*module)->setAttr("claim.validator", b.getStringAttr(contract.validator));
  b.setInsertionPointToEnd(module->getBody());
  auto attr = [&](StringRef key, StringRef value) {
    return b.getNamedAttr(key, b.getStringAttr(value));
  };
  auto ref = [&](StringRef key, StringRef value) {
    return b.getNamedAttr(key, FlatSymbolRefAttr::get(&ctx, value));
  };
  auto array = [&](StringRef key, const source::Names &values) {
    SmallVector<StringRef> strings(values.begin(), values.end());
    return b.getNamedAttr(key, b.getStrArrayAttr(strings));
  };
  auto integer = [&](StringRef key, uint64_t n) {
    return b.getNamedAttr(key, b.getI64IntegerAttr(n));
  };
  auto make = [&](StringRef name, ValueRange operands, TypeRange types,
                  ArrayRef<NamedAttribute> attrs) {
    OperationState state(b.getUnknownLoc(), name);
    state.addOperands(operands);
    state.addTypes(types);
    state.addAttributes(attrs);
    return b.create(state);
  };
  make(
      "claim.kind", {}, {},
      {attr("sym_name", "kind_guard"), array("types", {"bool"}),
       attr("meaning", "Exact Boolean enforced by validator control.require")});
  for (const auto &kind : contract.kinds)
    make("claim.kind", {}, {},
         {attr("sym_name", "kind_" + kind.name), array("types", kind.types),
          attr("meaning", kind.meaning)});
  for (const auto &law : contract.laws)
    make("claim.law", {}, {},
         {attr("sym_name", "law_" + law.name), attr("premise", law.premise)});
  std::map<std::string, mlir::Value> values, pending;
  for (const auto &[id, value] : checked.source.values) {
    auto bound = protocol::parseBoundType(value.type, false);
    if (!bound)
      return bound.takeError();
    Type type = protocol::decodeBoundType(&ctx, *bound);
    if (!type)
      return error("claim-subject");
    values.emplace(id, make("claim.binding", {}, type,
                            {attr("id", id), attr("origin", value.origin),
                             attr("name", value.name)})
                           ->getResult(0));
  }
  auto operands = [&](const source::Names &names) {
    SmallVector<mlir::Value> out;
    for (const auto &name : names)
      out.push_back(values.at(name));
    return out;
  };
  for (const auto &[path, invocation] : checked.source.invocations) {
    auto inputs = operands(invocation.inputs);
    auto outputs = operands(invocation.outputs);
    inputs.append(outputs);
    make("claim.invocation", inputs, {},
         {attr("path", path), attr("callee", invocation.callee),
          attr("instance", invocation.instance),
          integer("input_count", invocation.inputs.size())});
  }
  for (const auto &[path, count] : checked.source.loops)
    make("claim.loop", {}, {}, {attr("path", path), integer("count", count)});
  for (const auto &claim : contract.claims)
    pending.emplace(claim.name, make("claim.pending", operands(claim.values),
                                     ClaimPendingType::get(&ctx),
                                     {ref("kind", "kind_" + claim.kind),
                                      attr("id", claim.name)})
                                    ->getResult(0));
  for (const auto &required : contract.required)
    make("claim.require", pending.at(required), {}, {});
  std::map<uint32_t, mlir::Value> evidence;
  for (const auto &terminal : contract.terminals) {
    auto value = values.at(checked.source.guards.at(terminal.guard).value);
    auto *op =
        make("claim.terminal", {pending.at(terminal.claim), value},
             ClaimEvidenceType::get(&ctx), {attr("guard", terminal.guard)});
    evidence[checked.claimIds.at(terminal.claim)] = op->getResult(0);
  }
  for (const auto &rule : contract.rules) {
    auto args = operands(rule.inputs);
    args.append(operands(rule.outputs));
    for (const auto &guard : rule.guards)
      args.push_back(values.at(checked.source.guards.at(guard).value));
    make("claim.rule", args, {},
         {attr("sym_name", "rule_" + rule.name), ref("law", "law_" + rule.law),
          attr("invocation", rule.invocation), attr("callee", rule.callee),
          integer("input_count", rule.inputs.size()),
          integer("output_count", rule.outputs.size()),
          array("guards", rule.guards), array("premises", rule.premises),
          attr("conclusion", rule.conclusion)});
  }
  for (const auto &name : certificate.steps) {
    const auto &rule = contract.rules[checked.ruleIds.at(name)];
    SmallVector<mlir::Value> premises;
    for (const auto &p : rule.premises)
      premises.push_back(evidence.at(checked.claimIds.at(p)));
    auto *op = make("claim.apply", premises, ClaimEvidenceType::get(&ctx),
                    {ref("rule", "rule_" + name)});
    evidence[checked.claimIds.at(rule.conclusion)] = op->getResult(0);
  }
  SmallVector<mlir::Value> requirements;
  for (uint32_t id : checked.required)
    requirements.push_back(evidence.at(id));
  make("claim.finish", requirements, {}, {});
  if (failed(verify(*module)))
    return error("claim-ir");
  return module;
}
} // namespace
Expected<OwningOpRef<ModuleOp>> import(const source::Module &module,
                                       const Contract &contract,
                                       const Certificate &certificate,
                                       MLIRContext &ctx) {
  auto checked = admit(module, contract);
  if (!checked)
    return checked.takeError();
  auto proof = steps(*checked, certificate);
  if (!proof)
    return proof.takeError();
  return build(contract, certificate, *checked, ctx);
}
Error checkIR(const source::Module &module, const Contract &contract,
              ModuleOp candidate) {
  if (!candidate || !llvm::hasSingleElement(candidate.getBodyRegion()) ||
      candidate.getBody()->getNumArguments())
    return error("claim-ir");
  size_t operations = 0;
  for (auto &op : *candidate.getBody())
    if (++operations > maxItems + 4 * maxRecords || op.getNumRegions() ||
        op.getNumSuccessors())
      return error("claim-ir");
  if (failed(verify(candidate)))
    return error("claim-ir");
  auto checked = admit(module, contract);
  if (!checked)
    return checked.takeError();
  auto source = candidate->getAttrOfType<StringAttr>("claim.source");
  auto authority = candidate->getAttrOfType<StringAttr>("claim.contract");
  if (!source || !authority)
    return error("claim-ir-mismatch");
  Certificate certificate{source.str(), authority.str(), {}};
  for (auto &op : *candidate.getBody())
    if (auto application = dyn_cast<ClaimApplyOp>(op)) {
      auto name = application.getRule();
      if (!name.consume_front("rule_") ||
          certificate.steps.size() >= maxRecords)
        return error("claim-ir-mismatch");
      certificate.steps.push_back(name.str());
    }
  auto proof = steps(*checked, certificate);
  if (!proof)
    return proof.takeError();
  auto expected =
      build(contract, certificate, *checked, *candidate.getContext());
  if (!expected)
    return expected.takeError();
  if (!OperationEquivalence::isEquivalentTo(
          candidate, **expected, OperationEquivalence::IgnoreLocations))
    return error("claim-ir-mismatch");
  return Error::success();
}
} // namespace zkc::claims
