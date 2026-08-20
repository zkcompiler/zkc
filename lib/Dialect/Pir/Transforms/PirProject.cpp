//===- PirProject.cpp - the projection boundary -----------------*- C++ -*-===//
// The Fiat-Shamir handler, applied (docs/spec/boundaries.md §2,
// kernel.md §9.2): challenges become squeezes over a threaded sponge,
// slots become stream reads, the claim graph is erased into the
// decision structure, and every emitted op carries the canonical event
// positions it covers. Realization coverage (COV_realized, kernel.md
// §6.2) is proved at this boundary: the emitted program's coverage
// must equal the seal-derived obligation set — set equality per
// position, op families licensed per obligation — never a bare count.
// The walk is deterministic; the reference oracle computes the same
// artifact and byte parity on its encoding is the acceptance gate.
//===----------------------------------------------------------------------===//

#include "zkc/Dialect/Pir/Transforms/Passes.h"
#include "zkc/Dialect/Pir/Transforms/Projection.h"

#include "Artifact/ArtifactInternal.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Artifact/Artifact.h"
#include "zkc/Dialect/Oir/OirOps.h"
#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Encoding/CanonicalEncoder.h"
#include "zkc/Encoding/EncodingDomain.h"
#include "zkc/Registry/ProtocolEnvironment.h"
#include "zkc/Registry/ProtocolVocabulary.h"
#include "zkc/Semantics/SealBattery.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/TypeSwitch.h"
#include "llvm/Support/raw_ostream.h"

#include <functional>
#include <memory>
#include <string>
#include <utility>

namespace zkc {
namespace pir {

#define GEN_PASS_DEF_PIRPROJECT
#include "zkc/Dialect/Pir/Transforms/Passes.h.inc"

} // namespace pir
} // namespace zkc

using namespace mlir;

struct zkc::pir::ProjectedOirArtifact::Storage {
  Storage(artifact::detail::MutablePirArtifact backing,
          oir::ArtifactOp projected, EndpointKind endpointKind)
      : backing(std::move(backing)), projected(projected),
        id(projected.getId().str()), endpointKind(endpointKind) {}

  artifact::detail::MutablePirArtifact backing;
  oir::ArtifactOp projected;
  std::string id;
  EndpointKind endpointKind;
};

namespace {

/// The endpoint-effect family of one emitted op, in the vocabulary of
/// the closed discharge-kind table (kernel.md §6.1). Empty for the
/// program frame (init/expect_end/decide), which realizes no event.
static llvm::StringRef oirFamily(Operation *op) {
  return llvm::TypeSwitch<Operation *, llvm::StringRef>(op)
      .Case<zkc::oir::ConstantOp>([](auto) { return "const"; })
      .Case<zkc::oir::AbsorbOp>([](auto) { return "absorb"; })
      .Case<zkc::oir::ReadOp>([](auto) { return "read"; })
      .Case<zkc::oir::WriteOp>([](auto) { return "write"; })
      .Case<zkc::oir::SqueezeOp>([](auto) { return "squeeze"; })
      .Case<zkc::oir::AssertEqOp>([](auto) { return "assert_eq"; })
      .Case<zkc::oir::CheckCallOp>([](auto) { return "check_call"; })
      .Case<zkc::oir::FNegOp>([](auto) { return "f_neg"; })
      .Case<zkc::oir::FAddOp>([](auto) { return "f_add"; })
      .Case<zkc::oir::FMulOp>([](auto) { return "f_mul"; })
      .Case<zkc::oir::GExpOp>([](auto) { return "g_exp"; })
      .Case<zkc::oir::GMulOp>([](auto) { return "g_mul"; })
      .Default([](Operation *) { return llvm::StringRef(); });
}

/// Whether an op family may carry a position whose obligation has the
/// given discharge kind (kernel.md §6.2, the no-phantom-coverage
/// direction) — a lookup into the closed discharge-kind table, whose
/// single definition lives beside the obligation derivation
/// (SealBattery's dischargeKindTable), so licensing here cannot drift
/// from what the seal derived.
static bool licensedFamily(llvm::StringRef discharge, llvm::StringRef family,
                           zkc::pir::EndpointKind endpointKind) {
  const zkc::pir::DischargeKindRow *row =
      zkc::pir::findDischargeKind(discharge);
  if (!row)
    return false;
  ArrayRef<StringRef> families =
      endpointKind == zkc::pir::EndpointKind::Verifier ? row->verifierFamilies
                                                       : row->proverFamilies;
  return llvm::is_contained(families, family);
}

/// Lower one admitted expr subtree to algebra ops. The optional result keeps
/// the recursive builder total; admission has already established the grammar,
/// reference ranges, constants, and depth bound.
static Value lowerExpr(OpBuilder &builder, Location loc, ArrayAttr node,
                       ArrayRef<Value> inputs, DictionaryAttr constants,
                       ArrayAttr src, unsigned depth = 0) {
  if (depth > zkc::encoding::kMaxAttrDepth || node.empty())
    return Value();
  auto head = dyn_cast<StringAttr>(node[0]);
  if (!head)
    return Value();
  StringRef tag = head.getValue();
  if (tag == "in") {
    auto index =
        node.size() == 2 ? dyn_cast<IntegerAttr>(node[1]) : IntegerAttr();
    if (!index)
      return Value();
    int64_t position = index.getValue().getSExtValue();
    if (position < 0 || position >= static_cast<int64_t>(inputs.size()))
      return Value();
    return inputs[position];
  }
  if (tag == "const") {
    auto name = node.size() == 2 ? dyn_cast<StringAttr>(node[1]) : StringAttr();
    if (!name || !constants)
      return Value();
    auto named = constants.getNamed(name.getValue());
    if (!named)
      return Value();
    auto spec = dyn_cast<DictionaryAttr>(named->getValue());
    if (!spec)
      return Value();
    auto value = spec.getNamed("value");
    auto payloadClass = spec.getNamed("class");
    auto valueStr =
        value ? dyn_cast<StringAttr>(value->getValue()) : StringAttr();
    auto classStr = payloadClass
                        ? dyn_cast<StringAttr>(payloadClass->getValue())
                        : StringAttr();
    if (!valueStr || !classStr)
      return Value();
    return zkc::oir::ConstantOp::create(builder, loc, valueStr, classStr, src)
        .getVal();
  }
  bool unary = tag == "f_neg";
  if (!unary && tag != "g_exp" && tag != "g_mul" && tag != "f_add" &&
      tag != "f_mul")
    return Value();
  if (node.size() != (unary ? 2u : 3u))
    return Value();
  auto sub = [&](unsigned i) -> Value {
    auto subtree = dyn_cast<ArrayAttr>(node[i]);
    if (!subtree)
      return Value();
    return lowerExpr(builder, loc, subtree, inputs, constants, src, depth + 1);
  };
  if (unary) {
    Value v = sub(1);
    if (!v)
      return Value();
    return zkc::oir::FNegOp::create(builder, loc, v, src).getVal();
  }
  Value lhs = sub(1), rhs = sub(2);
  if (!lhs || !rhs)
    return Value();
  if (tag == "g_exp")
    return zkc::oir::GExpOp::create(builder, loc, lhs, rhs, src).getVal();
  if (tag == "g_mul")
    return zkc::oir::GMulOp::create(builder, loc, lhs, rhs, src).getVal();
  if (tag == "f_add")
    return zkc::oir::FAddOp::create(builder, loc, lhs, rhs, src).getVal();
  return zkc::oir::FMulOp::create(builder, loc, lhs, rhs, src).getVal();
}

class ProjectionEngine {
public:
  ProjectionEngine(zkc::pir::EndpointKind endpointKind,
                   const zkc::registry::ProtocolEnvironment &environment)
      : endpointKind(endpointKind), environment(environment) {}

  /// One walk projects both endpoints of the same seal
  /// (docs/spec/endpoints.md §6.1): the prover writes where the
  /// verifier reads, both absorb and squeeze identically on replica
  /// sponges, a check is the verifier's local verdict and the
  /// prover's counterparty row, and the frame terminators are the
  /// endpoint's own.
  LogicalResult project(zkc::pir::SealedOp sealed) {
    const bool prover = endpointKind == zkc::pir::EndpointKind::ProverSkeleton;
    auto refuse = [&](const llvm::Twine &message) -> LogicalResult {
      return sealed.emitOpError() << "[zkc-E239] " << message;
    };

    // The profile axes projection consumes; absent axes fail closed.
    // kappa is consumed HERE: codecs bake onto the program and
    // constants materialize as ops — the artifact executes without
    // the source.
    StringAttr spongeName, ivPolicy;
    DictionaryAttr codecs, constants, checkContractDigests;
    if (auto kappa = sealed.getKappa()) {
      if (auto s = kappa->getNamed("sponge"))
        spongeName = dyn_cast<StringAttr>(s->getValue());
      if (auto i = kappa->getNamed("iv"))
        ivPolicy = dyn_cast<StringAttr>(i->getValue());
      if (auto c = kappa->getNamed("codecs"))
        codecs = dyn_cast<DictionaryAttr>(c->getValue());
      if (auto k = kappa->getNamed("constants"))
        constants = dyn_cast<DictionaryAttr>(k->getValue());
    }
    if (auto vocab = sealed.getVocab())
      if (auto section = vocab->getNamed("check_contracts"))
        checkContractDigests = dyn_cast<DictionaryAttr>(section->getValue());
    if (!spongeName || !ivPolicy)
      return sealed.emitOpError()
             << "[zkc-E232] kappa must name the '"
             << (spongeName ? "iv" : "sponge") << "' axis for projection";

    // Construction routes are prover-endpoint input: every slot's
    // written value comes from one. Admission already checked every
    // cited contract against the sealed authority closure; projection
    // only retains the loaded schemas needed to type the emitted hole
    // calls.
    DictionaryAttr routes, instances;
    llvm::StringMap<const zkc::registry::HoleContract *> contracts;
    if (prover) {
      routes = sealed.getRoutesAttr();
      if (!routes)
        return refuse("prover projection requires construction routes "
                      "(docs/spec/endpoints.md §6.2); this protocol "
                      "declares none");
      instances = dyn_cast_or_null<DictionaryAttr>(routes.get("instances"));
      if (!instances)
        return refuse("routes carries no instances section");
      const zkc::registry::ProtocolVocabulary &vocabulary =
          environment.protocolVocabulary();
      for (NamedAttribute entry : instances) {
        auto instanceBody = dyn_cast<DictionaryAttr>(entry.getValue());
        auto contractId =
            instanceBody
                ? dyn_cast_or_null<StringAttr>(instanceBody.get("contract"))
                : StringAttr();
        // Admission establishes both of these, but this pass reads a
        // loaded artifact and every other failure here is a refusal;
        // an assertion is absent from the build that ships.
        if (!contractId)
          return refuse("route instance '" + entry.getName().strref() +
                        "' carries no contract");
        const zkc::registry::HoleContract *contract =
            vocabulary.lookupHoleContract(contractId.getValue());
        if (!contract)
          return refuse("route instance '" + entry.getName().strref() +
                        "' cites hole contract '" + contractId.getValue() +
                        "', which this environment does not admit");
        contracts[entry.getName().strref()] = contract;
      }
    }

    Block &body = sealed.getBody().front();

    // The instance-stage binds are collected once — the statement
    // labels and the block arguments below must be the same list, in
    // the same order, or argument indexing drifts.
    zkc::encoding::CanonicalIndex canonicalEvents =
        zkc::encoding::canonicalEventIndex(body);
    SmallVector<zkc::pir::BindOp> instanceBinds;
    SmallVector<zkc::pir::SlotOp> unboundSlots;
    int64_t eventCount = zkc::encoding::canonicalEventCount(canonicalEvents);
    bool hasCheck = false;
    for (Operation &op : body) {
      hasCheck |= isa<zkc::pir::CheckOp>(op);
      if (auto bind = dyn_cast<zkc::pir::BindOp>(op))
        if (bind.getStage() == zkc::pir::Stage::Instance)
          instanceBinds.push_back(bind);
      if (auto slot = dyn_cast<zkc::pir::SlotOp>(op))
        if (!slot.getBinding())
          unboundSlots.push_back(slot);
    }

    // An empty declared verifier face is refused (docs/spec/
    // boundaries.md §2): a program with no check decides on nothing
    // and accepts every proof — the accept-all verifier must be
    // unrepresentable, not merely unlikely.
    if (!hasCheck)
      return sealed.emitOpError()
             << "[zkc-E234] empty verifier face: the projected program "
                "would carry no check and accept every proof";
    // Route totality is the prover's own judgment (kernel.md §6.2):
    // a slot without a binding cannot be written honestly.
    if (prover && !unboundSlots.empty()) {
      InFlightDiagnostic diag = sealed.emitOpError();
      diag << "[zkc-E239] prover projection requires a construction route "
              "for every slot; unbound:";
      for (zkc::pir::SlotOp slot : unboundSlots)
        diag << " '" << slot.getLabel() << "'";
      return diag;
    }
    SmallVector<StringRef> statementLabels;
    for (zkc::pir::BindOp bind : instanceBinds)
      statementLabels.push_back(bind.getLabel());

    OpBuilder builder(sealed->getContext());
    builder.setInsertionPointAfter(sealed);
    Location loc = sealed.getLoc();
    MLIRContext *ctx = builder.getContext();
    auto artifact = zkc::oir::ArtifactOp::create(
        builder, loc, sealed.getProtocolName(), std::string(64, '0'),
        ("sha256:" + sealed.getId()).str(),
        zkc::pir::endpointKindName(endpointKind));
    builder.createBlock(&artifact.getBody());
    // The sealed construction pins travel with the endpoint: an executor
    // gates them against its supplier set before any transcript event
    // (endpoints.md §2). DictionaryAttr iterates sorted by name, matching
    // the reference's sorted emission.
    SmallVector<std::string> paramDigestStorage;
    SmallVector<StringRef> paramDigests;
    if (auto vocab = sealed.getVocab())
      if (auto section = vocab->getNamed("construction_profiles"))
        if (auto table = dyn_cast<DictionaryAttr>(section->getValue()))
          for (NamedAttribute entry : table)
            paramDigestStorage.push_back(
                (entry.getName().getValue() + "=" +
                 cast<StringAttr>(entry.getValue()).getValue())
                    .str());
    for (const std::string &pin : paramDigestStorage)
      paramDigests.push_back(pin);

    // witness_labels is prover-endpoint ABI: the routes' declared
    // (label, class) pairs, in order.
    SmallVector<Attribute> witnessPairs;
    llvm::StringMap<StringRef> witnessClass;
    if (prover)
      if (auto list = dyn_cast_or_null<ArrayAttr>(routes.get("witnesses")))
        for (Attribute entry : list) {
          auto pair = cast<ArrayAttr>(entry);
          StringRef label = cast<StringAttr>(pair[0]).getValue();
          witnessClass[label] = cast<StringAttr>(pair[1]).getValue();
          witnessPairs.push_back(pair);
        }

    auto program = zkc::oir::ProgramOp::create(
        builder, loc, builder.getStrArrayAttr(statementLabels),
        builder.getStrArrayAttr(paramDigests), codecs,
        prover ? builder.getArrayAttr(witnessPairs) : ArrayAttr(),
        /*counterparty=*/ArrayAttr());
    Block *programBlock = builder.createBlock(&program.getBody());

    SmallVector<Value> stmtArgs;
    unsigned argIdx = 0;
    llvm::StringMap<Value> bindValueByLabel;
    for (zkc::pir::BindOp bind : instanceBinds)
      stmtArgs.push_back(programBlock->addArgument(
          zkc::oir::ValType::get(ctx, bind.getPayloadClass(), "public"), loc));
    llvm::StringMap<Value> witnessArg;
    for (Attribute entry : witnessPairs) {
      auto pair = cast<ArrayAttr>(entry);
      StringRef label = cast<StringAttr>(pair[0]).getValue();
      witnessArg[label] = programBlock->addArgument(
          zkc::oir::HandleType::get(ctx, witnessClass[label]), loc);
    }
    Value stream =
        programBlock->addArgument(zkc::oir::StreamType::get(ctx), loc);

    builder.setInsertionPointToStart(programBlock);
    auto eventPosition = [&](Operation *op) {
      auto position =
          zkc::encoding::canonicalEventPosition(canonicalEvents, op);
      assert(position && "projected event absent from canonical event index");
      return *position;
    };
    auto src = [&](Operation *op) {
      return builder.getI64ArrayAttr({eventPosition(op)});
    };
    Value sponge = zkc::oir::TranscriptInitOp::create(
        builder, loc, spongeName.getValue(), ivPolicy.getValue(),
        /*src=*/nullptr);
    llvm::DenseMap<Value, Value> vals;
    llvm::StringMap<Value> slotValueByLabel, chalValueByLabel;
    // COV_realized's totality direction (kernel.md §6.2): per-position
    // coverage over the canonical event numbering, set exactly where
    // the walk realizes an event's obligation. The equality gate after
    // the walk names every unrealized position.
    llvm::BitVector covered(eventCount);
    auto cover = [&](Operation *op) { covered.set(eventPosition(op)); };
    SmallVector<int64_t> counterpartyPositions;

    // Lazy hole materialization at the canonical position (prover
    // slots only): immediately before the first op consuming any
    // result, dependencies emitted in need order (well-founded — the
    // seal refused cycles). The threaded sponge is fed to a pow_search
    // hole at its own materialization point, which is exactly the
    // peek's state.
    llvm::StringMap<SmallVector<Value>> holeResults;
    bool materializeFailed = false;
    auto materializeConst = [&](StringRef name) -> Value {
      auto entry = constants
                       ? dyn_cast_or_null<DictionaryAttr>(constants.get(name))
                       : DictionaryAttr();
      auto cls = entry ? dyn_cast_or_null<StringAttr>(entry.get("class"))
                       : StringAttr();
      auto value = entry ? dyn_cast_or_null<StringAttr>(entry.get("value"))
                         : StringAttr();
      if (!cls || !value) {
        sealed.emitOpError() << "[zkc-E239] kappa constant '" << name
                             << "' is malformed for route materialization";
        materializeFailed = true;
        return Value();
      }
      // Pure materialization covers no obligation: no src.
      return zkc::oir::ConstantOp::create(builder, loc, value.getValue(),
                                          cls.getValue(), /*src=*/nullptr)
          .getVal();
    };
    std::function<LogicalResult(StringRef)> materialize;
    auto resolveRef = [&](StringRef text) -> Value {
      StringRef rest = text;
      if (rest.consume_front("bind:"))
        return bindValueByLabel.lookup(rest);
      if (rest.consume_front("slot:"))
        return slotValueByLabel.lookup(rest);
      if (rest.consume_front("chal:"))
        return chalValueByLabel.lookup(rest);
      if (rest.consume_front("const:"))
        return materializeConst(rest);
      if (rest.consume_front("witness:"))
        return witnessArg.lookup(rest);
      // The hole form is `<instance>.<output>`, and it is parsed here exactly
      // as the encoder parses it. Discarding getAsInteger's result made
      // `inst` and `inst.garbage` both resolve to output 0 — a second, laxer
      // reading of one grammar, sitting downstream of the strict one.
      size_t dot = rest.rfind('.');
      if (dot == StringRef::npos || dot == 0)
        return Value();
      StringRef instance = rest.substr(0, dot);
      unsigned output = 0;
      if (rest.substr(dot + 1).getAsInteger(10, output))
        return Value();
      if (failed(materialize(instance)))
        return Value();
      ArrayRef<Value> results = holeResults[instance];
      return output < results.size() ? results[output] : Value();
    };
    materialize = [&](StringRef name) -> LogicalResult {
      if (holeResults.contains(name))
        return success();
      auto entry = instances.getNamed(name);
      const zkc::registry::HoleContract *contract = contracts.lookup(name);
      if (!entry || !contract)
        return refuse("route reference names unknown instance '" + name + "'");
      auto instanceBody = cast<DictionaryAttr>(entry->getValue());
      auto inputs = cast<ArrayAttr>(instanceBody.get("inputs"));
      // Params: the contract's sorted parameter names, each supplied. Both
      // kinds travel — a semantic parameter names material the supplier must
      // hold, so an endpoint that dropped it could not be executed away from
      // the protocol that produced it.
      auto declared =
          dyn_cast_or_null<DictionaryAttr>(instanceBody.get("params"));
      auto collect = [&](llvm::ArrayRef<std::string> names, StringRef what,
                         SmallVectorImpl<Attribute> &into) -> LogicalResult {
        for (const std::string &param : names) {
          auto value = declared
                           ? dyn_cast_or_null<StringAttr>(declared.get(param))
                           : StringAttr();
          if (!value)
            return refuse("route instance '" + name +
                          "' supplies no value "
                          "for contract " +
                          what + " parameter '" + param + "'");
          into.push_back(value);
        }
        return success();
      };
      SmallVector<Attribute> params, semanticParams;
      if (failed(collect(contract->parameters, "static", params)) ||
          failed(collect(contract->semanticParameters, "semantic",
                         semanticParams)))
        return failure();
      SmallVector<Value> operands;
      unsigned inputIdx = 0;
      for (const zkc::registry::HoleSegment &segment : contract->operands) {
        if (segment.sort == zkc::registry::HoleSegmentSort::Sponge) {
          operands.push_back(sponge);
          continue;
        }
        auto text = cast<StringAttr>(inputs[inputIdx++]).getValue();
        Value v = resolveRef(text);
        if (!v)
          return refuse("route instance '" + name + "' input '" + text +
                        "' does not resolve to a projected value");
        operands.push_back(v);
      }
      SmallVector<Type> resultTypes;
      for (const zkc::registry::HoleSegment &segment : contract->results) {
        switch (segment.sort) {
        case zkc::registry::HoleSegmentSort::Value:
          resultTypes.push_back(
              zkc::oir::ValType::get(ctx, segment.typeClass, "hole"));
          break;
        case zkc::registry::HoleSegmentSort::Handle:
          resultTypes.push_back(
              zkc::oir::HandleType::get(ctx, segment.typeClass));
          break;
        case zkc::registry::HoleSegmentSort::Sponge:
          resultTypes.push_back(zkc::oir::SpongeType::get(ctx));
          break;
        }
      }
      // A counted result carries its declared count onto the call, so
      // the executor can split the fill's flat output positionally;
      // all-scalar holes keep the empty attribute and their exact
      // historical encoding.
      SmallVector<Attribute> resultCounts;
      bool anyCounted = false;
      for (const zkc::registry::HoleSegment &segment : contract->results) {
        StringRef count = segment.count.empty() ? "1" : StringRef(segment.count);
        anyCounted |= count != "1";
        resultCounts.push_back(builder.getStringAttr(count));
      }
      auto hole = zkc::oir::HoleCallOp::create(
          builder, loc, resultTypes, operands, name, contract->kind,
          contract->contentDigest(), builder.getArrayAttr(params),
          builder.getArrayAttr(semanticParams),
          anyCounted ? builder.getArrayAttr(resultCounts)
                     : builder.getArrayAttr({}));
      SmallVector<Value> results(hole.getOutputs());
      for (auto [index, segment] : llvm::enumerate(contract->results))
        if (segment.sort == zkc::registry::HoleSegmentSort::Sponge)
          sponge = results[index];
      holeResults[name] = std::move(results);
      return success();
    };

    bool walkOk = true;
    for (Operation &op : body) {
      // A refused member stops the walk: later members may consume
      // the value the refused one never produced, and a diagnostic
      // must never be followed by a null-operand build.
      if (!walkOk || materializeFailed)
        break;
      llvm::TypeSwitch<Operation *>(&op)
          .Case<zkc::pir::BeginOp, zkc::pir::EndOp, zkc::pir::InstantiateOp,
                zkc::pir::ReduceOp, zkc::pir::MaterialBindOp,
                zkc::pir::DischargeOp, zkc::pir::ExportOp, zkc::pir::AssumeOp,
                zkc::pir::ResidualOp>([](auto) {
            // Deliberately erased: begin/end become the program frame,
            // and the claim graph — sources, reduces, sinks — projects
            // to routes and citations, views over the source artifact,
            // never runtime values (docs/spec/boundaries.md §2). A
            // reduce's executable content is already in the spine: its
            // round obligations are check events, its deps are squeezed
            // challenges; seal priced them (kernel.md §5.2).
          })
          .Case<zkc::pir::BindOp>([&](zkc::pir::BindOp op) {
            // A seal-stage binding carries its constant value:
            // admission refuses one without it (zkc-E227) before any
            // endpoint projects.
            Value v = op.getStage() == zkc::pir::Stage::Instance
                          ? stmtArgs[argIdx++]
                          : zkc::oir::ConstantOp::create(
                                builder, loc, *op.getValue(),
                                materialClass(op), src(op))
                                .getVal();
            sponge =
                zkc::oir::AbsorbOp::create(builder, loc, sponge, v, src(op))
                    .getOut();
            vals[op.getVal()] = v;
            bindValueByLabel[op.getLabel()] = v;
            cover(op);
          })
          .Case<zkc::pir::SlotOp>([&](zkc::pir::SlotOp op) {
            if (prover) {
              // The written value comes from the slot's construction
              // route: a hole-instance value output, a statement echo,
              // or a pinned constant — never a sampled value (the
              // erasure lint is a type fact of oir.write).
              Value v = resolveRef(*op.getBinding());
              if (!v) {
                if (!materializeFailed)
                  op.emitOpError()
                      << "[zkc-E239] slot binding '" << *op.getBinding()
                      << "' does not resolve to a projected value";
                walkOk = false;
                return;
              }
              auto write = zkc::oir::WriteOp::create(
                  builder, loc, stream, v, op.getLabel(), materialClass(op),
                  op.getCount(), src(op));
              stream = write.getOut();
              slotValueByLabel[op.getLabel()] = v;
              vals[op.getVal()] = v;
              if (!op.getUnabsorbed())
                sponge =
                    zkc::oir::AbsorbOp::create(builder, loc, sponge, v, src(op))
                        .getOut();
              cover(op);
              return;
            }
            auto read = zkc::oir::ReadOp::create(builder, loc, stream,
                                                 op.getLabel(),
                                                 materialClass(op),
                                                 op.getCount(), src(op));
            stream = read.getOut();
            vals[op.getVal()] = read.getVal();
            if (!op.getUnabsorbed())
              sponge = zkc::oir::AbsorbOp::create(builder, loc, sponge,
                                                  read.getVal(), src(op))
                           .getOut();
            cover(op);
          })
          .Case<zkc::pir::ChalOp>([&](zkc::pir::ChalOp op) {
            // The Fiat-Shamir erasure: both endpoints squeeze
            // identically on their replica sponges; nothing crosses
            // the wire. Projection consumes the protocol-neutral
            // challenge-capability face — semantic class, exact
            // multiplicity, sampling rule — so the endpoint realizes
            // scalar and vector sampling without recognizing a
            // protocol family or a `chal` pseudo-class.
            auto capability = cast<zkc::pir::ChallengeCapabilityOpInterface>(
                op.getOperation());
            auto squeeze = zkc::oir::SqueezeOp::create(
                builder, loc, sponge, op.getLabel(),
                capability.getChallengePayloadClass(),
                capability.getChallengeCount(), op.getDomain(),
                capability.getChallengeSamplingRule(), op.getSpace(), src(op));
            sponge = squeeze.getOut();
            vals[op.getVal()] = squeeze.getVal();
            chalValueByLabel[op.getLabel()] = squeeze.getVal();
            cover(op);
          })
          .Case<zkc::pir::CheckOp>([&](zkc::pir::CheckOp op) {
            if (prover) {
              // Counterparty realization: the check is the verifier's
              // local verdict; the prover emits nothing and records
              // the obligation as a row, so COV_realized stays set
              // equality in both directions.
              counterpartyPositions.push_back(eventPosition(op));
              cover(op);
              return;
            }
            SmallVector<Value> inputs;
            for (Value input : op.getInputs())
              inputs.push_back(vals.lookup(input));
            if (auto expr = op.getExpr()) {
              // Transparent interior: the admitted equation lowers to the
              // freely optimizable algebra region, ending in the protected
              // assert.
              ArrayAttr root = *expr;
              auto rootTag =
                  !root.empty() ? dyn_cast<StringAttr>(root[0]) : StringAttr();
              Value lhs, rhs;
              if (rootTag && rootTag.getValue() == "eq" && root.size() == 3 &&
                  isa<ArrayAttr>(root[1]) && isa<ArrayAttr>(root[2])) {
                lhs = lowerExpr(builder, loc, cast<ArrayAttr>(root[1]), inputs,
                                constants, src(op));
                rhs = lowerExpr(builder, loc, cast<ArrayAttr>(root[2]), inputs,
                                constants, src(op));
              }
              if (!lhs || !rhs) {
                op.emitOpError()
                    << "internal projection invariant: admitted expr did not "
                       "lower";
                walkOk = false;
                return;
              }
              zkc::oir::AssertEqOp::create(builder, loc, lhs, rhs,
                                           op.getLabel(), src(op));
            } else {
              // CheckContract names are the lowering identity. Its exact
              // dictionaries are stored in lexical key order, matching the
              // vocabulary's parameter and semantic-parameter order. The OIR
              // encoding carries their values as one static vector: ordinary
              // values first, then intrinsic semantic arguments. The contract
              // recovers both boundaries without another protocol-specific
              // lowering table.
              SmallVector<Attribute> params;
              auto appendValues = [&](std::optional<DictionaryAttr> values) {
                if (!values)
                  return;
                for (NamedAttribute entry : *values)
                  params.push_back(entry.getValue());
              };
              appendValues(op.getParams());
              appendValues(op.getSemanticArgs());
              auto digestEntry =
                  checkContractDigests
                      ? checkContractDigests.getNamed(op.getContract())
                      : std::optional<NamedAttribute>();
              auto contractDigest =
                  digestEntry ? dyn_cast<StringAttr>(digestEntry->getValue())
                              : StringAttr();
              if (!contractDigest ||
                  !zkc::encoding::isSha256Ref(contractDigest.getValue())) {
                op.emitOpError()
                    << "internal projection invariant: admitted opaque check "
                       "contract '"
                    << op.getContract() << "' has no content digest";
                walkOk = false;
                return;
              }
              zkc::oir::CheckCallOp::create(
                  builder, loc, inputs, op.getLabel(), op.getContract(),
                  contractDigest.getValue(), builder.getArrayAttr(params),
                  src(op));
            }
            cover(op);
          })
          .Case<zkc::pir::ArtifactVerifyOp>(
              [&](zkc::pir::ArtifactVerifyOp op) {
                // endpoints.md §3.1 reserves the contract: bounded artifact
                // verification becomes usable only through a versioned
                // carrier form, projection rule, execution rule, and
                // conformance surface that preserve every fact it binds.
                // The carrier form exists; the other three do not, and an
                // incomplete form fails closed. This refusal is what says
                // so, rather than the generic missing-rule diagnostic that
                // would read as an internal gap.
                op.emitOpError()
                    << "[zkc-E235] bounded artifact verification '"
                    << op.getLabel()
                    << "' is a reserved endpoint contract: the carrier form "
                       "seals its facts, and projection to endpoint '"
                    << zkc::pir::endpointKindName(endpointKind)
                    << "' awaits the versioned projection, execution, and "
                       "conformance surface that must preserve them "
                       "(docs/spec/endpoints.md §3.1)";
                walkOk = false;
              })
          .Default([&](Operation *op) {
            // Fail closed like the encoder does: a member kind without
            // a projection rule must never be silently erased — that
            // would drop sealed semantics from the endpoint with no
            // diagnostic.
            op->emitOpError()
                << "[zkc-E233] no projection rule for this operation on "
                   "endpoint '"
                << zkc::pir::endpointKindName(endpointKind) << "'";
            walkOk = false;
          });
    }
    if (!walkOk || materializeFailed)
      return failure();
    // The program frame is the endpoint's own: the verifier expects
    // the stream's end and decides; the prover ends its stream and
    // finishes.
    if (prover) {
      zkc::oir::EndStreamOp::create(builder, loc, stream, /*src=*/nullptr);
      zkc::oir::FinishOp::create(builder, loc, sponge, /*src=*/nullptr);
    } else {
      zkc::oir::ExpectEndOp::create(builder, loc, stream, /*src=*/nullptr);
      zkc::oir::DecideOp::create(builder, loc, sponge, /*src=*/nullptr);
    }

    // COV_realized (kernel.md §6.2): the emitted program's coverage
    // equals the obligation set exactly. The obligation table is the
    // derived view COV_obl established at seal — recomputed here, as
    // any consumer may (kernel.md §11).
    auto obligations = zkc::pir::deriveObligations(body, canonicalEvents);
    if (prover) {
      SmallVector<Attribute> counterpartyRows;
      for (int64_t position : counterpartyPositions)
        counterpartyRows.push_back(builder.getArrayAttr(
            {builder.getI64IntegerAttr(position),
             builder.getStringAttr(obligations[position].discharge)}));
      program.setCounterpartyAttr(builder.getArrayAttr(counterpartyRows));
    }

    // No phantom coverage: each op family must be licensed by the
    // obligation at every position its `src` cites, under this
    // endpoint's realization vocabulary (kernel.md §6.2). `src` is
    // the Tier-1 conformance evidence (boundaries.md §2); its
    // positions come from the canonical event index by construction,
    // so only the licensing judgment is a refusal.
    int64_t highestCovered = -1;
    for (Operation &op : *programBlock) {
      auto srcAttr = op.getAttrOfType<ArrayAttr>("src");
      if (!srcAttr)
        continue;
      StringRef family = oirFamily(&op);
      // Order: the emitted program realizes the spine's events in the
      // spine's order. The single-pass walk above produces that by
      // construction, and the endpoint-projection judgment is exactly
      // the claim that it holds, so it is checked here rather than
      // trusted to the walk that just ran.
      int64_t highestHere = -1;
      for (Attribute entry : srcAttr) {
        auto position = dyn_cast<IntegerAttr>(entry);
        if (!position)
          return op.emitOpError()
                 << "[zkc-E237] projection coverage does not equal the "
                    "obligation set: src carries an entry that is not an "
                    "event position";
        highestHere = std::max(highestHere, position.getInt());
      }
      // An op citing no position covers nothing, so it neither advances
      // the frontier nor can fall behind it.
      if (highestHere < 0)
        continue;
      if (highestHere < highestCovered) {
        InFlightDiagnostic diag = op.emitOpError();
        diag << "[zkc-E237] projection coverage does not equal the "
                "obligation set: op family '"
             << family << "' realizes event position " << highestHere
             << " after position " << highestCovered
             << ", so the emitted order is not the spine's";
        return diag;
      }
      highestCovered = highestHere;
      for (Attribute entry : srcAttr) {
        int64_t position = cast<IntegerAttr>(entry).getInt();
        if (position < 0 || position >= eventCount) {
          InFlightDiagnostic diag = op.emitOpError();
          diag << "[zkc-E237] projection coverage does not equal the "
                  "obligation set: src cites event position "
               << position << ", outside the canonical range";
          return diag;
        }
        if (!licensedFamily(obligations[position].discharge, family,
                            endpointKind)) {
          InFlightDiagnostic diag = op.emitOpError();
          diag << "[zkc-E237] projection coverage does not equal the "
                  "obligation set: op family '"
               << family << "' is not licensed to cover event position "
               << position << " (" << obligations[position].discharge << ")";
          if (prover)
            diag << " on the prover endpoint";
          return diag;
        }
      }
    }

    // Totality: every obligation realized (kernel.md §10 — total on
    // artifacts whose obligations' discharge kinds lie in this
    // endpoint's realization vocabulary).
    if (!covered.all()) {
      InFlightDiagnostic diag = sealed.emitOpError();
      diag << "[zkc-E237] projection coverage does not equal the "
              "obligation set: unrealized event position(s):";
      for (const zkc::pir::ProjectionObligation &obligation : obligations)
        if (!covered.test(obligation.eventRef))
          diag << " " << obligation.eventRef << " (" << obligation.discharge
               << ")";
      return diag;
    }

    // Verifier/prover lockstep is established by the independent reference
    // twin's byte parity over the same projection, not by this walk
    // re-reading the program it just authored — a same-call re-read became
    // a tautology once one engine owned both endpoint walks.
    auto id = zkc::encoding::computeOirId(artifact);
    if (!id) {
      sealed.emitOpError() << "pir-project: " << llvm::toString(id.takeError());
      return failure();
    }
    artifact.setId(*id);
    if (failed(verify(artifact)))
      return failure();
    return success();
  }

private:
  zkc::pir::EndpointKind endpointKind;
  /// The payload class a slot's material actually travels under.
  ///
  /// A profiled value names a value profile, not a class, and the class is
  /// the profile's element class. Emitting the profile name here would name a
  /// codec the emitted program does not have: seal admitted a codec for the
  /// element class, so a realized endpoint asking for the profile name asks
  /// for one nobody declared. Both seats a profile can sit on answer this.
  template <typename OpT> llvm::StringRef materialClass(OpT op) const {
    if (!op.getProfiled())
      return op.getPayloadClass();
    const zkc::registry::ValueProfile *profile =
        environment.protocolVocabulary().lookupValueProfile(
            op.getPayloadClass());
    // Seal resolved this already; an unresolved profile cannot reach
    // projection, and returning the profile name would be the bug this
    // exists to prevent.
    assert(profile && "seal admits only resolved value profiles");
    return profile->elementClass;
  }

  const zkc::registry::ProtocolEnvironment &environment;
};

} // namespace

llvm::Expected<zkc::pir::EndpointKind>
zkc::pir::parseEndpointKind(llvm::StringRef spelling) {
  if (spelling == zkc::oir::kEndpointVerifier)
    return EndpointKind::Verifier;
  if (spelling == zkc::oir::kEndpointProverSkeleton)
    return EndpointKind::ProverSkeleton;
  return llvm::createStringError("[zkc-E231] unknown endpoint kind '" +
                                 spelling +
                                 "' (expected verifier or prover_skeleton)");
}

llvm::StringRef zkc::pir::endpointKindName(EndpointKind kind) {
  switch (kind) {
  case EndpointKind::Verifier:
    return zkc::oir::kEndpointVerifier;
  case EndpointKind::ProverSkeleton:
    return zkc::oir::kEndpointProverSkeleton;
  }
  llvm_unreachable("all endpoint kinds handled");
}

llvm::StringRef zkc::pir::ProjectedOirArtifact::id() const {
  return storage_->id;
}

zkc::pir::EndpointKind zkc::pir::ProjectedOirArtifact::endpointKind() const {
  return storage_->endpointKind;
}

void zkc::pir::ProjectedOirArtifact::print(llvm::raw_ostream &os) const {
  storage_->projected->print(os);
}

llvm::Expected<zkc::pir::ProjectedOirArtifact>
zkc::pir::projectArtifact(const artifact::AdmittedPirArtifact &artifact,
                          EndpointKind endpointKind) {
  artifact::detail::MutablePirArtifact backing =
      artifact::detail::ArtifactAccess::cloneForReopen(artifact);
  MLIRContext *context = backing.module().getContext();
  context->loadDialect<oir::OirDialect>();
  std::string detail;
  ScopedDiagnosticHandler handler(context, [&](Diagnostic &diagnostic) {
    if (!detail.empty())
      detail += "; ";
    detail += diagnostic.str();
    return success();
  });

  if (failed(ProjectionEngine(endpointKind, artifact.environment())
                 .project(backing.sealed()))) {
    if (detail.empty())
      detail = "endpoint projection judgment failed";
    return llvm::createStringError("artifact projection refused: " + detail);
  }

  auto projected = backing.module().getOps<oir::ArtifactOp>();
  if (!llvm::hasSingleElement(projected))
    return llvm::createStringError(
        "artifact projection did not produce exactly one OIR artifact");
  oir::ArtifactOp result = *projected.begin();
  auto storage = std::make_shared<ProjectedOirArtifact::Storage>(
      std::move(backing), result, endpointKind);
  return ProjectedOirArtifact(std::move(storage));
}

namespace {

class PirProjectPass : public zkc::pir::impl::PirProjectBase<PirProjectPass> {
public:
  using PirProjectBase::PirProjectBase;

  void runOnOperation() override {
    ModuleOp module = getOperation();
    auto kind = zkc::pir::parseEndpointKind(endpointKind);
    if (!kind) {
      module.emitError() << "pir-project: " << llvm::toString(kind.takeError());
      return signalPassFailure();
    }
    auto environment = zkc::registry::ProtocolEnvironment::loadFromFiles(
        protocolVocabulary, constructionProfileRegistry);
    if (!environment) {
      module.emitError() << "pir-project: "
                         << llvm::toString(environment.takeError());
      return signalPassFailure();
    }

    SmallVector<zkc::pir::SealedOp> sealed(module.getOps<zkc::pir::SealedOp>());
    for (zkc::pir::SealedOp raw : sealed) {
      auto decoded = zkc::artifact::snapshotArtifact(raw);
      if (!decoded) {
        raw.emitOpError() << "pir-project raw adapter: "
                          << llvm::toString(decoded.takeError());
        signalPassFailure();
        continue;
      }
      auto admitted =
          zkc::artifact::admitArtifact(std::move(*decoded), *environment);
      if (!admitted) {
        raw.emitOpError() << "pir-project raw adapter: "
                          << llvm::toString(admitted.takeError());
        signalPassFailure();
        continue;
      }
      if (failed(ProjectionEngine(*kind, admitted->environment()).project(raw)))
        signalPassFailure();
    }
  }
};

} // namespace

llvm::Error zkc::pir::admitOirArtifact(
    zkc::oir::ArtifactOp artifact,
    const zkc::registry::ProtocolEnvironment &environment) {
  if (llvm::Error error = zkc::encoding::validateOirIdentity(artifact))
    return error;
  auto refuse = [](const llvm::Twine &message) {
    return llvm::createStringError("[zkc-E238] " + message);
  };
  auto program = *artifact.getBody().getOps<zkc::oir::ProgramOp>().begin();

  // Counterparty rows dispatch verifier-side checks; a kind outside the
  // closed discharge table names an event no verifier realizes.
  if (ArrayAttr counterparty = program.getCounterpartyAttr())
    for (Attribute entry : counterparty) {
      StringRef discharge =
          cast<StringAttr>(cast<ArrayAttr>(entry)[1]).getValue();
      if (!zkc::pir::findDischargeKind(discharge))
        return refuse("counterparty row cites unknown discharge kind '" +
                      discharge + "'");
    }

  // The content digest is the sole dispatch authority; the executor
  // marshals supplier calls from the op's own types, so the declared
  // segments must be exactly the contract's.
  const zkc::registry::ProtocolVocabulary &vocabulary =
      environment.protocolVocabulary();
  // Dispatch is by digest and the vocabulary is keyed by name, so the
  // index is built once rather than rescanned per hole.
  llvm::StringMap<const zkc::registry::HoleContract *> byDigest;
  for (const auto &[id, candidate] : vocabulary.holeContracts())
    byDigest[candidate.contentDigest()] = &candidate;
  for (zkc::oir::HoleCallOp hole :
       program.getBody().front().getOps<zkc::oir::HoleCallOp>()) {
    auto found = byDigest.find(hole.getContractDigest());
    const zkc::registry::HoleContract *contract =
        found == byDigest.end() ? nullptr : found->second;
    if (!contract)
      return refuse("hole_call '" + hole.getLabel() +
                    "' cites a contract digest with no loaded HoleContract");
    if (contract->kind != hole.getKind())
      return refuse("hole_call '" + hole.getLabel() + "' declares kind '" +
                    hole.getKind() + "', the cited contract is '" +
                    contract->kind + "'");
    // Parameter bindings are re-admitted here in full, not merely counted.
    // This boundary has no protocol behind it: the sealing checks that
    // established the binding are unavailable, so every property they
    // established has to be re-established from the artifact and the cited
    // contract alone.
    auto bindings = [&](ArrayAttr authored, llvm::ArrayRef<std::string> names,
                        StringRef what) -> llvm::Error {
      if (authored.size() != names.size())
        return refuse("hole_call '" + hole.getLabel() + "' carries " +
                      llvm::Twine(authored.size()) + " " + what +
                      " parameter(s), the cited contract declares " +
                      llvm::Twine(names.size()));
      for (auto [index, entry] : llvm::enumerate(authored)) {
        auto value = dyn_cast<StringAttr>(entry);
        if (!value || value.getValue().empty() ||
            !zkc::encoding::inEncodingDomain(value.getValue()))
          return refuse("hole_call '" + hole.getLabel() + "' " + what +
                        " parameter '" + names[index] +
                        "' must be a non-empty printable binding");
        // A semantic parameter names material by content. A supplier is
        // asked to hold that content, so a binding that is not a content
        // reference names nothing it could hold.
        if (what == "semantic" && !zkc::encoding::isSha256Ref(value.getValue()))
          return refuse("hole_call '" + hole.getLabel() +
                        "' semantic parameter '" + names[index] +
                        "' must be a sha256 content reference, got '" +
                        value.getValue() + "'");
      }
      return llvm::Error::success();
    };
    if (llvm::Error error =
            bindings(hole.getParams(), contract->parameters, "static"))
      return error;
    if (llvm::Error error = bindings(hole.getSemanticParams(),
                                     contract->semanticParameters, "semantic"))
      return error;

    auto matchSegments =
        [&](llvm::ArrayRef<zkc::registry::HoleSegment> segments,
            TypeRange types, StringRef direction) -> llvm::Error {
      size_t cursor = 0;
      // One ABI position per segment, counted or not: a counted value is a
      // single SSA value that carries its count (carrier.md §3), so expanding
      // a count-n segment into n positions would refuse exactly the endpoints
      // projection mints.
      for (const zkc::registry::HoleSegment &segment : segments) {
        if (cursor >= types.size())
          return refuse("hole_call '" + hole.getLabel() + "' is short of " +
                        direction + "s: segment '" + segment.role +
                        "' has no " + direction + " at position " +
                        llvm::Twine(cursor));
        Type type = types[cursor];
        bool matches = false;
        switch (segment.sort) {
        case zkc::registry::HoleSegmentSort::Value:
          if (auto val = dyn_cast<zkc::oir::ValType>(type))
            matches = val.getValueClass() == segment.typeClass;
          break;
        case zkc::registry::HoleSegmentSort::Handle:
          if (auto handle = dyn_cast<zkc::oir::HandleType>(type))
            matches = handle.getHandleClass() == segment.typeClass;
          break;
        case zkc::registry::HoleSegmentSort::Sponge:
          matches = isa<zkc::oir::SpongeType>(type);
          break;
        }
        if (!matches)
          return refuse("hole_call '" + hole.getLabel() + "' " + direction +
                        " #" + llvm::Twine(cursor) +
                        " does not match the cited contract's segment '" +
                        segment.role + "'");
        ++cursor;
      }
      if (cursor != types.size())
        return refuse("hole_call '" + hole.getLabel() + "' carries " +
                      llvm::Twine(types.size() - cursor) + " " + direction +
                      "(s) beyond the cited contract's segments");
      return llvm::Error::success();
    };
    if (llvm::Error error = matchSegments(
            contract->operands, hole.getInputs().getTypes(), "operand"))
      return error;
    if (llvm::Error error = matchSegments(
            contract->results, hole.getOutputs().getTypes(), "result"))
      return error;
  }

  // The check side of the same question. `kind` is the human-readable
  // contract id and `contract_digest` is the dispatch authority; projection
  // copies both from one sealed vocabulary entry, and nothing downstream had
  // re-established that they still name the same one. An artifact whose kind
  // was rewritten to another contract while the digest stayed put was
  // accepted here, which is exactly the mutation the hole side refuses.
  for (zkc::oir::CheckCallOp check :
       program.getBody().front().getOps<zkc::oir::CheckCallOp>()) {
    const zkc::registry::CheckContract *cited =
        vocabulary.lookupCheckContract(check.getKind());
    if (!cited)
      return refuse("check_call '" + check.getLabel() + "' names kind '" +
                    check.getKind() +
                    "', which resolves to no loaded CheckContract");
    if (cited->contentDigest() != check.getContractDigest())
      return refuse("check_call '" + check.getLabel() + "' names kind '" +
                    check.getKind() + "' whose loaded content is " +
                    cited->contentDigest() + ", but dispatches on " +
                    check.getContractDigest());
  }
  return llvm::Error::success();
}
