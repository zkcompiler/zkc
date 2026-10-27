#include "../lib/Conversion/Bindings.h"
#include "../lib/Conversion/Storage.h"
#include "../lib/Target/ExecutionPorts.h"
#include "../lib/Target/PhysicalPlan.h"
#include "../lib/Target/StorageSchedule.h"
#include "mlir/IR/Verifier.h"
#include "support/NativeCases.h"
#include "support/ScopedComputation.h"
#include "support/ScopedFixture.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Protocol.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/MemoryBuffer.h"
#include <limits>

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::target;
using namespace zkc::test;

namespace {
namespace sc = scopedComputation;
void accept(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}

void reject(Error error, StringRef code) {
  auto message = toString(std::move(error));
  require(namesIdentifier(message, code), "unexpected refusal: " + message);
}

std::string printed(ModuleOp module) {
  std::string text;
  raw_string_ostream out(text);
  module->print(out, OpPrintingFlags().printGenericOpForm().enableDebugInfo());
  return text;
}

OwningOpRef<ModuleOp> copy(ModuleOp module) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
}

std::string fixtureText(StringRef path) {
  auto bytes =
      MemoryBuffer::getFile((Twine(ZKC_SCHEDULE_FIXTURES) + "/" + path).str());
  require(bool(bytes), "cannot read storage scheduling fixture");
  return (*bytes)->getBuffer().str();
}

template <typename Op> Op first(ModuleOp module) {
  Op found;
  module.walk([&](Op op) {
    if (!found)
      found = op;
  });
  require(bool(found), "missing expected fixture operation");
  return found;
}

Operation *site(ModuleOp module, StringRef name) {
  auto flow = take(ExecutionPorts::read(module));
  auto expanded = "lc_" + std::to_string(name.size()) + "_" + name.str();
  Operation *found = nullptr;
  for (auto *op : flow.operations()) {
    auto attr = op->getAttrOfType<StringAttr>("site");
    if (flow.get(op).step && attr &&
        (attr.getValue() == name || attr.getValue() == expanded)) {
      require(!found, "ambiguous semantic site " + name);
      found = op;
    }
  }
  require(found != nullptr, "missing semantic site " + name);
  return found;
}

OperationIndex indexOf(ModuleOp module, Operation *operation) {
  auto operations = physicalPlanOperations(module);
  auto found = llvm::find(operations, operation);
  require(found != operations.end(), "operation outside selected subject");
  return found - operations.begin();
}

Value input(ModuleOp module, Operation *op, unsigned index) {
  return take(ExecutionPorts::read(module)).inputs(op)[index];
}
Value output(ModuleOp module, Operation *op, unsigned index = 0) {
  return take(ExecutionPorts::read(module)).outputs(op)[index];
}
Block *body(ModuleOp module, Operation *op) {
  return take(ExecutionPorts::read(module)).enclosingBody(op);
}
Value argument(ModuleOp module, Block *entry, unsigned index) {
  return take(ExecutionPorts::read(module)).body(entry).arguments[index];
}
SmallVector<Block *> regions(ModuleOp module, Operation *op) {
  return take(ExecutionPorts::read(module)).get(op).bodies;
}
Operation *completion(func::FuncOp function) {
  Operation *found = nullptr;
  function.walk([&](Operation *op) {
    if (isa<exec::ReturnOp, exec::CompleteOp>(op)) {
      require(!found, "multiple successful completions in storage fixture");
      found = op;
    }
  });
  require(found != nullptr, "missing successful completion");
  return found;
}
StringRef implementation(exec::ApplyOp op) {
  return SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
             op, op.getBindingAttr())
      .getImplementation();
}

// Decode semantic coordinates from the selected executable. A CFG payload
// argument belongs to its instruction, not to the continuation block.
StorageValue coordinate(ModuleOp selected, Value value) {
  auto flow = take(ExecutionPorts::read(selected));
  const auto &definition = flow.definition(value);
  return {definition.argument ? StorageValue::BlockArgument
                              : StorageValue::OperationResult,
          indexOf(selected, definition.owner), definition.port,
          definition.block};
}
StoragePoint after(ModuleOp selected, Operation *operation) {
  return {StoragePoint::AfterOperation, indexOf(selected, operation)};
}
StoragePoint entry(ModuleOp selected, Block *block) {
  auto flow = take(ExecutionPorts::read(selected));
  auto *owner = flow.body(block).owner;
  const auto &bodies = flow.get(owner).bodies;
  auto found = llvm::find(bodies, block);
  require(found != bodies.end(), "missing logical body");
  return {StoragePoint::BlockEntry, indexOf(selected, owner),
          unsigned(found - bodies.begin())};
}

PhysicalPlan propose(ModuleOp module, bool releases = true,
                     const CandidateCatalog &catalog = installedCandidates()) {
  auto before = printed(module);
  auto operations = physicalPlanOperations(module);
  auto proposal = take(proposePhysical(module, catalog, {}, {false, releases}));
  require(printed(module) == before &&
              physicalPlanOperations(module) == operations,
          "proposal changed input content or operation identities");
  return proposal;
}

CheckedPhysicalPlan
check(ModuleOp module, const PhysicalPlan &proposal,
      const CandidateCatalog &catalog = installedCandidates()) {
  auto before = printed(module);
  auto operations = physicalPlanOperations(module);
  auto checked = take(validatePhysical(module, proposal, catalog));
  require(printed(module) == before &&
              physicalPlanOperations(module) == operations,
          "validation changed input content or operation identities");
  return checked;
}

void refuse(ModuleOp module, const PhysicalPlan &proposal,
            StringRef code = "storage-schedule-lifetime") {
  auto before = printed(module);
  auto operations = physicalPlanOperations(module);
  refuses(validatePhysical(module, proposal), code);
  require(printed(module) == before &&
              physicalPlanOperations(module) == operations,
          "refused schedule changed input");
}

SmallVector<runtime::ReleaseBindingsOp> actualReleases(ModuleOp module) {
  SmallVector<runtime::ReleaseBindingsOp> result;
  module.walk([&](runtime::ReleaseBindingsOp op) { result.push_back(op); });
  return result;
}

void admitPhysical(ModuleOp module) {
  auto root = first<protocol_ir::ProtocolModuleOp>(module);
  require(root.getProfile() == protocol_ir::Profile::Physical &&
              succeeded(verify(module)),
          "candidate did not admit Physical profile");
}

// Freshness is identity sensitive. Rebind the same public decisions to a
// separately proposed copy; the independent reader still checks the original.
OwningOpRef<ModuleOp> materializedCopy(ModuleOp source,
                                       const CheckedPhysicalPlan &checked) {
  auto result = copy(source);
  auto own = propose(*result, false);
  own.bindings = checked.choices().bindings;
  own.operations = checked.choices().operations;
  own.contractions = checked.choices().contractions;
  own.releases = checked.choices().releases;
  auto ownChecked = check(*result, own);
  accept(materializePhysical(*result, ownChecked));
  admitPhysical(*result);
  accept(verifyPhysicalMaterialization(source, *result, checked));
  return result;
}

std::string scalarSource() {
  return scopedFixture(
      R"mlir(
"runtime.binding"() {sym_name="and",contract="bool.and",arguments=[],implementation=""} : ()->()
)mlir",
      "%a:i1,%b:i1,%unused:i1,%other:i1", "%a,%b,%unused,%other", "i1,i1,i1,i1",
      "i1",
      scopedApply("and", "first", "%a,%b", "i1,i1", "%first", "i1") +
          scopedApply("and", "middle", "%first,%b", "i1,i1", "%middle", "i1") +
          scopedApply("and", "last", "%b,%b", "i1,i1", "%last", "i1") +
          scopedReturn("%last", "i1"),
      4);
}
std::string conversionSource() {
  return R"mlir(!F = !algebra.field<"bls12-381.fr">
!T = !poly.multilinear<"bls12-381.fr">
)mlir" + scopedFixture(
             R"mlir(
"runtime.binding"() {sym_name="fold",contract="poly.fold",arguments=["bls12-381.fr"],implementation="arkworks-msb/poly.fold"} : ()->()
)mlir",
             "%a:!T,%b:!T,%r:!F", "%a,%b,%r", "!T,!T,!F", "!T",
             scopedApply("fold", "first", "%a,%r", "!T,!F", "%first", "!T") +
                 scopedApply("fold", "second", "%b,%r", "!T,!F", "%second",
                             "!T") +
                 scopedReturn("%second", "!T"),
             3);
}
OwningOpRef<ModuleOp> scalar(MLIRContext &context) {
  return take(executableFixture(scalarSource(), context));
}
OwningOpRef<ModuleOp> chunkSource(MLIRContext &context, unsigned count = 1025,
                                  bool simultaneous = false) {
  auto module =
      take(executableFixture(scopedFixture("", "%keep:i1", "%keep", "i1", "i1",
                                           scopedReturn("%keep", "i1"), 1),
                             context));
  auto function = first<func::FuncOp>(*module);
  function.getBody().getBlocks().clear();
  OpBuilder builder(function);
  builder.setInsertionPointToEnd(function.addEntryBlock());
  exec::ScopedExecutionBuilder control(builder, function);
  SmallVector<Value> values;
  for (unsigned i = 0; i < count; ++i)
    values.push_back(control.invoke(
        "exec.boolean", builder.getI1Type(), control.scoped({}),
        {builder.getNamedAttr("value", builder.getBoolAttr(true)),
         builder.getNamedAttr(
             "site", builder.getStringAttr("dead" + std::to_string(i)))})[0]);
  if (simultaneous)
    control.conditional(
        values.front(), ValueRange(values).drop_front(), builder.getI1Type(),
        "discard", [&](unsigned arm) {
          auto helper = sc::region(
              builder, function, "discard_arm" + std::to_string(arm),
              ValueRange(values).drop_front().getTypes(), builder.getI1Type());
          exec::ScopedExecutionBuilder inner(builder, helper);
          inner.complete(helper.getArgument(1));
          return helper;
        });
  control.returned(function.getArgument(1));
  require(succeeded(verify(*module)), "scoped storage fixture refused");
  return module;
}

// Exactly 1024 semantic control inputs plus its unused result die together.
// Each branch retains isolated captures; the data-port limit still holds.
OwningOpRef<ModuleOp> simultaneousDeathsSource(MLIRContext &context) {
  return chunkSource(context, 1024, true);
}

bool containsRelease(const PhysicalPlan &proposal, StoragePoint point,
                     StorageValue value) {
  return llvm::any_of(proposal.releases, [&](const StorageRelease &release) {
    return release.point == point && llvm::is_contained(release.values, value);
  });
}

// Preserve mathematical requests so source and selected indices differ.
OwningOpRef<ModuleOp> computationSource(MLIRContext &context) {
  auto module = parseSourceString<ModuleOp>(R"mlir(
!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%a:!F,%b:!F):
   %difference = algebra.field_subtract %a,%b : (!F,!F)->!F
   %product = algebra.field_multiply %difference,%b : (!F,!F)->!F
   "protocol.return"(%product) : (!F)->()
 }) {sym_name="main",function_type=(!F,!F)->!F,roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir",
                                            &context);
  require(bool(module), "computation source fixture did not parse");
  PassManager pipeline(&context);
  pipeline.addPass(createProjectProtocolPass(false));
  pipeline.addPass(createLowerMathPass());
  require(succeeded(pipeline.run(*module)),
          "computation fixture lowering failed");
  first<exec::ComputeOp>(*module);
  return module;
}

class CountingCatalog final : public CandidateCatalog {
public:
  mutable unsigned queries = 0;
  Expected<std::vector<std::string>>
  implementations(const BindingApplication &application) const override {
    ++queries;
    if (application.contract == "poly.fold")
      return std::vector<std::string>{"arkworks-msb/poly.fold",
                                      "arkworks/poly.fold"};
    return installedCandidates().implementations(application);
  }
  std::vector<std::string> diagonalImplementations(
      const BindingApplication &application) const override {
    ++queries;
    return installedCandidates().diagonalImplementations(application);
  }
  std::vector<BindingApplication>
  conversions(const BoundType &from, const BoundType &to) const override {
    ++queries;
    return installedCandidates().conversions(from, to);
  }
};
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;

  for (bool releases : {false, true})
    cases.run(releases ? "physical plan records releases"
                       : "physical plan keeps releases optional",
              [&] {
                auto module = scalar(context);
                auto proposal = propose(*module, releases);
                require(proposal.releases.empty() != releases,
                        "release option did not control proposed decisions");
                auto checked = check(*module, proposal);
                auto output = materializedCopy(*module, checked);
                require(actualReleases(*output).empty() != releases,
                        "materialization did not consume checked releases");
              });

  cases.run("storage coordinates exclude scope and own CFG payload results",
            [&] {
              auto module = scalar(context);
              auto proposal = propose(*module, false);
              auto selected = take(proposal.cloneSelectedSubject(*module));
              auto *firstOp = site(*selected, "first");
              auto function = firstOp->getParentOfType<func::FuncOp>();
              auto dispatch = cast<exec::DispatchOp>(firstOp->getNextNode());
              auto payload = dispatch.getReturned()->getArgument(0);
              require(coordinate(*selected, payload) ==
                              StorageValue{StorageValue::OperationResult,
                                           indexOf(*selected, firstOp), 0, 0} &&
                          coordinate(*selected, function.getArgument(3)) ==
                              StorageValue{StorageValue::BlockArgument,
                                           indexOf(*selected, function), 2, 0},
                      "CFG payload or scope shifted a semantic coordinate");
              require(!take(ExecutionPorts::read(*selected))
                           .contains(function.getArgument(0)),
                      "administrative scope became releasable data");
            });

  cases.run("storage option preserves all existing physical choices", [&] {
    auto module = take(executableFixture(conversionSource(), context));
    auto plain =
        materializedCopy(*module, check(*module, propose(*module, false)));
    auto released = materializedCopy(*module, check(*module, propose(*module)));
    for (auto release : actualReleases(*released))
      release.erase();
    require(printed(*plain) == printed(*released),
            "storage option changed ports, sites, bindings or conversions");
    unsigned fixed = 0;
    plain->walk([&](exec::ApplyOp op) {
      fixed += implementation(op) == "arkworks-msb/poly.fold";
    });
    require(fixed == 2, "fixed fold implementation was replaced");
  });

  for (StringRef timing : {"early", "delayed", "omitted"})
    cases.run(
        "independent schedule accepts only legal " + timing + " release", [&] {
          auto module = scalar(context);
          auto proposal = propose(*module, false);
          auto selected = take(proposal.cloneSelectedSubject(*module));
          if (timing != "omitted") {
            auto value = coordinate(
                *selected, output(*selected, site(*selected, "first")));
            auto point =
                after(*selected,
                      site(*selected, timing == "early" ? "first" : "last"));
            proposal.releases.push_back({point, {value}});
          }
          if (timing == "early")
            refuse(*module, proposal);
          else {
            auto output = materializedCopy(*module, check(*module, proposal));
            require(actualReleases(*output).size() ==
                        (timing == "omitted" ? 0u : 1u),
                    "materializer recomputed the proposer schedule");
          }
        });

  cases.run("release before definition refuses", [&] {
    auto module = scalar(context);
    auto proposal = propose(*module, false);
    auto selected = take(proposal.cloneSelectedSubject(*module));
    auto *firstOp = site(*selected, "first");
    proposal.releases.push_back(
        {entry(*selected, body(*selected, firstOp)),
         {coordinate(*selected, output(*selected, firstOp))}});
    refuse(*module, proposal, "storage-schedule-coordinate");
  });

  for (StringRef mutation :
       {"value owner", "result", "block", "argument", "conversion value",
        "value enum", "point owner", "point block", "conversion point",
        "point enum", "operation point index", "result block", "empty chunk"})
    cases.run("malformed storage coordinate refuses: " + mutation, [&] {
      auto module = scalar(context);
      auto proposal = propose(*module, false);
      auto selected = take(proposal.cloneSelectedSubject(*module));
      auto *operation = site(*selected, "first");
      auto *block = body(*selected, operation);
      StorageRelease release{
          entry(*selected, block),
          {coordinate(*selected, argument(*selected, block, 2))}};
      auto &value = release.values.front();
      constexpr auto hugeOwner = std::numeric_limits<size_t>::max();
      constexpr auto hugeIndex = std::numeric_limits<unsigned>::max();
      if (mutation == "value owner")
        value.operation = hugeOwner;
      else if (mutation == "result") {
        value = coordinate(*selected, output(*selected, operation));
        value.index = hugeIndex;
        release.point = after(*selected, site(*selected, "last"));
      } else if (mutation == "block")
        value.block = hugeIndex;
      else if (mutation == "argument")
        value.index = hugeIndex;
      else if (mutation == "conversion value")
        value = {StorageValue::ConversionResult, indexOf(*selected, operation),
                 hugeIndex};
      else if (mutation == "value enum")
        value.kind = static_cast<StorageValue::Kind>(3);
      else if (mutation == "point owner")
        release.point.operation = hugeOwner;
      else if (mutation == "point block")
        release.point.index = hugeIndex;
      else if (mutation == "conversion point")
        release.point = {StoragePoint::AfterConversion,
                         indexOf(*selected, operation), hugeIndex};
      else if (mutation == "point enum")
        release.point.kind = static_cast<StoragePoint::Kind>(3);
      else if (mutation == "operation point index") {
        release.point = after(*selected, operation);
        release.point.index = 1;
      } else if (mutation == "result block") {
        value = coordinate(*selected, output(*selected, operation));
        value.block = 1;
        release.point = after(*selected, site(*selected, "last"));
      } else
        release.values.clear();
      proposal.releases.push_back(release);
      refuse(*module, proposal, "storage-schedule-coordinate");
    });

  for (StringRef duplicate : {"within chunk", "across chunks", "across points"})
    cases.run("duplicate release refuses " + duplicate, [&] {
      auto module = scalar(context);
      auto proposal = propose(*module, false);
      auto selected = take(proposal.cloneSelectedSubject(*module));
      auto *operation = site(*selected, "first");
      auto value = coordinate(
          *selected, argument(*selected, body(*selected, operation), 2));
      StorageRelease release{entry(*selected, body(*selected, operation)),
                             {value}};
      proposal.releases.push_back(release);
      if (duplicate == "within chunk")
        proposal.releases.front().values.push_back(value);
      else {
        if (duplicate == "across points")
          release.point = after(*selected, operation);
        proposal.releases.push_back(release);
      }
      refuse(*module, proposal);
    });

  for (StringRef escape : {"return", "yield", "condition", "capture"})
    cases.run("release before " + escape + " escape refuses", [&] {
      auto module = take(executableFixture(
          fixtureText("structured-source/loops-and-captures.mlir"), context));
      auto proposal = propose(*module, false);
      auto selected = take(proposal.cloneSelectedSubject(*module));
      auto flow = take(ExecutionPorts::read(*selected));
      Operation *terminator = nullptr;
      unsigned operand = 0;
      for (auto *op : flow.operations()) {
        const auto *step = flow.get(op).step;
        if (!step)
          continue;
        if (escape == "condition" && isa<exec::RangeOp>(op) &&
            step->conditional) {
          for (auto *inner :
               flow.body(flow.get(op).bodies.front()).instructions)
            if (isa<exec::CompleteOp>(inner))
              terminator = inner;
          break;
        }
        bool matches = escape == "return" ? isa<exec::ReturnOp>(op)
                       : escape == "yield"
                           ? isa<exec::CompleteOp>(op)
                           : escape == "capture" && isa<exec::RangeOp>(op);
        if (matches && !flow.inputs(op).empty() &&
            flow.definition(flow.inputs(op)[0]).argument && !terminator)
          terminator = op;
      }
      require(terminator != nullptr, "missing escaping control");
      if (escape == "capture")
        operand = 2;
      Value value = flow.inputs(terminator)[operand];
      require(flow.definition(value).argument,
              "escape control needs a logical body argument");
      proposal.releases.push_back(
          {entry(*selected, flow.enclosingBody(terminator)),
           {coordinate(*selected, value)}});
      refuse(*module, proposal);
    });

  cases.run("release after a terminator has no legal point", [&] {
    auto module = scalar(context);
    auto proposal = propose(*module, false);
    auto selected = take(proposal.cloneSelectedSubject(*module));
    auto *block = body(*selected, site(*selected, "first"));
    proposal.releases.push_back(
        {after(*selected, completion(cast<func::FuncOp>(block->getParentOp()))),
         {coordinate(*selected, argument(*selected, block, 2))}});
    refuse(*module, proposal, "storage-schedule-coordinate");
  });

  cases.run(
      "nested blocks retain independent releases and escaping results", [&] {
        auto module = take(executableFixture(
            fixtureText("structured-source/loops-and-captures.mlir"), context));
        auto proposal = propose(*module);
        auto selected = take(proposal.cloneSelectedSubject(*module));
        Operation *choose = first<exec::TestOp>(*selected);
        auto branches = regions(*selected, choose);
        auto &left = *branches[0];
        auto &right = *branches[1];
        require(
            containsRelease(
                proposal, entry(*selected, &left),
                coordinate(*selected, argument(*selected, &left, 0))) &&
                containsRelease(
                    proposal, entry(*selected, &right),
                    coordinate(*selected, argument(*selected, &right, 1))),
            "unused isolated block arguments lost their own entry releases");
        auto flow = take(ExecutionPorts::read(*selected));
        for (auto *op : flow.operations()) {
          if (!isa<exec::ReturnOp, exec::CompleteOp>(op))
            continue;
          for (Value operand : flow.inputs(op))
            for (const auto &release : proposal.releases)
              require(!llvm::is_contained(release.values,
                                          coordinate(*selected, operand)),
                      "proposal released an escaping completion operand");
        }
        auto output = materializedCopy(*module, check(*module, proposal));
        require(!actualReleases(*output).empty(),
                "nested materialization lost releases");
      });

  cases.run("a capture source may release after the enclosing operation", [&] {
    auto module = take(executableFixture(
        fixtureText("structured-source/loops-and-captures.mlir"), context));
    auto proposal = propose(*module, false);
    auto selected = take(proposal.cloneSelectedSubject(*module));
    Operation *loop = first<exec::RangeOp>(*selected);
    proposal.releases.push_back(
        {after(*selected, loop),
         {coordinate(*selected, input(*selected, loop, 2))}});
    materializedCopy(*module, check(*module, proposal));
  });

  cases.run("a sibling block cannot release another block's value", [&] {
    auto module = take(executableFixture(
        fixtureText("structured-source/loops-and-captures.mlir"), context));
    auto proposal = propose(*module, false);
    auto selected = take(proposal.cloneSelectedSubject(*module));
    Operation *choose = first<exec::TestOp>(*selected);
    auto branches = regions(*selected, choose);
    auto &left = *branches[0];
    auto &right = *branches[1];
    proposal.releases.push_back(
        {entry(*selected, &right),
         {coordinate(*selected, argument(*selected, &left, 0))}});
    refuse(*module, proposal);
  });

  for (StringRef resource : {"used affine", "no Drop"})
    cases.run("normal type contracts refuse " + resource + " storage", [&] {
      auto path = resource == "used affine"
                      ? "mathematical/mixed-unit.mlir"
                      : "mathematical/schnorr-affine.mlir";
      auto module = take(executableFixture(fixtureText(path), context));
      auto proposal = propose(*module);
      auto selected = take(proposal.cloneSelectedSubject(*module));
      auto *consumer =
          site(*selected, resource == "used affine" ? "consume" : "respond");
      auto value =
          input(*selected, consumer, resource == "used affine" ? 0 : 2);
      auto encoded = take(encodeBoundType(value.getType(), false));
      require(affine(encoded.spelling()) && discardable(encoded.spelling()) ==
                                                (resource == "used affine"),
              "fixture does not distinguish affine use from Drop permission");
      auto reference = coordinate(*selected, value);
      for (const auto &release : proposal.releases)
        require(!llvm::is_contained(release.values, reference),
                "proposer released a used affine resource");
      proposal.releases.clear();
      proposal.releases.push_back({after(*selected, consumer), {reference}});
      refuse(*module, proposal, "storage-schedule-permission");
    });

  cases.run(
      "computation releases belong to the selected executable subject", [&] {
        auto module = computationSource(context);
        auto proposal = propose(*module);
        auto selected = take(proposal.cloneSelectedSubject(*module));
        auto sourceFunction =
            first<exec::ComputeOp>(*module)->getParentOfType<func::FuncOp>();
        auto selectedFunction =
            SymbolTable(&selected->getBody()->front())
                .lookup<func::FuncOp>(sourceFunction.getSymName());
        StorageValue original{StorageValue::BlockArgument,
                              indexOf(*module, sourceFunction), 0, 0};
        auto actual = coordinate(*selected, selectedFunction.getArgument(1));
        require(original.operation != actual.operation,
                "computation fixture did not distinguish source and selected "
                "indices");
        auto sourceBefore = printed(*module);
        materializedCopy(*module, check(*module, proposal));
        require(printed(*module) == sourceBefore,
                "computation scheduling changed source");
        proposal.releases.clear();
        proposal.releases.push_back(
            {after(*selected, first<exec::ApplyOp>(*selected)), {original}});
        refuse(*module, proposal, "storage-schedule-coordinate");
      });

  for (StringRef lifetime :
       {"source after conversion", "temporary after consumer",
        "source before conversion", "temporary before consumer"})
    cases.run("conversion storage lifetime: " + lifetime, [&] {
      auto module = take(executableFixture(conversionSource(), context));
      auto proposal = propose(*module, false);
      auto selected = take(proposal.cloneSelectedSubject(*module));
      auto *consumer = site(*selected, "first");
      auto index = indexOf(*selected, consumer);
      const auto &conversions = proposal.operations[index].conversions;
      require(conversions.size() == 1 && conversions.front().operand == 0,
              "fixed arkworks-msb fold did not require a table conversion");
      auto source = coordinate(*selected, input(*selected, consumer, 0));
      StorageValue temporary{StorageValue::ConversionResult, index, 0};
      StoragePoint converted{StoragePoint::AfterConversion, index, 0};
      bool early = lifetime == "source before conversion" ||
                   lifetime == "temporary before consumer";
      auto point = lifetime == "source before conversion"
                       ? entry(*selected, body(*selected, consumer))
                   : lifetime == "temporary after consumer"
                       ? after(*selected, consumer)
                       : converted;
      proposal.releases.push_back(
          {point, {lifetime.starts_with("source") ? source : temporary}});
      if (early)
        refuse(*module, proposal);
      else
        materializedCopy(*module, check(*module, proposal));
    });

  cases.run(
      "conversion proposal releases source and temporary at distinct points",
      [&] {
        auto module = take(executableFixture(conversionSource(), context));
        auto proposal = propose(*module);
        auto selected = take(proposal.cloneSelectedSubject(*module));
        auto *consumer = site(*selected, "first");
        auto index = indexOf(*selected, consumer);
        require(
            containsRelease(
                proposal, {StoragePoint::AfterConversion, index, 0},
                coordinate(*selected, input(*selected, consumer, 0))) &&
                containsRelease(proposal, after(*selected, consumer),
                                {StorageValue::ConversionResult, index, 0}),
            "conversion source or temporary retained beyond deterministic last "
            "use");
        materializedCopy(*module, check(*module, proposal));
      });

  for (bool point : {false, true})
    cases.run(
        point ? "huge conversion point index refuses"
              : "huge conversion result index refuses",
        [&] {
          auto module = take(executableFixture(conversionSource(), context));
          auto proposal = propose(*module, false);
          auto selected = take(proposal.cloneSelectedSubject(*module));
          auto *consumer = site(*selected, "first");
          auto index = indexOf(*selected, consumer);
          require(proposal.operations[index].conversions.size() == 1,
                  "conversion bound control needs an actual conversion");
          StorageRelease release{after(*selected, consumer),
                                 {{StorageValue::ConversionResult, index, 0}}};
          constexpr auto hugeIndex = std::numeric_limits<unsigned>::max();
          if (point)
            release.point = {StoragePoint::AfterConversion, index, hugeIndex};
          else
            release.values.front().index = hugeIndex;
          proposal.releases.push_back(release);
          refuse(*module, proposal, "storage-schedule-coordinate");
        });

  cases.run(
      "equal conversion inputs retain distinct temporary occurrences", [&] {
        auto module = take(executableFixture(
            replaceText(conversionSource(), "%scope,%b,%r", "%scope,%a,%r"),
            context));
        auto proposal = propose(*module);
        auto selected = take(proposal.cloneSelectedSubject(*module));
        auto *firstOp = site(*selected, "first");
        auto *secondOp = site(*selected, "second");
        auto firstIndex = indexOf(*selected, firstOp);
        auto secondIndex = indexOf(*selected, secondOp);
        auto source = coordinate(*selected, input(*selected, firstOp, 0));
        require(
            input(*selected, firstOp, 0) == input(*selected, secondOp, 0) &&
                containsRelease(proposal,
                                {StoragePoint::AfterConversion, secondIndex, 0},
                                source) &&
                containsRelease(
                    proposal, after(*selected, firstOp),
                    {StorageValue::ConversionResult, firstIndex, 0}) &&
                containsRelease(
                    proposal, after(*selected, secondOp),
                    {StorageValue::ConversionResult, secondIndex, 0}),
            "repeated source conversion occurrences collapsed or released "
            "source early");
        materializedCopy(*module, check(*module, proposal));
      });

  for (bool early : {false, true})
    cases.run(
        early ? "equal operands keep source alive through both conversions"
              : "equal operands produce two distinct conversion temporaries",
        [&] {
          auto text = R"mlir(!F = !algebra.field<"bls12-381.fr">
!T = !poly.multilinear<"bls12-381.fr">
)mlir" + scopedFixture(R"mlir(
"runtime.binding"() {sym_name="product",contract="poly.product_sum",arguments=["bls12-381.fr"],implementation="arkworks-msb/poly.product_sum"} : ()->()
)mlir",
                       "%table:!T", "%table", "!T", "!F",
                       scopedApply("product", "product", "%table,%table",
                                   "!T,!T", "%result", "!F") +
                           scopedReturn("%result", "!F"),
                       1);
          auto module = take(executableFixture(text, context));
          auto proposal = propose(*module);
          auto selected = take(proposal.cloneSelectedSubject(*module));
          auto *consumer = site(*selected, "product");
          auto index = indexOf(*selected, consumer);
          const auto &crossings = proposal.operations[index].conversions;
          require(crossings.size() == 2 && crossings[0].operand == 0 &&
                      crossings[1].operand == 1,
                  "equal operands did not retain two ordered conversions");
          auto source = coordinate(*selected, input(*selected, consumer, 0));
          require(
              containsRelease(proposal,
                              {StoragePoint::AfterConversion, index, 1},
                              source) &&
                  containsRelease(proposal, after(*selected, consumer),
                                  {StorageValue::ConversionResult, index, 0}) &&
                  containsRelease(proposal, after(*selected, consumer),
                                  {StorageValue::ConversionResult, index, 1}),
              "equal operands collapsed conversion identities or source "
              "lifetime");
          if (early) {
            proposal.releases.clear();
            proposal.releases.push_back(
                {{StoragePoint::AfterConversion, index, 0}, {source}});
            refuse(*module, proposal);
          } else
            materializedCopy(*module, check(*module, proposal));
        });

  cases.run(
      "proposer chunks 1025 simultaneous deaths within normal port limits",
      [&] {
        auto module = simultaneousDeathsSource(context);
        auto proposal = propose(*module);
        auto selected = take(proposal.cloneSelectedSubject(*module));
        auto point = after(*selected, first<exec::TestOp>(*selected));
        SmallVector<const StorageRelease *> chunks;
        for (const auto &release : proposal.releases)
          if (release.point == point)
            chunks.push_back(&release);
        require(chunks.size() == 2 && chunks[0]->values.size() == 1024 &&
                    chunks[1]->values.size() == 1,
                "proposer did not split simultaneous last uses into bounded "
                "chunks");
        auto repeated = propose(*module);
        require(repeated.releases == proposal.releases,
                "simultaneous-death proposal changed deterministic ordering");
        materializedCopy(*module, check(*module, proposal));
      });

  for (StringRef control :
       {"legal chunks", "oversized chunk", "duplicate across chunks",
        "changed chunk order", "changed operand order"})
    cases.run("1025 delayed values: " + control, [&] {
      auto module = chunkSource(context);
      auto proposal = propose(*module, false);
      auto selected = take(proposal.cloneSelectedSubject(*module));
      SmallVector<StorageValue> values;
      for (auto [index, operation] :
           enumerate(physicalPlanOperations(*selected)))
        if (isa<exec::BooleanOp>(operation))
          values.push_back({StorageValue::OperationResult, index, 0});
      require(values.size() == 1025, "chunk fixture lost dead definitions");
      auto point = after(*selected, site(*selected, "dead1024"));
      if (control == "oversized chunk") {
        proposal.releases.push_back({point, values});
        refuse(*module, proposal, "storage-schedule-coordinate");
        return;
      }
      proposal.releases.push_back(
          {point,
           SmallVector<StorageValue>(values.begin(), values.begin() + 1024)});
      proposal.releases.push_back({point, {values.back()}});
      if (control == "duplicate across chunks") {
        proposal.releases.back().values.front() = values.front();
        refuse(*module, proposal);
        return;
      }
      auto checked = check(*module, proposal);
      auto output = materializedCopy(*module, checked);
      auto releases = actualReleases(*output);
      require(releases.size() == 2 && releases[0].getValues().size() == 1024 &&
                  releases[1].getValues().size() == 1,
              "materializer merged, split or omitted checked chunks");
      auto actualFlow = take(ExecutionPorts::read(*output));
      for (unsigned i = 0; i < 1024; ++i)
        require(actualFlow.definition(releases[0].getValues()[i])
                        .owner->getAttrOfType<StringAttr>("site")
                        .getValue() == "dead" + std::to_string(i),
                "materializer changed deterministic operand order");
      require(actualFlow.definition(releases[1].getValues()[0]).owner ==
                  site(*output, "dead1024"),
              "materializer reversed chunk order");
      if (control == "changed chunk order")
        releases[1]->moveBefore(releases[0]);
      else if (control == "changed operand order") {
        Value firstValue = releases[0].getValues()[0];
        releases[0].getValuesMutable()[0].set(releases[0].getValues()[1]);
        releases[0].getValuesMutable()[1].set(firstValue);
      } else {
        auto repeated = propose(*module);
        auto again = propose(*module);
        require(repeated.releases == again.releases,
                "repeated proposals changed deterministic release order");
        auto repeatedOutput = materializedCopy(*module, checked);
        require(printed(*output) == printed(*repeatedOutput),
                "same checked schedule materialized nondeterministically");
        return;
      }
      admitPhysical(*output);
      reject(verifyPhysicalMaterialization(*module, *output, checked),
             "binding-materialization-correspondence");
    });

  for (StringRef mutation : {"missing", "extra", "wrong", "moved"})
    cases.run("independent output reader rejects " + mutation + " release",
              [&] {
                auto module = scalar(context);
                auto proposal = propose(*module, false);
                auto selected = take(proposal.cloneSelectedSubject(*module));
                auto *block = body(*selected, site(*selected, "first"));
                proposal.releases.push_back(
                    {entry(*selected, block),
                     {coordinate(*selected, argument(*selected, block, 2))}});
                auto checked = check(*module, proposal);
                auto output = materializedCopy(*module, checked);
                auto release = first<runtime::ReleaseBindingsOp>(*output);
                auto function = release->getParentOfType<func::FuncOp>();
                auto other = function.getArgument(4);
                if (mutation == "missing")
                  release.erase();
                else if (mutation == "wrong")
                  release.getValuesMutable()[0].set(other);
                else if (mutation == "moved")
                  release->moveBefore(site(*output, "last"));
                else {
                  OpBuilder builder(release);
                  runtime::ReleaseBindingsOp::create(builder, release.getLoc(),
                                                     function.getArgument(0),
                                                     ValueRange{other});
                }
                admitPhysical(*output);
                reject(verifyPhysicalMaterialization(*module, *output, checked),
                       "binding-materialization-correspondence");
              });

  cases.run(
      "checked releases own a copy and materialization never queries catalog",
      [&] {
        auto module = take(executableFixture(
            replaceText(conversionSource(),
                        "implementation=\"arkworks-msb/poly.fold\"",
                        "implementation=\"\""),
            context));
        auto original = copy(*module);
        CountingCatalog catalog;
        auto originalChecked =
            check(*original, propose(*original, true, catalog), catalog);
        auto proposal = propose(*module, true, catalog);
        auto checked = check(*module, proposal, catalog);
        bool preferred = false;
        for (const auto &binding : checked.choices().bindings)
          if (binding.binding.application.contract == "poly.fold")
            preferred |=
                !binding.fixed && binding.binding.application.implementation ==
                                      "arkworks-msb/poly.fold";
        require(preferred,
                "custom catalog did not select its nondefault fold preference");
        require(!proposal.releases.empty() && catalog.queries != 0,
                "catalog/copy control did not exercise scheduled choices");
        auto releaseCount = checked.choices().releases.size();
        proposal.releases.front().values.clear();
        proposal.releases.clear();
        proposal.bindings.clear();
        proposal.operations.clear();
        auto queries = catalog.queries;
        require(checked.choices().releases.size() == releaseCount &&
                    !checked.choices().releases.front().values.empty(),
                "mutable proposal aliases checked releases");
        accept(materializePhysical(*module, checked));
        admitPhysical(*module);
        accept(
            verifyPhysicalMaterialization(*original, *module, originalChecked));
        require(catalog.queries == queries, "materialization queried catalog");
      });

  for (bool checkedFirst : {false, true})
    cases.run(checkedFirst ? "checked storage refuses stale input"
                           : "storage validation refuses stale input",
              [&] {
                auto module = scalar(context);
                auto proposal = propose(*module);
                auto checked = check(*module, proposal);
                auto *operation = site(*module, "middle");
                cast<exec::ApplyOp>(operation).getInputsMutable()[0].set(
                    operation->getParentOfType<func::FuncOp>().getArgument(1));
                require(succeeded(verify(*module)),
                        "stale fixture must remain admitted");
                auto before = printed(*module);
                if (checkedFirst)
                  reject(materializePhysical(*module, checked),
                         "binding-stale-selection");
                else
                  refuses(validatePhysical(*module, proposal),
                          "binding-stale-selection");
                require(printed(*module) == before,
                        "stale refusal published changes");
              });

  cases.run("explicit fixed selection survives scheduled materialization", [&] {
    auto module = take(executableFixture(
        replaceText(conversionSource(),
                    "implementation=\"arkworks-msb/poly.fold\"",
                    "implementation=\"\""),
        context));
    auto proposal = take(proposePhysical(*module, installedCandidates(),
                                         {{"fold", "arkworks-msb/poly.fold"}},
                                         PhysicalPlanOptions{false, true}));
    bool fixed = false;
    for (const auto &binding : proposal.bindings)
      if (binding.binding.name == "fold")
        fixed |= binding.fixed && binding.binding.application.implementation ==
                                      "arkworks-msb/poly.fold";
    require(fixed, "explicit implementation selection was not fixed");
    auto checked = check(*module, proposal);
    accept(materializePhysical(*module, checked));
    admitPhysical(*module);
    unsigned folds = 0;
    module->walk([&](exec::ApplyOp op) {
      folds += implementation(op) == "arkworks-msb/poly.fold";
    });
    require(folds == 2 && !actualReleases(*module).empty(),
            "scheduled publication lost fixed implementations or releases");
  });

  cases.run(
      "textually identical input clone does not inherit checked identity", [&] {
        auto module = scalar(context);
        auto proposal = propose(*module);
        auto checked = check(*module, proposal);
        auto clone = copy(*module);
        auto before = printed(*clone);
        require(before == printed(*module),
                "identity control needs identical content");
        refuses(validatePhysical(*clone, proposal), "binding-stale-selection");
        reject(materializePhysical(*clone, checked), "binding-stale-selection");
        require(printed(*clone) == before,
                "identity refusal changed input clone");
      });

  cases.run("standalone storage release is exactly idempotent", [&] {
    auto module = scalar(context);
    auto output = materializedCopy(*module, check(*module, propose(*module)));
    auto before = printed(*output);
    auto once = copy(*output);
    require(succeeded(releaseLocalStorage(*output)),
            "standalone release refused");
    require(printed(*output) == before,
            "standalone release duplicated or moved existing releases");
    require(succeeded(verifyStoragePreserved(*once, *output)),
            "standalone reader refused preserved releases");
    require(succeeded(releaseLocalStorage(*output)) &&
                printed(*output) == before,
            "second standalone release changed already released output");
  });

  cases.run(
      "standalone release refuses unknown attributes without publication", [&] {
        auto module = scalar(context);
        auto output =
            materializedCopy(*module, check(*module, propose(*module)));
        first<runtime::ReleaseBindingsOp>(*output)->setAttr(
            "annotation", StringAttr::get(&context, "unknown"));
        auto before = printed(*output);
        require(failed(releaseLocalStorage(*output)),
                "unknown release metadata admitted");
        require(printed(*output) == before, "refused metadata changed source");
      });

  cases.run("oversized comparison refuses at shared source admission", [&] {
    auto module = simultaneousDeathsSource(context);
    auto output =
        materializedCopy(*module, check(*module, propose(*module, false)));
    auto positive = copy(*output);
    require(take(readStorageReleases(*output, *positive)).empty(),
            "bounded positive standalone comparison refused");
    auto *original = first<exec::TestOp>(*output).getOperation();
    auto flow = take(ExecutionPorts::read(*output));
    auto inputs = llvm::to_vector(flow.inputs(original));
    auto function = original->getParentOfType<func::FuncOp>();
    auto end = completion(function);
    auto *failure =
        cast<exec::DispatchOp>(original->getNextNode()).getStopped();
    IRRewriter rewriter(&context);
    auto *before = end->getBlock();
    auto *tail = rewriter.splitBlock(before, end->getIterator());
    OpBuilder builder(&context);
    builder.setInsertionPointToEnd(before);
    exec::ScopedExecutionBuilder control(builder, function);
    // Every occurrence has its own closed regions and respects the 1024-port
    // bound. The repeated semantic operand/argument work exceeds admission.
    for (unsigned i = 0; i < 400; ++i)
      control.conditional(
          inputs.front(), ValueRange(inputs).drop_front(), inputs[1].getType(),
          "extra" + std::to_string(i), [&](unsigned arm) {
            auto helper = sc::region(builder, function,
                                     "extra" + std::to_string(i) + "_arm" +
                                         std::to_string(arm),
                                     ValueRange(inputs).drop_front().getTypes(),
                                     inputs[1].getType());
            exec::ScopedExecutionBuilder inner(builder, helper);
            inner.complete(helper.getArgument(1));
            return helper;
          });
    rewriter.mergeBlocks(tail, builder.getInsertionBlock());
    SmallVector<Block *> redundantFailures;
    function.walk([&](exec::FailureOp op) {
      if (op->getBlock() != failure)
        redundantFailures.push_back(op->getBlock());
    });
    require(redundantFailures.size() == 1,
            "appended controls did not share their failure continuation");
    for (auto *block : redundantFailures) {
      block->replaceAllUsesWith(failure);
      block->erase();
    }
    // The independent reader now requires admitted ExecutionPorts. This exact
    // former 400-control workload reaches the shared source bound first; it
    // must not bypass that boundary to exercise a later private work counter.
    auto identical = copy(*output);
    bool sourceLimit = false;
    ScopedDiagnosticHandler diagnostic(&context, [&](Diagnostic &message) {
      for (const auto &refusal : diagnostics::refusals(message))
        sourceLimit |= refusal.code == "source-limit";
      return success();
    });
    refuses(readStorageReleases(*output, *identical),
            "binding-execution-profile");
    require(sourceLimit, "oversized comparison refused before its work bound");
  });

  cases.run("standalone and planned conversion lifetimes agree", [&] {
    auto module = take(executableFixture(conversionSource(), context));
    auto planned = materializedCopy(*module, check(*module, propose(*module)));
    auto standalone =
        materializedCopy(*module, check(*module, propose(*module, false)));
    require(succeeded(releaseLocalStorage(*standalone)),
            "standalone conversion release failed");
    require(printed(*planned) == printed(*standalone),
            "standalone and checked-plan conversion lifetimes disagree");
  });

  cases.run("release instruction admission failure publishes nothing", [&] {
    auto module = chunkSource(context, 8192);
    auto function = first<func::FuncOp>(*module);
    OpBuilder builder(function);
    for (unsigned i = 0; i < 3; ++i) {
      auto *extra = builder.clone(*function);
      SymbolTable::setSymbolName(extra, "extraWork" + std::to_string(i));
    }
    auto checked = check(*module, propose(*module));
    auto before = printed(*module);
    auto identities = physicalPlanOperations(*module);
    std::string admissionRefusals;
    ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
      for (const auto &refusal : diagnostics::refusals(diagnostic))
        admissionRefusals += refusal.code + ";";
      return success();
    });
    reject(materializePhysical(*module, checked),
           "binding-materialization-formation");
    require(namesIdentifier(admissionRefusals, "interactive-instruction-limit"),
            "candidate refused at: " + admissionRefusals);
    require(printed(*module) == before &&
                physicalPlanOperations(*module) == identities,
            "failed final admission published content or identities");
  });

  return cases.result();
}
