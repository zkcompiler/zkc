#include "../lib/Conversion/Bindings.h"
#include "../lib/Target/AggregateLayouts.h"
#include "../lib/Target/PhysicalPlan.h"
#include "mlir/AsmParser/AsmParser.h"
#include "mlir/IR/Verifier.h"
#include "support/MathematicalFixture.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/Implementations.h"
#include "zkc/Contracts/NativeOrigin.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include "zkc/Program/Admission.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/Signals.h"

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::target;
using namespace zkc::test;
namespace {
std::string emitDirectory;
void emitArtifact(const llvm::json::Value &program, StringRef name) {
  if (emitDirectory.empty() || name.empty())
    return;
  SmallString<256> path(emitDirectory);
  llvm::sys::path::append(path, name.str() + ".json");
  std::error_code error;
  raw_fd_ostream output(path, error, llvm::sys::fs::OF_Text);
  require(!error, "cannot create emitted program: " + error.message());
  output << printJson(program) << '\n';
  output.flush();
  require(!output.has_error(), "cannot write emitted program");
}
void accept(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
OperationDecision &at(PhysicalPlan &plan, ModuleOp module, StringRef site) {
  auto operations = physicalPlanOperations(module);
  for (auto &decision : plan.operations)
    if (auto name =
            operations[decision.operation]->getAttrOfType<StringAttr>("site"))
      if (name.getValue() == site)
        return decision;
  throw std::runtime_error("missing site " + site.str());
}
void abi(PhysicalPlanOptions &options, ModuleOp module, bool output,
         unsigned index, StringRef physical) {
  for (auto *op : physicalPlanOperations(module))
    if (isa<local::FuncOp, protocol_ir::ParticipantOp>(op))
      options.functionPorts.push_back(
          {op->getAttrOfType<StringAttr>("sym_name").getValue().str(), output,
           index, physical.str()});
}
void publish(ModuleOp module, const CheckedPhysicalPlan &checked,
             StringRef artifact = {}) {
  accept(materializePhysical(module, checked));
  require(succeeded(verify(module)), "physical verification");
  auto program = take(readExecutionModel(module));
  auto encoded = program::encode(program);
  auto *root = encoded.getAsArray();
  require(root && (*root)[1].getAsArray(), "program root");
  for (auto &row : *(*root)[1].getAsArray())
    require(row.getAsArray() && row.getAsArray()->size() == 5,
            "binding root is not uniformly five fields");
  take(program::decode(encoded));
  emitArtifact(encoded, artifact);
  if (!(*root)[1].getAsArray()->empty()) {
    auto old = encoded;
    (*(*old.getAsArray())[1].getAsArray())[0].getAsArray()->pop_back();
    refuses(program::decode(old), "binding-declaration");
  }
  module.walk([&](Operation *op) {
    require(!isa<UnrealizedConversionCastOp, local::ApplyOp>(op),
            "unresolved publication");
  });
}
std::string sequenceSource() {
  return R"(!F = !algebra.field<"bls12-381.fr">
!S = !data.sequence<!algebra.field<"bls12-381.fr">>
!T = !data.sequence<!data.sequence<!algebra.field<"bls12-381.fr">>>
)" + mathematicalFixture(R"(
"local.binding"() {sym_name="empty",contract="sequence.empty",arguments=["field:bls12-381.fr"],implementation="native/sequence.empty"} : ()->()
"local.binding"() {sym_name="append",contract="sequence.append",arguments=["field:bls12-381.fr"],implementation="native/sequence.append"} : ()->()
"local.binding"() {sym_name="outer",contract="sequence.empty",arguments=["sequence<field:bls12-381.fr>"],implementation="native/sequence.empty"} : ()->()
"local.binding"() {sym_name="pack",contract="sequence.append",arguments=["sequence<field:bls12-381.fr>"],implementation="native/sequence.append"} : ()->()
)",
                         "%x:!F", "%x", "!F", "!T", R"(
%s = "data.exec.sequence_empty"() {binding=@empty,site="empty",parameters=[]} : ()->!S
%values = "data.exec.sequence_append"(%s,%x) {binding=@append,site="append",parameters=[]} : (!S,!F)->!S
%t = "data.exec.sequence_empty"() {binding=@outer,site="outer",parameters=[]} : ()->!T
%out = "data.exec.sequence_append"(%t,%values) {binding=@pack,site="pack",parameters=[]} : (!T,!S)->!T
local.return %out : !T
)",
                         1);
}
std::string scalarJoinSource(unsigned count, bool nested) {
  std::string body = R"(
%v = "algebra.exec.field_add"(%x,%x) {binding=@add,site="add",parameters=[]} : (!F,!F)->!F
)";
  std::string value = "%v", condition = "%c";
  for (unsigned i = 0; i < count; ++i) {
    auto suffix = std::to_string(i);
    body += "%j" + suffix + " = \"local.if\"(" + condition + "," + value + "," +
            condition + ") ({^left" + suffix + "(%a" + suffix + ":!F,%c" +
            suffix + ":i1):\n";
    if (nested) {
      value = "%a" + suffix;
      condition = "%c" + suffix;
    } else {
      body += "\"local.yield\"(%a" + suffix + ") : (!F)->()\n}, {^right" +
              suffix + "(%b" + suffix + ":!F,%d" + suffix + ":i1):\n" +
              "\"local.yield\"(%b" + suffix + ") : (!F)->()\n}) {site=\"join" +
              suffix + "\"} : (i1,!F,i1)->!F\n";
      value = "%j" + suffix;
    }
  }
  if (nested)
    for (unsigned i = count; i-- > 0;) {
      auto suffix = std::to_string(i);
      body += "\"local.yield\"(" + value + ") : (!F)->()\n}, {^right" + suffix +
              "(%b" + suffix + ":!F,%d" + suffix + ":i1):\n";
      body += i % 3 == 0 ? "\"local.stop\"() {reason=\"reject\",site=\"stop" +
                               suffix + "\"} : ()->()\n"
                         : "\"local.yield\"(%b" + suffix + ") : (!F)->()\n";
      body += "}) {site=\"join" + suffix + "\"} : (i1,!F,i1)->!F\n";
      value = "%j" + suffix;
    }
  body += "local.return " + value + " : !F\n";
  return R"(!F = !algebra.field<"bls12-381.fr">
)" + mathematicalFixture(R"(
"local.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation="blst/resident/field.add"} : ()->()
)",
                         "%x:!F,%c:i1", "%x,%c", "!F,i1", "!F", body, 2);
}
std::string cyclicSequenceSource(bool seeded) {
  std::string body = R"(
%v = "algebra.exec.field_add"(%x,%x) {binding=@add,site="add",parameters=[]} : (!F,!F)->!F
%empty = "data.exec.sequence_empty"() {binding=@empty,site="empty",parameters=[]} : ()->!S
)";
  if (seeded)
    body += R"(
%seed = "data.exec.sequence_append"(%empty,%v) {binding=@append,site="seed",parameters=[]} : (!S,!F)->!S
)";
  body +=
      "%out = \"local.for\"(%lo,%hi," +
      std::string(seeded ? "%seed" : "%empty") +
      R"(,%v,%c,%lo) ({^body(%i:ui64,%state:!S,%element:!F,%condition:i1,%index:ui64):
  %loaded = "data.exec.sequence_at"(%state,%index) {binding=@at,site="at",parameters=[]} : (!S,ui64)->!F
  %picked = "local.if"(%condition,%loaded,%element) ({^left(%a:!F,%b:!F):
    "local.yield"(%a) : (!F)->()
  }, {^right(%a:!F,%b:!F):
    "local.yield"(%b) : (!F)->()
  }) {site="join"} : (i1,!F,!F)->!F
  %next = "data.exec.sequence_append"(%state,%picked) {binding=@append,site="append",parameters=[]} : (!S,!F)->!S
  "local.yield"(%next,%element,%condition,%index) : (!S,!F,i1,ui64)->()
}) {site="loop"} : (ui64,ui64,!S,!F,i1,ui64)->!S
%n = "data.exec.sequence_length"(%out) {binding=@length,site="length",parameters=[]} : (!S)->ui64
local.return %n : ui64
)";
  return R"(!F = !algebra.field<"bls12-381.fr">
!S = !data.sequence<!algebra.field<"bls12-381.fr">>
)" + mathematicalFixture(R"(
"local.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation="blst/resident/field.add"} : ()->()
"local.binding"() {sym_name="empty",contract="sequence.empty",arguments=["field:bls12-381.fr"],implementation="native/sequence.empty"} : ()->()
"local.binding"() {sym_name="append",contract="sequence.append",arguments=["field:bls12-381.fr"],implementation="native/sequence.append"} : ()->()
"local.binding"() {sym_name="at",contract="sequence.at",arguments=["field:bls12-381.fr"],implementation="native/sequence.at"} : ()->()
"local.binding"() {sym_name="length",contract="sequence.length",arguments=["field:bls12-381.fr"],implementation="native/sequence.length"} : ()->()
)",
                         "%x:!F,%c:i1,%lo:ui64,%hi:ui64", "%x,%c,%lo,%hi",
                         "!F,i1,ui64,ui64", "ui64", body, 4);
}
std::string inferredSequenceSource(StringRef control) {
  std::string body = R"(
%v = "algebra.exec.field_add"(%x,%x) {binding=@add,site="add",parameters=[]} : (!F,!F)->!F
%s = "data.exec.sequence_empty"() {binding=@empty,site="empty",parameters=[]} : ()->!S
)";
  if (control == "straight")
    body += R"(
%out = "data.exec.sequence_append"(%s,%v) {binding=@append,site="append",parameters=[]} : (!S,!F)->!S
)";
  else if (control == "scalar")
    body += R"(
%picked = "local.if"(%c,%v) ({^left(%element:!F):
  "local.yield"(%element) : (!F)->()
}, {^right(%element:!F):
  "local.yield"(%element) : (!F)->()
}) {site="scalar_branch"} : (i1,!F)->!F
%out = "data.exec.sequence_append"(%s,%picked) {binding=@append,site="append",parameters=[]} : (!S,!F)->!S
)";
  else if (control == "match")
    body += R"(
%values = "data.exec.sequence_append"(%s,%v) {binding=@append,site="append",parameters=[]} : (!S,!F)->!S
%tag = "local.variant_inject"(%values) {alternative="some",site="tag"} : (!S)->!Tag
%out = "local.match"(%tag,%values,%v) ({^none(%capture:!S,%element:!F):
  "local.yield"(%capture) : (!S)->()
}, {^some(%payload:!S,%capture:!S,%element:!F):
  %next = "data.exec.sequence_append"(%payload,%element) {binding=@append,site="match_append",parameters=[]} : (!S,!F)->!S
  "local.yield"(%next) : (!S)->()
}) {alternatives=["none","some"],site="match"} : (!Tag,!S,!F)->!S
)";
  else if (control == "loop")
    body += R"(
%out = "local.for"(%lo,%hi,%s,%v) ({^body(%i:ui64,%state:!S,%element:!F):
  %next = "data.exec.sequence_append"(%state,%element) {binding=@append,site="loop_append",parameters=[]} : (!S,!F)->!S
  "local.yield"(%next,%element) : (!S,!F)->()
}) {site="loop"} : (ui64,ui64,!S,!F)->!S
)";
  else {
    body += R"(
%out = "local.if"(%c,%s,%v,%c) ({^left(%values:!S,%element:!F,%allowed:i1):
  "local.exec.require"(%allowed) {binding=@guard,site="guard",parameters=[]} : (i1)->()
  %next = "data.exec.sequence_append"(%values,%element) {binding=@append,site="append_left",parameters=[]} : (!S,!F)->!S
  "local.yield"(%next) : (!S)->()
}, {^right(%values:!S,%element:!F,%allowed:i1):
)";
    if (control == "stop")
      body +=
          "\"local.stop\"() {reason=\"reject\",site=\"stopped\"} : ()->()\n";
    else if (control == "capture")
      body += "\"local.yield\"(%values) : (!S)->()\n";
    else
      body += R"(
  %next = "data.exec.sequence_append"(%values,%element) {binding=@append,site="append_right",parameters=[]} : (!S,!F)->!S
  "local.yield"(%next) : (!S)->()
)";
    body += "}) {site=\"branch\"} : (i1,!S,!F,i1)->!S\n";
  }
  body += R"(
%n = "data.exec.sequence_length"(%out) {binding=@length,site="length",parameters=[]} : (!S)->ui64
local.return %n : ui64
)";
  auto variant = *encodeVariant(
      {"Inferred", {{"none", {}}, {"some", {"sequence<field:bls12-381.fr>"}}}});
  return "!Tag = !local.variant<\"" + variant + "\">\n" +
         R"(!F = !algebra.field<"bls12-381.fr">
!S = !data.sequence<!algebra.field<"bls12-381.fr">>
)" +
         mathematicalFixture(R"(
"local.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation="blst/resident/field.add"} : ()->()
"local.binding"() {sym_name="empty",contract="sequence.empty",arguments=["field:bls12-381.fr"],implementation="native/sequence.empty"} : ()->()
"local.binding"() {sym_name="append",contract="sequence.append",arguments=["field:bls12-381.fr"],implementation="native/sequence.append"} : ()->()
"local.binding"() {sym_name="length",contract="sequence.length",arguments=["field:bls12-381.fr"],implementation="native/sequence.length"} : ()->()
"local.binding"() {sym_name="guard",contract="control.require",arguments=[],implementation=""} : ()->()
)",
                             "%x:!F,%c:i1,%lo:ui64,%hi:ui64", "%x,%c,%lo,%hi",
                             "!F,i1,ui64,ui64", "ui64", body, 4);
}
class DenseCandidates final : public CandidateCatalog {
public:
  bool conversionsAvailable = true;
  Expected<std::vector<std::string>>
  implementations(const BindingApplication &app) const override {
    if (app.contract == "fixed_vector.from_vector")
      return std::vector<std::string>{"blst/resident/fixed_vector.from_vector",
                                      "plonky3/fixed_vector.from_vector"};
    if (app.contract == "field_array.from_vector")
      return std::vector<std::string>{"arkworks/field_array.from_vector",
                                      "blst/resident/field_array.from_vector"};
    return installedCandidates().implementations(app);
  }
  std::vector<BindingApplication>
  conversions(const BoundType &from, const BoundType &to) const override {
    if (!conversionsAvailable)
      return {};
    return installedCandidates().conversions(from, to);
  }
};
struct LayoutFixture {
  MLIRContext &context;
  Block variables;
  mathematical::RealizationWork account;
  mathematical::NumericalSelection work{&account};
  AggregateLayouts layouts{work, [](ArrayRef<size_t>) {
                             require(false, "unexpected exact layout conflict");
                           }};
  explicit LayoutFixture(MLIRContext &context) : context(context) {}
  AggregateLayouts::Id variable(StringRef logical = "field:bls12-381.fr") {
    auto type = decodeBoundType(&context, take(parseBoundType(logical, false)));
    return take(
        layouts.get(variables.addArgument(type, UnknownLoc::get(&context))));
  }
};
} // namespace
int main(int argc, char **argv) {
  if (argc != 1) {
    if (argc != 3 || StringRef(argv[1]) != "--emit") {
      errs() << "usage: aggregate-layouts [--emit DIRECTORY]\n";
      return 2;
    }
    emitDirectory = argv[2];
    if (auto error = llvm::sys::fs::create_directories(emitDirectory)) {
      errs() << "cannot create artifact directory: " << error.message() << '\n';
      return 2;
    }
  }
  llvm::sys::PrintStackTraceOnErrorSignal("aggregate-layouts");
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  const std::string scalar = "field:bls12-381.fr@blst/fr";
  const std::string sequence =
      "sequence<field:bls12-381.fr>@logical.sequence/0[blst/fr]";
  const std::string nested = "sequence<sequence<field:bls12-381.fr>>@logical."
                             "sequence/0[logical.sequence/0[blst/fr]]";
  for (bool nestedJoins : {false, true})
    cases.run(nestedJoins
                  ? "nested scalar joins ignore stopped arms"
                  : "512 sequential scalar joins retain resident results",
              [&] {
                unsigned count = nestedJoins ? 16 : 512;
                auto module = take(executableFixture(
                    scalarJoinSource(count, nestedJoins), context));
                mathematical::RealizationWork work;
                PhysicalPlanOptions options;
                options.numericalWork = &work;
                auto plan = take(proposePhysical(*module, installedCandidates(),
                                                 {}, options));
                for (unsigned i = 0; i < count; ++i)
                  require(take(encodeBoundType(
                                   at(plan, *module, "join" + std::to_string(i))
                                       .outputs[0],
                                   true))
                                  .spelling() == scalar,
                          "unanimous scalar yields lost their representation");
                publish(*module, take(validatePhysical(*module, plan)));
                outs() << count << (nestedJoins ? " nested" : " sequential")
                       << " joins: " << 1000000 - work.selectionBookkeeping
                       << " selection bookkeeping units\n";
              });
  for (bool reverseDefinitions : {false, true})
    cases.run(
        reverseDefinitions ? "reverse join and packing dependency chain"
                           : "forward join and packing dependency chain",
        [&] {
          LayoutFixture fixture(context);
          auto &layouts = fixture.layouts;
          auto resident = fixture.variable();
          accept(layouts.pin(resident, take(parseBoundType(scalar, true)), 0));
          SmallVector<AggregateLayouts::Id> results, packed{resident};
          for (unsigned i = 0; i < 512; ++i) {
            results.push_back(fixture.variable());
            packed.push_back(fixture.variable());
            accept(layouts.pack(results.back(), packed.back(), false));
          }
          for (unsigned i = 0; i < results.size(); ++i) {
            auto index = reverseDefinitions ? results.size() - i - 1 : i;
            accept(
                layouts.join(results[index], {packed[index], packed[index]}));
          }
          accept(layouts.solve());
          for (auto result : packed)
            require(take(layouts.physical(result)).spelling() == scalar,
                    "join/packing dependency retained a provisional default");
          require(1000000 - fixture.account.selectionBookkeeping < 100000,
                  "linear dependency chain repeatedly rescanned the graph");
          outs() << "512 " << (reverseDefinitions ? "reverse" : "forward")
                 << " join/packing dependencies: "
                 << 1000000 - fixture.account.selectionBookkeeping
                 << " selection bookkeeping units\n";
        });
  cases.run("wide unanimous joins count each dependent yield once", [&] {
    LayoutFixture fixture(context);
    auto &layouts = fixture.layouts;
    auto resident = fixture.variable();
    accept(layouts.pin(resident, take(parseBoundType(scalar, true)), 0));
    SmallVector<AggregateLayouts::Id> sources;
    for (unsigned i = 0; i < 512; ++i)
      sources.push_back(fixture.variable());
    auto unanimous = fixture.variable(), mixed = fixture.variable();
    accept(layouts.join(unanimous, sources));
    auto ordinary = fixture.variable();
    auto native = take(defaultRepresentation(
        take(parseBoundType("field:bls12-381.fr", false))));
    accept(layouts.pin(ordinary, native, 1));
    auto mixedSources = sources;
    mixedSources.push_back(ordinary);
    accept(layouts.join(mixed, std::move(mixedSources)));
    for (auto source : sources)
      accept(layouts.join(source, {resident, resident}));
    accept(layouts.solve());
    require(take(layouts.physical(unanimous)).spelling() == scalar,
            "wide join lost unanimous resident evidence");
    require(take(layouts.physical(mixed)) == native,
            "mixed live yields did not select the default");
    require(1000000 - fixture.account.selectionBookkeeping < 100000,
            "wide joins repeatedly rescanned all live yields");
  });
  for (bool residentFirst : {false, true})
    for (bool reverseEdges : {false, true})
      cases.run(
          "competing packing sources preserve id priority " +
              std::to_string(residentFirst) + "/" +
              std::to_string(reverseEdges),
          [&] {
            LayoutFixture fixture(context);
            auto &layouts = fixture.layouts;
            auto first = fixture.variable(), second = fixture.variable();
            auto target = fixture.variable();
            auto ordinary = take(defaultRepresentation(
                take(parseBoundType("field:bls12-381.fr", false))));
            auto resident = take(parseBoundType(scalar, true));
            accept(layouts.pin(first, residentFirst ? resident : ordinary, 0));
            accept(layouts.pin(second, residentFirst ? ordinary : resident, 1));
            accept(layouts.pack(reverseEdges ? second : first, target, false));
            accept(layouts.pack(reverseEdges ? first : second, target, false));
            accept(layouts.solve());
            require(take(layouts.physical(target)) ==
                        (residentFirst ? resident : ordinary),
                    "edge order changed source-id preference priority");
            auto pinned = residentFirst ? ordinary : resident;
            accept(layouts.pin(target, pinned, 2));
            accept(layouts.solve());
            require(take(layouts.physical(target)) == pinned,
                    "packing preferences overrode an exact pin");
          });
  cases.run(
      "new equality refreshes cached aggregate and packing evidence", [&] {
        LayoutFixture fixture(context);
        auto &layouts = fixture.layouts;
        auto source = fixture.variable();
        auto container = fixture.variable("sequence<field:bls12-381.fr>");
        auto child = layouts.child(container, 0);
        accept(layouts.pack(source, child, false));
        accept(layouts.solve());
        require(take(layouts.physical(container)).spelling() ==
                    "sequence<field:bls12-381.fr>@logical.sequence/0",
                "unseeded aggregate did not retain its default");
        auto resident = fixture.variable();
        accept(layouts.pin(resident, take(parseBoundType(scalar, true)), 0));
        accept(layouts.equate(source, resident));
        accept(layouts.solve());
        require(take(layouts.physical(container)).spelling() == sequence,
                "new equality retained a cached physical child or stale "
                "provenance");
      });
  cases.run("scalar equalities cannot merge distinct join definitions", [&] {
    LayoutFixture fixture(context);
    auto &layouts = fixture.layouts;
    auto resident = fixture.variable(), ordinary = fixture.variable();
    accept(layouts.pin(resident, take(parseBoundType(scalar, true)), 0));
    accept(layouts.pin(ordinary,
                       take(defaultRepresentation(
                           take(parseBoundType("field:bls12-381.fr", false)))),
                       1));
    auto left = fixture.variable(), right = fixture.variable();
    accept(layouts.join(left, {resident, resident}));
    accept(layouts.join(right, {ordinary, ordinary}));
    accept(layouts.solve());
    accept(layouts.equate(left, right));
    require(namesIdentifier(toString(layouts.solve()),
                            "binding-operation-signature"),
            "merged scalar definitions bypassed the solver precondition");
  });
  cases.run(
      "packing cycles refresh changed definitions and physical children", [&] {
        LayoutFixture fixture(context);
        auto &layouts = fixture.layouts;
        auto resident = fixture.variable();
        auto ordinary = take(defaultRepresentation(
            take(parseBoundType("field:bls12-381.fr", false))));
        accept(layouts.pin(resident, take(parseBoundType(scalar, true)), 0));
        auto joined = fixture.variable();
        auto left = fixture.variable(), right = fixture.variable();
        auto derived = fixture.variable();
        auto container = fixture.variable("sequence<field:bls12-381.fr>");
        accept(layouts.join(joined, {resident, resident}));
        accept(layouts.pack(joined, left, false));
        accept(layouts.pack(left, right, false));
        accept(layouts.pack(right, left, false));
        accept(layouts.join(derived, {right, resident}));
        accept(layouts.pack(derived, layouts.child(container, 0), false));
        accept(layouts.solve());
        require(take(layouts.physical(container)).spelling() == sequence,
                "packing cycle lost unanimous evidence");
        auto before = fixture.account.selectionBookkeeping;
        accept(layouts.pin(joined, ordinary, 1));
        accept(layouts.solve());
        require(take(layouts.physical(left)) == ordinary &&
                    take(layouts.physical(right)) == ordinary &&
                    take(layouts.physical(derived)) == ordinary,
                "changed definition left stale evidence in a cycle or "
                "dependent join");
        require(take(layouts.physical(container)).spelling() ==
                    "sequence<field:bls12-381.fr>@logical.sequence/0",
                "subsequent solve reused a cached physical child");
        require(fixture.account.selectionBookkeeping < before,
                "subsequent solve replenished shared work");
        fixture.account.selectionBookkeeping = 1;
        require(
            namesIdentifier(toString(layouts.solve()), "finite-analysis-limit"),
            "solver ignored the remaining shared allowance");
      });
  cases.run(
      "cyclic joins retain defaults until every live yield has evidence", [&] {
        LayoutFixture fixture(context);
        auto &layouts = fixture.layouts;
        auto resident = fixture.variable();
        accept(layouts.pin(resident, take(parseBoundType(scalar, true)), 0));
        auto first = fixture.variable(), second = fixture.variable();
        auto packedFirst = fixture.variable(),
             packedSecond = fixture.variable();
        accept(layouts.pack(first, packedFirst, false));
        accept(layouts.pack(second, packedSecond, false));
        accept(layouts.join(first, {packedSecond, resident}));
        accept(layouts.join(second, {packedFirst, resident}));
        accept(layouts.solve());
        auto ordinary = take(defaultRepresentation(
            take(parseBoundType("field:bls12-381.fr", false))));
        require(take(layouts.physical(first)) == ordinary &&
                    take(layouts.physical(second)) == ordinary,
                "cyclic yields invented unanimous resident evidence");
        accept(layouts.pack(resident, packedFirst, false));
        accept(layouts.solve());
        require(take(layouts.physical(first)).spelling() == scalar &&
                    take(layouts.physical(second)).spelling() == scalar,
                "new lower-id packing evidence did not resolve the join cycle");
      });
  for (bool seeded : {false, true})
    cases.run(
        seeded ? "seeded scalar join and loop packing cycle"
               : "unseeded scalar join and loop packing cycle",
        [&] {
          auto module =
              take(executableFixture(cyclicSequenceSource(seeded), context));
          auto plan = take(proposePhysical(*module, installedCandidates()));
          auto expected =
              seeded ? sequence
                     : "sequence<field:bls12-381.fr>@logical.sequence/0";
          require(
              take(encodeBoundType(at(plan, *module, "loop").outputs[0], true))
                          .spelling() == expected &&
                  take(encodeBoundType(at(plan, *module, "empty").outputs[0],
                                       true))
                          .spelling() == expected,
              "cyclic packing disagrees with loop initialization");
          publish(*module, take(validatePhysical(*module, plan)));
        });
  for (StringRef control :
       {"straight", "scalar", "branch", "stop", "capture", "match", "loop"})
    cases.run("unseeded aggregate inference through " + control, [&] {
      auto module =
          take(executableFixture(inferredSequenceSource(control), context));
      auto plan = take(proposePhysical(*module, installedCandidates()));
      require(take(encodeBoundType(at(plan, *module, "length").inputs[0], true))
                      .spelling() == sequence,
              "consumer retained a provisional default");
      require(take(encodeBoundType(at(plan, *module, "empty").outputs[0], true))
                      .spelling() == sequence,
              "construction and control equations disagree");
      for (const auto &decision : plan.operations)
        for (const auto &conversion : decision.conversions)
          require(take(encodeBoundType(conversion.from, true)).kind == "field",
                  "inference inserted an aggregate conversion");
      if (control == "branch" || control == "stop") {
        auto forged = plan;
        at(forged, *module, "branch").blockArguments[0][0] = decodeBoundType(
            &context,
            take(parseBoundType(
                "sequence<field:bls12-381.fr>@logical.sequence/0", true)));
        refuses(validatePhysical(*module, forged),
                "binding-operation-signature");
      }
      publish(*module, take(validatePhysical(*module, plan)));
    });
  cases.run("settled scalar joins do not require packing conversions", [&] {
    auto module =
        take(executableFixture(inferredSequenceSource("scalar"), context));
    PhysicalPlanOptions options;
    abi(options, *module, false, 0, scalar);
    DenseCandidates catalog;
    catalog.conversionsAvailable = false;
    auto plan = take(proposePhysical(*module, catalog, {}, options));
    require(llvm::all_of(plan.operations,
                         [](const OperationDecision &decision) {
                           return decision.conversions.empty();
                         }),
            "packing retained a provisional scalar join layout");
    publish(*module, take(validatePhysical(*module, plan, catalog)));
  });
  for (StringRef control : {"branch", "stop"})
    cases.run(
        "explicit aggregate layout keeps conversions reached in " + control,
        [&] {
          auto module =
              take(executableFixture(inferredSequenceSource(control), context));
          PhysicalPlanOptions options;
          const std::string ordinary =
              "sequence<field:bls12-381.fr>@logical.sequence/0";
          options.valueLayouts.push_back({"Work", "branch", 0, ordinary});
          auto plan = take(
              proposePhysical(*module, installedCandidates(), {}, options));
          require(take(encodeBoundType(at(plan, *module, "branch").outputs[0],
                                       true))
                          .spelling() == ordinary,
                  "leaf preference overrode an explicit layout");
          auto &append = at(plan, *module, "append_left");
          require(append.conversions.size() == 1 &&
                      append.conversions[0].operand == 1,
                  "explicit layout did not convert the reached leaf");
          auto forged = plan;
          at(forged, *module, "append_left").conversions[0].operand = 0;
          refuses(validatePhysical(*module, forged), "binding-no-conversion");
          accept(materializePhysical(*module,
                                     take(validatePhysical(*module, plan))));
          module->walk([&](local::LocalIfOp branch) {
            bool guard = false, converted = false;
            for (auto &operation : branch->getRegion(0).front())
              if (auto apply = dyn_cast<plan::ApplyOp>(operation)) {
                guard |= apply.getSite() == "guard";
                if (apply.getSite().starts_with("layout_")) {
                  require(guard, "leaf conversion moved before the guard");
                  converted = true;
                }
              }
            require(converted, "leaf conversion escaped its branch");
            if (control == "stop")
              require(isa<local::StopOp>(branch->getRegion(1).front().front()),
                      "conversion was inserted in the stopped arm");
          });
          require(succeeded(verify(*module)),
                  "explicit control materialization");
          take(program::decode(
              program::encode(take(readExecutionModel(*module)))));
        });
  cases.run("default aggregate entry ports remain exact during packing", [&] {
    auto source = R"(!F = !algebra.field<"bls12-381.fr">
!S = !data.sequence<!algebra.field<"bls12-381.fr">>
)" + mathematicalFixture(R"(
"local.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation="blst/resident/field.add"} : ()->()
"local.binding"() {sym_name="append",contract="sequence.append",arguments=["field:bls12-381.fr"],implementation="native/sequence.append"} : ()->()
"local.binding"() {sym_name="length",contract="sequence.length",arguments=["field:bls12-381.fr"],implementation="native/sequence.length"} : ()->()
)",
                         "%x:!F,%s:!S", "%x,%s", "!F,!S", "ui64", R"(
%v = "algebra.exec.field_add"(%x,%x) {binding=@add,site="add",parameters=[]} : (!F,!F)->!F
%values = "data.exec.sequence_append"(%s,%v) {binding=@append,site="append",parameters=[]} : (!S,!F)->!S
%n = "data.exec.sequence_length"(%values) {binding=@length,site="length",parameters=[]} : (!S)->ui64
local.return %n : ui64
)",
                         2);
    auto module = take(executableFixture(source, context));
    auto plan = take(proposePhysical(*module, installedCandidates()));
    auto &append = at(plan, *module, "append");
    require(append.conversions.size() == 1 &&
                append.conversions[0].operand == 1,
            "entry layout did not take precedence over leaf preference");
    require(take(encodeBoundType(append.outputs[0], true)).spelling() ==
                "sequence<field:bls12-381.fr>@logical.sequence/0",
            "default entry layout changed");
    publish(*module, take(validatePhysical(*module, plan)));
  });
  cases.run("variant payload constraints solve independently", [&] {
    auto variant =
        *encodeVariant({"IndependentPayloads",
                        {{"left", {"sequence<field:bls12-381.fr>"}},
                         {"right", {"sequence<field:bls12-381.fr>"}}}});
    auto source = "!Tag = !local.variant<\"" + variant + "\">\n" + R"(
!F = !algebra.field<"bls12-381.fr">
!S = !data.sequence<!algebra.field<"bls12-381.fr">>
)" +
                  mathematicalFixture(R"(
"local.binding"() {sym_name="empty",contract="sequence.empty",arguments=["field:bls12-381.fr"],implementation="native/sequence.empty"} : ()->()
"local.binding"() {sym_name="length",contract="sequence.length",arguments=["field:bls12-381.fr"],implementation="native/sequence.length"} : ()->()
"local.binding"() {sym_name="append",contract="sequence.append",arguments=["field:bls12-381.fr"],implementation="native/sequence.append"} : ()->()
)",
                                      "%x:!F", "%x", "!F", "ui64", R"(
%s = "data.exec.sequence_empty"() {binding=@empty,site="empty",parameters=[]} : ()->!S
%tag = "local.variant_inject"(%s) {alternative="left",site="tag"} : (!S)->!Tag
%n = "local.match"(%tag,%x) ({^left(%payload:!S,%element:!F):
  %values = "data.exec.sequence_append"(%payload,%element) {binding=@append,site="left_append",parameters=[]} : (!S,!F)->!S
  %n = "data.exec.sequence_length"(%values) {binding=@length,site="left_length",parameters=[]} : (!S)->ui64
  "local.yield"(%n) : (ui64)->()
}, {^right(%payload:!S,%element:!F):
  %values = "data.exec.sequence_append"(%payload,%element) {binding=@append,site="right_append",parameters=[]} : (!S,!F)->!S
  %n = "data.exec.sequence_length"(%values) {binding=@length,site="right_length",parameters=[]} : (!S)->ui64
  "local.yield"(%n) : (ui64)->()
}) {alternatives=["left","right"],site="match"} : (!Tag,!F)->ui64
local.return %n : ui64
)",
                                      1);
    auto module = take(executableFixture(source, context));
    PhysicalPlanOptions options;
    options.valueLayouts.push_back({"Work", "left_append", 0, sequence});
    options.valueLayouts.push_back(
        {"Work", "right_append", 0,
         "sequence<field:bls12-381.fr>@logical.sequence/0"});
    auto plan =
        take(proposePhysical(*module, installedCandidates(), {}, options));
    auto tag = take(encodeBoundType(at(plan, *module, "tag").outputs[0], true));
    require((*tag.physicalChildren)[0].spelling() == sequence &&
                (*tag.physicalChildren)[1].spelling() ==
                    "sequence<field:bls12-381.fr>@logical.sequence/0",
            "constraining one payload fixed its sibling");
    publish(*module, take(validatePhysical(*module, plan)));
  });
  cases.run(
      "inapplicable family candidate advances before physical admission", [&] {
        auto source = R"(!V = !algebra.field_vector<"koala-bear">
!X = !algebra.fixed_vector<!algebra.field<"koala-bear">,2>
)" + mathematicalFixture(R"(
"local.binding"() {sym_name="fixed",contract="fixed_vector.from_vector",arguments=["koala-bear","2"],implementation=""} : ()->()
)",
                         "%v:!V", "%v", "!V", "!X", R"(
%out = "algebra.exec.fixed_vector_from_vector"(%v) {binding=@fixed,site="fixed",parameters=[]} : (!V)->!X
local.return %out : !X
)",
                         1);
        DenseCandidates catalog;
        auto module = take(executableFixture(source, context));
        auto plan = take(proposePhysical(*module, catalog));
        require(plan.bindings[*at(plan, *module, "fixed").binding]
                        .binding.application.implementation ==
                    "plonky3/fixed_vector.from_vector",
                "inapplicable first candidate prevented fallback");
        publish(*module, take(validatePhysical(*module, plan, catalog)));
        auto pinned = take(executableFixture(source, context));
        refuses(proposePhysical(
                    *pinned, catalog,
                    {{"fixed", "blst/resident/fixed_vector.from_vector"}}),
                "binding-implementation");
        refuses(
            selectImplementation({"fixed_vector.from_vector",
                                  {"koala-bear", "2"},
                                  "blst/resident/fixed_vector.from_vector"}),
            "binding-implementation");
        refuses(
            selectImplementation({"fixed_vector.from_vector",
                                  {"koala-bear", "bad"},
                                  "blst/resident/fixed_vector.from_vector"}),
            "binding-static-identity");
      });
  cases.run(
      "aggregate layout conflict advances its automatic family owner", [&] {
        auto source = R"(!V = !algebra.field_vector<"bls12-381.fr">
!A = !algebra.field_array<"bls12-381.fr",2>
)" + mathematicalFixture(R"(
"local.binding"() {sym_name="array",contract="field_array.from_vector",arguments=["bls12-381.fr","2"],implementation=""} : ()->()
)",
                         "%v:!V", "%v", "!V", "!A", R"(
%out = "algebra.exec.field_array_from_vector"(%v) {binding=@array,site="array",parameters=[]} : (!V)->!A
local.return %out : !A
)",
                         1);
        DenseCandidates catalog;
        auto module = take(executableFixture(source, context));
        PhysicalPlanOptions options;
        abi(options, *module, false, 0, "vector:bls12-381.fr@blst/fr");
        abi(options, *module, true, 0,
            "field_array<bls12-381.fr,2>@blst/field-array[blst/fr]");
        auto plan = take(proposePhysical(*module, catalog, {}, options));
        require(plan.bindings[*at(plan, *module, "array").binding]
                        .binding.application.implementation ==
                    "blst/resident/field_array.from_vector",
                "late layout failure did not advance its automatic owner");
        publish(*module, take(validatePhysical(*module, plan, catalog)));
        auto pinned = take(executableFixture(source, context));
        refuses(proposePhysical(*pinned, catalog,
                                {{"array", "arkworks/field_array.from_vector"}},
                                options),
                "binding-no-conversion");
      });
  for (unsigned declarations : {3u, 2049u, 4096u})
    cases.run(
        "default family declarations reuse origins at capacity " +
            Twine(declarations),
        [&] {
          std::string bindings = R"(
"local.binding"() {sym_name="length",contract="sequence.length",arguments=["field:bls12-381.fr"],implementation="native/sequence.length"} : ()->()
)";
          std::string body;
          for (unsigned i = 0; i + 1 < declarations; ++i) {
            auto suffix = std::to_string(i);
            bindings +=
                "\"local.binding\"() {sym_name=\"empty_" + suffix +
                "\",contract=\"sequence.empty\",arguments=[\"field:bls12-381."
                "fr\"],implementation=\"native/sequence.empty\"} : ()->()\n";
            body += "%s" + suffix +
                    " = \"data.exec.sequence_empty\"() {binding=@empty_" +
                    suffix + ",site=\"empty_" + suffix +
                    "\",parameters=[]} : ()->!S\n";
            body += "%n" + suffix + " = \"data.exec.sequence_length\"(%s" +
                    suffix + ") {binding=@length,site=\"length_" + suffix +
                    "\",parameters=[]} : (!S)->ui64\n";
          }
          body += "local.return %n" + std::to_string(declarations - 2) +
                  " : ui64\n";
          auto source = R"(!S = !data.sequence<!algebra.field<"bls12-381.fr">>
)" + mathematicalFixture(bindings, "", "", "", "ui64", body, 0);
          auto module = take(executableFixture(source, context));
          auto plan = take(proposePhysical(*module, installedCandidates()));
          require(plan.bindings.size() == declarations,
                  "default specialization duplicated its normalized origin");
          require(llvm::all_of(plan.bindings,
                               [](const BindingDecision &binding) {
                                 return binding.purpose ==
                                            BindingPurpose::Original &&
                                        !binding.origin &&
                                        binding.binding.application
                                                .physicalArguments.size() == 1;
                               }),
                  "default origin lost its complete application or provenance");
          auto forged = plan;
          while (forged.bindings.size() <= 4096)
            forged.bindings.push_back(plan.bindings.front());
          refuses(validatePhysical(*module, forged),
                  "binding-declaration-limit");
          if (declarations == 4096) {
            PhysicalPlanOptions selected;
            selected.valueLayouts.push_back({"Work", "empty_0", 0, sequence});
            refuses(
                proposePhysical(*module, installedCandidates(), {}, selected),
                "binding-declaration-limit");
          }
          publish(*module, take(validatePhysical(*module, plan)));
        });
  cases.run("complete canonical child layouts and erasure", [&] {
    for (const auto &spelling :
         {scalar, sequence, nested,
          std::string("field_array<bls12-381.fr,0>@blst/field-array[blst/fr]"),
          std::string("fixed_vector<field:bls12-381.fr,4>@blst/"
                      "fixed-vector[blst/fr]")}) {
      auto physical = take(parseBoundType(spelling, true));
      require(physical.spelling() == spelling, "canonical roundtrip");
      auto logical =
          take(parseBoundType(StringRef(spelling).split('@').first, false));
      require(erasePhysicalType(physical) == logical, "authoritative erasure");
      require(physical.arguments == logical.arguments,
              "physical metadata leaked into logical arguments");
      auto type = decodeBoundType(&context, physical);
      require(bool(type) && take(encodeBoundType(type, true)) == physical,
              "MLIR complete wrapper roundtrip");
      std::string printed;
      raw_string_ostream stream(printed);
      type.print(stream);
      require(parseType(printed, &context) == type,
              "MLIR complete child parser/printer roundtrip");
    }
    auto ordinary = take(parseBoundType(
        "sequence<field:bls12-381.fr>@logical.sequence/0", true));
    require(ordinary.physicalChildren && ordinary.physicalChildren->size() == 1,
            "elision lost stored default children");
  });
  cases.run(
      "canonical layout grammar refuses malformed and second spellings", [&] {
        for (const auto &spelling :
             {"sequence<field:bls12-381.fr>@logical.sequence/0[arkworks.fr/0]",
              "sequence<field:bls12-381.fr>@logical.sequence/0[]",
              "sequence<field:bls12-381.fr>@logical.sequence/0[blst/fr,blst/"
              "fr]",
              "sequence<field:bls12-381.fr>@logical.sequence/0[foreign/fr]",
              "field_array<bls12-381.fr,4>@arkworks.field-array/0[blst/fr]",
              "fixed_vector<field:bls12-381.fr,4>@blst/"
              "fixed-vector[arkworks.fr/0]",
              "field:bls12-381.fr@blst/fr[]"})
          refuses(parseBoundType(spelling, true), "binding-representation");
        auto schema =
            take(parseBoundType("sequence<field:bls12-381.fr>", false));
        refuses(
            physicalType(schema, "logical.sequence/0",
                         {take(parseBoundType(
                             "field:koala-bear@plonky3.koala-bear/0", true))}),
            "binding-representation");
        TypeParseBudget budget;
        budget.remaining = 2;
        refuses(parseBoundType(sequence, true, 0, &budget),
                "binding-type-limit");
        TypeParseBudget exact;
        exact.remaining = 4;
        take(parseBoundType(sequence, true, 0, &exact));
        require(exact.remaining == 0,
                "logical and layout nodes did not share one allowance");
        TypeParseBudget metadata;
        metadata.metadataRemaining = 0;
        refuses(parseBoundType(sequence, true, 0, &metadata),
                "binding-type-limit");
        refuses(
            parseBoundType(std::string(PhysicalSpellingBytes + 1, 'x'), true),
            "binding-type-limit");
      });
  cases.run("inactive variant children are identity and admission", [&] {
    auto spelling = *encodeVariant({"Complete",
                                    {{"none", {}},
                                     {"value", {"field:bls12-381.fr"}},
                                     {"unused", {"group:bls12-381.g2"}}}});
    auto schema = take(parseBoundType(spelling, false));
    auto physical = take(physicalType(
        schema, "logical.variant/0",
        {take(parseBoundType(scalar, true)),
         take(parseBoundType("group:bls12-381.g2@blst/g2", true))}));
    auto changed = take(physicalType(
        schema, "logical.variant/0",
        {take(parseBoundType(scalar, true)),
         take(parseBoundType("group:bls12-381.g2@arkworks.bls12-381-g2/0",
                             true))}));
    require(!(physical == changed),
            "inactive layout disappeared from equality");
    require(take(parseBoundType(physical.spelling(), true)) == physical,
            "variant roundtrip");
    refuses(parseBoundType(spelling + "@logical.variant/0[blst/fr,foreign/g2]",
                           true),
            "binding-representation");
    refuses(physicalType(schema, "logical.variant/0",
                         {take(parseBoundType(scalar, true))}),
            "binding-representation");
  });
  cases.run("implementation selection premises are descriptor data", [&] {
    auto ordinary =
        *installedImplementations().find("field.add", "arkworks/field.add");
    require(!ordinary.requiresExplicitSelection,
            "ordinary selection premise changed");
    ordinary.requiresExplicitSelection = true;
    auto catalog = take(ImplementationCatalog::create({ordinary}, {}));
    require(catalog.find("field.add", "arkworks/field.add")
                ->requiresExplicitSelection,
            "non-MSM descriptor lost its explicit premise");
    require(installedImplementations()
                .find("curve.msm", "blst/resident/curve.msm")
                ->requiresExplicitSelection,
            "resident MSM lost its explicit selection premise");
  });
  cases.run("trusted sequence and dense implementation families", [&] {
    auto append = take(resolveBinding({"sequence.append",
                                       {"field:bls12-381.fr"},
                                       "native/sequence.append",
                                       {sequence}},
                                      true));
    require(append.inputs[0].spelling() == sequence &&
                append.inputs[1].spelling() == scalar,
            "sequence family signature");
    for (const auto &kind : {"field_array", "fixed_vector"}) {
      std::string type =
          std::string(kind) == "field_array"
              ? "field_array<bls12-381.fr,4>@blst/field-array[blst/fr]"
              : "fixed_vector<field:bls12-381.fr,4>@blst/fixed-vector[blst/fr]";
      std::string contract = std::string(kind) + ".from_vector";
      auto operation = take(resolveBinding({contract,
                                            {"bls12-381.fr", "4"},
                                            "blst/resident/" + contract,
                                            {type}},
                                           true));
      require(operation.inputs[0].spelling() == "vector:bls12-381.fr@blst/fr" &&
                  operation.outputs[0].spelling() == type,
              "dense family signature");
    }
    refuses(resolveBinding({"sequence.append",
                            {"field:bls12-381.fr"},
                            "native/sequence.append",
                            {nested}},
                           true),
            "binding-representation");
    refuses(resolveBinding(
                {"representation.convert",
                 {"sequence<field:bls12-381.fr>"},
                 "native/representation.convert",
                 {"sequence<field:bls12-381.fr>@logical.sequence/0", sequence}},
                true),
            "binding-conversion");
  });
  cases.run(
      "compiled selected nested sequence and checked specialization", [&] {
        auto module = take(executableFixture(sequenceSource(), context));
        PhysicalPlanOptions options;
        abi(options, *module, false, 0, scalar);
        abi(options, *module, true, 0, nested);
        auto plan =
            take(proposePhysical(*module, installedCandidates(), {}, options));
        require(at(plan, *module, "append").conversions.empty() &&
                    at(plan, *module, "pack").conversions.empty(),
                "selected packing inserted conversions");
        require(
            take(encodeBoundType(at(plan, *module, "empty").outputs[0], true))
                    .spelling() == sequence,
            "empty sequence constraint lost");
        bool specialization = false;
        for (const auto &binding : plan.bindings)
          if (binding.purpose == BindingPurpose::Specialization) {
            specialization = true;
            require(binding.origin.has_value() && binding.fixed,
                    "specialization lost origin or fixed choice");
          }
        require(specialization, "no exact specialization recorded");
        auto forged = plan;
        for (auto &binding : forged.bindings)
          if (binding.purpose == BindingPurpose::Specialization) {
            binding.origin.reset();
            break;
          }
        refuses(validatePhysical(*module, forged),
                "binding-selection-conflict");
        publish(*module, take(validatePhysical(*module, plan)), "sequence");
      });
  cases.run("layout seeds are checked and stale source refuses", [&] {
    auto module = take(executableFixture(sequenceSource(), context));
    PhysicalPlanOptions options;
    abi(options, *module, false, 0, scalar);
    abi(options, *module, true, 0, nested);
    options.valueLayouts.push_back({"Work", "empty", 0, sequence});
    auto plan =
        take(proposePhysical(*module, installedCandidates(), {}, options));
    auto wrong = plan;
    at(wrong, *module, "empty").outputs[0] = decodeBoundType(
        &context,
        take(parseBoundType("sequence<field:bls12-381.fr>@logical.sequence/0",
                            true)));
    auto invalid = validatePhysical(*module, wrong);
    require(!invalid, "forged layout seed admitted");
    consumeError(invalid.takeError());
    (*module)->setAttr("changed", UnitAttr::get(&context));
    refuses(validatePhysical(*module, plan), "binding-stale-selection");
  });
  cases.run(
      "selected variant includes inactive children without defaults", [&] {
        auto variant = *encodeVariant(
            {"SelectedChoice",
             {{"none", {}},
              {"some", {"sequence<field:bls12-381.fr>"}},
              {"unused", {"fixed_vector<field:bls12-381.fr,2>"}}}});
        auto schema = take(parseBoundType(variant, false));
        auto full = take(
            physicalType(schema, "logical.variant/0",
                         {take(parseBoundType(sequence, true)),
                          take(parseBoundType("fixed_vector<field:bls12-381.fr,"
                                              "2>@blst/fixed-vector[blst/fr]",
                                              true))}));
        auto source = "!Tag = !local.variant<\"" + variant + "\">\n" +
                      R"(!F = !algebra.field<"bls12-381.fr">
!S = !data.sequence<!algebra.field<"bls12-381.fr">>
!X = !algebra.fixed_vector<!algebra.field<"bls12-381.fr">,2>
)" +
                      mathematicalFixture(R"(
"local.binding"() {sym_name="empty",contract="sequence.empty",arguments=["field:bls12-381.fr"],implementation="native/sequence.empty"} : ()->()
"local.binding"() {sym_name="append",contract="sequence.append",arguments=["field:bls12-381.fr"],implementation="native/sequence.append"} : ()->()
)",
                                          "%x:!F", "%x", "!F", "!S", R"(
%s = "data.exec.sequence_empty"() {binding=@empty,site="empty",parameters=[]} : ()->!S
%values = "data.exec.sequence_append"(%s,%x) {binding=@append,site="append",parameters=[]} : (!S,!F)->!S
%tag = "local.variant_inject"(%values) {alternative="some",site="tag"} : (!S)->!Tag
%out = "local.match"(%tag,%values) ({^none(%capture:!S):
  "local.yield"(%capture) : (!S)->()
}, {^some(%payload:!S,%capture:!S):
  "local.yield"(%payload) : (!S)->()
}, {^unused(%inactive:!X,%capture:!S):
  "local.yield"(%capture) : (!S)->()
}) {alternatives=["none","some","unused"],site="match"} : (!Tag,!S)->!S
local.return %out : !S
)",
                                          1);
        auto module = take(executableFixture(source, context));
        PhysicalPlanOptions options;
        abi(options, *module, false, 0, scalar);
        abi(options, *module, true, 0, sequence);
        options.valueLayouts.push_back({"Work", "tag", 0, full.spelling()});
        auto plan =
            take(proposePhysical(*module, installedCandidates(), {}, options));
        require(take(encodeBoundType(
                         at(plan, *module, "match").blockArguments[2][0], true))
                        .representation == "blst/fixed-vector",
                "inactive selected payload lost");
        require(at(plan, *module, "tag").conversions.empty(),
                "selected variant packing converted aggregate");
        auto forged = plan;
        at(forged, *module, "match").blockArguments[1][0] = decodeBoundType(
            &context,
            take(parseBoundType(
                "sequence<field:bls12-381.fr>@logical.sequence/0", true)));
        refuses(validatePhysical(*module, forged),
                "binding-operation-signature");
        publish(*module, take(validatePhysical(*module, plan)), "variant");
      });
  cases.run(
      "aggregate branch and loop equations keep leaf conversions reached", [&] {
        auto source = R"(!F = !algebra.field<"bls12-381.fr">
!S = !data.sequence<!algebra.field<"bls12-381.fr">>
)" + mathematicalFixture(R"(
"local.binding"() {sym_name="empty",contract="sequence.empty",arguments=["field:bls12-381.fr"],implementation="native/sequence.empty"} : ()->()
"local.binding"() {sym_name="append",contract="sequence.append",arguments=["field:bls12-381.fr"],implementation="native/sequence.append"} : ()->()
"local.binding"() {sym_name="guard",contract="control.require",arguments=[],implementation=""} : ()->()
)",
                         "%x:!F,%c:i1,%lo:ui64,%hi:ui64", "%x,%c,%lo,%hi",
                         "!F,i1,ui64,ui64", "!S", R"(
%s = "data.exec.sequence_empty"() {binding=@empty,site="empty",parameters=[]} : ()->!S
%joined = "local.if"(%c,%s,%x,%c) ({^left(%values:!S,%element:!F,%allowed:i1):
  "local.exec.require"(%allowed) {binding=@guard,site="branch_guard",parameters=[]} : (i1)->()
  %next = "data.exec.sequence_append"(%values,%element) {binding=@append,site="branch_append",parameters=[]} : (!S,!F)->!S
  "local.yield"(%next) : (!S)->()
}, {^right(%values:!S,%element:!F,%allowed:i1):
  "local.yield"(%values) : (!S)->()
}) {site="branch"} : (i1,!S,!F,i1)->!S
%out = "local.for"(%lo,%hi,%joined,%x,%c) ({^body(%i:ui64,%state:!S,%element:!F,%allowed:i1):
  "local.exec.require"(%allowed) {binding=@guard,site="loop_guard",parameters=[]} : (i1)->()
  %next = "data.exec.sequence_append"(%state,%element) {binding=@append,site="loop_append",parameters=[]} : (!S,!F)->!S
  "local.yield"(%next,%element,%allowed) : (!S,!F,i1)->()
}) {site="loop"} : (ui64,ui64,!S,!F,i1)->!S
local.return %out : !S
)",
                         4);
        auto module = take(executableFixture(source, context));
        PhysicalPlanOptions options;
        abi(options, *module, true, 0, sequence);
        auto plan =
            take(proposePhysical(*module, installedCandidates(), {}, options));
        require(at(plan, *module, "branch").conversions.empty() &&
                    at(plan, *module, "loop").conversions.empty(),
                "aggregate conversion at control boundary");
        require(at(plan, *module, "branch_append").conversions.size() == 1 &&
                    at(plan, *module, "loop_append").conversions.size() == 1,
                "leaf conversion missing");
        require(at(plan, *module, "branch_append").conversions[0].operand == 1,
                "converted aggregate operand");
        auto forged = plan;
        at(forged, *module, "loop").blockArguments[0][1] = decodeBoundType(
            &context,
            take(parseBoundType(
                "sequence<field:bls12-381.fr>@logical.sequence/0", true)));
        refuses(validatePhysical(*module, forged),
                "binding-operation-signature");
        auto checked = take(validatePhysical(*module, plan));
        accept(materializePhysical(*module, checked));
        module->walk([&](local::LocalForOp loop) {
          bool guard = false, conversion = false;
          for (auto &operation : loop.getBody().front())
            if (auto apply = dyn_cast<plan::ApplyOp>(operation)) {
              if (apply.getSite() == "loop_guard")
                guard = true;
              if (apply.getSite().starts_with("layout_")) {
                require(guard, "conversion moved before guard");
                conversion = true;
              }
            }
          require(conversion, "loop conversion was not kept inside loop");
        });
        require(succeeded(verify(*module)), "aggregate controls publication");
        auto encoded = program::encode(take(readExecutionModel(*module)));
        take(program::decode(encoded));
        emitArtifact(encoded, "control");
      });
  cases.run("unavailable aggregate conversion refuses", [&] {
    auto source = R"(!F = !algebra.field<"bls12-381.fr">
!S = !data.sequence<!algebra.field<"bls12-381.fr">>
)" + mathematicalFixture("", "%s:!S", "%s", "!S", "!S", "local.return %s : !S",
                         1);
    auto module = take(executableFixture(source, context));
    PhysicalPlanOptions options;
    abi(options, *module, true, 0, sequence);
    refuses(proposePhysical(*module, installedCandidates(), {}, options),
            "binding-no-conversion");
  });
  cases.run(
      "nested access propagates selected layouts without installed defaults",
      [&] {
        auto source = R"(!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
!X = !algebra.fixed_vector<!algebra.field<"bls12-381.fr">,2>
!S = !data.sequence<!algebra.fixed_vector<!algebra.field<"bls12-381.fr">,2>>
)" + mathematicalFixture(R"(
"local.binding"() {sym_name="fixed",contract="fixed_vector.from_vector",arguments=["bls12-381.fr","2"],implementation="blst/resident/fixed_vector.from_vector"} : ()->()
"local.binding"() {sym_name="empty",contract="sequence.empty",arguments=["fixed_vector<field:bls12-381.fr,2>"],implementation="native/sequence.empty"} : ()->()
"local.binding"() {sym_name="append",contract="sequence.append",arguments=["fixed_vector<field:bls12-381.fr,2>"],implementation="native/sequence.append"} : ()->()
"local.binding"() {sym_name="at",contract="sequence.at",arguments=["fixed_vector<field:bls12-381.fr,2>"],implementation="native/sequence.at"} : ()->()
)",
                         "%v:!V,%i:ui64", "%v,%i", "!V,ui64", "!X", R"(
%s = "data.exec.sequence_empty"() {binding=@empty,site="empty",parameters=[]} : ()->!S
%x = "algebra.exec.fixed_vector_from_vector"(%v) {binding=@fixed,site="fixed",parameters=[]} : (!V)->!X
%values = "data.exec.sequence_append"(%s,%x) {binding=@append,site="append",parameters=[]} : (!S,!X)->!S
%out = "data.exec.sequence_at"(%values,%i) {binding=@at,site="at",parameters=[]} : (!S,ui64)->!X
local.return %out : !X
)",
                         2);
        auto module = take(executableFixture(source, context));
        PhysicalPlanOptions options;
        abi(options, *module, false, 0, "vector:bls12-381.fr@blst/fr");
        abi(options, *module, true, 0,
            "fixed_vector<field:bls12-381.fr,2>@blst/fixed-vector[blst/fr]");
        auto plan =
            take(proposePhysical(*module, installedCandidates(), {}, options));
        require(at(plan, *module, "empty").outputs[0] ==
                    at(plan, *module, "at").inputs[0],
                "no-default sequence access lost selected storage");
        publish(*module, take(validatePhysical(*module, plan)));
      });
  cases.run(
      "one fixed source binding retains distinct checked specializations", [&] {
        auto source = replaceText(sequenceSource(), "%s =", R"(
%unused = "data.exec.sequence_empty"() {binding=@empty,site="ordinary_empty",parameters=[]} : ()->!S
%s =)");
        auto module = take(executableFixture(source, context));
        PhysicalPlanOptions options;
        abi(options, *module, false, 0, scalar);
        abi(options, *module, true, 0, nested);
        auto plan =
            take(proposePhysical(*module, installedCandidates(), {}, options));
        const auto &ordinary = at(plan, *module, "ordinary_empty");
        const auto &selected = at(plan, *module, "empty");
        require(ordinary.binding != selected.binding,
                "distinct specializations collapsed");
        const auto &a = plan.bindings[*ordinary.binding];
        const auto &b = plan.bindings[*selected.binding];
        require(a.purpose == BindingPurpose::Original &&
                    b.purpose == BindingPurpose::Specialization &&
                    b.origin == ordinary.binding && a.fixed && b.fixed,
                "source binding origin or fixed implementation lost");
        require(a.binding.application.physicalArguments !=
                    b.binding.application.physicalArguments,
                "full physical parameters collapsed");
        auto forged = plan;
        forged.bindings[*selected.binding].binding.application.implementation =
            "native/sequence.at";
        // Consume the independent refusal without relying on which admission
        // layer detects the deliberately inconsistent contract/implementation
        // pair first.
        auto invalid = validatePhysical(*module, forged);
        require(!invalid, "forged family implementation admitted");
        consumeError(invalid.takeError());
        publish(*module, take(validatePhysical(*module, plan)));
      });
  cases.run("compiled resident dense arrays and fixed vectors", [&] {
    auto source = R"(!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
!A = !algebra.field_array<"bls12-381.fr",4>
!X = !algebra.fixed_vector<!algebra.field<"bls12-381.fr">,4>
)" + mathematicalFixture(R"(
"local.binding"() {sym_name="array",contract="field_array.from_vector",arguments=["bls12-381.fr","4"],implementation="blst/resident/field_array.from_vector"} : ()->()
"local.binding"() {sym_name="get",contract="field_array.get",arguments=["bls12-381.fr","4"],implementation="blst/resident/field_array.get"} : ()->()
"local.binding"() {sym_name="fixed",contract="fixed_vector.from_vector",arguments=["bls12-381.fr","4"],implementation="blst/resident/fixed_vector.from_vector"} : ()->()
"local.binding"() {sym_name="dot",contract="fixed_vector.dot",arguments=["bls12-381.fr","4"],implementation="blst/resident/fixed_vector.dot"} : ()->()
)",
                         "%v:!V,%i:ui64", "%v,%i", "!V,ui64", "!F", R"(
%a = "algebra.exec.field_array_from_vector"(%v) {binding=@array,site="array",parameters=[]} : (!V)->!A
%x = "algebra.exec.field_array_get"(%a,%i) {binding=@get,site="get",parameters=[]} : (!A,ui64)->!F
%f = "algebra.exec.fixed_vector_from_vector"(%v) {binding=@fixed,site="fixed",parameters=[]} : (!V)->!X
%out = "algebra.exec.fixed_vector_dot"(%f,%f) {binding=@dot,site="dot",parameters=[]} : (!X,!X)->!F
local.return %out : !F
)",
                         2);
    auto module = take(executableFixture(source, context));
    PhysicalPlanOptions options;
    abi(options, *module, false, 0, "vector:bls12-381.fr@blst/fr");
    abi(options, *module, true, 0, scalar);
    auto plan =
        take(proposePhysical(*module, installedCandidates(), {}, options));
    require(take(encodeBoundType(at(plan, *module, "fixed").outputs[0], true))
                    .representation == "blst/fixed-vector",
            "fixed vector storage lost");
    publish(*module, take(validatePhysical(*module, plan)), "dense");
  });
  cases.run("complete layout wire permissions and logical custody", [&] {
    auto descriptor = *encodeVariant({"WireChoice",
                                      {{"none", {}},
                                       {"some", {"field:bls12-381.fr"}},
                                       {"unused", {"group:bls12-381.g2"}}}});
    auto selected = descriptor + "@logical.variant/0[blst/fr,blst/g2]";
    auto localDescriptor =
        *encodeVariant({"LocalChoice",
                        {{"some", {"field:bls12-381.fr"}},
                         {"unused", {"fixed_vector<field:bls12-381.fr,2>"}}}});
    auto local = localDescriptor +
                 "@logical.variant/0[blst/fr,blst/fixed-vector[blst/fr]]";
    auto affineDescriptor = *encodeVariant(
        {"AffineChoice",
         {{"some", {"field:bls12-381.fr"}}, {"unused", {"rng:bls12-381.fr"}}}});
    auto affine =
        affineDescriptor + "@logical.variant/0[blst/fr,host.resource/0]";
    auto paired = [&](StringRef type) {
      program::Participants model;
      model.stage = program::Participants::Stage::Physical;
      program::Participant sender, receiver;
      sender.name = "Sender";
      sender.instance = receiver.instance = "main";
      sender.role = "P";
      sender.arguments = {{"x", type.str()}};
      sender.body = {{"send", program::Send{"wire", "Q", "x"}},
                     {"", program::Return{}}};
      receiver.name = "Receiver";
      receiver.role = "Q";
      receiver.results = {type.str()};
      receiver.body = {
          {"receive", program::Receive{"wire", "P", "x", type.str()}},
          {"", program::Return{{"x"}}}};
      model.participants = {std::move(sender), std::move(receiver)};
      model.entries = {{"main", {{"P", "Sender"}, {"Q", "Receiver"}}}};
      return model;
    };
    for (const auto &type :
         {std::string("sequence<bool>@logical.sequence/0"),
          descriptor + "@logical.variant/0", sequence, nested, selected,
          std::string(
              "field_array<bls12-381.fr,4>@blst/field-array[blst/fr]")}) {
      auto formed = take(parseBoundType(type, true));
      require(nativeMessageData(formed), "complete supported frame refused");
      auto model = paired(type);
      accept(admit(model));
      take(program::decode(program::encode(model)));
    }
    for (const auto &type : {local, affine}) {
      auto formed = take(parseBoundType(type, true));
      require(!nativeMessageData(formed),
              "inactive local child acquired codec");
      auto refused = admit(paired(type));
      require(bool(refused), "inactive local wire admitted");
      consumeError(std::move(refused));
    }
    auto ownership = [&](StringRef type, bool release) {
      program::Participants model;
      model.stage = program::Participants::Stage::Physical;
      program::Function function;
      function.name = "Keep";
      function.origin = program::LogicalOrigin{"Keep", {}};
      function.arguments = {{"x", type.str()}};
      if (release)
        function.body = {{"", program::Release{{"x"}}},
                         {"", program::Return{}}};
      else {
        function.results = {type.str(), type.str()};
        function.body = {{"", program::Return{{"x", "x"}}}};
      }
      program::Names outputs =
          release ? program::Names{} : program::Names{"a", "b"};
      program::Participant participant;
      participant.name = "Owner";
      participant.instance = "main";
      participant.role = "P";
      participant.arguments = function.arguments;
      participant.results = function.results;
      participant.body = {{"keep", program::LocalCall{"Keep", {"x"}, outputs}},
                          {"", program::Return{outputs}}};
      model.functions.push_back(std::move(function));
      model.participants.push_back(std::move(participant));
      model.entries = {{"main", {{"P", "Owner"}}}};
      return model;
    };
    for (const auto &type : {selected, local}) {
      auto formed = take(parseBoundType(type, true));
      require(duplicable(formed) && discardable(formed) &&
                  custody(type) == Custody::PrivateImmutable &&
                  !nativeSetupType(formed),
              "selected logical custody changed");
      accept(admit(ownership(type, false)));
      accept(admit(ownership(type, true)));
    }
    auto formed = take(parseBoundType(affine, true));
    require(!duplicable(formed) && !discardable(formed) &&
                custody(affine) == Custody::Affine,
            "inactive affine child lost ownership");
    auto duplicate = admit(ownership(affine, false));
    require(bool(duplicate), "inactive affine child duplicated");
    consumeError(std::move(duplicate));
    auto release = admit(ownership(affine, true));
    require(bool(release), "inactive affine child released");
    consumeError(std::move(release));
  });
  cases.run("compiled indexed observation preserves selected payload", [&] {
    auto origin = take(encodeNativeOriginTemplate(
        "main", {}, {"message", "Round", "response", "response", "P", "V"}));
    auto source =
        R"(!T = !local.capability<"transcript:merlin3.bls12-381.fr64be/0">
!S = !data.sequence<!algebra.field<"bls12-381.fr">>
!I = !algebra.indices
)" + mathematicalFixture(
            R"(
"local.binding"() {sym_name="observe",contract="transcript.native.indexed.observe.data",arguments=["merlin3.bls12-381.fr64be/0","sequence<field:bls12-381.fr>"],implementation="arkworks/transcript.native.indexed.observe.data"} : ()->()
)",
            "%t:!T,%s:!S,%i:!I", "%t,%s,%i", "!T,!S,!I", "!T",
            R"(%out = "crypto.exec.indexed_transcript_observe_data"(%t,%s,%i) {binding=@observe,site="observe",parameters=[")" +
                origin + R"("]} : (!T,!S,!I)->!T
local.return %out : !T
)",
            3);
    auto module = take(executableFixture(source, context));
    PhysicalPlanOptions options;
    abi(options, *module, false, 1, sequence);
    auto plan =
        take(proposePhysical(*module, installedCandidates(), {}, options));
    auto &observation = at(plan, *module, "observe");
    require(observation.conversions.empty() &&
                take(encodeBoundType(observation.inputs[1], true)).spelling() ==
                    sequence,
            "observation relabeled or converted selected payload");
    const auto &binding = plan.bindings[*observation.binding];
    require(binding.binding.application.physicalArguments ==
                std::vector<std::string>{sequence},
            "observation lost exact parameter");
    auto wrong = binding.binding.application;
    wrong.physicalArguments = {scalar};
    refuses(resolveBinding(wrong, true), "binding-representation");
    publish(*module, take(validatePhysical(*module, plan)));
  });
  return cases.result();
}
