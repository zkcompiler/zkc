#include "../lib/Conversion/Bindings.h"
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
        require(a.purpose == BindingPurpose::Specialization &&
                    b.purpose == BindingPurpose::Specialization &&
                    a.origin == b.origin && a.fixed && b.fixed,
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
