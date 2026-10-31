#include "../lib/Transforms/OracleAnchorStorage.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Transforms/Mathematical.h"
#include <filesystem>
#include <fstream>
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::test;
namespace {
const char *source = R"mlir(
!F = !algebra.field<"koala-bear.ext4-binomial3">
!D = !algebra.field_vector<"koala-bear.ext4-binomial3">
#K = #protocol.oracle_kind<"table", [!F,16:ui64]>
!H = !protocol.oracle<#K>
module { "protocol.module"() ({
 relation.declare @admissible {kind="external",key="storage/virtual",revision="0",signature=(!D,!D,!F)->i1,purposes=["witness","witness","parameter"]}
 "protocol.oracle"() ({
  ^bb0(%a:!H,%b:!H,%weight:!F,%position:ui64):
   %x = "protocol.oracle_query"(%a,%position) {site="left"} : (!H,ui64)->!F
   %y = "protocol.oracle_query"(%b,%position) {site="right"} : (!H,ui64)->!F
   %weighted = "algebra.field_multiply"(%weight,%y) : (!F,!F)->!F
   %answer = "algebra.field_add"(%x,%weighted) : (!F,!F)->!F
   "protocol.oracle_yield"(%answer) : (!F)->()
 }) {sym_name="combine",function_type=(!H,!H,!F,ui64)->!F,kind=#K,shape_arguments={},shape_bounds={},admissibility=@admissible} : ()->()
 "protocol.func"() ({
  ^bb0(%data:!D,%raw:!H,%weight:!F):
   %input = "protocol.oracle_input"(%data,%raw) {holder="P",receivers=["V"],shape_bounds={}} : (!D,!H)->!H
   %rows = "data.index"() {value=16 : ui64} : ()->ui64
   %other = "protocol.oracle_send"(%data,%rows) {sender="P",receivers=["V"],site="word",shape_names=["rows"],shape_bounds={}} : (!D,ui64)->!H
   %trips = "data.index"() {value=3 : ui64} : ()->ui64
   %last = "protocol.repeat"(%trips,%input,%other,%weight) ({
    ^bb0(%i:ui64,%previous:!H,%second:!H,%w:!F):
     %next = "protocol.oracle_virtual"(%previous,%second,%w) {callee=@combine,holder="P",receivers=["V"]} : (!H,!H,!F)->!H
     %pair:2 = "protocol.oracle_components"(%next) {holder="P",receivers=["V"]} : (!H)->(!D,!H)
     %same = "protocol.oracle_input"(%pair#0,%pair#1) {holder="P",receivers=["V"],shape_bounds={}} : (!D,!H)->!H
     "protocol.yield"(%same) : (!H)->()
   }) {site="chain",carried=1:i64,maximum=3:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,!H,!H,!F)->!H
   %ok = arith.constant true
   "protocol.return"(%ok) : (i1)->()
 }) {sym_name="example",function_type=(!D,!H,!F)->i1,roles=["P","V"],input_roles=[["P"],["V"],["P","V"]],output_roles=[["V"]]} : ()->()
 }) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
const char *merkle = "rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0";
std::vector<std::string> fields(const OracleRoleStorage &storage) {
  std::vector<std::string> names;
  for (const auto &field : storage.fields)
    names.push_back(field.name);
  return names;
}
} // namespace
int main(int argc, char **argv) {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  std::string diagnostics;
  ScopedDiagnosticHandler capture(&context, [&](Diagnostic &message) {
    raw_string_ostream stream(diagnostics);
    message.print(stream);
    return success();
  });
  auto module =
      parseSourceString<ModuleOp>(source, ParserConfig(&context, false));
  require(bool(module) && succeeded(verify(*module)),
          "fixture refused: " + diagnostics);
  auto prepared = mathematical::prepareProtocol(*module, false);
  require(bool(prepared), "preparation failed: " + diagnostics);
  OwningOpRef<ModuleOp> frozen(cast<ModuleOp>(prepared->clone()));
  auto selects = [&](StringRef scheme) {
    return planOracleAnchorStorage(
        *prepared, "example",
        [&](const auto &) -> Expected<std::string> { return scheme.str(); });
  };
  auto ideal = take(selects(""));
  Cases cases;
  cases.run(
      "native store planning preserves rows beyond byte-profile depth", [&] {
        std::string row = "i1";
        for (unsigned i = 0; i < 12; ++i)
          row = "!data.sequence<" + row + ">";
        auto nativeSource = std::string("!Row = ") + row + R"mlir(
!Data = !data.sequence<!Row>
!Handle = !protocol.oracle<#protocol.oracle_kind<"table", [!Row]>>
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%data:!Data,%rows:ui64):
  %handle = "protocol.oracle_send"(%data,%rows) {sender="P",receivers=["V"],site="table",shape_names=["rows"],shape_bounds={rows=16:ui64}} : (!Data,ui64)->!Handle
  "protocol.return"() : ()->()
 }) {sym_name="main",function_type=(!Data,ui64)->(),roles=["P","V"],input_roles=[["P"],["P","V"]],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
        auto candidate = parseSourceString<ModuleOp>(nativeSource, &context);
        require(bool(candidate) && succeeded(verify(*candidate)),
                "native source refused: " + diagnostics);
        auto plan = take(planOracleAnchorStorage(
            *candidate, "main", [](const auto &) -> Expected<std::string> {
              return std::string();
            }));
        require(plan.constructors.size() == 1 &&
                    plan.constructors[0].roles.size() == 2,
                "native storage lost its holder/receiver pair");
        for (const auto &role : plan.constructors[0].roles) {
          auto sequence = cast<data::SequenceType>(role.sequence);
          require(sequence.getElementType() == role.record &&
                      succeeded(verifyLogicalType(
                          [&] { return emitError(candidate->getLoc()); },
                          role.sequence)),
                  "store did not retain its formed native record");
          auto bytes = encodeBoundType(role.sequence, false);
          require(!bytes, "native storage widened byte-profile admission");
          consumeError(bytes.takeError());
        }
        // Reference /0 still embeds public type spellings. Planning a native
        // store grants no serializable reference or executable installation for
        // this row.
        auto reference = oracleReferenceType(plan.constructors[0].kind);
        require(!reference,
                "native planning widened the reference identity schema");
        consumeError(reference.takeError());
      });
  cases.run(
      "fresh constructors survive identical data and recurrent references",
      [&] {
        require(ideal.constructors.size() == 3,
                "component rebinding allocated a new anchor");
        auto &input = ideal.constructors[0];
        auto &send = ideal.constructors[1];
        auto &created = ideal.constructors[2];
        require(input.constructor == OracleAnchorConstructor::Kind::Input &&
                    send.constructor == OracleAnchorConstructor::Kind::Send &&
                    created.constructor ==
                        OracleAnchorConstructor::Kind::Virtual,
                "constructor source order changed");
        require(input.maximumInstances == 1 && send.maximumInstances == 1 &&
                    created.maximumInstances == 3,
                "dynamic constructor multiplicity changed");
        require(input.path == std::vector<unsigned>{0} &&
                    send.path == std::vector<unsigned>{2} &&
                    created.path == std::vector<unsigned>({4, 0}),
                "prepared occurrence paths changed");
        require(input.roles[0].record != send.roles[0].record,
                "equal data merged fresh occurrences");
        require(created.declaration == "combine" && created.scheme.empty(),
                "virtual became a commitment");
        require(fields(created.roles[0]) ==
                    std::vector<std::string>({"iteration.0", "shape.rows",
                                              "query.leaves", "source.0",
                                              "source.1", "parameter.2"}),
                "virtual environment lost its actual sources or parameter "
                "positions");
      });
  cases.run("ideal and Merkle role storage preserve the data boundary", [&] {
    unsigned selections = 0;
    auto plan = take(planOracleAnchorStorage(
        *prepared, "example", [&](const auto &) -> Expected<std::string> {
          ++selections;
          return std::string(merkle);
        }));
    require(selections == 2,
            "a virtual or component rebinding selected a scheme");
    for (unsigned i : {0u, 1u}) {
      auto &created = plan.constructors[i];
      require(created.roles[0].role == "P" && created.roles[1].role == "V",
              "role family changed");
      require(fields(created.roles[0]) ==
                  std::vector<std::string>(
                      {"shape.rows", "query.leaves", "data", "opening_state"}),
              "holder lost data or private opening state");
      require(
          fields(created.roles[1]) ==
              std::vector<std::string>({"shape.rows", "query.leaves", "root"}),
          "receiver acquired holder-only data");
      auto holder = take(encodeBoundType(created.roles[0].sequence, false));
      auto receiver = take(encodeBoundType(created.roles[1].sequence, false));
      require(!nativeTypePolicy(holder)->wire &&
                  nativeTypePolicy(receiver)->wire,
              "private opening store acquired a public wire codec");
      require(
          fields(ideal.constructors[i].roles[1]) ==
              std::vector<std::string>({"shape.rows", "query.leaves", "data"}),
          "ideal delivery lost its clear table");
    }
    require(plan.constructors[2].roles[0].record ==
                ideal.constructors[2].roles[0].record,
            "commitment selection changed a virtual environment");
  });
  cases.run("reference carriers erase only static shape", [&] {
    auto kind = ideal.constructors[0].kind;
    auto unsized = protocol_ir::OracleKindAttr::get(
        &context, "table", ArrayAttr::get(&context, {kind.getArguments()[0]}));
    auto reference = take(oracleReferenceType(kind));
    require(reference == take(oracleReferenceType(unsized)),
            "shape forgetting changed the reference carrier");
    for (const auto &constructor : ideal.constructors)
      for (const auto &role : constructor.roles) {
        auto type = take(encodeBoundType(role.sequence, false));
        require(bool(parseBoundType(type.spelling(), false)),
                "storage is not an ordinary native type");
      }
    auto payload =
        decodeVariant(take(encodeBoundType(reference, false)).spelling());
    require(payload && payload->alternatives.size() == 1 &&
                payload->alternatives[0].payload ==
                    std::vector<std::string>({"index", "index"}),
            "reference hides an oracle runtime object");
  });
  cases.run("wrong schemes and source selections refuse without mutation", [&] {
    refuses(selects("rows.merkle-poseidon2-16.koala-bear/0"),
            "oracle-storage-scheme");
    auto unknown = selects("unknown/0");
    require(!unknown, "unknown scheme was admitted");
    consumeError(unknown.takeError());
    refuses(planOracleAnchorStorage(*prepared, "missing",
                                    [](const auto &) -> Expected<std::string> {
                                      return std::string();
                                    }),
            "oracle-storage-entry");
    require(OperationEquivalence::isEquivalentTo(
                *prepared, *frozen, OperationEquivalence::IgnoreLocations),
            "storage planning changed its source");
  });

  cases.run("source entry identity distinguishes storage types", [&] {
    OwningOpRef<ModuleOp> renamed(cast<ModuleOp>(prepared->clone()));
    auto unit =
        cast<protocol_ir::ProtocolModuleOp>(renamed->getBody()->front());
    auto function = cast<protocol_ir::MathematicalOp>(
        SymbolTable::lookupSymbolIn(unit, "example"));
    function.setSymName("oracle_other");
    auto plan = take(planOracleAnchorStorage(
        *renamed, "oracle_other",
        [](const auto &) -> Expected<std::string> { return std::string(); }));
    require(plan.constructors.size() == 3 &&
                plan.constructors[0].roles[0].record !=
                    ideal.constructors[0].roles[0].record,
            "source symbol encoding lost identity");
  });
  for (const auto scheme : {StringRef(), StringRef(merkle)}) {
    auto plan = take(selects(scheme));
    cases.run(
        "actual allocation bodies: " +
            (scheme.empty() ? std::string("ideal") : scheme.str()),
        [&] {
          OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(prepared->clone()));
          for (unsigned c = 0; c < plan.constructors.size(); ++c)
            for (unsigned role = 0; role < plan.constructors[c].roles.size();
                 ++role) {
              auto actual =
                  take(emitOracleAnchorAllocator(*candidate, plan, c, role));
              require(succeeded(verify(*candidate)),
                      "generated allocator is malformed: " + diagnostics);
              if (auto failure = checkOracleAnchorAllocator(*candidate, actual,
                                                            plan, c, role))
                throw std::runtime_error(toString(std::move(failure)));
              require(scopedDataSignature(actual).getNumInputs() ==
                          1 + plan.constructors[c].roles[role].fields.size(),
                      "allocator erased role payload");
            }
          // A second use must allocate a distinct helper without rewriting the
          // authored or previously generated symbol, and the reader ignores
          // names.
          auto again = take(emitOracleAnchorAllocator(*candidate, plan, 0, 0));
          require(again.getSymName() == "_oracle_allocate_0_0_0",
                  "allocator rewrote an existing helper");
          if (auto failure =
                  checkOracleAnchorAllocator(*candidate, again, plan, 0, 0))
            throw std::runtime_error(toString(std::move(failure)));
        });
  }
  using Mutator = std::function<void(func::FuncOp)>;
  auto variant = [](func::FuncOp function, StringRef site) {
    exec::VariantOp result;
    function.walk([&](exec::VariantOp op) {
      if (op.getSite() == site)
        result = op;
    });
    require(bool(result), "missing variant step");
    return result;
  };
  std::vector<std::pair<std::string, Mutator>> mutations;
  mutations.emplace_back(
      "wrong constructor ordinal", [&](func::FuncOp function) {
        function.walk([&](exec::ApplyOp op) {
          if (op.getSite() == "constructor")
            op.setParametersAttr(ArrayAttr::get(
                &context,
                {IntegerAttr::get(
                    IntegerType::get(&context, 64, IntegerType::Unsigned),
                    0)}));
        });
      });
  mutations.emplace_back("swapped constructor and instance",
                         [&](func::FuncOp function) {
                           auto op = variant(function, "reference");
                           auto values = SmallVector<Value>(op.getPayload());
                           std::swap(values[0], values[1]);
                           op.getPayloadMutable().assign(values);
                         });
  mutations.emplace_back("swapped virtual children of the same type",
                         [&](func::FuncOp function) {
                           auto op = variant(function, "record");
                           auto values = SmallVector<Value>(op.getPayload());
                           std::swap(values[3], values[4]);
                           op.getPayloadMutable().assign(values);
                         });
  mutations.emplace_back("reuse stale store after append",
                         [&](func::FuncOp function) {
                           function.walk([&](exec::ReturnOp op) {
                             op.setOperand(1, function.getArgument(1));
                           });
                         });
  mutations.emplace_back("changed occurrence", [&](func::FuncOp function) {
    variant(function, "reference").setSite("renamed");
  });
  for (const auto &mutation : mutations)
    cases.run(
        "well-formed allocation mutation refuses: " + mutation.first, [&] {
          OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(prepared->clone()));
          auto actual =
              take(emitOracleAnchorAllocator(*candidate, ideal, 2, 0));
          mutation.second(actual);
          require(succeeded(verify(*candidate)),
                  "mutation only failed formation: " + diagnostics);
          auto refusal =
              checkOracleAnchorAllocator(*candidate, actual, ideal, 2, 0);
          require(bool(refusal), "changed allocation was certified");
          require(namesIdentifier(toString(std::move(refusal)),
                                  "oracle-storage-allocation-body"),
                  "unexpected allocation refusal");
        });
  cases.run("allocation selection and kind errors refuse", [&] {
    refuses(oracleReferenceType({}), "oracle-storage-kind");
    refuses(emitOracleAnchorAllocator(*prepared, ideal, 3, 0),
            "oracle-storage-allocator");
    refuses(emitOracleAnchorAllocator(*prepared, ideal, 0, 2),
            "oracle-storage-allocator");
    require(OperationEquivalence::isEquivalentTo(
                *prepared, *frozen, OperationEquivalence::IgnoreLocations),
            "refused allocation changed its source");
  });

  cases.run("nested constructor capacity multiplication refuses overflow", [&] {
    OwningOpRef<ModuleOp> nested(cast<ModuleOp>(prepared->clone()));
    protocol_ir::RepeatOp outer;
    nested->walk([&](protocol_ir::RepeatOp op) { outer = op; });
    auto bound = IntegerAttr::get(IntegerType::get(&context, 64), 1048576);
    outer.setMaximumAttr(bound);
    for (unsigned depth = 0; depth < 3; ++depth) {
      auto &body = outer.getBody().front();
      IRMapping inputs;
      for (auto [input, argument] : zip(outer.getInputs(), body.getArguments()))
        inputs.map(input, argument);
      auto inner = cast<protocol_ir::RepeatOp>(outer->clone(inputs));
      inner.setSite("nested_" + std::to_string(depth));
      auto *yield = body.getTerminator();
      yield->setOperands(inner.getOutputs());
      while (&body.front() != yield)
        body.back().getPrevNode()->erase();
      body.getOperations().insert(Block::iterator(yield), inner);
    }
    require(succeeded(verify(*nested)),
            "capacity fixture malformed: " + diagnostics);
    refuses(planOracleAnchorStorage(*nested, "example",
                                    [](const auto &) -> Expected<std::string> {
                                      return std::string();
                                    }),
            "oracle-storage-capacity");
  });
  cases.run("missing selection and invalid subjects refuse", [&] {
    OracleStorageSelection missing;
    refuses(planOracleAnchorStorage(*prepared, "example", missing),
            "oracle-storage-source");
    refuses(planOracleAnchorStorage({}, "example",
                                    [](const auto &) -> Expected<std::string> {
                                      return std::string();
                                    }),
            "oracle-storage-source");
  });

  cases.run("generated allocation reaches the ordinary physical pipeline", [&] {
    OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(prepared->clone()));
    auto allocator = take(emitOracleAnchorAllocator(*candidate, ideal, 0, 0));
    auto unit =
        cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
    for (Operation &operation : make_early_inc_range(unit.getBody().front()))
      if (isa<protocol_ir::MathematicalOp, protocol_ir::OracleDefinitionOp>(
              operation))
        operation.erase();
    OpBuilder builder(&context);
    auto location = candidate->getLoc();
    builder.setInsertionPointToEnd(&unit.getBody().front());
    auto &storage = ideal.constructors[0].roles[0];
    auto index = IntegerType::get(&context, 64, IntegerType::Unsigned);
    auto data = ideal.constructors[0].kind.getDataType();
    auto role = builder.getArrayAttr({builder.getStringAttr("P")});
    OperationState state(location, "protocol.func");
    state.addAttribute("sym_name", builder.getStringAttr("main"));
    state.addAttribute("function_type", TypeAttr::get(builder.getFunctionType(
                                            data, {index, index})));
    state.addAttribute("roles", role);
    state.addAttribute("input_roles", builder.getArrayAttr({role}));
    state.addAttribute("output_roles", builder.getArrayAttr({role, role}));
    auto *body = new Block();
    body->addArgument(data, location);
    state.addRegion()->push_back(body);
    builder.create(state);
    builder.setInsertionPointToEnd(body);
    auto empty =
        data::SequenceEmptyOp::create(builder, location, storage.sequence);
    auto rows = data::IndexOp::create(builder, location, index, 16);
    auto count = data::IndexOp::create(builder, location, index, 1);
    auto signature = scopedDataSignature(allocator);
    auto call = protocol_ir::LocalCallOp::create(
        builder, location, signature.getResults(),
        ValueRange{empty, rows, count, body->getArgument(0)},
        allocator.getSymName(), "allocate", "P");
    auto tag =
        data::GetOp::create(builder, location, index, call.getOutputs()[0], 0);
    auto instance =
        data::GetOp::create(builder, location, index, call.getOutputs()[0], 1);
    protocol_ir::MathematicalReturnOp::create(builder, location,
                                              ValueRange{tag, instance});
    require(succeeded(verify(*candidate)),
            "allocation client malformed: " + diagnostics);
    std::string source;
    raw_string_ostream text(source);
    candidate->print(text);
    auto compiled =
        take(compileRun(source, "oracle-storage.mlir", {}, registry));
    require(succeeded(verify(compiled.compilation.module())),
            "physical allocation module failed admission");
    require(!compiled.bundle.empty(), "allocator has no executable bundle");
  });
  for (const auto scheme : {StringRef(), StringRef(merkle)}) {
    auto plan = take(selects(scheme));
    cases.run(
        "actual reference lookup: " +
            (scheme.empty() ? std::string("ideal") : scheme.str()),
        [&] {
          OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(prepared->clone()));
          for (unsigned constructor = 0; constructor < plan.constructors.size();
               ++constructor)
            for (unsigned role = 0;
                 role < plan.constructors[constructor].roles.size(); ++role) {
              auto helper = take(
                  emitOracleAnchorLookup(*candidate, plan, constructor, role));
              require(succeeded(verify(*candidate)),
                      "lookup formation failed: " + diagnostics);
              if (auto e = checkOracleAnchorLookup(*candidate, helper, plan,
                                                   constructor, role))
                throw std::runtime_error(toString(std::move(e)));
            }
        });
  }
  for (unsigned mutation = 0; mutation < 8; ++mutation)
    cases.run(Twine("well-formed lookup mutation ") + Twine(mutation), [&] {
      OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(prepared->clone()));
      auto helper = take(emitOracleAnchorLookup(*candidate, ideal, 2, 0));
      auto unit =
          cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
      auto closure = take(readSourceExecutionClosure(unit));
      auto selected = helper;
      auto &body = closure.bodies.at(selected.getSymName().str());
      Builder builder(&context);
      if (mutation == 0) {
        auto constant = cast<exec::ApplyOp>(body[0].operation);
        constant.setParametersAttr(builder.getArrayAttr(
            {builder.getIntegerAttr(builder.getIntegerType(64, false), 1)}));
      }
      if (mutation == 1)
        cast<exec::ApplyOp>(body[1].operation)
            .getInputsMutable()[0]
            .set(selected.getArgument(2));
      if (mutation == 2)
        cast<exec::ApplyOp>(body[3].operation)
            .getInputsMutable()[1]
            .set(selected.getArgument(1));
      if (mutation == 3 || mutation == 4) {
        auto unpacked = body[4].regions[0];
        auto &unpack = closure.bodies.at(unpacked.getSymName().str());
        auto complete = cast<exec::CompleteOp>(unpack[0].operation);
        unsigned i = mutation == 3 ? 0 : 3;
        auto left = complete.getValues()[i],
             right = complete.getValues()[i + 1];
        require(left.getType() == right.getType(),
                "mutation types do not agree");
        complete.getValuesMutable()[i].set(right);
        complete.getValuesMutable()[i + 1].set(left);
      }
      if (mutation == 5)
        selected.walk([&](Operation *op) {
          auto site = op->getAttrOfType<StringAttr>("site");
          if (site && site.getValue() == "record")
            op->setAttr("site", builder.getStringAttr("changed_record"));
        });
      if (mutation == 6) {
        auto call = cast<exec::ApplyOp>(body[1].operation);
        auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
            call, call.getBindingAttr());
        binding.setContract("index.less");
      }
      if (mutation == 7) {
        auto equality = cast<exec::ApplyOp>(body[1].operation);
        // Self-equality must not replace the remaining constructor guard.
        equality.getInputsMutable()[1].set(equality.getInputs()[0]);
      }
      require(succeeded(verify(*candidate)),
              "lookup mutation failed only formation: " + diagnostics);
      auto rejected = checkOracleAnchorLookup(*candidate, helper, ideal, 2, 0);
      require(bool(rejected), "lookup mutation passed correspondence");
      require(namesIdentifier(toString(std::move(rejected)),
                              "oracle-storage-lookup-body"),
              "wrong lookup refusal");
    });
  cases.run("lookup selections refuse out-of-inventory indices", [&] {
    refuses(emitOracleAnchorLookup(*prepared, ideal, 3, 0),
            "oracle-storage-lookup");
    refuses(emitOracleAnchorLookup(*prepared, ideal, 0, 2),
            "oracle-storage-lookup");
    require(OperationEquivalence::isEquivalentTo(
                *prepared, *frozen, OperationEquivalence::IgnoreLocations),
            "lookup refusal mutated original");
  });
  cases.run("allocation and lookup share the actual ordinary store", [&] {
    auto candidate = parseSourceString<ModuleOp>(R"mlir(
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%data:!algebra.indices,%rows:ui64):
  %handle = "protocol.oracle_send"(%data,%rows) {sender="P",receivers=["V"],site="table",shape_names=["rows"],shape_bounds={rows=16:ui64}} : (!algebra.indices,ui64)->!protocol.oracle<#protocol.oracle_kind<"table", [ui64]>>
  "protocol.return"() : ()->()
 }) {sym_name="main",function_type=(!algebra.indices,ui64)->(),roles=["P","V"],input_roles=[["P"],["P","V"]],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir",
                                                 &context);
    require(bool(candidate), "lookup client source failed: " + diagnostics);
    auto plan = take(planOracleAnchorStorage(
        *candidate, "main",
        [](const auto &) -> Expected<std::string> { return std::string(); }));
    auto allocator = take(emitOracleAnchorAllocator(*candidate, plan, 0, 0));
    auto lookup = take(emitOracleAnchorLookup(*candidate, plan, 0, 0));
    auto unit =
        cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
    SymbolTable::lookupSymbolIn(unit, "main")->erase();
    OpBuilder builder(&context);
    auto loc = candidate->getLoc();
    auto &storage = plan.constructors[0].roles[0];
    auto dataType = plan.constructors[0].kind.getDataType();
    auto index = IntegerType::get(&context, 64, IntegerType::Unsigned);
    auto role = builder.getStrArrayAttr({"P"});
    SmallVector<Type> inputs{dataType, dataType, index, index};
    SmallVector<Type> outputs{index, dataType, index, index};
    OperationState function(loc, "protocol.func");
    function.addAttribute("sym_name", builder.getStringAttr("main"));
    function.addAttribute(
        "function_type",
        TypeAttr::get(builder.getFunctionType(inputs, outputs)));
    function.addAttribute("roles", role);
    function.addAttribute(
        "input_roles", builder.getArrayAttr(SmallVector<Attribute>(4, role)));
    function.addAttribute(
        "output_roles", builder.getArrayAttr(SmallVector<Attribute>(4, role)));
    auto *body = new Block();
    body->addArguments(inputs, SmallVector<Location>(4, loc));
    function.addRegion()->push_back(body);
    builder.setInsertionPointToEnd(&unit.getBody().front());
    builder.create(function);
    builder.setInsertionPointToEnd(body);
    Value store = data::SequenceEmptyOp::create(builder, loc, storage.sequence);
    SmallVector<Value> references;
    for (unsigned i = 0; i < 2; ++i) {
      auto rows =
          data::DimOp::create(builder, loc, index, body->getArgument(i), 0);
      auto count = data::IndexOp::create(builder, loc, index, 1);
      auto allocated = protocol_ir::LocalCallOp::create(
          builder, loc, scopedDataSignature(allocator).getResults(),
          ValueRange{store, rows, count, body->getArgument(i)},
          allocator.getSymName(), "allocate_" + std::to_string(i), "P");
      references.push_back(allocated.getOutputs()[0]);
      store = allocated.getOutputs()[1];
    }
    auto loaded = protocol_ir::LocalCallOp::create(
        builder, loc, scopedDataSignature(lookup).getResults(),
        ValueRange{body->getArgument(2), body->getArgument(3), store},
        lookup.getSymName(), "lookup", "P");
    auto first = data::GetOp::create(builder, loc, index, references[0], 1);
    auto second = data::GetOp::create(builder, loc, index, references[1], 1);
    protocol_ir::MathematicalReturnOp::create(builder, loc,
                                              ValueRange{loaded.getOutputs()[0],
                                                         loaded.getOutputs()[2],
                                                         first, second});
    require(succeeded(verify(*candidate)),
            "lookup client malformed: " + diagnostics);
    std::string source;
    raw_string_ostream text(source);
    candidate->print(text);
    auto compiled =
        take(compileRun(source, "oracle-anchor-lookup.mlir", {}, registry));
    require(!compiled.bundle.empty(), "lookup client has no executable bundle");
    if (argc == 2) {
      std::filesystem::create_directories(argv[1]);
      std::ofstream out(std::filesystem::path(argv[1]) / "anchors.bundle");
      out << compiled.bundle;
      require(bool(out), "could not retain anchor client");
    }
  });
  return cases.result();
}
