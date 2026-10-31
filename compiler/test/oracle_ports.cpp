#include "../lib/Dialect/Protocol/IR/OracleAnalysis.h"
#include "../lib/Transforms/OracleAnchorStorage.h"
#include "../lib/Transforms/OracleCommonRealization.h"
#include "../lib/Transforms/OracleQueryCapacity.h"
#include "../lib/Transforms/PreparedProtocol.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/Contracts.h"
#include "zkc/Dialect/Protocol/OraclePorts.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/Support/JSON.h"
using namespace mlir;
using namespace zkc::test;
using namespace zkc::protocol_ir;
namespace {
std::string source() {
  return R"mlir(
#K = #protocol.oracle_kind<"table", [!algebra.field<"koala-bear">, 16 : ui64]>
!F = !algebra.field<"koala-bear">
!D = !algebra.field_vector<"koala-bear">
!H = !protocol.oracle<#K>
module {
 "protocol.module"() ({
  "protocol.func"() ({
   ^bb0(%data:!D,%anchor:!H,%rows:ui64,%position:ui64):
    %word = "protocol.oracle_input"(%data,%anchor) {shape_bounds={},holder="A",receivers=["B"]} : (!D,!H)->!H
    %contents = "protocol.oracle_contents"(%word) {owner="A"} : (!H)->!D
    %value = "protocol.oracle_query"(%word,%position) {owner="B",site="read"} : (!H,ui64)->!F
    %parts:2 = "protocol.oracle_components"(%word) {holder="A",receivers=["B"]} : (!H)->(!D,!H)
    "protocol.return"(%parts#0,%parts#1,%value) : (!D,!H,!F)->()
  }) {sym_name="reader",function_type=(!D,!H,ui64,ui64)->(!D,!H,!F),
      roles=["A","B"],input_roles=[["A"],["B"],["A","B"],["B"]],
      output_roles=[["A"],["B"],["B"]]} : ()->()
  "protocol.func"() ({
   ^bb0(%data:!D,%rows:ui64,%position:ui64):
    %word = "protocol.oracle_send"(%data,%rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="word"} : (!D,ui64)->!H
    %parts:2 = "protocol.oracle_components"(%word) {holder="P",receivers=["V"]} : (!H)->(!D,!H)
    %result:3 = "protocol.apply"(%parts#0,%parts#1,%rows,%position) {callee=@reader,roles=["P","V"],site="call"} : (!D,!H,ui64,ui64)->(!D,!H,!F)
    %returned = "protocol.oracle_input"(%result#0,%result#1) {shape_bounds={},holder="P",receivers=["V"]} : (!D,!H)->!H
    %contents = "protocol.oracle_contents"(%returned) {owner="P"} : (!H)->!D
    %value = "protocol.oracle_query"(%returned,%position) {owner="V",site="again"} : (!H,ui64)->!F
    "protocol.return"(%value) : (!F)->()
  }) {sym_name="example",function_type=(!D,ui64,ui64)->!F,
      roles=["P","V"],input_roles=[["P"],["P","V"],["V"]],
      output_roles=[["V"]]} : ()->()
 }) {profile=#protocol.profile<protocol>} : ()->()
})mlir";
}
std::string replace(std::string text, llvm::StringRef before,
                    llvm::StringRef after) {
  auto pos = text.find(before.str());
  require(pos != std::string::npos, "missing port mutation target");
  text.replace(pos, before.size(), after.str());
  return text;
}
OwningOpRef<ModuleOp> parse(llvm::StringRef text, MLIRContext &context) {
  auto module =
      parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
  require(bool(module), "port fixture did not parse");
  return module;
}
std::string contractSource() {
  return R"mlir(
#K = #protocol.oracle_kind<"table", [ui64,4:ui64]>
!H = !protocol.oracle<#K>
!D = !algebra.indices
module { "protocol.module"() ({
 relation.declare @claimed {kind="external",key="test/anchor-contract",revision="0",signature=(!D)->i1,purposes=["statement"]}
 "protocol.func"() ({
 ^entry(%data:!D,%anchor:!H):
  %handle = "protocol.oracle_input"(%data,%anchor) {holder="A",receivers=["B"],shape_bounds={}} : (!D,!H)->!H
  %parts:2 = "protocol.oracle_components"(%handle) {holder="A",receivers=["B"]} : (!H)->(!D,!H)
  %accepted = arith.constant true
  "protocol.statement"(%anchor) {relation=@claimed,selectors=["anchor"],target="selected",acceptance=2:i64} : (!H)->()
  "protocol.return"(%parts#0,%parts#1,%accepted) : (!D,!H,i1)->()
 }) {sym_name="reader",function_type=(!D,!H)->(!D,!H,i1),roles=["A","B"],input_roles=[["A"],["B"]],output_roles=[["A"],["B"],["B"]],contracts=[
  ["target","other",[@claimed,[["anchor","input",1:i64]]],unit,["output",2:i64,"B"]],
  ["input","premise",[@claimed,[["input",0:i64,"A"]]],unit,unit],
  ["output","result",[@claimed,[["anchor","output",1:i64]]],unit,unit],
  ["continuation","reduction",[@claimed,[["anchor","input",1:i64]]],[@claimed,[["anchor","output",1:i64]]],["output",2:i64,"B"]],
  ["target","selected",[@claimed,[["anchor","input",1:i64]]],unit,["output",2:i64,"B"]]
 ]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
}
std::string dynamic() {
  auto text = replace(source(), ", 16 : ui64", "");
  size_t position;
  while ((position = text.find("shape_bounds={}")) != std::string::npos)
    text.replace(position, llvm::StringRef("shape_bounds={}").size(),
                 "shape_bounds={rows=32:ui64}");
  return text;
}
std::string sequenceSource(bool dynamic = false) {
  std::string text = R"mlir(
#K = #protocol.oracle_kind<"table", [ui64, 16 : ui64]>
!H = !protocol.oracle<#K>
!S = !protocol.oracle_sequence<#K, 3>
!D = !algebra.indices
!DS = !data.sequence<!D>
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%data:!DS,%anchor:!S):
  %sequence = "protocol.oracle_input"(%data,%anchor) {holder="A",receivers=["B"],shape_bounds={}} : (!DS,!S)->!S
  %parts:2 = "protocol.oracle_components"(%sequence) {holder="A",receivers=["B"]} : (!S)->(!DS,!S)
  "protocol.return"(%parts#0,%parts#1) : (!DS,!S)->()
 }) {sym_name="relay",function_type=(!DS,!S)->(!DS,!S),roles=["A","B"],input_roles=[["A"],["B"]],output_roles=[["A"],["B"]]} : ()->()
 "protocol.func"() ({
 ^entry(%data:!D,%rows:ui64,%position:ui64):
  %first = "protocol.oracle_send"(%data,%rows) {sender="P",receivers=["V"],site="first",shape_names=["rows"],shape_bounds={}} : (!D,ui64)->!H
  %second = "protocol.oracle_send"(%data,%rows) {sender="P",receivers=["V"],site="second",shape_names=["rows"],shape_bounds={}} : (!D,ui64)->!H
  %empty = "protocol.oracle_sequence_empty"() : ()->!S
  %one = "protocol.oracle_sequence_append"(%empty,%first) {roles=["P","V"],site="one"} : (!S,!H)->!S
  %two = "protocol.oracle_sequence_append"(%one,%second) {roles=["P","V"],site="two"} : (!S,!H)->!S
  %sequence = "protocol.oracle_sequence_append"(%two,%first) {roles=["P","V"],site="three"} : (!S,!H)->!S
  %other = "protocol.oracle_sequence_append"(%two,%second) {roles=["P","V"],site="other"} : (!S,!H)->!S
  %parts:2 = "protocol.oracle_components"(%sequence) {holder="P",receivers=["V"]} : (!S)->(!DS,!S)
  %otherParts:2 = "protocol.oracle_components"(%other) {holder="P",receivers=["V"]} : (!S)->(!DS,!S)
  %result:2 = "protocol.apply"(%parts#0,%parts#1) {callee=@relay,roles=["P","V"],site="call"} : (!DS,!S)->(!DS,!S)
  %returned = "protocol.oracle_input"(%result#0,%result#1) {holder="P",receivers=["V"],shape_bounds={}} : (!DS,!S)->!S
  %selected = "protocol.oracle_sequence_at"(%returned,%position) {roles=["P","V"],site="select"} : (!S,ui64)->!H
  %contents = "protocol.oracle_contents"(%selected) {owner="P"} : (!H)->!D
  %value = "protocol.oracle_query"(%selected,%position) {owner="V",site="read"} : (!H,ui64)->ui64
  "protocol.return"(%value) : (ui64)->()
 }) {sym_name="example",function_type=(!D,ui64,ui64)->ui64,roles=["P","V"],input_roles=[["P"],["P","V"],["P","V"]],output_roles=[["V"]]} : ()->()
 }) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
  if (dynamic) {
    text = replace(text, ", 16 : ui64", "");
    size_t at;
    while ((at = text.find("shape_bounds={}")) != std::string::npos)
      text.replace(at, llvm::StringRef("shape_bounds={}").size(),
                   "shape_bounds={rows=32:ui64}");
  }
  return text;
}
} // namespace
int main() {
  DialectRegistry registry;
  zkc::registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler silence(&context,
                                  [](Diagnostic &) { return success(); });
  Cases cases;
  auto accepted = [&](llvm::StringRef text, bool prepare = false) {
    std::string message;
    ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
      message += diagnostic.str();
      return success();
    });
    auto module = parse(text, context);
    require(succeeded(zkc::admitStage(*module)),
            "valid oracle ports refused: " + message);
    if (prepare) {
      auto candidate = zkc::mathematical::prepareProtocol(*module);
      require(bool(candidate), "port preparation failed: " + message);
    }
  };
  auto refused = [&](llvm::StringRef text) {
    auto module = parse(text, context);
    require(failed(zkc::admitStage(*module)), "invalid oracle ports admitted");
  };
  cases.run(
      "typed contracts preserve anchors, residuals and exact selection", [&] {
        auto module = parse(contractSource(), context);
        require(succeeded(zkc::admitStage(*module)),
                "contract fixture formation");
        auto unit = *module->getOps<ProtocolModuleOp>().begin();
        auto reader =
            cast<MathematicalOp>(SymbolTable::lookupSymbolIn(unit, "reader"));
        SymbolTableCollection symbols;
        auto inventory = readContracts(reader, symbols);
        require(succeeded(inventory) && inventory->clauses.size() == 5 &&
                    inventory->statements.size() == 1,
                "incomplete contract inventory");
        auto &clauses = inventory->clauses;
        auto &anchor =
            std::get<ContractAnchor>(clauses[0].subject.operands.front());
        auto &data =
            std::get<ContractComponent>(clauses[1].subject.operands.front());
        auto &residual =
            std::get<ContractAnchor>(clauses[3].residual->operands.front());
        require(!anchor.port.output && anchor.port.index == 1 &&
                    anchor.kind.getDataType() == data.type &&
                    !data.port.output && data.port.index == 0 &&
                    data.role == "A" && residual.port.output &&
                    residual.port.index == 1 && residual.kind == anchor.kind,
                "anchor became a role-local data read or residual lost its "
                "direction");
        require(
            clauses[4].decision && clauses[4].decision->port.output &&
                clauses[4].decision->port.index == 2 &&
                clauses[4].decision->role == "B" &&
                inventory->statements.front().clause == 4,
            "equal predicates collapsed the selected target or decision role");
        auto selected = inventory->statements.front().statement;
        selected.setTargetAttr(StringAttr::get(&context, "other"));
        inventory = readContracts(reader, symbols);
        require(succeeded(inventory) &&
                    inventory->statements.front().clause == 0,
                "mutation reused a stale selected-target view");
      });
  auto contractRefusal = [&](llvm::StringRef name, llvm::StringRef before,
                             llvm::StringRef after, llvm::StringRef code) {
    cases.run(name, [&] {
      auto module = parse(replace(contractSource(), before, after), context);
      auto unit = *module->getOps<ProtocolModuleOp>().begin();
      auto reader =
          cast<MathematicalOp>(SymbolTable::lookupSymbolIn(unit, "reader"));
      std::string message;
      ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
        message += diagnostic.str();
        return success();
      });
      SymbolTableCollection symbols;
      require(failed(readContracts(reader, symbols)) &&
                  namesIdentifier(message, code),
              "typed contract reader missed refusal: " + message);
    });
  };
  contractRefusal("typed contracts refuse anchor-to-component substitution",
                  "[\"anchor\",\"input\",1:i64]", "[\"input\",1:i64,\"B\"]",
                  "protocol-contract");
  contractRefusal(
      "typed contracts refuse wrong residual direction",
      "[@claimed,[[\"anchor\",\"output\",1:i64]]],[\"output\",2:i64,\"B\"]",
      "[@claimed,[[\"anchor\",\"input\",1:i64]]],[\"output\",2:i64,\"B\"]",
      "protocol-contract");
  contractRefusal("typed contracts refuse unavailable decision role",
                  "[\"output\",2:i64,\"B\"]", "[\"output\",2:i64,\"A\"]",
                  "protocol-contract");
  cases.run("typed contracts refuse a mutated referenced signature", [&] {
    auto module = parse(contractSource(), context);
    auto unit = *module->getOps<ProtocolModuleOp>().begin();
    auto reader =
        cast<MathematicalOp>(SymbolTable::lookupSymbolIn(unit, "reader"));
    auto *relation = SymbolTable::lookupSymbolIn(unit, "claimed");
    relation->setAttr("signature",
                      TypeAttr::get(IntegerType::get(&context, 64)));
    std::string message;
    ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
      message += diagnostic.str();
      return success();
    });
    SymbolTableCollection symbols;
    require(failed(readContracts(reader, symbols)) &&
                namesIdentifier(message, "protocol-contract"),
            "malformed referenced signature reached typed readback: " +
                message);
  });
  contractRefusal("typed contracts refuse unknown selected target",
                  "target=\"selected\"", "target=\"absent\"",
                  "protocol-contract-statement");
  cases.run("typed oracle interface retains the actual paired leaves", [&] {
    auto module = parse(source(), context);
    require(succeeded(zkc::admitStage(*module)), "source formation");
    auto unit = *module->getOps<ProtocolModuleOp>().begin();
    auto reader =
        cast<MathematicalOp>(SymbolTable::lookupSymbolIn(unit, "reader"));
    SymbolTableCollection symbols;
    unsigned remaining = 100000;
    auto layout =
        zkc::mathematical::readOraclePortLayout(reader, symbols, remaining);
    require(succeeded(layout) && layout->inputs.size() == 1 &&
                layout->outputs.size() == 1,
            "missing input/result pair");
    for (const auto *pair : {&layout->inputs.front(), &layout->outputs.front()})
      require(
          pair->data == 0 && pair->anchor == 1 && pair->holder == "A" &&
              pair->receivers ==
                  ArrayAttr::get(&context, {StringAttr::get(&context, "B")}) &&
              pair->type == reader.getBody().front().getArgument(1).getType(),
          "logical pairing differs from admitted ports");
    remaining = 0;
    require(failed(zkc::mathematical::readOraclePortLayout(reader, symbols,
                                                           remaining)),
            "interface work limit ignored");
  });
  cases.run(
      "logical statement entry layout preserves the component-call refusal",
      [&] {
        auto module = parse(R"mlir(
#K = #protocol.oracle_kind<"table", [ui64,4:ui64]>
!H = !protocol.oracle<#K>
!D = !algebra.indices
module { "protocol.module"() ({
 relation.declare @claimed {kind="external",key="test/port-statement",revision="0",signature=(!D)->i1,purposes=["statement"]}
 "protocol.func"() ({
 ^entry(%data:!D,%anchor:!H):
  %handle = "protocol.oracle_input"(%data,%anchor) {holder="A",receivers=["B"],shape_bounds={}} : (!D,!H)->!H
  %accepted = arith.constant true
  "protocol.statement"(%anchor) {relation=@claimed,selectors=["anchor"],target="valid",acceptance=0:i64} : (!H)->()
  "protocol.return"(%accepted) : (i1)->()
 }) {sym_name="reader",function_type=(!D,!H)->i1,roles=["A","B"],input_roles=[["A"],["B"]],output_roles=[["B"]],contracts=[["target","valid",[@claimed,[["anchor","input",1:i64]]],unit,["output",0:i64,"B"]]]} : ()->()
 "protocol.func"() ({
 ^entry(%data:!D):
  %rows = "data.index"() {value=4 : ui64} : ()->ui64
  %handle = "protocol.oracle_send"(%data,%rows) {sender="P",receivers=["V"],site="word",shape_names=["rows"],shape_bounds={}} : (!D,ui64)->!H
  %parts:2 = "protocol.oracle_components"(%handle) {holder="P",receivers=["V"]} : (!H)->(!D,!H)
  %accepted = "protocol.apply"(%parts#0,%parts#1) {callee=@reader,roles=["P","V"],site="check"} : (!D,!H)->i1
  "protocol.return"(%accepted) : (i1)->()
 }) {sym_name="main",function_type=(!D)->i1,roles=["P","V"],input_roles=[["P"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir",
                            context);
        auto unit = *module->getOps<ProtocolModuleOp>().begin();
        auto reader =
            cast<MathematicalOp>(SymbolTable::lookupSymbolIn(unit, "reader"));
        auto anchor = reader.getBody().front().getArgument(1);
        require(isa<StatementOp>(*anchor.getUsers().begin()),
                "fixture must put statement before binder in the use list");
        std::string diagnostics;
        ScopedDiagnosticHandler capture(&context, [&](Diagnostic &message) {
          diagnostics += message.str();
          return success();
        });
        require(failed(zkc::admitStage(*module)) &&
                    diagnostics.find(
                        "entry statement bindings cannot be applied") !=
                        std::string::npos,
                "selected statement entry became an applicable component");
        auto caller =
            cast<MathematicalOp>(SymbolTable::lookupSymbolIn(unit, "main"));
        caller.erase();
        diagnostics.clear();
        require(succeeded(zkc::admitStage(*module)),
                "standalone logical statement entry refused: " + diagnostics);
        SymbolTableCollection symbols;
        unsigned remaining = 100000;
        auto layout =
            zkc::mathematical::readOraclePortLayout(reader, symbols, remaining);
        require(succeeded(layout) && layout->inputs.size() == 1 &&
                    layout->inputs.front().data == 0 &&
                    layout->inputs.front().anchor == 1,
                "logical statement changed the input association");
      });
  cases.run(
      "entry and returned ports retain a paired role family through calls",
      [&] {
        accepted(source(), true);
        accepted(dynamic(), true);
      });
  cases.run(
      "closed oracle family observations preserve sequence projection", [&] {
        auto module = parse(sequenceSource(), context);
        auto unit = *module->getOps<ProtocolModuleOp>().begin();
        auto relay =
            cast<MathematicalOp>(SymbolTable::lookupSymbolIn(unit, "relay"));
        auto sequence =
            cast<OracleSequenceType>(relay.getFunctionType().getInput(1));
        auto handle = OracleHandleType::get(&context, sequence.getKind());
        require(
            getOracleFamilyKind(sequence) == sequence.getKind() &&
                getOracleFamilyKind(handle) == sequence.getKind() &&
                getOracleFamilyDataType(handle) ==
                    sequence.getKind().getDataType() &&
                getOracleFamilyDataType(sequence) ==
                    relay.getFunctionType().getInput(0) &&
                !getOracleFamilyKind(IntegerType::get(&context, 1)) &&
                !getOracleFamilyDataType(IntegerType::get(&context, 1)) &&
                !getOracleFamilyKind(Type{}) &&
                !getOracleFamilyDataType(Type{}),
            "closed family observations lost shape or admitted ordinary data");
      });
  cases.run(
      "internal sequence applications and results retain complete types", [&] {
        accepted(sequenceSource(), true);
        accepted(sequenceSource(true), true);
        auto module = parse(sequenceSource(), context);
        auto unit = *module->getOps<ProtocolModuleOp>().begin();
        auto relay =
            cast<MathematicalOp>(SymbolTable::lookupSymbolIn(unit, "relay"));
        SymbolTableCollection symbols;
        unsigned remaining = 100000;
        auto layout =
            zkc::mathematical::readOraclePortLayout(relay, symbols, remaining);
        require(succeeded(layout) && layout->inputs.size() == 1 &&
                    layout->outputs.size() == 1,
                "sequence interface lacks its actual pair");
        for (const auto *pair :
             {&layout->inputs.front(), &layout->outputs.front()})
          require(pair->data == 0 && pair->anchor == 1 &&
                      pair->type == relay.getFunctionType().getInput(1) &&
                      cast<OracleSequenceType>(pair->type).getMaximum() == 3,
                  "sequence pairing discarded capacity");
        auto capacity =
            zkc::protocol::analyzeOracleQueryCapacity(*module, "relay");
        require(bool(capacity), "sequence source capacity was refused");
        auto input = *relay.getBody().front().getOps<OracleInputOp>().begin();
        auto bound = capacity->constructors.lookup(input.getOperation());
        require(bound.leaves == 3 && bound.nodes == 3,
                "source sequence accounting omitted possible elements");
      });
  cases.run("sequence pairs refuse equal-typed swapped components", [&] {
    refused(replace(sequenceSource(), "\"protocol.apply\"(%parts#0,%parts#1)",
                    "\"protocol.apply\"(%parts#0,%otherParts#1)"));
    refused(replace(sequenceSource(),
                    "\"protocol.oracle_input\"(%result#0,%result#1)",
                    "\"protocol.oracle_input\"(%otherParts#0,%result#1)"));
    refused(replace(sequenceSource(), "\"protocol.return\"(%parts#0,%parts#1)",
                    "\"protocol.return\"(%data,%parts#1)"));
    refused(replace(sequenceSource(), "{holder=\"A\",receivers=[\"B\"]}",
                    "{holder=\"B\",receivers=[\"A\"]}"));
  });
  cases.run("sequence components refuse family and capacity changes", [&] {
    for (unsigned mutation = 0; mutation < 4; ++mutation) {
      auto module = parse(sequenceSource(), context);
      auto unit = *module->getOps<ProtocolModuleOp>().begin();
      auto relay =
          cast<MathematicalOp>(SymbolTable::lookupSymbolIn(unit, "relay"));
      auto input = *relay.getBody().front().getOps<OracleInputOp>().begin();
      auto view = *relay.getBody().front().getOps<OracleComponentsOp>().begin();
      auto type = cast<OracleSequenceType>(input.getHandle().getType());
      if (mutation == 0)
        input.getHandle().setType(
            OracleSequenceType::get(&context, type.getKind(), 4));
      else if (mutation == 1)
        input.getHandle().setType(
            OracleHandleType::get(&context, type.getKind()));
      else if (mutation == 2)
        view.getAnchor().setType(
            OracleSequenceType::get(&context, type.getKind(), 2));
      else
        view.getData().setType(type.getKind().getDataType());
      require(mutation < 2 ? failed(input.verify()) : failed(view.verify()),
              "component verifier ignored the complete family projection");
      require(failed(zkc::admitStage(*module)),
              "mismatched sequence family admitted");
    }
    refused(replace(sequenceSource(true), "shape_bounds={rows=32:ui64}",
                    "shape_bounds={}"));
    refused(replace(sequenceSource(), "shape_bounds={}",
                    "shape_bounds={rows=32:ui64}"));
  });
  cases.run("sequence port shapes follow actual elements and selection", [&] {
    auto text = replace(sequenceSource(true), "  %contents =", R"mlir(
  %selectedRows = "protocol.oracle_shape"(%selected) {dimension="rows"} : (!H)->ui64
  %next = "protocol.oracle_send"(%data,%selectedRows) {sender="P",receivers=["V"],site="next",shape_names=["rows"],shape_bounds={rows=32:ui64}} : (!D,ui64)->!H
  %contents =)mlir");
    accepted(text, true);
    text = replace(text, "  %selected =", R"mlir(
  %answerPosition = "protocol.oracle_query"(%first,%position) {owner="V",site="choose"} : (!H,ui64)->ui64
  %selected =)mlir");
    auto module = parse(text, context);
    OracleSequenceAtOp selected;
    OracleQueryOp query;
    OracleShapeOp shape;
    module->walk([&](OracleSequenceAtOp op) { selected = op; });
    module->walk([&](OracleQueryOp op) {
      if (op.getSite() == "choose")
        query = op;
    });
    module->walk([&](OracleShapeOp op) { shape = op; });
    require(selected && query && shape, "missing sequence shape dependencies");
    // This read checks shape dependency only; ordinary role availability is
    // independently required by full protocol admission.
    selected.getPositionMutable().set(query.getAnswer());
    SymbolTableCollection symbols;
    unsigned remaining = 100000;
    require(failed(zkc::mathematical::verifyInitialOracleShape(
                shape.getExtent(), shape->getParentOfType<MathematicalOp>(),
                shape, symbols, remaining)),
            "query-selected sequence dimensions became initial configuration");
  });
  cases.run("prepared sequence rebindings allocate no fresh anchors", [&] {
    auto original = parse(sequenceSource(true), context);
    auto prepared = zkc::mathematical::prepareProtocol(*original, false);
    require(bool(prepared), "sequence preparation failed");
    bool application = false;
    prepared->walk([&](ApplyOp) { application = true; });
    require(!application,
            "preparation left an unexpanded sequence application");
    auto storage = zkc::protocol::planOracleAnchorStorage(
        *prepared, "example", [](const auto &) -> llvm::Expected<std::string> {
          return std::string();
        });
    require(bool(storage) && storage->constructors.size() == 2,
            "sequence rebinding allocated an occurrence anchor");
    for (const auto &constructor : storage->constructors)
      require(constructor.constructor ==
                  zkc::protocol::OracleAnchorConstructor::Kind::Send,
              "sequence rebinding replaced the actual constructor inventory");
  });
  cases.run(
      "prepared sequence correspondence preserves order and multiplicity", [&] {
        auto original = parse(sequenceSource(), context);
        auto prepared = zkc::mathematical::prepareProtocol(*original, false);
        require(bool(prepared), "sequence preparation failed");
        OracleComponentsOp other;
        OracleInputOp rebound;
        prepared->walk([&](OracleComponentsOp view) {
          auto append =
              view.getHandle().getDefiningOp<OracleSequenceAppendOp>();
          if (append && append.getSite() == "other")
            other = view;
        });
        prepared->walk([&](OracleInputOp input) {
          if (!rebound &&
              input->getParentOfType<MathematicalOp>().getSymName() ==
                  "example")
            rebound = input;
        });
        require(other && rebound, "missing prepared sequence pair");
        rebound.getDataMutable().set(other.getData());
        rebound.getAnchorMutable().set(other.getAnchor());
        require(succeeded(zkc::admitStage(*prepared)),
                "pair-preserving sequence mutation lost formation");
        require(
            failed(zkc::mathematical::verifyProtocolPreparationPreserved(
                &original->getBody()->front(), &prepared->getBody()->front())),
            "a different equal-length sequence passed preparation "
            "correspondence");
      });
  cases.run(
      "sequence rebinding checks metadata without demanding holder data", [&] {
        for (bool dynamic : {false, true}) {
          auto original = parse(sequenceSource(dynamic), context);
          auto owner = zkc::mathematical::PreparedProtocol::prepare(*original);
          require(bool(owner) && succeeded(owner->selectEntries({"example"})),
                  "sequence deployment preparation failed");
          auto prepared = owner->snapshot();
          auto authored = owner->originalSnapshot();
          auto originalUnit = *authored->getOps<ProtocolModuleOp>().begin();
          require(SymbolTable::lookupSymbolIn(originalUnit, "relay"),
                  "deployment selection lost the original library declaration");
          auto emitted = take(zkc::protocol::emitOracleRealization(*prepared));
          auto record = take(
              zkc::protocol::serializeOracleRealization(*prepared, emitted));
          if (auto error = zkc::protocol::checkOracleRealization(
                  *prepared, *emitted.module, record))
            throw std::runtime_error(llvm::toString(std::move(error)));
          unsigned capacities = 0, rows = 0, data = 0;
          emitted.module->walk([&](zkc::protocol_ir::LocalCallOp call) {
            auto site = call.getSite();
            capacities += site.contains("sequence_capacity");
            rows += site.contains("element_shape");
            data += site.contains("component_data") ||
                    site.contains("component_element");
          });
          require(capacities == 4 && rows == (dynamic ? 4u : 0u) && !data,
                  "sequence rebinding lost capacity/element checks or demanded "
                  "all data");
        }
      });
  cases.run(
      "sequence results record the complete type and demand data explicitly",
      [&] {
        auto text = replace(
            sequenceSource(), "\"protocol.return\"(%value) : (ui64)->()",
            "\"protocol.return\"(%parts#0,%parts#1) : (!DS,!S)->()");
        text = replace(text, "function_type=(!D,ui64,ui64)->ui64",
                       "function_type=(!D,ui64,ui64)->(!DS,!S)");
        text = replace(text, "output_roles=[[\"V\"]]",
                       "output_roles=[[\"P\"],[\"V\"]]");
        auto original = parse(text, context);
        auto owner = zkc::mathematical::PreparedProtocol::prepare(*original);
        require(bool(owner) && succeeded(owner->selectEntries({"example"})),
                "sequence-result deployment preparation failed");
        auto prepared = owner->snapshot();
        auto emitted = take(zkc::protocol::emitOracleRealization(*prepared));
        auto record =
            take(zkc::protocol::serializeOracleRealization(*prepared, emitted));
        auto description = take(llvm::json::parse(record));
        auto *entries = description.getAsObject()->getArray("entries");
        require(entries && entries->size() == 1,
                "missing sequence-result entry");
        auto *logical =
            entries->front().getAsObject()->getObject("logical_interface");
        auto *outputs = logical ? logical->getArray("outputs") : nullptr;
        require(outputs && outputs->size() == 1,
                "missing sequence-result pair");
        auto *pair = outputs->front().getAsObject();
        require(pair && pair->getInteger("type") && !pair->get("kind"),
                "sequence record kept a kind-only pair or compatibility alias");
        require(emitted.entries.front().resultReferences.size() == 1 &&
                    !emitted.entries.front().resultStores.empty(),
                "sequence result lost its reference support stores");
        unsigned demanded = 0;
        emitted.module->walk([&](LocalCallOp call) {
          demanded += call.getSite().contains("component_element");
        });
        require(demanded == 1,
                "explicit sequence data demand lacks its ordered traversal");
      });
  cases.run(
      "sequence metadata traversal refuses an unsupported native capacity",
      [&] {
        auto original = parse(replace(sequenceSource(true),
                                      "!protocol.oracle_sequence<#K, 3>",
                                      "!protocol.oracle_sequence<#K, 1048577>"),
                              context);
        auto owner = zkc::mathematical::PreparedProtocol::prepare(*original);
        require(bool(owner) && succeeded(owner->selectEntries({"example"})),
                "large logical sequence deployment was refused");
        auto prepared = owner->snapshot();
        auto emitted = zkc::protocol::emitOracleRealization(*prepared);
        require(!emitted,
                "native sequence traversal silently narrowed its capacity");
        require(namesIdentifier(llvm::toString(emitted.takeError()),
                                "oracle-common-limit"),
                "unsupported native traversal did not name its refusal");
      });
  cases.run("deployment selection is explicit, atomic and retains source", [&] {
    auto original = parse(sequenceSource(), context);
    auto owner = zkc::mathematical::PreparedProtocol::prepare(*original);
    require(bool(owner), "deployment preparation failed");
    auto count = [&] {
      auto current = owner->snapshot();
      auto unit = *current->getOps<ProtocolModuleOp>().begin();
      return std::distance(unit.getBody().front().getOps<MathematicalOp>().begin(),
                           unit.getBody().front().getOps<MathematicalOp>().end());
    };
    require(failed(owner->selectEntries({})) && count() == 2 &&
                failed(owner->selectEntries({"absent"})) && count() == 2 &&
                failed(owner->selectEntries({"example", "example"})) &&
                count() == 2,
            "invalid deployment selection changed its prepared owner");
    require(succeeded(owner->selectEntries({"example", "relay"})) && count() == 2,
            "explicit companion entry was lost");
    require(succeeded(owner->selectEntries({"example"})) && count() == 1,
            "expanded internal declaration became a deployment root");
    auto authored = owner->originalSnapshot();
    auto unit = *authored->getOps<ProtocolModuleOp>().begin();
    require(SymbolTable::lookupSymbolIn(unit, "relay"),
            "full source provenance was pruned");
  });
  cases.run("root Host sequence ingress is explicitly refused", [&] {
    auto module = parse(sequenceSource(), context);
    require(succeeded(zkc::admitStage(*module)),
            "logical sequence declaration refused");
    auto storage = zkc::protocol::planOracleAnchorStorage(
        *module, "relay", [](const auto &) -> llvm::Expected<std::string> {
          return std::string();
        });
    require(!storage, "root Host sequence ingress acquired storage");
    require(namesIdentifier(llvm::toString(storage.takeError()),
                            "oracle-common-interface"),
            "root sequence ingress did not name its explicit refusal");
  });
  cases.run(
      "remote input and returned ports retain dynamic helper handles", [&] {
        for (bool unsized : {false, true}) {
          auto original = parse(unsized ? dynamic() : source(), context);
          auto owner = zkc::mathematical::PreparedProtocol::prepare(*original);
          require(bool(owner) && succeeded(owner->selectEntries({"reader"})),
                  "remote port preparation failed");
          auto prepared = owner->snapshot();
          zkc::protocol::OracleRealizationPolicy policy;
          policy.roots = take(zkc::protocol::resolveOracleRealizationSelection(
              *prepared, policy));
          auto &roots =
              std::get<std::vector<zkc::protocol::OracleRootSelection>>(
                  policy.roots);
          require(roots.size() == 1, "remote input allocated another anchor");
          roots.front().realization = {
              "rows.merkle-keccak256.koala-bear/0",
              zkc::protocol::OracleLeafGrouping::AntipodalPairs,
              zkc::protocol::OracleLeafOrder::Natural};
          auto candidate =
              take(zkc::protocol::emitOracleRealization(*prepared, policy));
          auto record = take(zkc::protocol::serializeOracleRealization(
              *prepared, candidate, policy));
          require(candidate.entries.size() == 1,
                  "wrong remote deployment inventory");
          const auto &entry = candidate.entries.front();
          require(entry.entry == "reader" && entry.remotes.size() == 1 &&
                      entry.batches.size() == 1 &&
                      entry.batches.front().remotes ==
                          std::vector<unsigned>{0} &&
                      entry.remotes.front().window.capacity == 1 &&
                      entry.inputShapes.size() == unsigned(unsized) &&
                      !entry.resultStores.empty() &&
                      entry.resultReferences.size() == 1,
                  "dynamic helpers changed logical input/result associations");
          std::string text;
          llvm::raw_string_ostream stream(text);
          candidate.module->print(stream);
          auto fresh = parse(text, context);
          if (auto error = zkc::protocol::checkOracleRealization(
                  *prepared, *fresh, record, policy))
            throw std::runtime_error(llvm::toString(std::move(error)));
          auto encoded = take(llvm::json::parse(record));
          auto &row = *encoded.getAsObject()
                           ->getArray("entries")
                           ->front()
                           .getAsObject();
          auto &logical = *row.getObject("logical_interface");
          auto &inputs = *logical.getArray("inputs");
          auto &outputs = *logical.getArray("outputs");
          require(inputs.size() == 1 && outputs.size() == 1 &&
                      inputs.front().getAsObject()->getInteger("anchor") == 1 &&
                      outputs.front().getAsObject()->getInteger("anchor") == 1,
                  "remote realization changed original port positions");
          auto &remote = *row.getArray("remotes")->front().getAsObject();
          // Every primitive is decoded using the fresh candidate's symbol
          // table. A source signature or same-typed function cannot fill
          // another slot.
          (*remote.getObject("demand"))["initialize"] = "reader";
          std::string changed;
          llvm::raw_string_ostream(changed) << encoded;
          auto error = zkc::protocol::checkOracleRealization(*prepared, *fresh,
                                                             changed, policy);
          require(bool(error), "source program accepted as a demand helper");
          require(namesIdentifier(llvm::toString(std::move(error)),
                                  "oracle-realization-record"),
                  "foreign helper did not refuse at strict symbol lookup");
        }
      });
  cases.run(
      "raw handle entries require unique bindings and exact role leaves", [&] {
        refused(replace(source(),
                        "\"protocol.oracle_contents\"(%word) {owner=\"A\"}",
                        "\"protocol.oracle_contents\"(%anchor) {owner=\"A\"}"));
        refused(replace(source(), "input_roles=[[\"A\"],[\"B\"]",
                        "input_roles=[[\"A\",\"B\"],[\"B\"]"));
        refused(replace(source(), "input_roles=[[\"A\"],[\"B\"]",
                        "input_roles=[[\"A\"],[\"A\",\"B\"]"));
        refused(replace(source(), "{owner=\"A\"}", "{owner=\"B\"}"));
        refused(replace(source(), "{holder=\"A\",receivers=[\"B\"]}",
                        "{holder=\"B\",receivers=[\"A\"]}"));
        refused(replace(source(), "    %contents =", R"mlir(
    %extra = "protocol.oracle_input"(%data,%anchor) {shape_bounds={},holder="A",receivers=["B"]} : (!D,!H)->!H
    %contents =)mlir"));
      });
  cases.run(
      "root bindings precede protocol effects and remain when unused", [&] {
        refused(
            replace(source(), "    %word = \"protocol.oracle_input\"", R"mlir(
    %early = "protocol.oracle_send"(%data,%rows) {shape_names=["rows"],shape_bounds={},sender="A",receivers=["B"],site="early"} : (!D,ui64)->!H
    %word = "protocol.oracle_input")mlir"));
        auto original = parse(source(), context);
        auto candidate = zkc::mathematical::prepareProtocol(*original);
        require(bool(candidate), "root preparation failed");
        unsigned bindings = 0;
        candidate->walk([&](OracleInputOp) { ++bindings; });
        require(bindings == 3, "preparation dropped an input or rebound check");
      });
  cases.run("calls and result tuples cannot mix equal-typed components", [&] {
    refused(replace(source(), "\"protocol.apply\"(%parts#0,%parts#1",
                    "\"protocol.apply\"(%data,%parts#1"));
    refused(replace(source(), "\"protocol.return\"(%parts#0,%parts#1,%value)",
                    "\"protocol.return\"(%contents,%parts#1,%value)"));
    refused(replace(source(), "\"protocol.return\"(%parts#0,%parts#1,%value)",
                    "\"protocol.return\"(%parts#0,%word,%value)"));
    refused(replace(source(), "\"protocol.oracle_input\"(%result#0,%result#1",
                    "\"protocol.oracle_input\"(%parts#0,%result#1"));
    auto two = replace(source(), "    %result:3 =", R"mlir(
    %other = "protocol.oracle_send"(%data,%rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="other"} : (!D,ui64)->!H
    %otherParts:2 = "protocol.oracle_components"(%other) {holder="P",receivers=["V"]} : (!H)->(!D,!H)
    %result:3 =)mlir");
    accepted(two);
    refused(replace(two, "\"protocol.apply\"(%parts#0,%parts#1",
                    "\"protocol.apply\"(%parts#0,%otherParts#1"));
  });
  cases.run("shape reads preserve initial input and send dependencies", [&] {
    auto text = replace(dynamic(), "    %result:3 =", R"mlir(
    %actualRows = "protocol.oracle_shape"(%word) {dimension="rows"} : (!H)->ui64
    %next = "protocol.oracle_send"(%data,%actualRows) {shape_names=["rows"],sender="P",receivers=["V"],site="next",shape_bounds={rows=32:ui64}} : (!D,ui64)->!H
    %result:3 =)mlir");
    accepted(text, true);
    auto returnedShape = replace(
        dynamic(), "    %contents = \"protocol.oracle_contents\"(%returned)",
        R"mlir(
    %actualRows = "protocol.oracle_shape"(%returned) {dimension="rows"} : (!H)->ui64
    %next = "protocol.oracle_send"(%data,%actualRows) {shape_names=["rows"],sender="P",receivers=["V"],site="next",shape_bounds={rows=32:ui64}} : (!D,ui64)->!H
    %contents = "protocol.oracle_contents"(%returned))mlir");
    accepted(returnedShape, true);
    auto malformed = parse(source(), context);
    malformed->walk([&](OracleInputOp input) {
      input.setShapeBoundsAttr(DictionaryAttr::get(
          &context, {NamedAttribute(StringAttr::get(&context, "rows"),
                                    IntegerAttr::get(
                                        IntegerType::get(&context, 64,
                                                         IntegerType::Unsigned),
                                        32))}));
    });
    require(failed(zkc::admitStage(*malformed)),
            "sized input accepted a second row maximum");
    auto unsized = dynamic();
    refused(replace(unsized, "shape_bounds={rows=32:ui64},", ""));
  });
  cases.run(
      "unsized selection preserves answer-dependent shape information", [&] {
        auto text = replace(
            dynamic(), "!H = !protocol.oracle<#K>",
            "!H = !protocol.oracle<#K>\n!S = !protocol.oracle_sequence<#K, 2>");
        size_t at = 0;
        const std::string field = "!algebra.field<\"koala-bear\">";
        while ((at = text.find(field)) != std::string::npos)
          text.replace(at, field.size(), "ui64");
        text = replace(text, "!algebra.field_vector<\"koala-bear\">",
                       "!algebra.indices");
        text = replace(text, "    %result:3 =", R"mlir(
    %selector = "protocol.oracle_query"(%word,%position) {owner="V",site="selector"} : (!H,ui64)->!F
    %empty = "protocol.oracle_sequence_empty"() : ()->!S
    %sequence = "protocol.oracle_sequence_append"(%empty,%word) {roles=["V"],site="append"} : (!S,!H)->!S
    %selected = "protocol.oracle_sequence_at"(%sequence,%selector) {roles=["V"],site="select"} : (!S,ui64)->!H
    %selectedRows = "protocol.oracle_shape"(%selected) {dimension="rows"} : (!H)->ui64
    %result:3 =)mlir");
        auto module = parse(text, context);
        require(succeeded(zkc::admitStage(*module)),
                "dynamic selection fixture refused");
        OracleQueryOp query;
        OracleShapeOp rows;
        module->walk([&](OracleQueryOp op) {
          if (op.getSite() == "selector")
            query = op;
        });
        module->walk([&](OracleShapeOp op) { rows = op; });
        SymbolTableCollection symbols;
        auto program = rows->getParentOfType<MathematicalOp>();
        unsigned remaining = 1000;
        require(query && rows &&
                    failed(zkc::mathematical::verifyInitialOracleShape(
                        rows.getExtent(), program, rows, symbols, remaining)),
                "answer-selected dimensions became initial configuration");
        auto selection = rows.getHandle().getDefiningOp<OracleSequenceAtOp>();
        selection.getPositionMutable().set(query.getPosition());
        remaining = 1000;
        require(succeeded(zkc::mathematical::verifyInitialOracleShape(
                    rows.getExtent(), program, rows, symbols, remaining)),
                "initially selected dimensions were refused");
        remaining = 0;
        require(failed(zkc::mathematical::verifyInitialOracleShape(
                    rows.getExtent(), program, rows, symbols, remaining)),
                "exhausted shape analysis admitted another traversal");
      });
  cases.run(
      "shape substitution distinguishes two calls to the same declaration",
      [&] {
        auto text = source();
        const std::string field = "!algebra.field<\"koala-bear\">";
        size_t at;
        while ((at = text.find(field)) != std::string::npos)
          text.replace(at, field.size(), "ui64");
        text = replace(text, "!algebra.field_vector<\"koala-bear\">",
                       "!algebra.indices");
        text = replace(text, "  \"protocol.func\"()", R"mlir(
    func.func private @choose(%a:ui64,%b:ui64)->ui64 { return %a : ui64 }
    "protocol.func"())mlir");
        text = replace(text, "\"protocol.return\"(%parts#0,%parts#1,%value)",
                       "\"protocol.return\"(%parts#0,%parts#1,%position)");
        text = replace(text, "    \"protocol.return\"(%value)", R"mlir(
    %later:3 = "protocol.apply"(%parts#0,%parts#1,%rows,%value) {callee=@reader,roles=["P","V"],site="later"} : (!D,!H,ui64,ui64)->(!D,!H,!F)
    %shape = func.call @choose(%later#2,%result#2) : (ui64,ui64)->ui64
    "protocol.return"(%value))mlir");
        auto module = parse(text, context);
        require(succeeded(zkc::admitStage(*module)),
                "repeated-call shape fixture refused");
        func::CallOp shape;
        ApplyOp later;
        module->walk([&](func::CallOp op) { shape = op; });
        module->walk([&](ApplyOp op) {
          if (op.getSite() == "later")
            later = op;
        });
        require(shape && later, "missing repeated call controls");
        auto program = shape->getParentOfType<MathematicalOp>();
        SymbolTableCollection symbols;
        unsigned remaining = 1000;
        require(failed(zkc::mathematical::verifyInitialOracleShape(
                    shape.getResult(0), program, shape, symbols, remaining)),
                "an earlier application hid a later query-dependent actual "
                "argument");
        later.setOperand(3, program.getBody().front().getArgument(2));
        remaining = 1000;
        require(succeeded(zkc::mathematical::verifyInitialOracleShape(
                    shape.getResult(0), program, shape, symbols, remaining)),
                "initial actual arguments failed shape substitution");
      });
  cases.run(
      "preparation checks actual paired operands after role substitution", [&] {
        auto text = replace(source(), "    %result:3 =", R"mlir(
    %other = "protocol.oracle_send"(%data,%rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="other"} : (!D,ui64)->!H
    %otherParts:2 = "protocol.oracle_components"(%other) {holder="P",receivers=["V"]} : (!H)->(!D,!H)
    %result:3 =)mlir");
        auto original = parse(text, context);
        auto candidate = zkc::mathematical::prepareProtocol(*original, false);
        require(bool(candidate), "candidate preparation failed");
        OracleComponentsOp other;
        OracleInputOp selected;
        candidate->walk([&](OracleComponentsOp view) {
          auto send = view.getHandle().getDefiningOp<OracleSendOp>();
          if (send && send.getSite() == "other")
            other = view;
        });
        candidate->walk([&](OracleInputOp input) {
          if (!selected &&
              input->getParentOfType<MathematicalOp>().getSymName() ==
                  "example")
            selected = input;
        });
        require(other && selected, "missing prepared port components");
        selected.getDataMutable().set(other.getData());
        selected.getAnchorMutable().set(other.getAnchor());
        require(succeeded(zkc::admitStage(*candidate)),
                "pair-preserving mutation lost formation");
        require(
            failed(zkc::mathematical::verifyProtocolPreparationPreserved(
                &original->getBody()->front(), &candidate->getBody()->front())),
            "different equal-data anchor passed preparation correspondence");
      });
  return cases.result();
}
