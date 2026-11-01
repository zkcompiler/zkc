#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Analysis/MathematicalFacts.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
using facts::Precision;
using facts::Status;
std::string source(StringRef declarations) {
  return R"mlir(
!S = !data.sequence<i1>
!F = !algebra.field<"bls12-381.fr">
!V = !data.field_vector<"bls12-381.fr">
!A = !data.field_array<"bls12-381.fr", 4>
!M = !data.field_matrix<"bls12-381.fr">
module { "protocol.module"() ({
)mlir" + declarations.str() +
         R"mlir(
 "protocol.func"() ({ ^entry(%xs:!S):
   "protocol.return"(%xs) : (!S)->()
 }) {sym_name="main",function_type=(!S)->!S,roles=["P"],
     input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
}
func::FuncOp helper(ModuleOp module, StringRef name) {
  func::FuncOp result;
  module.walk([&](func::FuncOp op) {
    if (op.getSymName() == name)
      result = op;
  });
  require(bool(result), "missing helper " + name);
  return result;
}
SmallVector<Value> returned(func::FuncOp helper) {
  return SmallVector<Value>(helper.getBody().front().back().getOperands());
}
void exact(MathematicalFactAnalysis &analysis, Value value, uint64_t expected,
           facts::Work &work) {
  auto result = analysis.extent(value, 0, work);
  require(result.status == Status::Proven && result.value == expected,
          "exact extent missing or incorrect");
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  auto parse = [&](StringRef declarations) {
    auto module = parseSourceString<ModuleOp>(source(declarations), &context);
    require(bool(module), "valid mathematical fact fixture refused");
    return module;
  };
  cases.run(
      "many formation premises retain direct and transferred bounds", [&] {
        constexpr unsigned count = 256;
        std::string declarations = "func.func private @subject(%i:ui64";
        for (unsigned i = 0; i < count; ++i)
          declarations += ",%x" + std::to_string(i) + ":!V";
        declarations += ")->!F attributes {data.preconditions=["
                        "#data.index_bound<0,1,0>";
        for (unsigned i = 1; i < count; ++i)
          declarations += ",#data.equal_extent<" + std::to_string(i) + ",0," +
                          std::to_string(i + 1) + ",0>";
        declarations += "]} {\n"
                        "%read = \"data.bounded_at\"(%x0,%i) : (!V,ui64)->!F\n"
                        "func.return %read : !F\n}";
        auto module = parse(declarations);
        require(succeeded(verify(*module)),
                "valid direct bound program refused");
        auto subject = helper(*module, "subject");
        MathematicalFactAnalysis analysis(*module);
        uint64_t remaining = 65536;
        facts::Work work(remaining);
        require(analysis.bound(subject.getArgument(0), subject.getArgument(1),
                               0, work) == Status::Proven,
                "many unrelated premises exhausted a direct formation bound");
        require(analysis.bound(subject.getArgument(0),
                               subject.getArgument(count), 0,
                               work) == Status::Proven &&
                    !work.exhausted(),
                "linear equality chain lost its transferred bound");
        require(analysis.extent(subject.getArgument(count), 0, work).status ==
                        Status::Unknown &&
                    !work.exhausted(),
                "symbolic premises invented a count or exhausted its query");
      });
  cases.run("helper observations ignore unread bodies and cache warmth", [&] {
    auto fixture = [&](unsigned unused) {
      std::string declarations;
      for (StringRef name : {"forward", "make"}) {
        declarations +=
            "func.func private @" + name.str() + "(%s:!S,%flag:i1)->!S {\n";
        for (unsigned i = 0; i < unused; ++i)
          declarations += "%unused" + std::to_string(i) +
                          " = \"data.index\"() {value=0 : ui64} : ()->ui64\n";
        if (name == "make")
          declarations += "%empty = \"data.sequence_empty\"() : ()->!S\n"
                          "%next = \"data.sequence_append\"(%empty,%flag)"
                          " : (!S,i1)->!S\nfunc.return %next : !S\n}\n";
        else
          declarations += "func.return %s : !S\n}\n";
      }
      declarations += R"mlir(
 func.func private @subject(%s:!S,%flag:i1)->(!S,!S) {
   %a = func.call @forward(%s,%flag) : (!S,i1)->!S
   %b = func.call @make(%s,%flag) : (!S,i1)->!S
   func.return %a,%b : !S,!S
 }
)mlir";
      return parse(declarations);
    };
    auto quiet = fixture(0), busy = fixture(512);
    auto cost = [&](MathematicalFactAnalysis &analysis, ModuleOp module) {
      auto subject = helper(module, "subject");
      auto values = returned(subject);
      uint64_t remaining = 65536;
      facts::Work work(remaining);
      require(analysis.origin(values[0], work).value == subject.getArgument(0),
              "helper return forwarding lost");
      exact(analysis, values[1], 1, work);
      return 65536 - remaining;
    };
    MathematicalFactAnalysis quietAnalysis(*quiet), busyAnalysis(*busy);
    auto expected = cost(quietAnalysis, *quiet);
    require(cost(quietAnalysis, *quiet) == expected &&
                cost(busyAnalysis, *busy) == expected &&
                cost(busyAnalysis, *busy) == expected,
            "logical observation cost depends on cache warmth or unread body");
    busyAnalysis.clear();
    require(cost(busyAnalysis, *busy) == expected,
            "clear changed the logical observation cost");
  });
  cases.run("public queries preserve their caller's consumed depth", [&] {
    auto module = parse(R"mlir(
 func.func private @subject(%xs:!A)->ui64 {
   %i = "data.index"() {value=0 : ui64} : ()->ui64
   func.return %i : ui64
 }
)mlir");
    auto subject = helper(*module, "subject");
    Value xs = subject.getArgument(0), i = returned(subject)[0];
    MathematicalFactAnalysis analysis(*module);
    for (unsigned depth : {256u, 257u})
      for (unsigned query = 0; query < 6; ++query) {
        uint64_t remaining = 65536;
        facts::Work work(remaining);
        Status status = Status::Unknown;
        switch (query) {
        case 0:
          status = analysis.origin(xs, work, depth).status;
          break;
        case 1:
          status = analysis.integer(i, work, depth).status;
          break;
        case 2:
          status = analysis.extent(xs, 0, work, depth).status;
          break;
        case 3:
          status = analysis.cardinality(xs, 0, work, depth).status;
          break;
        case 4:
          status = analysis.equalExtent(xs, 0, xs, 0, work, depth);
          break;
        case 5:
          status = analysis.bound(i, xs, 0, work, depth);
          break;
        }
        require(status == (depth == 256 ? Status::Proven : Status::Capacity),
                "query reset or over-counted the inherited depth");
        require(work.exhausted() == (depth > 256) && remaining > 65000,
                "depth capacity reset or drained the shared work counter");
      }
  });
  cases.run("status wrappers retain exact work boundaries", [&] {
    auto module = parse(R"mlir(
 func.func private @subject(%xs:!V,%i:ui64)->!V attributes {
   data.preconditions=[#data.index_bound<1,0,0>]
 } { func.return %xs : !V }
)mlir");
    auto subject = helper(*module, "subject");
    auto xs = subject.getArgument(0), i = subject.getArgument(1);
    uint64_t remaining = 65536;
    require(finite::boundStatus(i, xs, 0, remaining) == Status::Proven,
            "status wrapper lost direct evidence");
    auto cost = 65536 - remaining;
    remaining = cost;
    require(finite::boundStatus(i, xs, 0, remaining) == Status::Proven &&
                remaining == 0,
            "successful final charge was reported as capacity");
    remaining = cost - 1;
    require(finite::boundStatus(i, xs, 0, remaining) == Status::Capacity &&
                remaining == 0,
            "failed final charge was reported as unknown");
    remaining = 1;
    require(finite::equalExtentStatus(xs, 0, xs, 0, remaining) ==
                    Status::Proven &&
                remaining == 0,
            "reflexive status query lost its exact one-unit boundary");
  });
  for (StringRef operation : {"lookup", "matrix lookup", "call"})
    cases.run(
        "mandatory " + operation + " reports capacity separately from unknown",
        [&] {
          bool call = operation == "call",
               matrix = operation == "matrix lookup";
          std::string container = matrix ? "!M" : "!S";
          std::string element = matrix ? "!F" : "i1";
          auto lookup = [&](StringRef input) {
            return std::string(matrix ? "\"data.bounded_matrix_at\"("
                                      : "\"data.bounded_at\"(") +
                   input.str() + (matrix ? ",%i,%i) : (" : ",%i) : (") +
                   container + (matrix ? ",ui64,ui64)->" : ",ui64)->") +
                   element;
          };
          std::string premises = "attributes {data.preconditions=["
                                 "#data.index_bound<1,0,0>";
          if (matrix)
            premises += ",#data.index_bound<1,0,1>";
          premises += "]}";
          auto fixture = [&](unsigned length) {
            std::string declarations =
                "func.func private @identity(%s:" + container + ")->" +
                container + " { func.return %s : " + container + " }\n" +
                "func.func private @read(%s:" + container + ",%i:ui64)->" +
                element + " " + premises + " {\n%x = " + lookup("%s") +
                "\nfunc.return %x : " + element + "\n}\n" +
                "func.func private @subject(%s:" + container + ",%i:ui64)->" +
                element + " ";
            if (length)
              declarations += premises;
            declarations += " {\n";
            std::string previous = "%s";
            for (unsigned i = 0; i < length; ++i) {
              auto next = "%v" + std::to_string(i);
              declarations += next + " = func.call @identity(" + previous +
                              ") : (" + container + ")->" + container + "\n";
              previous = next;
            }
            declarations += "%result = " +
                            (call ? "func.call @read(" + previous + ",%i) : (" +
                                        container + ",ui64)->" + element
                                  : lookup(previous)) +
                            "\nfunc.return %result : " + element + "\n}";
            return declarations;
          };
          for (unsigned length : {0u, 257u}) {
            SmallVector<std::string> codes;
            ScopedDiagnosticHandler capture(
                &context, [&](Diagnostic &diagnostic) {
                  for (auto &refusal : diagnostics::refusals(diagnostic))
                    codes.push_back(refusal.code);
                  return success();
                });
            auto module =
                parseSourceString<ModuleOp>(source(fixture(length)), &context);
            StringRef expected =
                length ? "finite-analysis-limit" : "finite-bound";
            require((!module || failed(admitStage(*module))) &&
                        llvm::is_contained(codes, expected.str()),
                    "mandatory check lost its status-specific diagnostic " +
                        expected);
            require(!llvm::is_contained(codes, length
                                                   ? "finite-bound"
                                                   : "finite-analysis-limit"),
                    "capacity and absent evidence diagnostics were conflated");
          }
        });
  cases.run("exact identity differs from reconstruction and equal shape", [&] {
    auto module = parse(R"mlir(
 func.func private @second(%a:!S,%b:!S)->!S { func.return %b : !S }
 func.func private @make()->!S {
   %s = "data.sequence_empty"() : ()->!S
   func.return %s : !S
 }
 func.func private @subject(%x:!S,%y:!S)->(!S,!S,!S,!S) {
   %forward = func.call @second(%x,%y) : (!S,!S)->!S
   %alias = func.call @second(%x,%x) : (!S,!S)->!S
   %a = func.call @make() : ()->!S
   %b = func.call @make() : ()->!S
   func.return %forward,%alias,%a,%b : !S,!S,!S,!S
 }
)mlir");
    auto subject = helper(*module, "subject");
    auto values = returned(subject);
    MathematicalFactAnalysis analysis(*module);
    uint64_t remaining = 65536;
    facts::Work work(remaining);
    require(analysis.origin(values[0], work).value == subject.getArgument(1),
            "formal order changed while forwarding");
    require(analysis.origin(values[1], work).value == subject.getArgument(0),
            "aliased actuals lost exact forwarding");
    require(analysis.origin(values[2], work).value == values[2] &&
                analysis.origin(values[3], work).value == values[3],
            "constructor invocations acquired a shared value identity");
    require(analysis.equalExtent(values[2], 0, values[3], 0, work) ==
                Status::Proven,
            "equal constructor extents were lost");
    require(analysis.equalExtent(subject.getArgument(0), 0,
                                 subject.getArgument(1), 0,
                                 work) == Status::Unknown,
            "distinct unknown inputs acquired equal extent");
  });
  cases.run("constructor actual substitution and helper rebuild", [&] {
    auto module = parse(R"mlir(
 func.func private @append(%s:!S,%flag:i1)->!S {
   %next = "data.sequence_append"(%s,%flag) : (!S,i1)->!S
   func.return %next : !S
 }
 func.func private @subject(%flag:i1)->!S {
   %empty = "data.sequence_empty"() : ()->!S
   %a = func.call @append(%empty,%flag) : (!S,i1)->!S
   %b = func.call @append(%a,%flag) : (!S,i1)->!S
   func.return %b : !S
 }
)mlir");
    auto subject = helper(*module, "subject");
    auto result = returned(subject)[0];
    MathematicalFactAnalysis analysis(*module);
    uint64_t remaining = 65536;
    facts::Work work(remaining);
    exact(analysis, result, 2, work);
    auto append = helper(*module, "append");
    append.getBody().front().back().setOperand(0, append.getArgument(0));
    require(succeeded(verify(*module)), "changed valid helper refused");
    analysis.clear();
    exact(analysis, result, 0, work);
    auto origin = analysis.origin(result, work);
    require(origin.value &&
                (*origin.value).getDefiningOp<data::SequenceEmptyOp>(),
            "rebuilt helper forwarding did not inspect changed return");
    MathematicalFactAnalysis rebuilt(*module);
    exact(rebuilt, result, 0, work);
  });
  cases.run("formation equality closure and selected matrix axes", [&] {
    auto module = parse(R"mlir(
 func.func private @subject(%i:ui64,%a:!M,%b:!M,%c:!M)->ui64 attributes {
   data.preconditions=[#data.index_bound<0,1,0>,
     #data.equal_extent<1,0,2,1>,#data.equal_extent<2,1,3,0>]
 } { func.return %i : ui64 }
 func.func private @other(%i:ui64,%a:!M)->ui64 { func.return %i : ui64 }
)mlir");
    auto subject = helper(*module, "subject"), other = helper(*module, "other");
    MathematicalFactAnalysis analysis(*module);
    uint64_t remaining = 65536;
    facts::Work work(remaining);
    require(analysis.equalExtent(subject.getArgument(1), 0,
                                 subject.getArgument(3), 0,
                                 work) == Status::Proven,
            "transitive extent formation premise missing");
    require(analysis.bound(subject.getArgument(0), subject.getArgument(3), 0,
                           work) == Status::Proven,
            "strict bound failed to transfer across equal extents");
    require(analysis.bound(subject.getArgument(0), subject.getArgument(2), 0,
                           work) == Status::Unknown,
            "bound transferred to wrong axis");
    require(analysis.bound(other.getArgument(0), other.getArgument(1), 0,
                           work) == Status::Unknown &&
                analysis.bound(subject.getArgument(0), other.getArgument(1), 0,
                               work) == Status::Unknown,
            "formation premises escaped their exact subjects");
    auto second = parse(R"mlir(
 func.func private @subject(%i:ui64,%a:!M)->ui64 { func.return %i : ui64 }
)mlir");
    require(analysis.origin(helper(*second, "subject").getArgument(0), work)
                    .status == Status::Unknown,
            "foreign immutable subject was accepted");
  });
  cases.run("learned extent preserves nominal collection family", [&] {
    auto module = parse(R"mlir(
 func.func private @subject(%xs:!V,%fixed:!A)->!V attributes {
   data.preconditions=[#data.equal_extent<0,0,1,0>]
 } { func.return %xs : !V }
)mlir");
    auto subject = helper(*module, "subject");
    auto value = subject.getArgument(0);
    auto type = value.getType();
    MathematicalFactAnalysis analysis(*module);
    uint64_t remaining = 65536;
    facts::Work work(remaining);
    exact(analysis, value, 4, work);
    require(value.getType() == type && type != subject.getArgument(1).getType(),
            "extent query refined a nominal type");
  });
  cases.run("unknown and capacity differ and nested calls share work", [&] {
    auto module = parse(R"mlir(
 func.func private @identity(%s:!S)->!S { func.return %s : !S }
 func.func private @subject(%s:!S)->!S {
   %x = func.call @identity(%s) : (!S)->!S
   %y = func.call @identity(%x) : (!S)->!S
   func.return %y : !S
 }
)mlir");
    auto subject = helper(*module, "subject");
    auto value = returned(subject)[0];
    MathematicalFactAnalysis analysis(*module);
    uint64_t remaining = 65536;
    facts::Work work(remaining);
    require(analysis.extent(value, 0, work).status == Status::Unknown &&
                !work.exhausted(),
            "absent dynamic extent was reported as capacity");
    remaining = 1;
    facts::Work tiny(remaining);
    require(analysis.extent(value, 0, tiny).status == Status::Capacity &&
                remaining == 0 && tiny.exhausted(),
            "nested helper query reset the work allowance");
    require(analysis.equalExtent(value, 0, value, 0, tiny) == Status::Capacity,
            "exhausted work allowed a subsequent query");
    remaining = 1;
    facts::Work identity(remaining);
    require(analysis.equalExtent(value, 0, value, 0, identity) ==
                    Status::Proven &&
                remaining == 0,
            "exact same-axis evidence lost its one-unit allowance");
  });
  cases.run("unfiltered collect exact count and filtered upper count", [&] {
    auto module = parse(R"mlir(
 "data.domain"() ({ ^entry(%xs:!S):
   %d = "data.domain_elements"(%xs) : (!S)->!data.domain<i1>
   "data.domain_yield"(%d) : (!data.domain<i1>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!S)->!data.domain<i1>} : ()->()
 func.func private @body(%x:i1,%xs:!S)->i1 { func.return %x : i1 }
 func.func private @predicate(%x:i1,%xs:!S)->i1 { func.return %x : i1 }
 func.func private @subject(%flag:i1,%dynamic:!S)->(!S,!S,!S,!S,!S) {
   %empty = "data.sequence_empty"() : ()->!S
   %one = "data.sequence_append"(%empty,%flag) : (!S,i1)->!S
   %two = "data.sequence_append"(%one,%flag) : (!S,i1)->!S
   %zero = "data.index"() {value=0 : ui64} : ()->ui64
   %all = "data.finite_collect"(%two) {domain=@items,body=@body} : (!S)->!S
   %some = "data.finite_collect"(%two) {domain=@items,body=@body,predicate=@predicate} : (!S)->!S
   %none = "data.finite_collect"(%empty) {domain=@items,body=@body,predicate=@predicate} : (!S)->!S
   %mapped = "data.finite_collect"(%dynamic) {domain=@items,body=@body} : (!S)->!S
   %filtered = "data.finite_collect"(%dynamic) {domain=@items,body=@body,predicate=@predicate} : (!S)->!S
   func.return %all,%some,%none,%mapped,%filtered : !S,!S,!S,!S,!S
 }
)mlir");
    auto subject = helper(*module, "subject");
    auto values = returned(subject);
    MathematicalFactAnalysis analysis(*module);
    uint64_t remaining = 65536;
    facts::Work work(remaining);
    exact(analysis, values[0], 2, work);
    data::IndexOp zero;
    subject.walk([&](data::IndexOp op) { zero = op; });
    require(bool(zero) &&
                analysis.bound(zero.getResult(), values[0], 0, work) ==
                    Status::Proven &&
                analysis.bound(zero.getResult(), values[1], 0, work) ==
                    Status::Unknown,
            "filtered upper count incorrectly licensed a strict bound");
    auto upper = analysis.cardinality(values[1], 0, work);
    require(upper.status == Status::Proven && upper.value->value == 2 &&
                upper.value->precision == Precision::Upper,
            "filtered collect did not retain only an upper count");
    require(analysis.extent(values[1], 0, work).status == Status::Unknown,
            "filtered upper count became an exact extent");
    exact(analysis, values[2], 0, work);
    require(analysis.equalExtent(values[3], 0, subject.getArgument(1), 0,
                                 work) == Status::Proven,
            "unfiltered collect lost symbolic cardinality");
    require(analysis.equalExtent(values[4], 0, subject.getArgument(1), 0,
                                 work) == Status::Unknown,
            "filter acquired symbolic exact cardinality");
    require(analysis.origin(values[3], work).value == values[3],
            "unfiltered collect inherited input value identity");
  });
  cases.run("constructor and filter counts use caller formation premises", [&] {
    auto module = parse(R"mlir(
 "data.domain"() ({ ^entry(%xs:!S):
   %d = "data.domain_elements"(%xs) : (!S)->!data.domain<i1>
   "data.domain_yield"(%d) : (!data.domain<i1>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!S)->!data.domain<i1>} : ()->()
 func.func private @body(%x:i1,%xs:!S)->i1 { func.return %x : i1 }
 func.func private @predicate(%x:i1,%xs:!S)->i1 { func.return %x : i1 }
 func.func private @append(%xs:!S,%flag:i1)->!S {
   %next = "data.sequence_append"(%xs,%flag) : (!S,i1)->!S
   func.return %next : !S
 }
 func.func private @subject(%xs:!S,%fixed:!A,%flag:i1)->(!S,!S) attributes {
   data.preconditions=[#data.equal_extent<0,0,1,0>]
 } {
   %next = func.call @append(%xs,%flag) : (!S,i1)->!S
   %some = "data.finite_collect"(%xs) {domain=@items,body=@body,predicate=@predicate} : (!S)->!S
   func.return %next,%some : !S,!S
 }
)mlir");
    auto subject = helper(*module, "subject");
    auto values = returned(subject);
    MathematicalFactAnalysis analysis(*module);
    uint64_t remaining = 65536;
    facts::Work work(remaining);
    exact(analysis, values[0], 5, work);
    auto upper = analysis.cardinality(values[1], 0, work);
    require(upper.status == Status::Proven && upper.value->value == 4 &&
                upper.value->precision == Precision::Upper,
            "filter failed to use its caller's established extent");
    auto append = helper(*module, "append");
    require(analysis.extent(append.getArgument(0), 0, work).status ==
                Status::Unknown,
            "caller premises leaked into reusable helper formals");
  });
  cases.run("guards stay ordered and zero-trip control is conservative", [&] {
    auto module = parse(R"mlir(
 "runtime.binding"() {sym_name="require",contract="control.require",arguments=[],implementation="",function_type=(!runtime.scope, i1) -> !exec.outcome<>} : ()->()
)mlir");
    auto unit = cast<protocol_ir::ProtocolModuleOp>(module->getBody()->front());
    OpBuilder builder(&context);
    auto scope = runtime::ScopeType::get(&context);
    auto sequence = data::SequenceType::get(&context, builder.getI1Type());
    auto index = IntegerType::get(&context, 64, IntegerType::Unsigned);
    auto outcome = exec::OutcomeType::get(&context, {sequence});
    auto make = [&](StringRef name, TypeRange inputs, bool region) {
      builder.setInsertionPointToEnd(&unit.getBody().front());
      auto function =
          func::FuncOp::create(builder, unit.getLoc(), name,
                               builder.getFunctionType(inputs, {outcome}));
      function.setPrivate();
      function.setNoInline(true);
      if (region)
        function->setAttr("runtime.region", builder.getUnitAttr());
      else
        function->setAttr("runtime.origin",
                          builder.getArrayAttr({builder.getStringAttr(name),
                                                builder.getArrayAttr({})}));
      builder.setInsertionPointToEnd(function.addEntryBlock());
      return function;
    };
    auto body = make("body", {scope, index, sequence}, true);
    exec::ScopedExecutionBuilder bodyControl(builder, body);
    bodyControl.complete(body.getArgument(2));
    auto subject =
        make("guarded", {scope, builder.getI1Type(), index, sequence}, false);
    exec::ScopedExecutionBuilder control(builder, subject);
    control.invoke(
        "exec.apply", {}, control.scoped(subject.getArgument(1)),
        {builder.getNamedAttr("binding",
                              FlatSymbolRefAttr::get(&context, "require")),
         builder.getNamedAttr("site", builder.getStringAttr("guard")),
         builder.getNamedAttr("parameters", builder.getArrayAttr({}))});
    auto values = control.loop(subject.getArgument(2), subject.getArgument(2),
                               subject.getArgument(3), {}, {sequence}, false,
                               "zero", [&](unsigned) { return body; });
    require(values.size() == 1, "zero-trip fixture construction failed");
    auto result = values.front();
    control.returned(values);
    MathematicalFactAnalysis analysis(*module);
    uint64_t remaining = 65536;
    facts::Work work(remaining);
    require(analysis.bound(subject.getArgument(2), subject.getArgument(3), 0,
                           work) == Status::Unknown,
            "uninterpreted guard became a formation bound");
    require(analysis.extent(result, 0, work).status == Status::Unknown &&
                analysis.origin(result, work).value == result,
            "loop result imported body or initial identity without analysis");
    unsigned guards = 0;
    module->walk([&](exec::ApplyOp) { ++guards; });
    require(guards == 1 && succeeded(verify(*module)),
            "fact query changed ordered guard/control structure");
  });
  return cases.result();
}
