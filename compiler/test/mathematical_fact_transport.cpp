#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/MathematicalFacts.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
using facts::Status;
template <typename Query> void checkAllowance(Query query) {
  auto run = [&](uint64_t remaining) {
    facts::Work work(remaining);
    auto status = query(work);
    require(work.exhausted() == (status == Status::Capacity),
            "capacity did not preserve sticky exhaustion");
    return std::make_pair(status, remaining);
  };
  auto cold = run(65536), warm = run(65536);
  require(cold == warm && cold.first == Status::Proven,
          "mixed extraction changed with helper cache warmth");
  uint64_t cost = 65536 - cold.second;
  for (uint64_t allowance = 0; allowance <= cost; ++allowance)
    require(run(allowance) == std::make_pair(allowance == cost
                                                 ? Status::Proven
                                                 : Status::Capacity,
                                             uint64_t(0)),
            "mixed extraction bypassed the exact work boundary");
}
std::string source(StringRef declarations) {
  return R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !data.field_vector<"bls12-381.fr">
!M = !data.field_matrix<"bls12-381.fr">
!S = !data.sequence<i1>
!Choice = !data.variant<#data.identity<["atom", "IndexChoice"]>, [#data.alternative<"none">, #data.alternative<"some", [ui64]>]>
module { "protocol.module"() ({
 func.func private @identity(%v:!V)->!V { return %v : !V }
 func.func private @read(%v:!V,%i:ui64)->!F attributes {
   data.preconditions=[#data.index_bound<1,0,0>]
 } {
   %r = "data.bounded_at"(%v,%i) : (!V,ui64)->!F
   return %r : !F
 }
)mlir" + declarations.str() +
         R"mlir(
 "protocol.func"() ({ ^entry(%v:!V):
   "protocol.return"(%v) : (!V)->()
 }) {sym_name="main",function_type=(!V)->!V,roles=["P"],
     input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
}
std::string selected(unsigned nesting, bool call, bool top = true) {
  auto args = [](std::string suffix) {
    return "%c" + suffix + ",%v" + suffix + ",%w" + suffix + ",%k" + suffix +
           ",%l" + suffix + ",%alias" + suffix;
  };
  auto incoming = args(top ? "" : std::to_string(nesting + 1));
  auto suffix = std::to_string(nesting);
  auto name = [&](StringRef base) { return "%" + base.str() + suffix; };
  std::string arms;
  for (unsigned arm = 0; arm != 2; ++arm) {
    if (arm)
      arms += ",";
    arms += "{ ^arm(" + name("c") + ":i1," + name("v") + ":!V," + name("w") +
            ":!V," + name("k") + ":ui64," + name("l") + ":ui64," +
            name("alias") + ":!V):\n";
    if (nesting)
      arms += selected(nesting - 1, call, false);
    else {
      arms +=
          "%forward = func.call @identity(" + name("alias") + ") : (!V)->!V\n";
      arms += (call ? "%r = func.call @read(%forward,"
                    : "%r = \"data.bounded_at\"(%forward,") +
              name("k") + ") : (!V,ui64)->!F\n";
    }
    arms += "\"data.yield\"(%r) : (!F)->() }";
  }
  auto selector = top ? std::string("%c") : "%c" + std::to_string(nesting + 1);
  return "%r = \"data.branch\"(" + selector + "," + incoming + ") (" + arms +
         ") {alternatives=[\"then\",\"else\"]} : "
         "(i1,i1,!V,!V,ui64,ui64,!V)->!F\n";
}
std::string subject(unsigned nesting, bool call) {
  return "func.func private @subject(%c:i1,%v:!V,%w:!V,%k:ui64,%l:ui64)"
         "->!F attributes {data.preconditions=[#data.index_bound<3,1,0>]} {\n"
         "%alias = func.call @identity(%v) : (!V)->!V\n" +
         selected(nesting, call) + "return %r : !F\n}";
}
func::FuncOp subject(ModuleOp module) {
  func::FuncOp result;
  module.walk([&](func::FuncOp op) {
    if (op.getSymName() == "subject")
      result = op;
  });
  require(bool(result), "missing subject");
  return result;
}
void refuse(ModuleOp module, MLIRContext &context, StringRef code) {
  require(succeeded(verify(module)), "mutation is not native well-typed IR");
  SmallVector<std::string> codes;
  ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
    for (const auto &refusal : diagnostics::refusals(diagnostic))
      codes.push_back(refusal.code);
    return success();
  });
  require(failed(admitStage(module)) && llvm::is_contained(codes, code.str()),
          "missing semantic refusal " + code);
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
    require(bool(module), "fact transport fixture did not parse");
    return module;
  };
  for (bool call : {false, true})
    for (unsigned nesting : {0u, 2u})
      cases.run(
          Twine(call ? "calls" : "direct reads") + " in both arms at depth " +
              Twine(nesting),
          [&] {
            auto module = parse(subject(nesting, call));
            require(succeeded(admitStage(*module)), "captured bound was lost");
            auto function = subject(*module);
            MathematicalFactAnalysis analysis(*module);
            function.walk([&](data::BranchOp branch) {
              for (Region &region : branch.getArms()) {
                auto args = region.front().getArguments();
                uint64_t remaining = 65536;
                facts::Work work(remaining);
                require(analysis.origin(args[1], work).value ==
                                function.getArgument(1) &&
                            analysis.origin(args[5], work).value ==
                                function.getArgument(1),
                        "capture aliases changed actual identity");
                require(analysis.bound(args[3], args[5], 0, work) ==
                            Status::Proven,
                        "alias capture lost bound");
                require(analysis.bound(args[4], args[1], 0, work) ==
                                Status::Unknown &&
                            analysis.bound(args[3], args[2], 0, work) ==
                                Status::Unknown,
                        "same-typed wrong index/container borrowed bound");
                require(
                    analysis.bound(args[0], args[1], 0, work) ==
                            Status::Unknown &&
                        analysis.bound(args[3], args[1], 1, work) ==
                            Status::Unknown,
                    "capture transport changed index type or collection rank");
              }
            });
          });
  for (StringRef mutation : {"container", "index", "premise", "dormant"})
    cases.run("well-typed native mutation: " + mutation, [&] {
      auto module = parse(subject(1, true));
      auto function = subject(*module);
      data::BranchOp outer;
      function.walk<WalkOrder::PreOrder>([&](data::BranchOp branch) {
        if (!outer)
          outer = branch;
      });
      if (mutation == "premise")
        function->removeAttr("data.preconditions");
      else if (mutation == "dormant") {
        OpBuilder builder(outer);
        auto flag = arith::ConstantIntOp::create(builder, outer.getLoc(), 1, 1);
        outer->setOperand(0, flag);
        auto &arm = outer.getArms()[1].front();
        arm.walk([&](func::CallOp call) {
          if (call.getCallee() == "read")
            call.setOperand(1, call->getBlock()->getArgument(4));
        });
      } else
        outer->setOperand(
            mutation == "container" ? 6 : 4,
            function.getArgument(mutation == "container" ? 2 : 4));
      refuse(*module, context, "finite-bound");
    });
  cases.run("enum payload offset preserves captures but not payload identity",
            [&] {
              auto module = parse(R"mlir(
 func.func private @subject(%tag:!Choice,%outer_v:!V,%outer_k:ui64)->!F attributes {
   data.preconditions=[#data.index_bound<2,1,0>]
 } {
   %r = "data.branch"(%tag,%outer_v,%outer_k) ({ ^none(%v:!V,%k:ui64):
     %r = func.call @read(%v,%k) : (!V,ui64)->!F
     "data.yield"(%r) : (!F)->()
   }, { ^some(%payload:ui64,%v:!V,%k:ui64):
     %r = func.call @read(%v,%k) : (!V,ui64)->!F
     "data.yield"(%r) : (!F)->()
   }) {alternatives=["none","some"]} : (!Choice,!V,ui64)->!F
   return %r : !F
 }
)mlir");
              require(succeeded(admitStage(*module)),
                      "enum capture offset lost bound");
              data::BranchOp branch;
              module->walk([&](data::BranchOp op) { branch = op; });
              auto &arm = branch.getArms()[1].front();
              MathematicalFactAnalysis analysis(*module);
              uint64_t remaining = 65536;
              facts::Work work(remaining);
              require(analysis.origin(arm.getArgument(0), work).value ==
                          arm.getArgument(0),
                      "payload was mistaken for a capture");
              for (auto call : arm.getOps<func::CallOp>())
                call.setOperand(1, arm.getArgument(0));
              refuse(*module, context, "finite-bound");
            });
  cases.run("bounds never imply equality and preserve the selected axis", [&] {
    auto module = parse(R"mlir(
 func.func private @subject(%c:i1,%outer_m:!M,%outer_n:!M,%outer_k:ui64)->ui64 attributes {
   data.preconditions=[#data.index_bound<3,1,0>,#data.index_bound<3,2,0>]
 } {
   %r = "data.branch"(%c,%outer_m,%outer_n,%outer_k) ({ ^a(%m:!M,%n:!M,%k:ui64):
     "data.yield"(%k) : (ui64)->()
   }, { ^b(%m:!M,%n:!M,%k:ui64):
     "data.yield"(%k) : (ui64)->()
   }) {alternatives=["then","else"]} : (i1,!M,!M,ui64)->ui64
   return %r : ui64
 }
)mlir");
    MathematicalFactAnalysis analysis(*module);
    module->walk([&](data::BranchOp branch) {
      for (Region &region : branch.getArms()) {
        auto a = region.front().getArguments();
        uint64_t remaining = 65536;
        facts::Work work(remaining);
        require(analysis.bound(a[2], a[0], 0, work) == Status::Proven &&
                    analysis.bound(a[2], a[0], 1, work) == Status::Unknown &&
                    analysis.equalExtent(a[0], 0, a[1], 0, work) ==
                        Status::Unknown,
                "bound changed axis or supplied equality");
        require(analysis.origin(branch.getResult(0), work).value ==
                    branch.getResult(0),
                "branch result borrowed an arm's origin");
      }
    });
  });
  cases.run("capture traversal preserves exact work and inherited depth", [&] {
    auto module = parse(subject(2, true));
    data::BranchOp branch;
    module->walk<WalkOrder::PreOrder>([&](data::BranchOp op) { branch = op; });
    auto a = branch.getArms()[0].front().getArguments();
    MathematicalFactAnalysis analysis(*module);
    auto query = [&](uint64_t allowance) {
      facts::Work work(allowance);
      return std::make_pair(analysis.bound(a[3], a[5], 0, work), allowance);
    };
    auto cold = query(65536), warm = query(65536);
    require(cold == warm && cold.first == Status::Proven,
            "cache changed capture charges");
    uint64_t cost = 65536 - cold.second;
    require(query(cost) == std::make_pair(Status::Proven, uint64_t(0)) &&
                query(cost - 1).first == Status::Capacity,
            "capture query bypassed exact work boundary");
    for (unsigned depth : {253u, 254u, 257u}) {
      uint64_t remaining = 65536;
      facts::Work work(remaining);
      auto result = analysis.origin(a[3], work, depth);
      require(result.status ==
                      (depth == 253 ? Status::Proven : Status::Capacity) &&
                  bool(result.value) == (depth == 253),
              "capture traversal reset its consumed depth");
    }
  });

  const StringRef capturedConstructor = R"mlir(
 func.func private @subject(%c:i1)->i1 {
   %empty = "data.sequence_empty"() : ()->!S
   %xs = "data.sequence_append"(%empty,%c) : (!S,i1)->!S
   %i = "data.index"() {value=0:ui64} : ()->ui64
   %r = "data.branch"(%c,%xs,%i) ({ ^a(%v:!S,%k:ui64):
     %r = "data.bounded_at"(%v,%k) : (!S,ui64)->i1
     "data.yield"(%r) : (i1)->()
   }, { ^b(%v:!S,%k:ui64):
     %r = "data.bounded_at"(%v,%k) : (!S,ui64)->i1
     "data.yield"(%r) : (i1)->()
   }) {alternatives=["then","else"]} : (i1,!S,ui64)->i1
   return %r : i1
 }
)mlir";
  cases.run("captured dynamic constructors retain exact cardinality", [&] {
    auto module = parse(capturedConstructor);
    require(succeeded(admitStage(*module)),
            "capture hid exact constructed extent");
    module->walk([&](data::IndexOp index) {
      index->setAttr("value", IntegerAttr::get(index.getType(), 1));
    });
    refuse(*module, context, "finite-bound");
  });

  cases.run(
      "captured constructor retains depth before cardinality analysis", [&] {
        auto module = parse(capturedConstructor);
        require(succeeded(verify(*module)) && succeeded(admitStage(*module)),
                "constructor boundary fixture failed admission");
        MathematicalFactAnalysis analysis(*module);
        module->walk([&](data::BranchOp branch) {
          for (Region &arm : branch.getArms()) {
            checkAllowance([&](facts::Work &work) {
              auto result =
                  analysis.cardinality(arm.front().getArgument(0), 0, work);
              require(bool(result.value) == (result.status == Status::Proven),
                      "capacity supplied constructor evidence");
              return result.status;
            });
            for (unsigned depth : {254u, 255u}) {
              uint64_t remaining = 65536;
              facts::Work work(remaining);
              auto result = analysis.cardinality(arm.front().getArgument(0), 0,
                                                 work, depth);
              require(result.status == (depth == 254 ? Status::Proven
                                                     : Status::Capacity) &&
                          bool(result.value) == (depth == 254) &&
                          work.exhausted() == (depth == 255),
                      "capture -> append -> empty at depth " + Twine(depth) +
                          " returned status " + Twine(unsigned(result.status)) +
                          " with evidence " + Twine(bool(result.value)));
              if (result.value)
                require(result.value->precision == facts::Precision::Exact &&
                            result.value->value == 1,
                        "constructor cardinality changed");
              remaining = 65536;
              facts::Work extentWork(remaining);
              auto extent = analysis.extent(arm.front().getArgument(0), 0,
                                            extentWork, depth);
              require(extent.status == result.status &&
                          bool(extent.value) == bool(result.value),
                      "exact extent projection reset constructor depth");
            }
          }
        });
      });
  cases.run(
      "captured word expression retains depth before range analysis", [&] {
        auto module = parse(R"mlir(
 func.func private @subject(%c:i1,%x:ui64,%xs:!data.field_array<"bls12-381.fr",8>)->!F {
   %mask = "data.index"() {value=7:ui64} : ()->ui64
   %word = "data.index_bit_and"(%x,%mask) : (ui64,ui64)->ui64
   %r = "data.branch"(%c,%word,%xs) ({ ^a(%k:ui64,%v:!data.field_array<"bls12-381.fr",8>):
     %v0 = "data.bounded_at"(%v,%k) : (!data.field_array<"bls12-381.fr",8>,ui64)->!F
     "data.yield"(%v0) : (!F)->()
   }, { ^b(%k:ui64,%v:!data.field_array<"bls12-381.fr",8>):
     %v0 = "data.bounded_at"(%v,%k) : (!data.field_array<"bls12-381.fr",8>,ui64)->!F
     "data.yield"(%v0) : (!F)->()
   }) {alternatives=["then","else"]} : (i1,ui64,!data.field_array<"bls12-381.fr",8>)->!F
   return %r : !F
 }
)mlir");
        require(succeeded(verify(*module)) && succeeded(admitStage(*module)),
                "word boundary fixture failed admission");
        MathematicalFactAnalysis analysis(*module);
        module->walk([&](data::BranchOp branch) {
          for (Region &arm : branch.getArms()) {
            auto index = arm.front().getArgument(0);
            auto array = arm.front().getArgument(1);
            checkAllowance([&](facts::Work &work) {
              auto result = analysis.wordRange(index, work);
              require(bool(result.value) == (result.status == Status::Proven),
                      "capacity supplied range evidence");
              return result.status;
            });
            checkAllowance([&](facts::Work &work) {
              return analysis.bound(index, array, 0, work);
            });
            for (unsigned depth : {254u, 255u}) {
              uint64_t remaining = 65536;
              facts::Work work(remaining);
              auto result =
                  analysis.wordRange(arm.front().getArgument(0), work, depth);
              require(result.status == (depth == 254 ? Status::Proven
                                                     : Status::Capacity) &&
                          bool(result.value) == (depth == 254) &&
                          work.exhausted() == (depth == 255),
                      "capture -> bit_and -> operands at depth " +
                          Twine(depth) + " returned status " +
                          Twine(unsigned(result.status)) + " with evidence " +
                          Twine(bool(result.value)));
              if (result.value)
                require(result.value->minimum == 0 &&
                            result.value->maximum == 7,
                        "captured word range changed");
              remaining = 65536;
              facts::Work boundWork(remaining);
              require(analysis.bound(index, array, 0, boundWork, depth) ==
                          result.status,
                      "cached origin reset depth before a strict bound query");
            }
          }
        });
      });

  cases.run(
      "nested helper aliases retain depth before captured constructors", [&] {
        std::string declarations = capturedConstructor.str();
        auto position = declarations.find("   %i =");
        declarations.insert(position,
                            "   %alias = func.call @outer(%xs) : (!S)->!S\n");
        position = declarations.find("(%c,%xs,%i)");
        declarations.replace(position, std::string("(%c,%xs,%i)").size(),
                             "(%c,%alias,%i)");
        auto module = parse(R"mlir(
 func.func private @forward(%s:!S)->!S { return %s : !S }
 func.func private @relay(%s:!S)->!S {
   %a = func.call @forward(%s) : (!S)->!S
   %b = func.call @forward(%a) : (!S)->!S
   return %b : !S
 }
 func.func private @outer(%s:!S)->!S {
   %r = func.call @relay(%s) : (!S)->!S
   return %r : !S
 }
)mlir" + declarations);
        require(succeeded(verify(*module)) && succeeded(admitStage(*module)),
                "aliased constructor fixture failed admission");
        MathematicalFactAnalysis analysis(*module);
        module->walk([&](data::BranchOp branch) {
          for (Region &arm : branch.getArms()) {
            auto value = arm.front().getArgument(0);
            checkAllowance([&](facts::Work &work) {
              return analysis.cardinality(value, 0, work).status;
            });
            for (unsigned depth : {250u, 251u}) {
              uint64_t remaining = 65536;
              facts::Work work(remaining);
              auto result = analysis.cardinality(value, 0, work, depth);
              require(result.status == (depth == 250 ? Status::Proven
                                                     : Status::Capacity) &&
                          bool(result.value) == (depth == 250) &&
                          work.exhausted() == (depth == 251),
                      "nested forwarding summary lost its deepest dependency");
            }
          }
        });
      });

  cases.run("cached forwarding and shared ranges retain composed depth", [&] {
    auto module = parse(R"mlir(
 func.func private @forward(%s:ui64)->ui64 { return %s : ui64 }
 func.func private @relay(%s:ui64)->ui64 {
   %a = func.call @forward(%s) : (ui64)->ui64
   %b = func.call @forward(%a) : (ui64)->ui64
   return %b : ui64
 }
 func.func private @subject(%c:i1,%x:ui64)->ui64 {
   %mask = "data.index"() {value=7:ui64} : ()->ui64
   %word = "data.index_bit_and"(%x,%mask) : (ui64,ui64)->ui64
   %r = "data.branch"(%c,%word) ({ ^a(%k:ui64):
     %left = func.call @relay(%k) : (ui64)->ui64
     %right = func.call @relay(%k) : (ui64)->ui64
     %both = "data.index_bit_and"(%left,%right) : (ui64,ui64)->ui64
     "data.yield"(%both) : (ui64)->()
   }, { ^b(%k:ui64):
     %shared = "data.index_bit_and"(%k,%k) : (ui64,ui64)->ui64
     %deep = "data.index_bit_and"(%k,%shared) : (ui64,ui64)->ui64
     "data.yield"(%deep) : (ui64)->()
   }) {alternatives=["then","else"]} : (i1,ui64)->ui64
   return %r : ui64
 }
)mlir");
    require(succeeded(verify(*module)) && succeeded(admitStage(*module)),
            "shared mixed-expression fixture failed admission");
    data::BranchOp branch;
    module->walk([&](data::BranchOp op) { branch = op; });
    MathematicalFactAnalysis analysis(*module);
    auto check = [&](Value value, unsigned lastDepth) {
      checkAllowance([&](facts::Work &work) {
        return analysis.wordRange(value, work).status;
      });
      for (unsigned depth : {lastDepth, lastDepth + 1}) {
        uint64_t remaining = 65536;
        facts::Work work(remaining);
        auto result = analysis.wordRange(value, work, depth);
        require(result.status == (depth == lastDepth ? Status::Proven
                                                     : Status::Capacity) &&
                    bool(result.value) == (depth == lastDepth) &&
                    work.exhausted() == (depth != lastDepth),
                "cached extraction hid a composed over-depth dependency");
        if (result.value)
          require(result.value->minimum == 0 && result.value->maximum == 7,
                  "shared captured range changed");
      }
    };
    check(branch.getArms()[0].front().back().getOperand(0), 250);
    auto deep = branch.getArms()[1].front().back().getOperand(0);
    check(deep.getDefiningOp()->getOperand(1), 253);
    check(deep, 252);
    auto *op = deep.getDefiningOp();
    auto left = op->getOperand(0);
    op->setOperand(0, op->getOperand(1));
    op->setOperand(1, left);
    analysis.clear();
    check(deep, 252);
  });

  cases.run(
      "captured singleton expressions retain depth in integer queries", [&] {
        auto module = parse(R"mlir(
 func.func private @subject(%c:i1)->ui64 {
   %zero = "data.index"() {value=0:ui64} : ()->ui64
   %one = "data.index"() {value=1:ui64} : ()->ui64
   %word = "data.index_wrapping_add"(%zero,%one) : (ui64,ui64)->ui64
   %r = "data.branch"(%c,%word) ({ ^a(%k:ui64):
     "data.yield"(%k) : (ui64)->()
   }, { ^b(%k:ui64):
     "data.yield"(%k) : (ui64)->()
   }) {alternatives=["then","else"]} : (i1,ui64)->ui64
   return %r : ui64
 }
)mlir");
        require(succeeded(verify(*module)) && succeeded(admitStage(*module)),
                "singleton fixture failed admission");
        MathematicalFactAnalysis analysis(*module);
        module->walk([&](data::BranchOp branch) {
          for (Region &arm : branch.getArms()) {
            auto value = arm.front().getArgument(0);
            checkAllowance([&](facts::Work &work) {
              auto result = analysis.integer(value, work);
              require(bool(result.value) == (result.status == Status::Proven),
                      "capacity supplied singleton evidence");
              return result.status;
            });
            for (unsigned depth : {254u, 255u}) {
              uint64_t remaining = 65536;
              facts::Work work(remaining);
              auto result = analysis.integer(value, work, depth);
              require(result.status == (depth == 254 ? Status::Proven
                                                     : Status::Capacity) &&
                          bool(result.value) == (depth == 254),
                      "integer projection reset captured expression depth");
              if (result.value)
                require(*result.value == 1, "captured singleton changed");
            }
          }
        });
      });

  cases.run("excessive capture nesting reports capacity without evidence", [&] {
    std::string chain = "\"data.yield\"(%k0) : (ui64)->()\n";
    for (unsigned level = 0; level != 257; ++level) {
      auto input = std::to_string(level + 1), arm = std::to_string(level);
      chain = "%r = \"data.branch\"(%c" + input + ",%c" + input + ",%k" +
              input + ") ({ ^a(%c" + arm + ":i1,%k" + arm + ":ui64):\n" +
              chain + "}, { ^b(%c" + arm + ":i1,%k" + arm +
              ":ui64):\n"
              "\"data.yield\"(%k" +
              arm +
              ") : (ui64)->()\n"
              "}) {alternatives=[\"then\",\"else\"]} : (i1,i1,ui64)->ui64\n"
              "\"data.yield\"(%r) : (ui64)->()\n";
    }
    chain.resize(chain.size() -
                 std::string("\"data.yield\"(%r) : (ui64)->()\n").size());
    auto module =
        parse("func.func private @subject(%c257:i1,%k257:ui64)->ui64 {\n" +
              chain + "return %r : ui64\n}");
    data::BranchOp deepest;
    unsigned depth = 0;
    module->walk([&](data::BranchOp branch) {
      unsigned candidate = 0;
      for (auto *op = branch->getParentOp(); op; op = op->getParentOp())
        candidate += isa<data::BranchOp>(op);
      if (!deepest || candidate > depth) {
        deepest = branch;
        depth = candidate;
      }
    });
    require(depth == 256, "deep nesting fixture lost a capture hop");
    MathematicalFactAnalysis analysis(*module);
    uint64_t remaining = 65536;
    facts::Work work(remaining);
    auto result =
        analysis.origin(deepest.getArms()[0].front().getArgument(1), work);
    require(result.status == Status::Capacity && !result.value &&
                work.exhausted(),
            "over-depth captures supplied an origin");
  });

  cases.run(
      "explicit dominating extent equality transfers a captured bound", [&] {
        auto declarations = subject(1, true);
        auto position = declarations.find("#data.index_bound<3,1,0>");
        require(position != std::string::npos, "missing subject premise");
        declarations.insert(position, "#data.equal_extent<1,0,2,0>,");
        auto module = parse(declarations);
        MathematicalFactAnalysis analysis(*module);
        module->walk([&](data::BranchOp branch) {
          for (Region &arm : branch.getArms()) {
            auto a = arm.front().getArguments();
            uint64_t remaining = 65536;
            facts::Work work(remaining);
            require(analysis.equalExtent(a[1], 0, a[2], 0, work) ==
                            Status::Proven &&
                        analysis.bound(a[3], a[2], 0, work) == Status::Proven,
                    "capture hid an established dominating extent equality");
          }
        });
      });
  return cases.result();
}
