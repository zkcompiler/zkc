#include "mlir/IR/Verifier.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include <string>
#include <tuple>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;

namespace {
constexpr llvm::StringLiteral aliases = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!A = !algebra.field_array<"bls12-381.fr", 2>
!P = !poly.polynomial<"bls12-381.fr", 1>
)mlir";
constexpr llvm::StringLiteral numbers = R"mlir(
 module @numbers attributes {exec.computation} {
   func.func private @twice(%x:!F) -> !F {
     %v = algebra.field_add %x, %x : (!F,!F)->!F
     func.return %v : !F
   }
   func.func @entry(%x:!F) -> !F {
     %v = func.call @twice(%x) : (!F)->!F
     func.return %v : !F
   }
 }
)mlir";
constexpr llvm::StringLiteral work = R"mlir(
 local.func @work(%x:!F) -> !F attributes {logical_origin=["work",[]]} {
   %v = kernel.call @numbers::@entry(%x) {site="numerical"} : (!F)->!F
   local.return %v : !F
 }
)mlir";
std::string standalone(StringRef declarations) {
  return aliases.str() + "module {" + declarations.str() + "}";
}
OwningOpRef<mlir::ModuleOp> parse(StringRef text, MLIRContext &context) {
  auto result =
      parseSourceString<mlir::ModuleOp>(text, ParserConfig(&context, false));
  require(bool(result), "test input did not parse");
  return result;
}
LogicalResult admit(mlir::ModuleOp module) {
  if (failed(verify(module)))
    return failure();
  auto result = module.walk([](mlir::ModuleOp unit) {
    if (mathematical::isComputationUnit(unit) &&
        failed(mathematical::verifyComputationUnit(unit)))
      return WalkResult::interrupt();
    return WalkResult::advance();
  });
  return failure(result.wasInterrupted());
}
void accepts(StringRef text, MLIRContext &context) {
  auto module = parse(text, context);
  require(succeeded(admit(*module)), "valid Kernel IR was refused");
}
void rejects(StringRef text, StringRef code, MLIRContext &context) {
  auto module = parse(text, context);
  std::string diagnostic;
  ScopedDiagnosticHandler handler(&context, [&](Diagnostic &value) {
    diagnostic += value.str();
    return success();
  });
  require(failed(admit(*module)), "malformed Kernel IR was admitted");
  require(namesIdentifier(diagnostic, code),
          "unexpected refusal: " + diagnostic);
}
// Exercise call admission before the enclosing unit's region verifier, as can
// happen during SymbolTable verification of malformed nested declarations.
void rejects(kernel::CallOp call, StringRef code) {
  std::string diagnostic;
  ScopedDiagnosticHandler handler(call.getContext(), [&](Diagnostic &value) {
    diagnostic += value.str();
    return success();
  });
  SymbolTableCollection symbols;
  require(failed(call.verify()) || failed(call.verifySymbolUses(symbols)),
          "malformed Kernel call was admitted");
  require(namesIdentifier(diagnostic, code),
          "unexpected refusal: " + diagnostic);
}
std::string replace(StringRef original, StringRef from, StringRef to) {
  std::string result = original.str();
  auto offset = result.find(from.str());
  require(offset != std::string::npos, "missing test substitution");
  result.replace(offset, from.size(), to.str());
  return result;
}
std::string profileUnit(StringRef profile, StringRef locals = work) {
  std::string declarations = numbers.str() + locals.str();
  if (profile == "protocol") {
    declarations += R"mlir(
      "protocol.func"() ({
      ^entry(%x:!F):
        %v = "protocol.local_call"(%x) {callee=@work,role="P",site="work"} : (!F)->!F
        "protocol.return"(%v) : (!F)->()
      }) {sym_name="main",function_type=(!F)->!F,roles=["P"],
          input_roles=[["P"]],output_roles=[["P"]]} : ()->()
    )mlir";
  } else {
    declarations += R"mlir(
      "protocol.participant"() ({
      ^entry(%x:!F):
        %v = local.call @work(%x) {site="work"} : (!F)->!F
        "protocol.finish"(%v) : (!F)->()
      }) {sym_name="endpoint",function_type=(!F)->!F,instance="main",role="P"} : ()->()
      "protocol.entry"() {sym_name="main",targets=[["P",@endpoint]]} : ()->()
    )mlir";
    if (profile == "participant")
      declarations += R"mlir(
        "protocol.projection"() {calculations=[],interfaces=[{
          source="main",entry=@main,original_type=(!F)->!F,roles=["P"],
          input_roles=[["P"]],output_roles=[["P"]],statements=[],
          participants=[{participant=@endpoint,role="P",inputs=[0:i64],
                         service_inputs=[],outputs=[0:i64]}],
          actions=[{site="work",kind="protocol.local_call",callee=@work,
                    targets=[{participant=@endpoint,operation="local.call"}]}]
        }]} : ()->()
      )mlir";
  }
  return standalone("\"protocol.module\"() ({" + declarations +
                    "}) {profile=#protocol.profile<" + profile.str() +
                    ">} : ()->()");
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler silence(&context,
                                  [](Diagnostic &) { return success(); });
  Cases cases;
  cases.run("closed standalone unit, nested linkage and ordered call", [&] {
    auto module = parse(standalone(numbers.str() + work.str()), context);
    require(succeeded(admit(*module)), "standalone numerical unit refused");
    auto unit = *module->getOps<mlir::ModuleOp>().begin();
    auto entry = mathematical::getComputationEntry(unit);
    require(entry && entry.getSymName() == "entry", "wrong public entry");
    auto function = *module->getOps<local::FuncOp>().begin();
    auto call = cast<kernel::CallOp>(function.getBody().front().front());
    SymbolTableCollection symbols;
    require(kernel::resolve(call, symbols) == entry,
            "nested entry lookup failed");
    auto interface = cast<CallOpInterface>(call.getOperation());
    require(mlir::call_interface_impl::resolveCallable(interface, &symbols) ==
                    entry.getOperation() &&
                interface.getArgOperands() == call.getInputs(),
            "standard call interface differs from the numerical invocation");
    require(!isMemoryEffectFree(call) && !isSpeculatable(call),
            "ordered Kernel invocation gained purity or speculation");
    std::string printed;
    llvm::raw_string_ostream stream(printed);
    module->print(stream);
    accepts(printed, context);
  });
  cases.run("profile marker is required even on an unused nested module", [&] {
    auto text = replace(profileUnit("exec"), " local.func @work",
                        " module @unclassified {func.func @entry() "
                        "{func.return}} local.func @work");
    rejects(text, "computation-profile", context);
  });
  cases.run("profile marker does not admit an unused external helper", [&] {
    auto text = replace(profileUnit("exec"), " local.func @work",
                        " module @unused attributes {exec.computation} {"
                        "func.func @entry() {func.return} func.func private "
                        "@external()} local.func @work");
    rejects(text, "mathematical-formation", context);
  });
  cases.run("computation marker has an exact type", [&] {
    rejects(standalone("module @unit attributes {exec.computation=true} {"
                       "func.func @entry() {func.return}}"),
            "computation-profile", context);
  });
  cases.run("computation marker cannot decorate a function", [&] {
    rejects(
        standalone(
            "func.func @entry() attributes {exec.computation} {func.return}"),
        "computation-profile", context);
  });
  for (StringRef profile : {"protocol", "participant", "exec"})
    cases.run("logical Kernel admission in " + profile,
              [&] { accepts(profileUnit(profile), context); });
  for (StringRef profile : {"protocol", "participant", "exec"})
    cases.run("Kernel selection policy in " + profile, [&] {
      accepts(
          profileUnit(profile,
                      replace(work, "site=\"numerical\"",
                              "site=\"numerical\",policy=[true,false,false]")),
          context);
    });
  for (StringRef evidence :
       {"policy=[false,false,false]", "policy=[false,true,false]",
        "policy=[true,false,false]", "policy=[true,true,false]",
        "policy=[false,false,true]", "policy=[false,true,true]",
        "policy=[true,false,true]", "policy=[true,true,true]"})
    cases.run("independent optional Kernel evidence " + evidence, [&] {
      auto module =
          parse(standalone(numbers.str() +
                           replace(work, "site=\"numerical\"",
                                   ("site=\"numerical\"," + evidence).str())),
                context);
      require(succeeded(admit(*module)), "optional Kernel evidence refused");
      auto function = *module->getOps<local::FuncOp>().begin();
      auto call = cast<kernel::CallOp>(function.getBody().front().front());
      require(!isMemoryEffectFree(call) && !isSpeculatable(call),
              "compile-time evidence changed ordered Kernel semantics");
      std::string printed;
      llvm::raw_string_ostream stream(printed);
      module->print(stream);
      accepts(printed, context);
    });
  cases.run("return-only numerical entry", [&] {
    accepts(standalone(R"mlir(
      module @empty attributes {exec.computation} { func.func @entry() {func.return} }
      local.func @work() {
        kernel.call @empty::@entry() {site="empty"} : ()->()
        local.return
      }
    )mlir"),
            context);
  });
  for (StringRef policy :
       {"[]", "[true]", "[true,false]", "[true,false,true,false]",
        "[1:i64,false,true]", "[true,0:i64,false]", "[true,false,0:i64]",
        "[\"true\",false,true]"})
    cases.run("malformed Kernel policy " + policy, [&] {
      rejects(
          standalone(numbers.str() +
                     replace(work, "site=\"numerical\"",
                             ("site=\"numerical\",policy=" + policy).str())),
          "kernel-call-policy", context);
    });
  for (StringRef attribute : {"policy"})
    cases.run("non-array Kernel evidence " + attribute, [&] {
      std::string diagnostic;
      ScopedDiagnosticHandler handler(&context, [&](Diagnostic &value) {
        diagnostic += value.str();
        return success();
      });
      // ODS may refuse the declared attribute type during property conversion,
      // before custom operation verification.
      auto module = parseSourceString<mlir::ModuleOp>(
          standalone(
              numbers.str() +
              replace(
                  work, "site=\"numerical\"",
                  ("site=\"numerical\"," + attribute + "=\"invalid\"").str())),
          ParserConfig(&context, false));
      require(!module || failed(admit(*module)),
              "non-array Kernel evidence was admitted");
      require(diagnostic.find(attribute.str()) != std::string::npos,
              "unexpected attribute type refusal: " + diagnostic);
    });
  for (StringRef mutation :
       {"entry visibility", "helper visibility", "entry signature",
        "external entry", "empty block", "multiple blocks", "missing return"})
    cases.run("safe early call admission with malformed " + mutation, [&] {
      auto module = parse(
          standalone(numbers.str() +
                     replace(work, "site=\"numerical\"",
                             "site=\"numerical\",policy=[true,false,false]")),
          context);
      auto unit = *module->getOps<mlir::ModuleOp>().begin();
      auto entry = mathematical::getComputationEntry(unit);
      auto function = *module->getOps<local::FuncOp>().begin();
      auto call = cast<kernel::CallOp>(function.getBody().front().front());
      if (mutation == "entry visibility" || mutation == "helper visibility") {
        auto target = mutation == "entry visibility"
                          ? entry
                          : *unit.getBody()->getOps<func::FuncOp>().begin();
        target->setAttr("sym_visibility", StringAttr::get(&context, "invalid"));
      } else if (mutation == "entry signature") {
        entry->setAttr("function_type",
                       TypeAttr::get(IntegerType::get(&context, 64)));
      } else if (mutation == "external entry") {
        entry.getBody().getBlocks().clear();
      } else if (mutation == "multiple blocks") {
        entry.getBody().push_back(new Block());
      } else {
        entry.getBody().front().back().erase();
        if (mutation == "empty block")
          entry.getBody().front().front().erase();
      }
      rejects(call, mutation == "entry signature" ? "kernel-call-signature"
                                                  : "kernel-call-symbol");
    });
  for (StringRef evidence : {"policy=[true,false,false]"})
    cases.run("ordinary Local calls refuse Kernel evidence " + evidence, [&] {
      rejects(replace(profileUnit("exec"), "site=\"work\"",
                      ("site=\"work\"," + evidence).str()),
              "interactive-unknown-attribute", context);
    });
  cases.run("physical refuses a dormant logical unit", [&] {
    rejects(R"mlir(module {
      "protocol.module"() ({ module @unused attributes {exec.computation} {
        func.func @entry() { func.return }
      } }) {profile=#protocol.profile<physical>} : ()->()
    })mlir",
            "kernel-profile", context);
  });
  cases.run(
      "public execution reader refuses unresolved Kernel publication", [&] {
        auto module = parse(profileUnit("exec"), context);
        require(succeeded(admit(*module)), "logical Exec control refused");
        refuses(protocol::readExecutionModel(*module), "kernel-profile");
      });
  cases.run("internal realization names cannot collide with authored locals",
            [&] {
              accepts(profileUnit("exec", work.str() + R"mlir(
      local.func @kernel_entry_0() attributes {logical_origin=["kernel_entry_0",[]]} {
        local.return
      }
    )mlir"),
                      context);
            });
  cases.run("Local control retains typed captures and Kernel invocation order",
            [&] {
              accepts(profileUnit("protocol", R"mlir(
      local.func @work(%x:!F) -> !F attributes {logical_origin=["work",[]]} {
        %go = "local.bool_constant"() {value=true,site="go"} : ()->i1
        %v = "local.if"(%go,%x) ({
        ^then(%a:!F):
          %v = kernel.call @numbers::@entry(%a) {site="yes",policy=[true,false,false]} : (!F)->!F
          "local.yield"(%v) : (!F)->()
        }, {
        ^else(%a:!F):
          %v = kernel.call @numbers::@entry(%a) {site="no",policy=[false,true,false]} : (!F)->!F
          "local.yield"(%v) : (!F)->()
        }) {site="branch"} : (i1,!F)->!F
        local.return %v : !F
      }
    )mlir"),
                      context);
            });
  cases.run("structured Local loop admits nested Kernel calls", [&] {
    accepts(standalone(numbers.str() + R"mlir(
      local.func @loop(%lo:ui64,%hi:ui64,%x:!F) -> !F {
        %v = "local.for"(%lo,%hi,%x) ({
        ^body(%i:ui64,%a:!F):
          %v = kernel.call @numbers::@entry(%a) {site="iteration"} : (!F)->!F
          "local.yield"(%v) : (!F)->()
        }) {site="loop"} : (ui64,ui64,!F)->!F
        local.return %v : !F
      }
    )mlir"),
            context);
  });
  for (const auto &test : {
           std::tuple<StringRef, StringRef, StringRef>{
               "missing entry", "module @unit attributes {exec.computation} {}",
               "computation-entry"},
           {"two entries",
            "module @unit attributes {exec.computation} { func.func @a() "
            "{func.return} func.func @b() "
            "{func.return} }",
            "computation-entry"},
           {"no public entry",
            "module @unit attributes {exec.computation} {func.func private "
            "@a() {func.return}}",
            "computation-entry"},
           {"external entry",
            "module @unit attributes {exec.computation} {func.func @a()}",
            "func.func"},
           {"external dormant helper",
            "module @unit attributes {exec.computation} {func.func @a() "
            "{func.return} func.func "
            "private @unused()}",
            "mathematical-formation"},
           {"unsupported declaration",
            "module @unit attributes {exec.computation} {func.func @a() "
            "{func.return} local.func "
            "@unused() {local.return}}",
            "computation-formation"},
           {"unit attribute",
            "module @unit attributes {exec.computation, test.assume=true} "
            "{func.func @a() "
            "{func.return}}",
            "computation-formation"},
           {"entry attribute",
            "module @unit attributes {exec.computation} {func.func @a() "
            "attributes {assume=true} "
            "{func.return}}",
            "mathematical-formation"},
           {"polynomial port",
            "module @unit attributes {exec.computation} {func.func @a(%p:!P) "
            "-> !P {func.return "
            "%p:!P}}",
            "computation-entry"},
           {"affine port",
            "module @unit attributes {exec.computation} {func.func "
            "@a(%r:!local.capability<\"rng:bls12-381.fr\">) {func.return}}",
            "computation-entry"},
           {"dormant resource helper",
            "module @unit attributes {exec.computation} {func.func @a() "
            "{func.return} func.func "
            "private @r(%r:!local.capability<\"rng:bls12-381.fr\">) "
            "{func.return}}",
            "mathematical-formation"},
           {"entry preconditions",
            "module @unit attributes {exec.computation} {func.func "
            "@a(%x:!A,%i:ui64) attributes "
            "{data.preconditions=[#data.index_bound<1,0,0>]} {func.return}}",
            "computation-entry"},
           {"dormant recursive helper",
            "module @unit attributes {exec.computation} {func.func @a() "
            "{func.return} func.func "
            "private @r() {func.call @r():()->() func.return}}",
            "mathematical-formation"},
           {"dormant unsupported body",
            "module @unit attributes {exec.computation} {func.func @a() "
            "{func.return} func.func "
            "private @r() {%v=arith.constant 1:i32 func.return}}",
            "mathematical-dependencies"},
           {"discardable mathematical attribute",
            "module @unit attributes {exec.computation} {func.func "
            "@a(%x:!F)->!F "
            "{%v=algebra.field_add %x,%x {assume=true}:(!F,!F)->!F func.return "
            "%v:!F}}",
            "mathematical-formation"},
       })
    cases.run(std::get<0>(test), [&] {
      rejects(standalone(std::get<1>(test)), std::get<2>(test), context);
    });
  for (StringRef callee : {"@numbers", "@numbers::@twice",
                           "@numbers::@entry::@deeper", "@missing::@entry"})
    cases.run("invalid nested target " + callee, [&] {
      rejects(
          standalone(numbers.str() + replace(work, "@numbers::@entry", callee)),
          "kernel-call-symbol", context);
    });
  cases.run("call signature cannot substitute nominal types", [&] {
    rejects(standalone(numbers.str() + R"mlir(
      local.func @wrong(%x:ui64) -> ui64 {
        %v = kernel.call @numbers::@entry(%x) {site="call"} : (ui64)->ui64
        local.return %v : ui64
      }
    )mlir"),
            "kernel-call-signature", context);
  });
  cases.run("call attributes cannot carry assumptions", [&] {
    rejects(
        standalone(numbers.str() + replace(work, "site=\"numerical\"",
                                           "site=\"numerical\",assume=true")),
        "kernel-call-attribute", context);
  });
  cases.run("standard call port attributes carry no assumptions", [&] {
    auto source =
        standalone(numbers.str() +
                   replace(work, "site=\"numerical\"",
                           "site=\"numerical\",arg_attrs=[{}],res_attrs=[{}]"));
    auto module = parse(source, context);
    require(bool(module) && succeeded(admit(*module)),
            "empty standard port dictionaries should be admitted");
    rejects(replace(source, "arg_attrs=[{}]", "arg_attrs=[{assume=true}]"),
            "kernel-call-attribute", context);
    rejects(replace(source, "res_attrs=[{}]", "res_attrs=[]"),
            "kernel-call-attribute", context);
  });
  cases.run("participant cannot invoke Kernel directly", [&] {
    rejects(replace(profileUnit("exec"), "local.call @work",
                    "kernel.call @numbers::@entry"),
            "kernel-call-context", context);
  });
  cases.run("Kernel calls cannot occur at module scope", [&] {
    rejects(standalone(R"mlir(
      module @unit attributes {exec.computation} { func.func @entry() {func.return} }
      kernel.call @unit::@entry() {site="call"} : ()->()
    )mlir"),
            "kernel-call-context", context);
  });
  cases.run("standard functions cannot invoke Kernel", [&] {
    rejects(standalone(numbers.str() + R"mlir(
      func.func @wrong(%x:!F) -> !F {
        %v = kernel.call @numbers::@entry(%x) {site="call"} : (!F)->!F
        func.return %v : !F
      }
    )mlir"),
            "kernel-call-context", context);
  });
  cases.run("dormant helper cannot escape its owning symbol table", [&] {
    rejects(standalone(R"mlir(
      func.func private @outside(%x:!F) -> !F {func.return %x:!F}
      module @unit attributes {exec.computation} {
        func.func @entry() {func.return}
        func.func private @unused(%x:!F) -> !F {
          %v = func.call @outside(%x) : (!F)->!F
          func.return %v : !F
        }
      }
    )mlir"),
            "func.call", context);
  });
  for (bool valid : {true, false})
    cases.run(valid ? "helper premise discharged by actual index"
                    : "helper premise refused at actual call",
              [&] {
                std::string text = standalone(R"mlir(
        module @bounded attributes {exec.computation} {
          func.func private @at(%xs:!A,%i:ui64) -> !F
              attributes {data.preconditions=[#data.index_bound<1,0,0>]} {
            %v = "data.bounded_at"(%xs,%i) : (!A,ui64)->!F
            func.return %v : !F
          }
          func.func @entry(%xs:!A) -> !F {
            %i = "data.index"() {value="INDEX"} : ()->ui64
            %v = func.call @at(%xs,%i) : (!A,ui64)->!F
            func.return %v : !F
          }
        }
      )mlir");
                text = replace(text, "INDEX", valid ? "0" : "2");
                if (valid)
                  accepts(text, context);
                else
                  rejects(text, "finite-bound", context);
              });
  for (bool valid : {true, false})
    cases.run(valid ? "generic polynomial observation has known actual bound"
                    : "generic summary cannot hide an overflowing observation",
              [&] {
                std::string text = standalone(R"mlir(
        module @polynomial attributes {exec.computation} {
          func.func private @observe(%p:!P) -> !A {
            %v = "poly.coefficients"(%p) : (!P)->!A
            func.return %v : !A
          }
          func.func @entry(%a:!A) -> !A {
            %p = "poly.from_coefficients"(%a) : (!A)->!P
            %square = "poly.multiply"(%p,%p) : (!P,!P)->!P
            %v = func.call @observe(%ACTUAL) : (!P)->!A
            func.return %v : !A
          }
        }
      )mlir");
                text = replace(text, "ACTUAL", valid ? "p" : "square");
                if (valid)
                  accepts(text, context);
                else
                  rejects(text, "polynomial-formation", context);
              });
  cases.run("closed finite mathematics retains its owned domain and premises",
            [&] {
              accepts(standalone(R"mlir(
      module @sum attributes {exec.computation} {
        "data.domain"() ({
        ^entry(%xs:!A):
          %d = "data.domain_indices"(%xs) {axis=0:i64} : (!A)->!data.domain<ui64>
          "data.domain_yield"(%d) : (!data.domain<ui64>)->()
        }) {sym_name="items",sym_visibility="private",function_type=(!A)->!data.domain<ui64>} : ()->()
        func.func private @step(%state:!F,%i:ui64,%xs:!A) -> !F
            attributes {data.preconditions=[#data.index_bound<1,2,0>]} {
          %x = "data.bounded_at"(%xs,%i) : (!A,ui64)->!F
          %v = algebra.field_add %state,%x : (!F,!F)->!F
          func.return %v : !F
        }
        func.func @entry(%xs:!A,%initial:!F) -> !F {
          %v = "algebra.finite_fold"(%xs,%initial) {domain=@items,step=@step} : (!A,!F)->!F
          func.return %v : !F
        }
      }
    )mlir"),
                      context);
            });
  cases.run("unused domain dependencies still verify their constructors", [&] {
    rejects(standalone(R"mlir(
      module @unit attributes {exec.computation} {
        func.func @entry() {func.return}
        "data.domain"() ({
        ^entry(%xs:!A):
          %d = "data.domain_indices"(%xs) {axis=1:i64} : (!A)->!data.domain<ui64>
          "data.domain_yield"(%d) : (!data.domain<ui64>)->()
        }) {sym_name="unused",sym_visibility="private",function_type=(!A)->!data.domain<ui64>} : ()->()
      }
    )mlir"),
            "finite-domain", context);
  });
  cases.run("Kernel admission preserves affine Local state validation", [&] {
    rejects(profileUnit("protocol", work.str() + R"mlir(
      local.func @unused(%x:!F,%resource:!local.capability<"rng:bls12-381.fr">)
          -> (!local.capability<"rng:bls12-381.fr">,!local.capability<"rng:bls12-381.fr">)
          attributes {logical_origin=["unused",[]]} {
        %v = kernel.call @numbers::@entry(%x) {site="math"} : (!F)->!F
        local.return %resource,%resource : !local.capability<"rng:bls12-381.fr">,!local.capability<"rng:bls12-381.fr">
      }
    )mlir"),
            "interactive-resource-reuse", context);
  });
  cases.run("logical Kernel calls preserve Local site uniqueness", [&] {
    rejects(profileUnit("protocol", R"mlir(
      local.func @work(%x:!F) -> !F attributes {logical_origin=["work",[]]} {
        %v = kernel.call @numbers::@entry(%x) {site="same"} : (!F)->!F
        %w = kernel.call @numbers::@entry(%v) {site="same",policy=[true,false,false]} : (!F)->!F
        local.return %w : !F
      }
    )mlir"),
            "interactive-site", context);
  });
  return cases.result();
}
