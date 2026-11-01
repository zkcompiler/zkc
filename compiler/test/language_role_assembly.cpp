#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/NativeLanguage.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Language/Inspection.h"
using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
namespace {
Expected<CheckedProject> check(StringRef code) {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto source = capture({{"m", code.str(), "assembly.zkc"}}, options);
  if (!source)
    return source.takeError();
  return analyze(*source).checkedProject();
}
CheckedOriginal original(StringRef code) {
  auto project = take(check(code));
  auto written = take(inspectWrittenSource(project));
  require(written.find("expr.role_assembly") != std::string::npos,
          "written role assembly disappeared");
  return take(prepareOriginal(take(closeNativeRun(project, "m::Run"))));
}
constexpr StringLiteral shared = R"(pub protocol Run roles(P, V)(
    a: bool @(P, V); b: bool @(P, V)
) -> bool @(P, V):
    return @(V = b, P = a)
)";
} // namespace
int main() {
  Cases cases;
  cases.run("authored role order survives inference and actual comparison", [] {
    auto value = original(shared);
    require(value.bytes().contains("protocol.assemble_roles"),
            "assembly did not reach Protocol IR");
    for (bool simplify : {false, true}) {
      EntryOptions options;
      options.simplify = simplify;
      take(compileEntry(value, options));
    }
  });
  cases.run("communication keeps separate sender and receiver components", [] {
    auto value = original(R"(pub protocol Run roles(P, V)(
    a: bool @V
) -> bool @(P, V):
    delivered <- send a to P
    return @(P = delivered, V = a)
)");
    require(value.bytes().contains("protocol.exchange"),
            "explicit delivery disappeared");
    take(compileEntry(value));
  });
  cases.run("ordinary aggregate components flatten pointwise", [] {
    auto value = original(R"(pub protocol Run roles(P, V)(
    a: (bool, index) @P; b: (bool, index) @V
) -> (bool, index) @(P, V):
    return @(P = a, V = b)
)");
    take(compileEntry(value));
  });
  cases.run("unit assembly retains authored meaning with an empty layout", [] {
    take(compileEntry(original(R"(pub protocol Run roles(P, V)() -> () @(P, V):
    return @(P = (), V = ())
)")));
  });
  cases.run("role substitution maps assembly components through a callee", [] {
    take(compileEntry(original(R"(protocol Join roles(A, B)(
    a: bool @A; b: bool @B
) -> bool @(A, B):
    return @(A = a, B = b)
pub protocol Run roles(P, V)(x: bool @V; y: bool @P) -> bool @(P, V):
    result <- Join(x, y) @(V, P)
    return result
)")));
  });
  for (StringRef body :
       {"@(P = b, V = a)", "@(P = a, P = a)", "@(Unknown = a)", "@()", "@(P)",
        "@(P: a)", "@(P = a) @V", "a @P", "(a, b) @P"})
    cases.run("invalid role assembly or annotation refuses: " + body, [&] {
      refuses(
          check(
              (R"(pub protocol Run roles(P, V)(a: bool @P; b: bool @V) -> bool @P:
    result = )" +
               body + "\n    return a\n")
                  .str()),
          "source.roles");
    });
  cases.run("heterogeneous components cannot share a value type", [] {
    refuses(check(R"(pub protocol Run roles(P, V)(
    a: bool @P; b: index @V
) -> bool @P:
    result = @(P = a, V = b)
    return a
)"),
            "source.type");
  });
  cases.run("assembly is pure", [] {
    refuses(check(R"(pub protocol Run roles(P)(a: bool @P) -> bool @P:
    result <- @(P = a)
    return result
)"),
            "source.action");
  });
  cases.run("inactive loop roles cannot be reactivated by constants", [] {
    refuses(check(R"(pub protocol Run roles(P, V)() -> bool @P:
    for i in 0..1 roles(P):
        result = @(V = true)
    return true
)"),
            "source.roles");
  });
  cases.run("ordinary affine records cannot acquire assembled aliases", [] {
    refuses(check(R"(#[affine]
struct Token:
    value: bool
pub protocol Run roles(P, V)(a: Token @P; b: Token @V) -> Token @P:
    result = @(P = a, V = b)
    return a
)"),
            "source.permission");
  });
  cases.run("generic assembly rechecks the closed data policy", [] {
    auto project = take(check(R"(type State = builtin("sequence", bool)
protocol Join<T: Type + Copy + Drop> roles(P, V)(
    a: T @P; b: T @V
) -> T @(P, V):
    return @(P = a, V = b)
pub protocol Run roles(P, V)(a: State @P; b: State @V) -> State @P:
    joined <- Join(a, b)
    return a
)"));
    refuses(closeNativeRun(project, "m::Run"), "source.roles");
  });
  cases.run("formal source retains ordered written components", [] {
    auto project =
        take(check(R"(pub protocol Run roles(P, V)(a: bool @P) -> bool @P:
    return a
spec for Run:
    ensures @(P = a, V = true)
)"));
    auto written = take(inspectWrittenSource(project));
    require(written.find("formal.role-assembly") != std::string::npos,
            "formal assembly erased or translated into an equality");
  });
  cases.run("assembly is confined to protocol mode", [] {
    refuses(check(R"(def wrong(a: bool) -> bool:
    return @(P = a)
)"),
            "source.mode");
  });
  cases.run("owner-local data cannot become a shared family", [] {
    refuses(check(R"(type State = builtin("shake128_state")
pub protocol Run roles(P, V)(a: State @P; b: State @V) -> State @P:
    result = @(P = a, V = b)
    return a
)"),
            "source.roles");
  });
  cases.run("oracle handles cannot enter ordinary role assembly", [] {
    refuses(check(R"(type Kind = builtin("oracle.table", bool, 4)
type Oracle = builtin("oracle", Kind)
pub protocol Run roles(P, V)(word: Oracle @P -> V) -> bool @P:
    result = @(P = word, V = word)
    return true
)"),
            "source.oracle-boundary");
  });
  cases.run("service queries cannot silently discard expression roles", [] {
    refuses(check(R"(domain F = field("bls12-381.fr")
pub protocol Run roles(P, V)(coins: Random<F> @P) -> F @P:
    value <- coins.draw() @V
    return value
)"),
            "source.roles");
  });
  cases.run("ordinary calls refuse a protocol role substitution", [] {
    refuses(check(R"(def identity(x: bool) -> bool:
    return x
pub protocol Run roles(P)(x: bool @P) -> bool @P:
    return identity(x) @P
)"),
            "source.call");
  });
  cases.run(
      "valid IR with changed role operands fails source correspondence", [] {
        auto value = original(shared);
        mlir::DialectRegistry registry;
        registerDialects(registry);
        mlir::MLIRContext context(registry);
        context.loadAllAvailableDialects();
        auto module =
            mlir::parseSourceString<mlir::ModuleOp>(value.bytes(), &context);
        require(bool(module), "original did not parse");
        module->walk([](protocol_ir::AssembleRolesOp op) {
          auto first = op.getInputs()[0];
          op.getInputsMutable()[0].set(op.getInputs()[1]);
          op.getInputsMutable()[1].set(first);
        });
        require(mlir::succeeded(mlir::verify(*module)),
                "mutation failed formation");
        refuses(compareOriginal(value.entry(), *module),
                "source.correspondence");
      });
  return cases.result();
}
