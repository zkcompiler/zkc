#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Translation/Language.h"
using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
namespace {
CheckedProject checked(StringRef code) {
  CaptureOptions options;
  options.format = "zkc-layout";
  return take(analyze(take(capture({{"m", code.str(), "record-transport.zkc"}},
                                   options)))
                  .checkedProject());
}
void original(StringRef code,
              function_ref<void(const ClosedEntry &, mlir::ModuleOp)> test) {
  auto project = checked(code);
  auto entry = take(closeNativeRun(project, "m::Run"));
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto bytes = take(emitOriginal(entry, context));
  auto candidate = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
  require(bool(candidate), "record source original did not parse");
  take(compareOriginal(entry, *candidate));
  require(mlir::succeeded(admitStage(*candidate)),
          "record source original failed native stage admission");
  test(entry, *candidate);
}
} // namespace
int main() {
  Cases cases;
  cases.run(
      "distributed payload passage compares actual equal-typed operands", [] {
        original(
            R"(struct State roles(P, V):
    pub left: index @P
    pub right: index @P
    pub empty: () @V
protocol read roles(P, V)(state: State roles(P, V)) -> index @P:
    return state.left
pub protocol Run roles(P, V)() -> index @P:
    state = State roles(P, V) {right: 2, empty: (), left: 1}
    result <- state.read()
    return result
)",
            [](const ClosedEntry &entry, mlir::ModuleOp candidate) {
              unsigned changed = 0;
              candidate.walk([&](mlir::Operation *operation) {
                if (operation->getName().getStringRef() != "protocol.apply")
                  return;
                require(operation->getNumOperands() == 2 &&
                            operation->getOperand(0).getType() ==
                                operation->getOperand(1).getType(),
                        "record payload fixture has unexpected ABI");
                auto first = operation->getOperand(0);
                operation->setOperand(0, operation->getOperand(1));
                operation->setOperand(1, first);
                ++changed;
              });
              require(
                  changed == 1 && mlir::succeeded(admitStage(candidate)),
                  "equal-role payload mutation should remain natively formed");
              refuses(compareOriginal(entry, candidate),
                      "source.correspondence");
            });
      });
  cases.run(
      "empty restricted record keeps every role-local custody fragment", [] {
        original(
            R"(#[linear]
struct Ticket roles(P, V):
protocol forward roles(P, V)(ticket: Ticket roles(P, V)) -> Ticket roles(P, V):
    return ticket
pub protocol Run roles(P, V)() -> bool @V:
    ticket <- Ticket roles(P, V) {}
    next <- ticket.forward()
    empty <- unpack(next)
    return true
)",
            [](const ClosedEntry &entry, mlir::ModuleOp candidate) {
              unsigned applications = 0, localCalls = 0;
              candidate.walk([&](mlir::Operation *operation) {
                if (operation->getName().getStringRef() ==
                    "protocol.local_call")
                  ++localCalls;
                if (operation->getName().getStringRef() != "protocol.apply")
                  return;
                require(operation->getNumOperands() == 2 &&
                            operation->getNumResults() == 2,
                        "empty record lost distinct native custody fragments");
                operation->setOperand(1, operation->getOperand(0));
                ++applications;
              });
              require(applications == 1 && localCalls == 4,
                      "empty custody creation or destruction was erased");
              refuses(compareOriginal(entry, candidate), "target.admission");
            });
      });
  cases.run("qualified installed unpack retains distributed field placements",
            [] {
              original(R"(#[linear]
struct Ticket roles(P, V):
    pub value: index @P
    pub empty: () @V
pub protocol Run roles(P, V)() -> index @P:
    ticket <- Ticket roles(P, V) {value: 7, empty: ()}
    fields <- zkc::records::unpack(ticket)
    return fields.0
)",
                       [](const ClosedEntry &, mlir::ModuleOp) {});
            });
  cases.run("authored unpack spelling keeps its protocol target", [] {
    original(R"(struct State roles(P, V):
    pub value: index @P
protocol unpack roles(P, V)(state: State roles(P, V)) -> index @P:
    return 9
pub protocol Run roles(P, V)() -> index @P:
    state = State roles(P, V) {value: 7}
    result <- unpack(state)
    return result
)",
             [](const ClosedEntry &, mlir::ModuleOp candidate) {
               unsigned calls = 0;
               candidate.walk([&](mlir::Operation *operation) {
                 calls +=
                     operation->getName().getStringRef() == "protocol.apply";
               });
               require(calls == 1,
                       "authored unpack was intercepted by its spelling");
             });
  });
  cases.run("two holders retain distinct anchors across a nested record", [] {
    original(
        R"(domain F = field("bls12-381.fr")
type Vec = builtin("vector", F)
type Kind = builtin("oracle.table", F, 16)
type O = builtin("oracle", Kind)
struct Pair roles(A, B, V):
    pub left: O @A -> V
    pub right: O @B -> V
struct State roles(A, B, V):
    pub pair: Pair roles(B, A, V)
protocol read roles(A, B, V)(state: State roles(A, B, V)) -> F @V:
    word = state.pair.right
    answer <- query word at 0
    return answer
pub protocol Run roles(P, Q, V)(xs: Vec @P, ys: Vec @Q) -> F @V:
    first <- send xs from P to V as oracle<Kind>
    second <- send ys from Q to V as oracle<Kind>
    pair = Pair roles(P, Q, V) {left: first, right: second}
    state = State roles(Q, P, V) {pair: pair}
    answer <- state.read()
    return answer
)",
        [](const ClosedEntry &entry, mlir::ModuleOp candidate) {
          unsigned applications = 0;
          candidate.walk([&](mlir::Operation *operation) {
            if (operation->getName().getStringRef() != "protocol.apply")
              return;
            require(operation->getNumOperands() == 4,
                    "two holders did not retain two independent native pairs");
            require(operation->getOperand(1).getType() ==
                        operation->getOperand(3).getType(),
                    "anchor fixture does not have equal static kinds");
            auto first = operation->getOperand(1);
            operation->setOperand(1, operation->getOperand(3));
            operation->setOperand(3, first);
            ++applications;
          });
          require(applications == 1, "missing nested record application");
          refuses(compareOriginal(entry, candidate), "target.admission");
        });
  });
  return cases.result();
}
