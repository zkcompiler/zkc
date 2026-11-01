#include "mlir/IR/SymbolTable.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/NativeLanguage.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Language/Layout.h"
#include "zkc/Language/Names.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
namespace {
Expected<CheckedProject> check(StringRef code) {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto captured =
      capture({{"m", code.str(), "distributed-succession.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
const Declaration &named(ArrayRef<Declaration> declarations, StringRef name) {
  auto at = llvm::find_if(declarations, [&](const auto &declaration) {
    return declaration.name == name;
  });
  require(at != declarations.end(), "missing declaration: " + name);
  return *at;
}
Body &body(const CheckedProject &project, StringRef name) {
  return const_cast<Body &>(*named(project.declarations(), name).body);
}
void accept(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
void reject(Error error, StringRef code) {
  require(bool(error), "expected refusal: " + code);
  auto message = toString(std::move(error));
  require(namesIdentifier(message, code), "unexpected refusal: " + message);
}
CheckedOriginal original(StringRef code) {
  auto project = take(check(code));
  accept(checkScopedElaboration(project));
  auto closed = take(closeNativeRun(project, "m::Run"));
  accept(checkScopedSpecialization(closed));
  return take(prepareOriginal(closed));
}
void withModule(const CheckedOriginal &source,
                function_ref<void(mlir::ModuleOp)> test) {
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry, mlir::MLIRContext::Threading::DISABLED);
  auto candidate =
      mlir::parseSourceString<mlir::ModuleOp>(source.bytes(), &context);
  require(bool(candidate), "original did not parse");
  test(*candidate);
}
void complete(const CheckedOriginal &source) {
  auto interface = take(readInterface(source.bytes(), source.interfaceJson()));
  accept(compareInterface(source.entry(), interface));
  take(admitOriginal(source.entry(), source.bytes(), source.interfaceJson()));
  for (auto options :
       {EntryOptions{}, EntryOptions{false}, EntryOptions{true, true}})
    take(compileEntry(source, options));
}
bool contract(exec::ApplyOp op, StringRef name) {
  auto binding = mlir::dyn_cast_or_null<runtime::BindingOp>(
      mlir::SymbolTable::lookupNearestSymbolFrom(op, op.getBindingAttr()));
  return binding && binding.getContract() == name;
}
SmallVector<mlir::Operation *> passes(mlir::ModuleOp module) {
  SmallVector<mlir::Operation *> result;
  module.walk([&](mlir::Operation *op) {
    if (op->getName().getStringRef() != "protocol.local_call")
      return;
    auto callee = op->getAttrOfType<mlir::FlatSymbolRefAttr>("callee");
    auto *helper = mlir::SymbolTable::lookupNearestSymbolFrom(op, callee);
    require(helper != nullptr, "missing custody helper");
    bool pass = false;
    helper->walk([&](exec::ApplyOp apply) {
      pass |= contract(apply, "resource_unit.pass");
    });
    if (pass)
      result.push_back(op);
  });
  return result;
}
std::string fixture() {
  auto contents = MemoryBuffer::getFile(ZKC_SUCCESSION_FIXTURE);
  require(bool(contents), "missing distributed succession fixture");
  return (*contents)->getBuffer().str();
}
const char *twoRoots = R"(#[linear]
struct Ticket roles(A, B):
    pub first: index @A
    pub second: index @A
    pub empty: () @B
pub protocol Run roles(P, V)() -> index @P:
    left <- Ticket roles(P, V) {first: 7, second: 11, empty: ()}
    right <- Ticket roles(P, V) {first: 17, second: 19, empty: ()}
    a <- inspect_record(left)
    b <- inspect_record(right)
    next_left <- repack_record(a.0, a.1)
    next_right <- repack_record(b.0, b.1)
    fields <- unpack(next_left)
    other <- unpack(next_right)
    result <- fields.0 + other.1
    return result
)";
} // namespace
int main() {
  Cases cases;
  for (unsigned iterations : {0, 1, 3})
    cases.run(
        "nested sealed succession with " + Twine(iterations) + " trips", [&] {
          auto code = fixture();
          auto at = code.find("0..3");
          require(at != std::string::npos, "missing repeat count");
          code.replace(at, 4, "0.." + std::to_string(iterations));
          auto source = original(code);
          complete(source);
          withModule(source, [&](mlir::ModuleOp module) {
            unsigned creates = 0, consumes = 0;
            module.walk([&](exec::ApplyOp op) {
              creates += contract(op, "resource_unit.create");
              consumes += contract(op, "resource_unit.consume");
            });
            require(creates == 4 && consumes == 4 && passes(module).size() == 2,
                    "lost or duplicated a fixed-roster custody fragment");
            mlir::Operation *root = nullptr;
            module.walk([&](mlir::Operation *op) {
              auto symbol = op->getAttrOfType<mlir::StringAttr>("sym_name");
              if (op->getName().getStringRef() == "protocol.func" && symbol &&
                  symbol.getValue() == source.entry().protocol().symbol)
                root = op;
            });
            require(root != nullptr, "missing root protocol");
            root->walk([&](mlir::Operation *op) {
              if (op->getName().getStringRef() == "protocol.local_call")
                require(
                    op->getAttrOfType<mlir::StringAttr>("role").getValue() !=
                        nativeRoleName(1),
                    "custody operation touched the absent participant Q");
            });
          });
        });
  cases.run("empty wrapper repacks unit at its exact partial roster", [] {
    complete(original(R"(#[linear]
struct Empty<Tag: nat> roles(A, B):
pub protocol Run roles(P, Q, V)() -> bool @P:
    initial <- Empty<3> roles(V, P) {}
    mut state = initial
    for i in 0..2 roles(P, V):
        observed <- inspect_record(state)
        next <- repack_record(observed.0, ())
        state := next
    fields <- unpack(state)
    return true
)"));
  });
  cases.run("direct inspection preserves both equal-type roots",
            [] { complete(original(twoRoots)); });
  cases.run("multiple participant components remain distinct payload data", [] {
    complete(original(R"(#[affine]
struct Ticket roles(A, B):
    value: bool @(A, B)
pub protocol Run roles(P, V)() -> bool @V:
    value <- Ticket roles(V, P) {value: true}
    observed <- inspect_record(value)
    next <- repack_record(observed.0, (false,))
    fields <- unpack(next)
    return true
)"));
  });
  cases.run("nested oracle observations preserve both holder families", [] {
    complete(original(R"(domain F = field("bls12-381.fr")
type Vec = builtin("vector", F)
type K = builtin("oracle.table", F, 16)
type O = builtin("oracle", K)
struct Sources roles(A, B, V):
    left: O @A -> V
    right: O @B -> V
#[linear]
struct Ticket roles(A, B, V):
    sources: Sources roles(B, A, V)
    point: index @V
pub protocol Run roles(P, Q, V)(xs: Vec @P, ys: Vec @Q) -> F @V:
    left <- send xs from P to V as oracle<K>
    right <- send ys from Q to V as oracle<K>
    sources = Sources roles(P, Q, V) {left: left, right: right}
    value <- Ticket roles(Q, P, V) {sources: sources, point: 0}
    observed <- inspect_record(value)
    next <- repack_record(observed.0, observed.1)
    fields <- unpack(next)
    answer <- query fields.0.right at fields.1
    return answer
)"));
  });
  for (unsigned mutation = 0; mutation < 4; ++mutation)
    cases.run(
        "independent interface fragment/schema mutation " + Twine(mutation),
        [&] {
          auto source = original(fixture());
          auto document = take(json::parse(source.interfaceJson()));
          bool changed = false;
          for (auto &protocol : *document.getAsObject()->getArray("protocols"))
            for (auto &output : *protocol.getAsObject()->getArray("outputs")) {
              auto &schema = *output.getAsObject()->getObject("schema");
              if (changed || schema.getInteger("custody") != 2)
                continue;
              if (mutation == 0)
                schema["custody"] = int64_t(1);
              else if (mutation == 1)
                schema["custody"] = int64_t(3);
              else if (mutation == 2)
                schema["type"] = "different nominal or phantom instance";
              else
                schema.getArray("fields")->pop_back();
              changed = true;
            }
          require(changed, "missing distributed helper result schema");
          reject(checkInterface(source, printJson(document)),
                 "source.interface");
        });
  for (unsigned mutation = 0; mutation < 5; ++mutation)
    cases.run("actual candidate custody mutation " + Twine(mutation), [&] {
      auto source = original(twoRoots);
      withModule(source, [&](mlir::ModuleOp module) {
        auto calls = passes(module);
        require(calls.size() == 4, "fixture needs two fragments per root");
        if (mutation == 0) {
          // Exchange the P fragments of two live equal-type roots. Native
          // formation alone cannot establish their authored correspondence.
          auto left = calls[0]->getOperand(0);
          calls[0]->setOperand(0, calls[2]->getOperand(0));
          calls[2]->setOperand(0, left);
          require(succeeded(admitStage(module)),
                  "balanced root exchange should remain natively formed");
          refuses(compareOriginal(source.entry(), module),
                  "source.correspondence");
        } else if (mutation == 1) {
          calls[1]->setOperand(0, calls[0]->getOperand(0));
          refuses(compareOriginal(source.entry(), module), "target.admission");
        } else if (mutation == 2) {
          calls[0]->getResult(0).replaceAllUsesWith(calls[0]->getOperand(0));
          calls[0]->erase();
          require(succeeded(admitStage(module)),
                  "forwarding without a pass should remain formed");
          refuses(compareOriginal(source.entry(), module),
                  "source.correspondence");
        } else if (mutation == 3) {
          mlir::OpBuilder builder(calls[0]);
          builder.clone(*calls[0]);
          refuses(compareOriginal(source.entry(), module), "target.admission");
        } else {
          auto first = calls[0]->getOperand(0);
          calls[0]->setOperand(0, calls[1]->getOperand(0));
          calls[1]->setOperand(0, first);
          refuses(compareOriginal(source.entry(), module), "target.admission");
        }
      });
    });
  cases.run("actual candidate cannot exchange equal-type payload fields", [] {
    auto source = original(twoRoots);
    withModule(source, [&](mlir::ModuleOp module) {
      unsigned changed = 0;
      module.walk([&](mlir::Operation *op) {
        if (op->getName().getStringRef() != "protocol.return" ||
            op->getNumOperands() != 1)
          return;
        auto *sum = op->getOperand(0).getDefiningOp();
        require(sum && sum->getNumOperands() == 2, "missing returned sum");
        sum->setOperand(0, sum->getOperand(1));
        ++changed;
      });
      require(changed == 1 && succeeded(admitStage(module)),
              "equal-type payload mutation should remain formed");
      refuses(compareOriginal(source.entry(), module), "source.correspondence");
    });
  });
  for (unsigned mutation = 0; mutation < 7; ++mutation)
    cases.run(
        "independent distributed invocation mutation " + Twine(mutation), [&] {
          auto project = take(check(twoRoots));
          auto &checked = body(project, "Run");
          SmallVector<Operation *> inspections, repacks;
          for (auto &op : checked.operations)
            if (auto *action = std::get_if<Construct>(&op.action)) {
              if (action->kind == Construct::Kind::Inspect)
                inspections.push_back(&op);
              if (action->kind == Construct::Kind::Repack)
                repacks.push_back(&op);
            }
          require(inspections.size() == 2 && repacks.size() == 2,
                  "missing intrinsics");
          if (mutation == 0) {
            std::swap(std::get<Construct>(inspections[0]->action).operands[0],
                      std::get<Construct>(inspections[1]->action).operands[0]);
            std::swap(inspections[0]->binding->operands[0],
                      inspections[1]->binding->operands[0]);
          } else if (mutation == 1) {
            auto &placed =
                *checked.values[repacks[0]->results[0].index].placement;
            std::swap(std::get<ProductPlacement>(placed.value).arguments[0],
                      std::get<ProductPlacement>(placed.value).arguments[1]);
          } else if (mutation == 2) {
            auto id = repacks[0]->binding->operands[1];
            auto &placed = std::get<ProductPlacement>(
                checked.values[id.index].placement->value);
            placed.fields.back() = DataPlacement{{0}};
          } else if (mutation == 3)
            repacks[0]->binding->lexicalOwner =
                repacks[0]->binding->target.declaration;
          else if (mutation == 4)
            std::get<Construct>(repacks[0]->action).operands[0] =
                repacks[1]->binding->operands[0];
          else {
            auto id = repacks[0]->binding->operands[1];
            auto &placed = std::get<ProductPlacement>(
                checked.values[id.index].placement->value);
            if (mutation == 5)
              placed.fields.pop_back();
            else
              placed.fields.push_back(placed.fields.back());
          }
          reject(checkScopedElaboration(project), "source.binding-witness");
        });
  for (StringRef call : {"inspect_record(value)", "repack_record(value, ())"})
    cases.run("foreign home cannot invoke " + call, [&] {
      refuses(check("module Home:\n    #[linear]\n    pub struct Ticket "
                    "roles(A, B):\n"
                    "protocol invalid roles(P, V)(value: Home::Ticket roles(P, "
                    "V)) -> () @P:\n"
                    "    observed <- " +
                    call.str() + "\n    return ()\n"),
              "source.private");
    });
  for (StringRef child : {"#[linear]", "#[affine]"})
    cases.run("succession refuses a noncopyable child " + child, [&] {
      refuses(check(child.str() + R"(
struct Child:
#[linear]
struct Parent roles(P, V):
    child: Child @P
protocol invalid roles(P, V)(value: Parent roles(P, V)) -> Parent roles(P, V):
    observed <- inspect_record(value)
    return observed.0
 )"),
              "source.permission");
    });
  cases.run("zero-storage child permissions remain required", [] {
    refuses(check(R"(#[linear]
struct Child:
#[linear]
struct Parent roles(P, V):
    children: [Child; 0] @P
protocol invalid roles(P, V)(value: Parent roles(P, V)) -> Parent roles(P, V):
    observed <- inspect_record(value)
    return observed.0
)"),
            "source.permission");
  });
  cases.run("equal-type payloads at different participants cannot be swapped",
            [] {
              refuses(check(R"(#[linear]
struct Ticket roles(A, B):
    first: index @A
    second: index @B
protocol invalid roles(P, V)(value: Ticket roles(P, V)) -> Ticket roles(P, V):
    observed <- inspect_record(value)
    next <- repack_record(observed.0, (observed.1.1, observed.1.0))
    return next
)"),
                      "source.roles");
            });
  for (StringRef target : {"Ticket<2>", "Other<1>"})
    cases.run("equal storage cannot replace nominal or phantom identity " +
                  target,
              [&] {
                refuses(check(R"(#[linear]
struct Ticket<Tag: nat> roles(A, B):
#[linear]
struct Other<Tag: nat> roles(A, B):
protocol invalid roles(P, V)(value: Ticket<1> roles(P, V)) -> )" +
                              target.str() +
                              R"( roles(P, V):
    observed <- inspect_record(value)
    next <- repack_record(observed.0, ())
    return next
)"),
                        "source.type");
              });
  cases.run("empty wrapper role permutation cannot change on succession", [] {
    refuses(check(R"(#[linear]
struct Ticket roles(A, B):
protocol invalid roles(P, V)(value: Ticket roles(P, V)) -> Ticket roles(V, P):
    observed <- inspect_record(value)
    next <- repack_record(observed.0, ())
    return next
)"),
            "source.placement");
  });
  cases.run("partial active roster cannot operate on absent custody", [] {
    refuses(check(R"(#[linear]
struct Ticket roles(A, B):
pub protocol Run roles(P, V)() -> bool @P:
    initial <- Ticket roles(P, V) {}
    mut state = initial
    for i in 0..1 roles(P):
        observed <- inspect_record(state)
        state := observed.0
    fields <- unpack(state)
    return true
)"),
            "source.roles");
  });
  cases.run("intrinsic invocation cannot override the wrapper role map", [] {
    refuses(check(R"(#[linear]
struct Ticket roles(A, B):
protocol invalid roles(P, V)(value: Ticket roles(P, V)) -> Ticket roles(P, V):
    observed <- inspect_record roles(V, P)(value)
    return observed.0
)"),
            "source.layout");
  });
  cases.run("foreign projection cannot expose a sealed observation", [] {
    refuses(check(R"(module Home:
    #[sealed]
    #[linear]
    pub struct Ticket roles(A, B):
        pub value: bool @A
protocol invalid roles(P, V)(value: Home::Ticket roles(P, V)) -> bool @P:
    return value.value
)"),
            "source.private");
  });
  for (bool copied : {false, true})
    cases.run(copied ? "inspection cannot copy a wrapper"
                     : "inspection cannot hide a drop",
              [&] {
                refuses(
                    check(R"(#[linear]
struct Ticket roles(P, V):
protocol invalid roles(P, V)(value: Ticket roles(P, V)) -> bool @P:
    observed <- inspect_record(value)
)" +
                          std::string(copied ? "    again <- unpack(value)\n   "
                                               " done <- unpack(observed.0)\n"
                                             : "") +
                          "    return true\n"),
                    copied ? "source.move" : "source.drop");
              });
  cases.run("consume and fresh-create remains an invalid repeat successor", [] {
    auto project = take(check(R"(#[linear]
struct Ticket roles(P, V):
    pub value: index @P
    pub empty: () @V
pub protocol Run roles(P, V)() -> index @P:
    initial <- Ticket roles(P, V) {value: 7, empty: ()}
    mut state = initial
    for i in 0..2 roles(P, V):
        fields <- unpack(state)
        next <- Ticket roles(P, V) {value: fields.0, empty: fields.1}
        state := next
    fields <- unpack(state)
    return fields.0
)"));
    refuses(prepareOriginal(take(closeNativeRun(project, "m::Run"))),
            "mathematical-formation");
  });
  return cases.result();
}
