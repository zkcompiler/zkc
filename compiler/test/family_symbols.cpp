#include "Names.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Source/Codec.h"
#include "zkc/Transforms/Protocol.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <functional>
#include <set>

using namespace mlir;
using namespace llvm;
using namespace zkc;
namespace {
unsigned checks = 0, failures = 0;
void check(bool condition, StringRef label) {
  ++checks;
  if (!condition) {
    ++failures;
    errs() << "FAIL: " << label << '\n';
  }
}
template <class T> T accept(Expected<T> result) {
  if (!result) {
    errs() << toString(result.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*result);
}
ProtocolModuleOp root(ModuleOp module) {
  return cast<ProtocolModuleOp>(&module.getBody()->front());
}
Operation *symbol(ModuleOp module, StringRef name) {
  return SymbolTable::lookupSymbolIn(root(module), name);
}
Operation *user(ModuleOp module, bool participant) {
  Operation *result = nullptr;
  module.walk([&](Operation *op) {
    if (!result && (participant ? isa<ParticipantOp>(op) : isa<InstanceOp>(op)))
      result = op;
  });
  return result;
}
Operation *owner(ModuleOp module, bool participant) {
  return participant ? user(module, true) : symbol(module, "Family");
}
ArrayAttr replace(ArrayAttr array, unsigned i, Attribute value) {
  SmallVector<Attribute> items(array.begin(), array.end());
  items[i] = value;
  return ArrayAttr::get(array.getContext(), items);
}
void binding(Operation *op, Attribute value) {
  auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
  auto pair = cast<ArrayAttr>(parameters[0]);
  op->setAttr("parameters", replace(parameters, 0, replace(pair, 1, value)));
}
ArrayAttr ingress(Operation *op) {
  return cast<ArrayAttr>(
      cast<ArrayAttr>(op->getAttrOfType<ArrayAttr>("parameters")[0])[1]);
}
void selector(Operation *op, unsigned field, Attribute value) {
  auto family = ingress(op);
  auto selectors = cast<ArrayAttr>(family[2]);
  auto record = cast<ArrayAttr>(selectors[0]);
  binding(op, replace(family, 2,
                      replace(selectors, 0, replace(record, field, value))));
}
void refuse(ModuleOp original, bool participant, StringRef label,
            StringRef code,
            const std::function<void(ModuleOp, Operation *)> &mutate) {
  OwningOpRef<ModuleOp> copy(cast<ModuleOp>(original->clone()));
  auto *op = user(*copy, participant);
  mutate(*copy, op);
  std::string diagnostic;
  ScopedDiagnosticHandler handler(original.getContext(), [&](Diagnostic &d) {
    raw_string_ostream stream(diagnostic);
    d.print(stream);
    return success();
  });
  // Direct dispatch proves closure at the symbol user, without the module's
  // export/admission verifier masking a missing dialect check.
  SymbolTableCollection tables;
  auto interface = dyn_cast<SymbolUserOpInterface>(op);
  check(interface && failed(interface.verifySymbolUses(tables)) &&
            namesIdentifier(diagnostic, code),
        (Twine(participant ? "participant " : "common ") + label).str());
  check(failed(verify(*copy)), (Twine("whole IR refusal: ") + label).str());
}
void negatives(ModuleOp module, bool participant) {
  Builder b(module.getContext());
  auto s = [&](StringRef text) { return b.getStringAttr(text); };
  auto test = [&](StringRef label, StringRef code, auto mutate) {
    refuse(module, participant, label, code, mutate);
  };
  test("lost function", "interactive-family-selector",
       [](ModuleOp m, Operation *) { symbol(m, "Select")->erase(); });
  test("wrong symbol kind", "interactive-family-selector",
       [&](ModuleOp, Operation *op) {
         selector(
             op, 1,
             FlatSymbolRefAttr::get(op->getAttrOfType<StringAttr>("sym_name")));
       });
  test("external function", "interactive-family-selector",
       [](ModuleOp m, Operation *) {
         symbol(m, "Select")->getRegion(0).getBlocks().clear();
       });
  test("missing signature", "interactive-family-signature",
       [](ModuleOp m, Operation *) {
         symbol(m, "Select")->removeAttr("function_type");
       });
  for (auto results : {SmallVector<Type>{}, SmallVector<Type>{b.getI1Type()},
                       SmallVector<Type>{b.getIntegerType(64, false),
                                         b.getIntegerType(64, false)}})
    test("return signature", "interactive-family-signature",
         [&](ModuleOp m, Operation *) {
           symbol(m, "Select")
               ->setAttr("function_type",
                         TypeAttr::get(b.getFunctionType(
                             {b.getIntegerType(64, false)}, results)));
         });
  test("input signature", "interactive-family-signature",
       [&](ModuleOp m, Operation *) {
         symbol(m, "Select")
             ->setAttr("function_type",
                       TypeAttr::get(b.getFunctionType(
                           {b.getI1Type()}, {b.getIntegerType(64, false)})));
       });
  test("string function", "interactive-family-binding",
       [&](ModuleOp, Operation *op) { selector(op, 1, s("Select")); });
  test("nested symbol", "interactive-family-binding",
       [&](ModuleOp, Operation *op) {
         selector(op, 1,
                  SymbolRefAttr::get(
                      b.getContext(), "Select",
                      {FlatSymbolRefAttr::get(b.getContext(), "nested")}));
       });
  test("malformed parameter", "interactive-family-binding",
       [&](ModuleOp, Operation *op) {
         op->setAttr("parameters", b.getArrayAttr({s("bad")}));
       });
  test("malformed ingress", "interactive-family-binding",
       [&](ModuleOp, Operation *op) {
         binding(op, b.getArrayAttr({s("ingress")}));
       });
  test("wrong tag", "interactive-family-binding", [&](ModuleOp, Operation *op) {
    binding(op, replace(ingress(op), 0, s("unknown")));
  });
  for (StringRef bound : {"01", "-1"})
    test("malformed bound", "interactive-family-binding",
         [&](ModuleOp, Operation *op) {
           binding(op, replace(ingress(op), 1, s(bound)));
         });
  for (StringRef bound : {"1048577", "18446744073709551616"})
    test("bound past the limit", "interactive-family-bound",
         [&](ModuleOp, Operation *op) {
           binding(op, replace(ingress(op), 1, s(bound)));
         });
  test("malformed selector", "interactive-family-binding",
       [&](ModuleOp, Operation *op) {
         auto selectors = cast<ArrayAttr>(ingress(op)[2]);
         binding(op, replace(ingress(op), 2, replace(selectors, 0, s("bad"))));
       });
  test("wrong role", "interactive-family-roles",
       [&](ModuleOp, Operation *op) { selector(op, 0, s("Nobody")); });
  test("duplicate role", "interactive-family-roles",
       [&](ModuleOp, Operation *op) {
         auto selectors = cast<ArrayAttr>(ingress(op)[2]);
         binding(op,
                 replace(ingress(op), 2, replace(selectors, 1, selectors[0])));
       });
  test("missing role", "interactive-family-roles",
       [&](ModuleOp, Operation *op) {
         binding(op, replace(ingress(op), 2, b.getArrayAttr({})));
       });
  test("argument shape", "interactive-family-binding",
       [&](ModuleOp, Operation *op) { selector(op, 2, s("pn")); });
  test("argument element", "interactive-family-argument",
       [&](ModuleOp, Operation *op) {
         selector(op, 2, b.getArrayAttr({b.getI64IntegerAttr(0)}));
       });
  test("missing argument", "interactive-family-argument",
       [&](ModuleOp, Operation *op) {
         selector(op, 2, b.getArrayAttr({s("missing")}));
       });
  test("duplicate argument", "interactive-family-argument",
       [&](ModuleOp, Operation *op) {
         selector(op, 2, b.getArrayAttr({s("pn"), s("pn")}));
       });
  test("wrong owner",
       participant ? "interactive-family-argument" : "interactive-family-input",
       [&](ModuleOp, Operation *op) {
         selector(op, 2, b.getArrayAttr({s("vn")}));
       });
  test("missing binder table", "interactive-family-argument-names",
       [&](ModuleOp m, Operation *) {
         owner(m, participant)->removeAttr("argument_names");
       });
  test("wrong binder attribute", "interactive-family-argument-names",
       [&](ModuleOp m, Operation *) {
         owner(m, participant)->setAttr("argument_names", s("bad"));
       });
  test("short binder table", "interactive-family-argument-names",
       [&](ModuleOp m, Operation *) {
         owner(m, participant)
             ->setAttr("argument_names", b.getArrayAttr({s("pn")}));
       });
  test("duplicate binder", "interactive-family-argument-names",
       [&](ModuleOp m, Operation *) {
         auto *def = owner(m, participant);
         auto names = def->getAttrOfType<ArrayAttr>("argument_names");
         def->setAttr("argument_names", replace(names, 1, names[0]));
       });
  test("malformed owner signature", "interactive-callable-type",
       [&](ModuleOp m, Operation *) {
         owner(m, participant)
             ->setAttr("function_type", TypeAttr::get(b.getI1Type()));
       });
  test("capability input", "interactive-family-input",
       [&](ModuleOp m, Operation *) {
         auto *def = owner(m, participant);
         auto ft = cast<FunctionType>(
             def->getAttrOfType<TypeAttr>("function_type").getValue());
         SmallVector<Type> inputs(ft.getInputs());
         inputs[0] = CapabilityType::get(b.getContext(), "rng:goldilocks");
         def->setAttr("function_type", TypeAttr::get(b.getFunctionType(
                                           inputs, ft.getResults())));
       });
  test("duplicate parameter", "interactive-parameter-binding",
       [&](ModuleOp, Operation *op) {
         auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
         op->setAttr("parameters", replace(parameters, 1, parameters[0]));
       });
  if (!participant) {
    test("undeclared parameter", "interactive-parameter-binding",
         [&](ModuleOp, Operation *op) {
           auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
           op->setAttr("parameters",
                       replace(parameters, 0,
                               replace(cast<ArrayAttr>(parameters[0]), 0,
                                       s("unknown"))));
         });
    test("unbound parameter", "interactive-parameter-binding",
         [&](ModuleOp, Operation *op) {
           auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
           op->setAttr("parameters", b.getArrayAttr({parameters[0]}));
         });
    test("short role table", "interactive-port-roles",
         [&](ModuleOp m, Operation *) {
           owner(m, false)->setAttr("input_roles", b.getArrayAttr({}));
         });
  } else {
    test("lost sibling", "interactive-family-roles",
         [](ModuleOp m, Operation *op) {
           for (auto p : llvm::make_early_inc_range(
                    root(m).getBody().front().getOps<ParticipantOp>()))
             if (p.getOperation() != op)
               p.erase();
         });
    test("malformed sibling", "interactive-callable-type",
         [](ModuleOp m, Operation *op) {
           for (auto p : root(m).getBody().front().getOps<ParticipantOp>())
             if (p.getOperation() != op)
               p->removeAttr("function_type");
         });
  }
}
void rename(ModuleOp module, unsigned expected) {
  auto *function = symbol(module, "Select");
  auto uses = SymbolTable::getSymbolUses(function, root(module));
  std::set<Operation *> users;
  if (uses)
    for (auto use : *uses) {
      users.insert(use.getUser());
      check(isa<SymbolUserOpInterface>(use.getUser()),
            "selector has symbol user interface");
    }
  check(uses && users.size() == expected &&
            !SymbolTable::symbolKnownUseEmpty(function, root(module)),
        "generic use discovery finds every selector owner");
  auto name = StringAttr::get(module.getContext(), "Renamed");
  check(succeeded(
            SymbolTable::replaceAllSymbolUses(function, name, root(module))),
        "generic symbol rename succeeds");
  SymbolTable::setSymbolName(function, name);
  check(succeeded(verify(module)), "renamed selectors verify");
  auto source = accept(protocol::exportSource(module));
  auto &functions = std::holds_alternative<source::Module>(source)
                        ? std::get<source::Module>(source).functions
                        : std::get<source::Participants>(source).functions;
  check(functions.front().name == "Renamed", "renamed function exported");
  auto renamed = [&](const source::ParameterBindings &parameters) {
    for (const auto &[key, value] : parameters)
      for (const auto &selector :
           std::get<source::FamilyIngress>(value).selectors)
        check(selector.function == "Renamed", "every nested selector renamed");
  };
  if (auto *common = std::get_if<source::Module>(&source))
    for (const auto &instance : common->instances)
      renamed(instance.parameters);
  else
    for (const auto &participant :
         std::get<source::Participants>(source).participants)
      renamed(participant.parameters);
}
void roundtrip(ModuleOp module) {
  auto content = accept(protocol::exportSource(module));
  auto decoded = accept(source::decode(source::encode(content)));
  auto restored = accept(protocol::importModule(decoded, *module.getContext()));
  auto again = accept(protocol::exportSource(*restored));
  check(source::encode(content) == source::encode(again),
        "carrier roundtrip and alpha renaming");
  std::string text;
  raw_string_ostream stream(text);
  module.print(stream);
  auto parsed = parseSourceString<ModuleOp>(text, module.getContext());
  check(bool(parsed), "textual MLIR roundtrip");
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto document = accept(frontend::parseProtocolDocument(R"pir(module {
    fn Select(n: index) -> index { return n; }
    protocol Family {
      roles (P, V);
      parameters (rounds, unused);
      inputs (P pn: index, P spare: bool, V vn: index, V extra: bool);
      outputs (P index, V index);
      loop [round] rounds carry (a = pn, b = vn) -> (x, y) {
        message [ping] index: P(a) -> V(got);
        yield (a, got);
      }
      return (x, y);
    }
    instance Main: Family {
      parameters (rounds = ingress(10, Prover = Select(pn), Verifier = Select(vn)),
                  unused = ingress(10, Prover = Select(pn), Verifier = Select(vn)));
      roles (P = Prover, V = Verifier);
    }
    entry main = Main;
  })pir"));
  auto common = accept(protocol::importModule(document.root(), context));
  negatives(*common, false);
  roundtrip(*common);
  auto participants = accept(protocol::project(*common));
  negatives(*participants, true);
  roundtrip(*participants);
  rename(*common, 1);
  // Projection after generic rename must preserve references too.
  auto renamedProjection = accept(protocol::project(*common));
  roundtrip(*renamedProjection);
  rename(*participants, 2);
  check(succeeded(protocol::lowerPhysical(*participants)), "physical lowering");
  check(succeeded(verify(*participants)), "physical symbol verification");
  roundtrip(*participants);
  outs() << checks << " family symbol checks, " << failures << " failures\n";
  return failures ? 1 : 0;
}
