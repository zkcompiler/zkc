#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Analysis/TotalClosure.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/IR.h"
#include <fstream>
#include <sstream>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;

namespace {
const char *helpers = R"mlir(
!F = !algebra.field<"bls12-381.fr">
module {
 func.func private @choose(%a:!F, %b:!F) -> !F {
   %unused = algebra.field_add %a, %b : (!F,!F)->!F
   func.return %a : !F
 }
 func.func @entry(%a:!F, %b:!F) -> !F {
   %v = func.call @choose(%a,%b) : (!F,!F)->!F
   func.return %v : !F
 }
})mlir";
OwningOpRef<ModuleOp> parse(StringRef text, MLIRContext &context) {
  auto result =
      parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
  require(bool(result), "test input did not parse");
  return result;
}
func::FuncOp function(ModuleOp owner, StringRef name) {
  return owner.lookupSymbol<func::FuncOp>(name);
}
std::string fixture(StringRef name) {
  std::ifstream input(std::string(ZKC_FIXTURES) + "/" + name.str() + ".mlir");
  require(bool(input), "missing closure fixture");
  std::ostringstream text;
  text << input.rdbuf();
  return text.str();
}
// Relocation of the same declarations is the control: no Protocol owner or
// participant information is needed to admit their mathematical closure.
OwningOpRef<ModuleOp> mathematicalDefinitions(ModuleOp source) {
  auto result = ModuleOp::create(source.getLoc());
  auto unit = *source.getOps<protocol_ir::ProtocolModuleOp>().begin();
  OpBuilder builder(source.getContext());
  builder.setInsertionPointToEnd(result.getBody());
  for (auto &op : unit.getBody().front())
    if (isa<data::DomainOp>(op) ||
        (isa<func::FuncOp>(op) &&
         !protocol::isScopedExecutionFunction(cast<func::FuncOp>(op))))
      builder.clone(op);
  return OwningOpRef<ModuleOp>(result);
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
  cases.run("finite root selection requires unique immediate ownership", [&] {
    auto module = parse(helpers, context);
    auto other = parse(helpers, context);
    auto entry = function(*module, "entry");
    auto helper = function(*module, "choose");
    require(
        succeeded(finite::verifyDefinitionClosure(*module, {entry, helper})),
        "owned finite closure roots were refused");
    require(failed(finite::verifyDefinitionClosure(*module, {entry, entry})),
            "duplicate roots granted another traversal budget");
    require(failed(finite::verifyDefinitionClosure(
                *module, {function(*other, "entry")})),
            "foreign root escaped the selected symbol table");
    require(failed(finite::verifyDefinitionClosure(*module, {nullptr})) &&
                failed(finite::verifyDefinitionClosure(nullptr, {})) &&
                failed(finite::verifyDefinitionClosure(entry, {})),
            "malformed root selection was accepted");
  });
  cases.run("explicit entry preserves unused dependency requirements", [&] {
    auto module = parse(helpers, context);
    SymbolTableCollection symbols;
    auto entry = function(*module, "entry");
    mathematical::TotalClosure closure(*module, symbols, entry);
    require(succeeded(closure.verify()), "closed entry was refused");
    const mathematical::TotalSummary *summary;
    require(succeeded(closure.get(entry, summary)), "missing entry summary");
    require(summary->results.size() == 1 && summary->results[0].count() == 1 &&
                summary->results[0].test(0),
            "result dependency changed");
    require(summary->requirements.count(std::vector<unsigned>{0, 1}),
            "unused intermediate dependency disappeared");
    require(summary->depth == 2 && summary->expandedOperations == 4,
            "callee expansion was not charged");
  });
  cases.run("observation snapshots require owned flat blocks", [&] {
    auto module = parse(helpers, context);
    auto other = parse(helpers, context);
    SymbolTableCollection symbols;
    auto entry = function(*module, "entry");
    mathematical::TotalClosure control(*module, symbols, entry);
    require(succeeded(control.verifyObservations(entry.front())),
            "owned observation body was refused");
    mathematical::TotalClosure foreign(*module, symbols, entry);
    require(
        failed(foreign.verifyObservations(function(*other, "entry").front())),
        "foreign observation body entered this symbol table");
    mathematical::TotalClosure detached(*module, symbols, entry);
    Block unparented;
    require(failed(detached.verifyObservations(unparented)),
            "unparented observation body was accepted");
    auto nested = parse(R"mlir(module {
      func.func @entry(%condition:i1) {
        scf.if %condition { scf.yield }
        func.return
      }
    })mlir",
                        context);
    auto nestedEntry = function(*nested, "entry");
    mathematical::TotalClosure regions(*nested, symbols, nestedEntry);
    require(failed(regions.verifyObservations(nestedEntry.front())),
            "nested body bypassed the flat observation closure");
  });
  cases.run("summaries remain stable across cache growth", [&] {
    auto module = parse(helpers, context);
    auto helper = function(*module, "choose");
    SmallVector<func::FuncOp> copies;
    for (unsigned i = 0; i < 128; ++i) {
      auto copy = cast<func::FuncOp>(helper->clone());
      copy.setName("helper_" + std::to_string(i));
      module->push_back(copy);
      copies.push_back(copy);
    }
    require(succeeded(verify(*module)), "control module is malformed");
    SymbolTableCollection symbols;
    mathematical::TotalClosure closure(*module, symbols,
                                       function(*module, "entry"));
    const mathematical::TotalSummary *first, *next;
    require(succeeded(closure.get(helper, first)), "first query refused");
    for (auto copy : copies)
      require(succeeded(closure.get(copy, next)), "later query refused");
    require(succeeded(closure.get(helper, next)) && first == next &&
                first->results[0].test(0),
            "cache growth invalidated an earlier summary");
  });
  cases.run("failed analysis cannot resume with partial summaries", [&] {
    auto module = parse(R"mlir(module {
      func.func private @valid() { func.return }
      func.func private @cycle() {
        func.call @cycle() : () -> ()
        func.return
      }
    })mlir",
                        context);
    SymbolTableCollection symbols;
    mathematical::TotalClosure closure(*module, symbols);
    const mathematical::TotalSummary *summary;
    require(succeeded(closure.get(function(*module, "valid"), summary)),
            "valid initial query refused");
    require(failed(closure.get(function(*module, "cycle"), summary)) &&
                !summary,
            "cycle query retained a successful output");
    require(failed(closure.get(function(*module, "valid"), summary)) &&
                !summary && failed(closure.verify()),
            "failed analysis resumed using a partial cache");
  });
  cases.run("work exhaustion invalidates all later queries", [&] {
    auto module = parse(helpers, context);
    auto entry = function(*module, "entry");
    auto field = entry.getArgumentTypes().front();
    SmallVector<Type> inputs(10000, field);
    auto wide = func::FuncOp::create(
        module->getLoc(), "wide", FunctionType::get(&context, inputs, {field}));
    wide.setPrivate();
    module->push_back(wide);
    auto *body = wide.addEntryBlock();
    OpBuilder builder(&context);
    builder.setInsertionPointToEnd(body);
    func::ReturnOp::create(builder, wide.getLoc(), body->getArgument(0));
    require(succeeded(verify(*module)), "wide control is malformed");
    SymbolTableCollection symbols;
    mathematical::TotalClosure closure(*module, symbols, entry);
    const mathematical::TotalSummary *summary;
    std::string diagnostics;
    ScopedDiagnosticHandler record(&context, [&](Diagnostic &diagnostic) {
      diagnostics += diagnostic.str();
      return success();
    });
    require(failed(closure.get(wide, summary)) && !summary &&
                diagnostics.find("mathematical-analysis-limit") !=
                    std::string::npos,
            "dependency budget did not refuse wide input");
    require(failed(closure.get(entry, summary)) && !summary,
            "exhausted analysis admitted another query");
  });
  cases.run(
      "polynomial observation bounds do not depend on finite operations", [&] {
        for (unsigned length : {2u, 3u}) {
          std::string text = R"mlir(
        !A = !data.field_array<"bls12-381.fr", 2>
        !P = !poly.polynomial<"bls12-381.fr", 1>
        !R = !data.field_array<"bls12-381.fr", LENGTH>
        module {
          func.func @entry(%a:!A) -> !A {
            %p = "poly.from_coefficients"(%a) : (!A)->!P
            %square = "poly.multiply"(%p,%p) : (!P,!P)->!P
            %unused = "poly.coefficients"(%square) : (!P)->!R
            func.return %a : !A
          }
        })mlir";
          text.replace(text.find("LENGTH"), 6, std::to_string(length));
          auto module = parse(text, context);
          require(succeeded(verify(*module)),
                  "local polynomial invariants failed");
          std::string diagnostics;
          ScopedDiagnosticHandler record(&context, [&](Diagnostic &diagnostic) {
            diagnostics += diagnostic.str();
            return success();
          });
          auto result = mathematical::verifyTotalClosure(
              *module, function(*module, "entry"));
          require(succeeded(result) == (length == 3),
                  "coefficient output did not respect the derived degree");
          if (length == 2)
            require(diagnostics.find("polynomial-formation") !=
                        std::string::npos,
                    "observation refusal lost its diagnostic");
        }
      });
  cases.run("formal polynomial obligations are checked at actual callers", [&] {
    for (bool square : {false, true}) {
      std::string text = R"mlir(
        !A = !data.field_array<"bls12-381.fr", 2>
        !P = !poly.polynomial<"bls12-381.fr", 1>
        module {
          func.func private @observe(%p:!P) -> !A {
            %coefficients = "poly.coefficients"(%p) : (!P)->!A
            func.return %coefficients : !A
          }
          func.func @entry(%a:!A) -> !A {
            %p = "poly.from_coefficients"(%a) : (!A)->!P
            %square = "poly.multiply"(%p,%p) : (!P,!P)->!P
            %unused = func.call @observe(%ACTUAL) : (!P)->!A
            func.return %a : !A
          }
        })mlir";
      text.replace(text.find("ACTUAL"), 6, square ? "square" : "p");
      auto module = parse(text, context);
      require(succeeded(verify(*module)),
              "formal observation control is malformed");
      SymbolTableCollection symbols;
      mathematical::TotalClosure closure(*module, symbols,
                                         function(*module, "entry"));
      const mathematical::TotalSummary *summary;
      require(succeeded(closure.get(function(*module, "observe"), summary)),
              "unknown formal bound was rejected before a caller supplies it");
      require(succeeded(closure.verify()) == !square,
              "generic helper hid an invalid actual observation");
    }
  });
  cases.run("public functions need an explicit owner-selected entry", [&] {
    auto module = parse(helpers, context);
    require(failed(mathematical::verifyTotalClosure(*module)),
            "public helper was silently admitted");
    auto entry = function(*module, "entry");
    function(*module, "choose").setPublic();
    require(failed(mathematical::verifyTotalClosure(*module, entry)),
            "a second public entry was admitted");
  });
  cases.run("entry cannot come from another symbol table", [&] {
    auto module = parse(helpers, context);
    auto other = parse(helpers, context);
    require(failed(mathematical::verifyTotalClosure(*module,
                                                    function(*other, "entry"))),
            "foreign entry was admitted");
  });
  cases.run("retained uncalled definitions are checked", [&] {
    auto module = parse(helpers, context);
    auto unused = func::FuncOp::create(module->getLoc(), "unused",
                                       FunctionType::get(&context, {}, {}));
    unused.setPrivate();
    module->push_back(unused);
    require(failed(mathematical::verifyTotalClosure(
                *module, function(*module, "entry"))),
            "uncalled external helper was ignored");
  });
  cases.run("cycles and authority ports remain outside total mathematics", [&] {
    for (const char *text : {
             R"mlir(module { func.func private @cycle() {
               func.call @cycle() : () -> ()
               func.return
             } })mlir",
             R"mlir(module { func.func private @authority(
               %s:!protocol.service_ref<"random.bls12-381.fr/0">) {
               func.return
             } })mlir"}) {
      auto module = parse(text, context);
      require(failed(mathematical::verifyTotalClosure(*module)),
              "non-total closure was admitted");
    }
  });
  cases.run("fresh analysis follows body changes", [&] {
    auto module = parse(helpers, context);
    auto entry = function(*module, "entry");
    require(succeeded(mathematical::verifyTotalClosure(*module, entry)),
            "original entry refused");
    auto helper = function(*module, "choose");
    auto returned = cast<func::ReturnOp>(helper.front().back());
    returned->setOperand(0, helper.getArgument(1));
    SymbolTableCollection symbols;
    mathematical::TotalClosure closure(*module, symbols, entry);
    require(succeeded(closure.verify()), "changed entry refused");
    const mathematical::TotalSummary *summary;
    require(succeeded(closure.get(entry, summary)) &&
                summary->results[0].count() == 1 && summary->results[0].test(1),
            "fresh analysis reused an old body summary");
  });
  for (StringRef name :
       {"mathematical/helper-realization", "finite/realized-total",
        "structured-source/indexed-helper"})
    cases.run("owner-independent closure: " + name, [&] {
      auto source = parse(fixture(name), context);
      require(succeeded(zkc::admitStage(*source)), "Protocol fixture refused");
      auto unit = *source->getOps<protocol_ir::ProtocolModuleOp>().begin();
      SmallVector<Operation *> definitions;
      SmallVector<func::FuncOp> mathematics, execution;
      for (Operation &op : unit.getBody().front()) {
        if (isa<data::DomainOp>(op))
          definitions.push_back(&op);
        if (auto function = dyn_cast<func::FuncOp>(op)) {
          if (protocol::isScopedExecutionFunction(function))
            execution.push_back(function);
          else {
            mathematics.push_back(function);
            definitions.push_back(&op);
          }
        }
      }
      require(!mathematics.empty() &&
                  succeeded(finite::verifyDefinitionClosure(unit, definitions)),
              "selected mathematical closure refused");
      auto bare = mathematicalDefinitions(*source);
      require(succeeded(verify(*bare)) &&
                  succeeded(mathematical::verifyTotalClosure(*bare)),
              "identical definitions require a Protocol owner");
      SymbolTableCollection symbols;
      mathematical::TotalClosure original(unit, symbols),
          relocated(*bare, symbols);
      for (auto function : mathematics) {
        const mathematical::TotalSummary *before, *after;
        require(succeeded(original.get(function, before)) &&
                    succeeded(relocated.get(
                        bare->lookupSymbol<func::FuncOp>(function.getSymName()),
                        after)) &&
                    before->results == after->results &&
                    before->requirements == after->requirements &&
                    before->expandedOperations == after->expandedOperations &&
                    before->depth == after->depth &&
                    before->observesPolynomial == after->observesPolynomial,
                "relocation changed mathematical dependencies or work");
      }
      for (auto function : execution) {
        mathematical::TotalClosure isolated(unit, symbols);
        const mathematical::TotalSummary *summary;
        require(failed(isolated.get(function, summary)) && !summary,
                "scoped execution acquired a total mathematical summary");
      }
    });
  cases.run("finite bounds follow actual operands across owners", [&] {
    auto source = parse(fixture("structured-source/indexed-helper"), context);
    auto unit = *source->getOps<protocol_ir::ProtocolModuleOp>().begin();
    auto step = unit.lookupSymbol<func::FuncOp>("step");
    auto call = *step.getOps<func::CallOp>().begin();
    // The domain proves an index into xs, not into another vector of the same
    // type. The helper signature itself is unchanged by this substitution.
    call->setOperand(0, step.getArgument(3));
    auto bare = mathematicalDefinitions(*source);
    auto refused = [&](Operation *owner) {
      std::string diagnostics;
      ScopedDiagnosticHandler record(&context, [&](Diagnostic &diagnostic) {
        diagnostics += diagnostic.str();
        return success();
      });
      require(failed(mathematical::verifyTotalClosure(owner)),
              "foreign vector inherited the index bound");
      return diagnostics;
    };
    auto protocolDiagnostic = refused(unit);
    require(!protocolDiagnostic.empty() && protocolDiagnostic == refused(*bare),
            "mathematical closure diagnostics depend on the enclosing owner");
  });
  return cases.result();
}
