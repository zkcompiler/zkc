#include "mlir/IR/OperationSupport.h"
#include "support/ScopedComputation.h"
#include "support/ScopedFinite.h"
#include "support/ScopedFixture.h"
#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace sf = zkc::test::scopedFinite;
namespace sc = zkc::test::scopedComputation;
namespace {
std::string edit(StringRef source, StringRef from, StringRef to) {
  auto text = source.str();
  auto position = text.find(from.str());
  require(position != std::string::npos, "missing fixture fragment " + from);
  text.replace(position, from.size(), to.str());
  return text;
}
func::FuncOp function(ModuleOp module, StringRef name = "work") {
  return sf::function(module, name);
}
exec::ApplyOp nth(ModuleOp module, StringRef contract, unsigned index = 0,
                  StringRef owner = "work") {
  auto found = sf::executionApplications(module, owner, contract);
  require(index < found.size(), "missing invocation " + contract);
  return found[index];
}
MathematicalSelectionPolicy vectorPolicy() {
  MathematicalSelectionPolicy policy;
  policy.numericalExpressions = NumericalExpressionMode::VectorOnly;
  return policy;
}
OwningOpRef<ModuleOp>
prepare(ModuleOp source, MathematicalSelectionPolicy policy = vectorPolicy()) {
  mathematical::RealizationWork work;
  uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
  std::optional<CapacityCause> capacity;
  auto result = protocol::prepareScopedFinite(source, work, copy, bytes,
                                              capacity, policy);
  require(bool(result), "scoped collection preparation refused");
  return result;
}
LogicalResult compare(ModuleOp source, ModuleOp candidate,
                      MathematicalSelectionPolicy policy = vectorPolicy()) {
  mathematical::RealizationWork work;
  return protocol::verifyScopedFinitePreparation(source, candidate, work,
                                                 policy);
}
bool same(Operation *left, Operation *right) {
  return OperationEquivalence::isEquivalentTo(
      left, right, OperationEquivalence::IgnoreLocations);
}
std::string invoke(StringRef operation, StringRef attributes, StringRef site,
                   StringRef inputs, StringRef types, StringRef output,
                   StringRef result) {
  auto text = scopedApply("unused", site, inputs, types, output, result);
  text = replaceText(text, "\"exec.apply\"", "\"" + operation.str() + "\"");
  text = replaceText(text, "binding=@unused", attributes);
  return replaceText(text, ",parameters=[]", "");
}
std::string functionText(StringRef name, StringRef arguments, StringRef result,
                         StringRef body, bool privateFunction = false) {
  auto outcome = "!exec.outcome<(" + result.str() + ")>";
  return std::string(privateFunction ? "func.func private @" : "func.func @") +
         name.str() + "(%scope:!runtime.scope," + arguments.str() + ")->" +
         outcome + " attributes {no_inline,runtime.origin=[\"" + name.str() +
         "\",[]]} {\n" + body.str() +
         (body.contains("^failed")
              ? "\n^failed(%reason:!exec.stop):\n%failure = "
                "\"exec.failed\"(%reason) : (!exec.stop)->" +
                    outcome + "\nfunc.return %failure : " + outcome
              : "") +
         "\n}\n";
}
// Actual general collection declarations and scoped callbacks. All captures
// remain explicit, including scalar formula arguments whose values are unused.
std::string oneRowFixture(StringRef mathematics, unsigned scalarCaptures = 0,
                          unsigned roots = 1) {
  std::string arguments = "%xs:!V", inputs = "%xs", types = "!V";
  std::string formulaInputs = "%x", formulaTypes = "!F";
  for (unsigned i = 0; i < scalarCaptures; ++i) {
    auto name = "%s" + std::to_string(i);
    arguments += "," + name + ":!F";
    inputs += "," + name;
    types += ",!F";
    formulaInputs += "," + name;
    formulaTypes += ",!F";
  }
  std::string declarations = mathematics.str() + R"mlir(
"data.domain"() ({^entry(%xs:!V):
  %values = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
  "data.domain_yield"(%values) : (!data.domain<!F>)->()
}) {sym_name="elements",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
)mlir";
  std::string rootBody;
  for (unsigned i = 0; i < roots; ++i) {
    auto suffix = std::to_string(i);
    declarations +=
        functionText("row" + suffix, "%x:!F," + arguments, "!F",
                     invoke("exec.compute", "callee=@outer", "calculate",
                            formulaInputs, formulaTypes, "%r", "!F") +
                         scopedReturn("%r", "!F"),
                     true);
    auto body = invoke("exec.collect", "domain=@elements,body=@row" + suffix,
                       "map", inputs, types, "%r", "!V") +
                scopedReturn("%r", "!V");
    if (i == 0)
      rootBody = body;
    else
      declarations += functionText("work" + suffix, arguments, "!V", body);
  }
  auto text = "!F = !algebra.field<\"koala-bear\">\n!V = "
              "!algebra.field_vector<\"koala-bear\">\n" +
              scopedFixture(declarations, arguments, inputs, types, "!V",
                            rootBody, 1 + scalarCaptures);
  return replaceText(replaceText(text, "@Work", "@work"), "\"Work\"",
                     "\"work\"");
}
std::string chain(unsigned steps, bool subtract = false, unsigned calls = 1,
                  bool unused = false, unsigned roots = 1) {
  std::string text = "func.func private @chain(%x:!F)->!F {\n"
                     "%v0 = algebra.field_add %x,%x : (!F,!F)->!F\n";
  for (unsigned i = 1; i < steps; ++i) {
    auto previous = "%v" + std::to_string(i - 1);
    text += "%v" + std::to_string(i) + " = algebra.field_" +
            (subtract ? "subtract %x," + previous : "add " + previous + ",%x") +
            " : (!F,!F)->!F\n";
  }
  text += "func.return %v" + std::to_string(unused ? 0 : steps - 1) +
          " : !F\n}\nfunc.func private @outer(%x:!F)->!F {\n";
  for (unsigned i = 0; i < calls; ++i)
    text += "%c" + std::to_string(i) + " = func.call @chain(" +
            (i ? "%c" + std::to_string(i - 1) : "%x") + ") : (!F)->!F\n";
  text += "func.return %c" + std::to_string(calls - 1) + " : !F\n}\n";
  return oneRowFixture(text, 0, roots);
}
// Relocate a zero-payload invocation with its complete dispatch continuation.
// Leaving the old dispatch behind would test malformed CFG, not ordered work.
void moveAfter(exec::ApplyOp operation, exec::ApplyOp after) {
  require(operation.getOutcome().getType().getPayload().empty(),
          "only zero-result invocation can be moved without SSA rebinding");
  auto inputs = llvm::to_vector(operation->getOperands());
  NamedAttrList attributes(operation->getAttrs());
  auto helper = operation->getParentOfType<func::FuncOp>();
  auto stop = cast<exec::DispatchOp>(operation->getNextNode()).getStopped();
  sc::omit(operation);
  auto *block = cast<exec::DispatchOp>(after->getNextNode()).getReturned();
  IRRewriter rewriter(helper.getContext());
  auto *tail = rewriter.splitBlock(block, block->begin());
  OpBuilder builder(helper.getContext());
  builder.setInsertionPointToEnd(block);
  exec::ScopedExecutionBuilder control(builder, helper);
  control.invoke("exec.apply", {}, inputs, attributes.getAttrs(), stop);
  rewriter.mergeBlocks(tail, builder.getInsertionBlock());
}

} // namespace
int main(int argc, char **argv) {
  require(argc == 2, "expected a scoped map fixture");
  auto bytes = llvm::MemoryBuffer::getFile(argv[1]);
  require(bool(bytes), "cannot read scoped map fixture");
  // Reuse the shared general collection while preserving this suite's field.
  auto fixture = replaceText(
      replaceText((*bytes)->getBuffer().str(), "bls12-381.fr", "koala-bear"),
      "ui255", "ui31");
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry, MLIRContext::Threading::DISABLED);
  context.loadAllAvailableDialects();
  Cases cases;
  auto parse = [&](StringRef text) {
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "scoped map fixture refused");
    return module;
  };
  auto source = parse(fixture);
  auto expanded = prepare(*source);
  cases.run("ordered shape admission precedes vector realization", [&] {
    auto closure = take(
        protocol::readSourceExecutionClosure(&expanded->getBody()->front()));
    std::vector<std::string> contracts;
    for (auto &step : closure.bodies.at("work"))
      contracts.push_back(
          isa<exec::ApplyOp>(step.operation)
              ? sf::contract(cast<exec::ApplyOp>(step.operation)).str()
              : step.operation->getName().getStringRef().str());
    // General strict-zip admission measures all row extents, then compares
    // them in order. Every shape guard still precedes formula arithmetic.
    const std::vector<std::string> expected = {
        "vector.length",   "vector.length", "vector.length",   "index.equal",
        "control.require", "index.equal",   "control.require", "field.constant",
        "vector.mul",      "vector.sub",    "field.add",       "vector.scale",
        "vector.fill",     "vector.add",    "exec.returned"};
    require(contracts == expected, "ordered vector schedule changed");
    auto scale = nth(*expanded, "vector.scale");
    require(
        scale.getInputs()[0] == sc::payload(nth(*expanded, "vector.sub"))[0] &&
            scale.getInputs()[1] == sc::payload(nth(*expanded, "field.add"))[0],
        "scalar factor lost its scale coordinates");
    require(nth(*expanded, "vector.length", 2).getInputs()[0] ==
                function(*expanded).getArgument(3),
            "unused row was not measured");
    require(
        succeeded(compare(*source, *expanded)) &&
            same(function(*source, "formula"), function(*expanded, "formula")),
        "original formula or independent correspondence changed");
    bool pending = false;
    expanded->walk([&](exec::CollectOp) { pending = true; });
    require(!pending, "collection survived finite preparation");
  });
  cases.run("realization is deterministic", [&] {
    auto again = prepare(*source);
    require(same(*expanded, *again),
            "fresh realization changed sites or operations");
  });
  auto mutation = [&](StringRef label,
                      llvm::function_ref<void(ModuleOp)> change) {
    cases.run(label, [&] {
      auto candidate = sf::clone(*expanded);
      change(*candidate);
      require(succeeded(verify(*candidate)),
              "semantic mutation must remain admitted");
      ScopedDiagnosticHandler quiet(&context,
                                    [](Diagnostic &) { return success(); });
      require(failed(compare(*source, *candidate)),
              "independent reader accepted changed realization");
    });
  };
  mutation("compare an extent with itself", [&](ModuleOp module) {
    auto equal = nth(module, "index.equal", 1);
    equal->setOperand(2, equal.getInputs()[0]);
  });
  mutation("drop unused row shape guard", [&](ModuleOp module) {
    sc::omit(nth(module, "control.require", 1));
  });
  mutation("swap subtraction operands", [&](ModuleOp module) {
    auto sub = nth(module, "vector.sub");
    auto left = sub.getInputs()[0];
    sub->setOperand(1, sub.getInputs()[1]);
    sub->setOperand(2, left);
  });
  mutation("broadcast another scalar", [&](ModuleOp module) {
    nth(module, "vector.fill")
        ->setOperand(1, sc::payload(nth(module, "field.add"))[0]);
  });
  mutation("return a vector intermediate", [&](ModuleOp module) {
    sc::returned(function(module))
        ->setOperand(0, sc::payload(nth(module, "vector.scale"))[0]);
  });
  mutation("change a scalar literal", [&](ModuleOp module) {
    nth(module, "field.constant")
        ->setAttr("parameters",
                  ArrayAttr::get(&context,
                                 {take(algebra::decodeFieldLiteral(
                                     cast<algebra::FieldType>(sc::payload(nth(
                                         module, "field.constant"))[0]
                                                                  .getType()),
                                     "2"))}));
  });
  mutation("change retained scalar mathematics", [&](ModuleOp module) {
    function(module, "formula").walk([&](algebra::ConstantFieldOp op) {
      op.setValueAttr(cantFail(algebra::makeFieldLiteral(
          op.getResult().getType(), llvm::APInt(2, 2))));
    });
  });
  mutation("move shape admission after arithmetic", [&](ModuleOp module) {
    moveAfter(nth(module, "control.require"), nth(module, "field.constant"));
  });
  mutation("broadcast to another row extent", [&](ModuleOp module) {
    nth(module, "vector.fill")
        ->setOperand(2, sc::payload(nth(module, "vector.length", 1))[0]);
  });
  mutation("change the scoped root origin", [&](ModuleOp module) {
    function(module)->setAttr(
        "runtime.origin",
        ArrayAttr::get(&context, {StringAttr::get(&context, "square"),
                                  ArrayAttr::get(&context, {})}));
  });
  mutation("add an unaccounted binding", [&](ModuleOp module) {
    OpBuilder builder(&context);
    builder.setInsertionPointToStart(
        &module.getBody()->front().getRegion(0).front());
    runtime::BindingOp::create(builder, module.getLoc(), "extra", "vector.add",
                               builder.getStrArrayAttr({"koala-bear"}), "");
  });
  mutation("pin a generated vector implementation", [&](ModuleOp module) {
    auto call = nth(module, "vector.add");
    auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
        call, call.getBindingAttr());
    binding.setImplementation("plonky3/vector.add");
  });
  for (StringRef change : {"scale-types", "binding-field",
                           "invocation-attribute", "function-attribute"})
    cases.run("formation refuses " + change, [&] {
      auto candidate = sf::clone(*expanded);
      if (change == "scale-types") {
        auto scale = nth(*candidate, "vector.scale");
        auto rows = scale.getInputs()[0];
        scale->setOperand(1, scale.getInputs()[1]);
        scale->setOperand(2, rows);
      } else if (change == "binding-field") {
        auto call = nth(*candidate, "vector.add");
        auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
            call, call.getBindingAttr());
        binding->setAttr(
            "arguments",
            ArrayAttr::get(&context,
                           {StringAttr::get(&context, "bls12-381.fr")}));
      } else if (change == "invocation-attribute")
        nth(*candidate, "vector.add")
            ->setAttr("note", StringAttr::get(&context, "extra"));
      else
        function(*candidate)
            ->setAttr("note", StringAttr::get(&context, "extra"));
      std::string diagnostics;
      ScopedDiagnosticHandler quiet(&context, [&](Diagnostic &diagnostic) {
        diagnostics += diagnostic.str();
        return success();
      });
      require(failed(verify(*candidate)) &&
                  failed(compare(*source, *candidate)),
              "malformed candidate escaped actual source admission");
      require(namesIdentifier(diagnostics, change == "scale-types" ||
                                                   change == "binding-field"
                                               ? "binding-signature"
                                               : "execution-source-closure"),
              "unexpected refusal owner: " + diagnostics);
    });
  cases.run(
      "composed mathematical helpers preserve multiple and empty returns", [&] {
        auto text = edit(fixture, " func.func private @formula", R"mlir(
 func.func private @pair(%a:!F,%b:!F)->(!F,!F) {
   %sq = func.call @square(%a) : (!F)->!F
   func.return %sq,%b : !F,!F
 }
 func.func private @observe(%a:!F) {
   %unused = algebra.field_add %a,%a : (!F,!F)->!F
   func.return
 }
 func.func private @formula)mlir");
        text = edit(text, "   %sq = func.call @square(%a) : (!F)->!F\n   %d",
                    "   func.call @observe(%a) : (!F)->()\n   %pair:2 = "
                    "func.call @pair(%a,%b) : (!F,!F)->(!F,!F)\n   %d");
        text = edit(text, "(%sq,%b)", "(%pair#0,%pair#1)");
        auto original = parse(text), candidate = prepare(*original);
        require(succeeded(compare(*original, *candidate)),
                "composed helper readback failed");
        auto sub = nth(*candidate, "vector.sub");
        auto left = sub.getInputs()[0];
        sub->setOperand(1, sub.getInputs()[1]);
        sub->setOperand(2, left);
        require(succeeded(verify(*candidate)),
                "substitution mutation malformed");
        ScopedDiagnosticHandler quiet(&context,
                                      [](Diagnostic &) { return success(); });
        require(failed(compare(*original, *candidate)),
                "multiple return positions were not checked");
      });
  // Formation and preparation independently read actual domains and callback
  // signatures. A parser with verification disabled is no admission shortcut.
  auto sourceRefusal = [&](StringRef label, StringRef text, StringRef code) {
    cases.run(label, [&] {
      std::string diagnostics;
      ScopedDiagnosticHandler quiet(&context, [&](Diagnostic &diagnostic) {
        diagnostics += diagnostic.str();
        return success();
      });
      require(!parseSourceString<ModuleOp>(text, &context),
              "malformed scoped source admitted");
      auto unchecked =
          parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
      require(bool(unchecked), "test must remain syntactically valid");
      auto unchanged = sf::clone(*unchecked);
      mathematical::RealizationWork work;
      uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
      std::optional<CapacityCause> capacity;
      auto result = protocol::prepareScopedFinite(*unchecked, work, copy, bytes,
                                                  capacity, vectorPolicy());
      require(!result && same(*unchecked, *unchanged),
              "preparation admitted or changed malformed source");
      require(namesIdentifier(diagnostics, code),
              "unexpected source refusal: " + diagnostics);
    });
  };
  sourceRefusal("missing computation helper",
                edit(fixture, "callee=@formula", "callee=@missing"),
                "execution-computation-symbol");
  sourceRefusal("missing collection domain",
                edit(fixture, "domain=@rows", "domain=@missing"),
                "finite-formation");
  sourceRefusal("plain function cannot substitute for a domain",
                edit(fixture, "domain=@rows", "domain=@formula"),
                "finite-formation");
  sourceRefusal("callback item and capture signature disagree",
                edit(fixture, "body=@row", "body=@work"), "finite-formation");
  sourceRefusal("callback item field differs from the domain element",
                edit(edit(fixture, "%a0:!F,%a1:!F,%a2:!F",
                          "%a0:!algebra.field<\"bls12-381.fr\">,%a1:!F,%a2:!F"),
                     "%scope,%a0,%a1,%a2,%a6", "%scope,%a1,%a1,%a2,%a6"),
                "finite-formation");
  auto foreignHelper = edit(fixture, " func.func private @formula", R"mlir(
func.func private @foreign(%a:!algebra.field<"bls12-381.fr">,
  %b:!algebra.field<"bls12-381.fr">,%c:!algebra.field<"bls12-381.fr">,
  %s:!algebra.field<"bls12-381.fr">)->!algebra.field<"bls12-381.fr"> {
  func.return %a : !algebra.field<"bls12-381.fr">
}
 func.func private @formula)mlir");
  sourceRefusal("computation helper field differs from its actual inputs",
                edit(foreignHelper, "callee=@formula", "callee=@foreign"),
                "execution-computation-signature");
  sourceRefusal("protocol call cannot bypass a callback signature",
                edit(fixture, "callee=@work", "callee=@row"),
                "interactive-call-type");

  for (StringRef kind :
       {"unused equality", "nested equality", "foreign constant",
        "foreign helper result", "dormant helper"})
    cases.run("general callback admits " + kind, [&] {
      auto text = fixture;
      if (kind == "unused equality")
        text =
            edit(text, "   %dead =",
                 "   %e = algebra.field_equal %a,%b : (!F,!F)->i1\n   %dead =");
      else if (kind == "nested equality")
        text = edit(text, "   %r =",
                    "   %e = algebra.field_equal %x,%x : (!F,!F)->i1\n   %r =");
      else if (kind == "foreign constant")
        text = edit(text, "   %dead =",
                    "   %foreign = \"algebra.constant\"() "
                    "{value=#algebra.literal<!algebra.field<\"bls12-381.fr\">, "
                    "2 : ui255>} : ()->"
                    "!algebra.field<\"bls12-381.fr\">\n   %dead =");
      else if (kind == "foreign helper result") {
        text = edit(text, " func.func private @formula", R"mlir(
func.func private @wide()->!algebra.field<"koala-bear.ext8-binomial3"> {
  %w = "algebra.constant"() {value=#algebra.literal<!algebra.field<"koala-bear.ext8-binomial3">, 3 : ui31>} : ()->!algebra.field<"koala-bear.ext8-binomial3">
  func.return %w : !algebra.field<"koala-bear.ext8-binomial3">
}
 func.func private @formula)mlir");
        text = edit(
            text, "   %dead =",
            "   %wide = func.call @wide() : "
            "()->!algebra.field<\"koala-bear.ext8-binomial3\">\n   %dead =");
      } else
        text = edit(text, " func.func private @formula", R"mlir(
func.func private @test(%x:!F)->i1 {
  %e = algebra.field_equal %x,%x : (!F,!F)->i1
  func.return %e : i1
}
 func.func private @formula)mlir");
      auto original = parse(text), unchanged = sf::clone(*original);
      auto candidate = prepare(*original);
      require(
          succeeded(compare(*original, *candidate)) &&
              same(*original, *unchanged) &&
              same(function(*original, "formula"),
                   function(*candidate, "formula")),
          "general typed mathematics was changed or not independently checked");
    });

  for (auto [steps, subtract, calls] :
       {std::tuple<unsigned, bool, unsigned>{1023, false, 1},
        {1024, false, 1},
        {512, true, 1},
        {513, true, 1},
        {600, false, 2}})
    cases.run("general formula with " + Twine(steps) +
                  (subtract ? " right subtractions" : " additions") + " in " +
                  Twine(calls) + " helper calls",
              [&, steps = steps, subtract = subtract, calls = calls] {
                auto original = parse(chain(steps, subtract, calls));
                auto unchanged = sf::clone(*original);
                auto candidate = prepare(*original);
                require(succeeded(compare(*original, *candidate)) &&
                            same(*original, *unchanged) &&
                            same(function(*original, "chain"),
                                 function(*candidate, "chain")),
                        "formula depth changed mathematics or escaped "
                        "independent checking");
                require(sf::hasLoop(*candidate) ||
                            !sf::executionApplications(*candidate, "work",
                                                       "vector.add")
                                 .empty(),
                        "deep formula lost both ordered and vector execution");
              });

  for (bool unused : {false, true})
    cases.run(
        unused ? "ninety seven maps with 99522 helper operations"
               : "twenty four maps with deep live formulas",
        [&] {
          auto original =
              parse(chain(1023, false, 1, unused, unused ? 97 : 24));
          auto unchanged = sf::clone(*original);
          mathematical::RealizationWork work;
          uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
          std::optional<CapacityCause> capacity;
          std::string diagnostics;
          ScopedDiagnosticHandler quiet(&context, [&](Diagnostic &diagnostic) {
            diagnostics += diagnostic.str();
            return success();
          });
          auto result = protocol::prepareScopedFinite(
              *original, work, copy, bytes, capacity, vectorPolicy());
          require(same(*original, *unchanged),
                  "large preparation changed source");
          if (unused) {
            require(!result &&
                        namesIdentifier(diagnostics, "finite-preparation"),
                    "oversized actual candidate escaped bounded admission");
            // Required ordered construction exposes the original owner
            // that a speculative attempt deliberately keeps private.
            work = mathematical::RealizationWork{};
            copy = 1000000;
            bytes = 16 * 1024 * 1024;
            diagnostics.clear();
            result = protocol::prepareScopedFinite(
                *original, work, copy, bytes, capacity, {false, false, false});
            require(!result &&
                        namesIdentifier(diagnostics,
                                        "mathematical-analysis-limit") &&
                        same(*original, *unchanged),
                    "large retained/outlined computation admission changed: " +
                        diagnostics);
          } else
            require(bool(result) && succeeded(compare(*original, *result)),
                    "large live map readback refused");
        });
  for (auto mode : {NumericalExpressionMode::PreferNative,
                    NumericalExpressionMode::VectorOnly})
    cases.run(
        mode == NumericalExpressionMode::PreferNative
            ? "two hundred wide maps share optional bulk work"
            : "two hundred wide maps retain vector selection",
        [&] {
          std::string mathematics = "func.func private @outer(%x:!F";
          for (unsigned i = 1; i < 128; ++i)
            mathematics += ",%unused" + std::to_string(i) + ":!F";
          mathematics +=
              ")->!F { %r = algebra.field_multiply %x,%x : (!F,!F)->!F "
              "func.return %r : !F }\n";
          auto original = parse(oneRowFixture(mathematics, 127, 200));
          auto unchanged = sf::clone(*original);
          mathematical::RealizationWork work;
          uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
          std::optional<CapacityCause> capacity;
          auto policy = vectorPolicy();
          policy.numericalExpressions = mode;
          std::string diagnostics;
          ScopedDiagnosticHandler quiet(&context, [&](Diagnostic &diagnostic) {
            diagnostics += diagnostic.str();
            return success();
          });
          auto result = protocol::prepareScopedFinite(*original, work, copy,
                                                      bytes, capacity, policy);
          require(bool(result) && same(*original, *unchanged),
                  "wide preparation refused or changed source: " + diagnostics);
          {
            unsigned native = 0, vectors = 0, ordered = 0;
            for (unsigned i = 0; i < 200; ++i) {
              auto name = i ? "work" + std::to_string(i) : "work";
              auto helper = function(*result, name);
              native += !sf::applications(helper, "numerical.map").empty();
              vectors += !sf::applications(helper, "vector.mul").empty();
              ordered += sf::hasLoop(helper);
            }
            require(native + vectors + ordered == 200 && ordered > 0 &&
                        (mode == NumericalExpressionMode::PreferNative
                             ? native > 0 && vectors == 0
                             : native == 0 && vectors > 0),
                    "shared optional work was reset or lost the required "
                    "ordered fallback");
            require(succeeded(compare(*original, *result, policy)),
                    "wide readback refused");
            if (native) {
              auto applications = sf::applications(*result, "numerical.map");
              auto call = applications.front();
              auto parameters = call->getAttrOfType<ArrayAttr>("parameters");
              auto wrong =
                  edit(take(algebra::encodeRingExpression(
                           cast<algebra::RingExpressionAttr>(parameters[0]))),
                       "[\"input\",0]", "[\"input\",1]");
              call->setAttr(
                  "parameters",
                  ArrayAttr::get(
                      &context,
                      {take(algebra::importRingExpression(
                          &context, take(ring::readExpressionText(wrong))))}));
              require(
                  succeeded(verify(*result)) &&
                      failed(compare(*original, *result, policy)),
                  "capacity fallback concealed an admitted semantic mismatch");
            }
          }
        });
  for (unsigned dead : {0u, 3u})
    cases.run(
        "exact required allowance with " + Twine(dead) +
            " dead root operations",
        [&] {
          std::string math = R"mlir(
func.func private @square(%x:!F)->!F {
  %r = algebra.field_multiply %x,%x : (!F,!F)->!F
  func.return %r : !F
}
func.func private @outer(%x:!F)->!F {
  %s = func.call @square(%x) : (!F)->!F
)mlir";
          for (unsigned i = 0; i < dead; ++i)
            math += "%d" + std::to_string(i) +
                    " = algebra.field_add %x,%x : (!F,!F)->!F\n";
          math += "func.return %s : !F\n}\n";
          auto original = parse(oneRowFixture(math)),
               unchanged = sf::clone(*original);
          constexpr uint64_t copyLimit = 1000000, siteLimit = 16 * 1024 * 1024;
          mathematical::RealizationWork measure;
          uint64_t copy = copyLimit, bytes = siteLimit;
          std::optional<CapacityCause> capacity;
          auto candidate = protocol::prepareScopedFinite(
              *original, measure, copy, bytes, capacity, {false, false, false});
          require(bool(candidate), "required measurement refused");
          auto copyCost = copyLimit - copy;
          auto checkCost = uint64_t(1000000) - measure.requiredFiniteChecking;
          require(copyCost > 1 && checkCost > 1, "required work not charged");
          for (bool checking : {false, true}) {
            mathematical::RealizationWork exact;
            exact.requiredFiniteChecking = checking ? checkCost : 1000000;
            copy = checking ? copyLimit : copyCost;
            bytes = siteLimit;
            auto result = protocol::prepareScopedFinite(
                *original, exact, copy, bytes, capacity, {false, false, false});
            require(bool(result) &&
                        (checking ? exact.requiredFiniteChecking : copy) == 0,
                    "exact required allowance refused or not charged");
            ScopedDiagnosticHandler quiet(
                &context, [](Diagnostic &) { return success(); });
            mathematical::VerificationDecision outcome;
            auto repeated = protocol::prepareScopedFinite(
                *original, exact, copy, bytes, capacity, {false, false, false},
                nullptr, nullptr, &outcome);
            require(!repeated &&
                        (checking
                             ? outcome.outcome ==
                                       mathematical::VerificationObservation::
                                           RequiredCapacity &&
                                   outcome.capacity.has_value()
                             : capacity.has_value()),
                    "repeated work replenished exhausted allowance");
            mathematical::RealizationWork shortWork;
            shortWork.requiredFiniteChecking =
                checking ? checkCost - 1 : 1000000;
            copy = checking ? copyLimit : copyCost - 1;
            bytes = siteLimit;
            auto shortCandidate = protocol::prepareScopedFinite(
                *original, shortWork, copy, bytes, capacity,
                {false, false, false}, nullptr, nullptr, &outcome);
            require(!shortCandidate &&
                        (checking
                             ? outcome.outcome ==
                                       mathematical::VerificationObservation::
                                           RequiredCapacity &&
                                   outcome.capacity.has_value()
                             : capacity.has_value()) &&
                        same(*original, *unchanged),
                    "one-short required allowance changed source or published");
          }
        });
  cases.run("finite preparation requires a protocol owner", [&] {
    auto module = parse("module {func.func private @empty() {func.return}}");
    auto unchanged = sf::clone(*module);
    mathematical::RealizationWork work;
    uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
    std::optional<CapacityCause> capacity;
    require(
        !protocol::prepareScopedFinite(*module, work, copy, bytes, capacity) &&
            same(*module, *unchanged),
        "non-protocol context admitted or changed");
  });
  for (bool collection : {false, true})
    cases.run(
        collection ? "collection in an affine repeat helper"
                   : "computation in an affine repeat helper",
        [&] {
          auto type = collection ? "!V" : "!F";
          std::string declarations = R"mlir(
func.func private @twice(%x:!F)->!F {
  %r = algebra.field_add %x,%x : (!F,!F)->!F
  func.return %r : !F
}
)mlir";
          if (collection) {
            declarations += R"mlir(
"data.domain"() ({^entry(%xs:!V):
  %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
  "data.domain_yield"(%d) : (!data.domain<!F>)->()
}) {sym_name="elements",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
)mlir";
            declarations +=
                functionText("row", "%x:!F,%xs:!V", "!F",
                             invoke("exec.compute", "callee=@twice", "twice",
                                    "%x", "!F", "%r", "!F") +
                                 scopedReturn("%r", "!F"),
                             true);
          }
          declarations += functionText(
              "step", std::string("%state:!S,%v:") + type,
              std::string("!S,") + type,
              invoke(collection ? "exec.collect" : "exec.compute",
                     collection ? "domain=@elements,body=@row"
                                : "callee=@twice",
                     "map", "%v", type, "%r", type) +
                  scopedReturn("%state,%r", std::string("!S,") + type));
          auto text = R"mlir(
!S = !runtime.capability<rng, "bls12-381.fr">
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
)mlir" + declarations +
                      R"mlir(
"protocol.func"() ({^entry(%n:ui64,%s:!S,%v:VALUE):
  %done:2 = "protocol.repeat"(%n,%s,%v) ({
    ^round(%i:ui64,%state:!S,%value:VALUE):
      %next:2 = "protocol.local_call"(%state,%value) {callee=@step,role="P",site="step"} : (!S,VALUE)->(!S,VALUE)
      "protocol.yield"(%next#0,%next#1) : (!S,VALUE)->()
  }) {site="rounds",carried=2:i64,maximum=8:i64,roles=["P"],carried_roles=[["P"],["P"]]} : (ui64,!S,VALUE)->(!S,VALUE)
  "protocol.return"(%done#0,%done#1) : (!S,VALUE)->()
}) {sym_name="main",function_type=(ui64,!S,VALUE)->(!S,VALUE),roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
          auto original = parse(replaceText(text, "VALUE", type));
          auto candidate = prepare(*original);
          require(
              succeeded(compare(*original, *candidate)) &&
                  sc::returned(function(*candidate, "step")).getOperand(0) ==
                      function(*candidate, "step").getArgument(1),
              "affine state was cloned, reordered or lost across preparation");
          PassManager manager(&context);
          manager.addPass(protocol::createProjectProtocolPass(false));
          manager.addPass(protocol::createLowerMathPass());
          manager.addPass(computation::createRealizeComputationsPass());
          manager.addPass(protocol::createSelectPhysicalPass());
          require(succeeded(manager.run(*original)),
                  "affine repeat failed physical selection");
        });
  cases.run("one formula serves scalar and two domain partitions", [&] {
    auto declarations =
        R"mlir(
"data.domain"() ({^entry(%xs:!V):
  %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
  "data.domain_yield"(%d) : (!data.domain<!F>)->()
}) {sym_name="one",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
)mlir" +
        functionText("single_row", "%x:!F,%xs:!V,%b:!F,%c:!F,%s:!F", "!F",
                     invoke("exec.compute", "callee=@formula", "calculate",
                            "%x,%b,%c,%s", "!F,!F,!F,!F", "%r", "!F") +
                         scopedReturn("%r", "!F"),
                     true) +
        functionText("single", "%xs:!V,%b:!F,%c:!F,%s:!F", "!V",
                     invoke("exec.collect", "domain=@one,body=@single_row",
                            "map", "%xs,%b,%c,%s", "!V,!F,!F,!F", "%r", "!V") +
                         scopedReturn("%r", "!V"));
    auto original = parse(edit(fixture, " \"protocol.func\"",
                               declarations + " \"protocol.func\""));
    auto scalar = sc::computation(function(*original, "formula"), "scalar");
    require(succeeded(verify(*original)),
            "shared scalar computation malformed");
    auto candidate = prepare(*original);
    require(
        succeeded(compare(*original, *candidate)) &&
            sf::executionApplications(*candidate, "scalar", "control.require")
                .empty() &&
            sf::executionApplications(*candidate, "single", "control.require")
                .empty() &&
            sf::executionApplications(*candidate, "work", "control.require")
                    .size() == 2 &&
            same(function(*original, "formula"),
                 function(*candidate, "formula")),
        "scalar and finite consumers conflated shape admission or source "
        "mathematics");
    require(scalar.getFunctionType() ==
                function(*candidate, "scalar").getFunctionType(),
            "scalar ABI changed during finite preparation");
  });
  for (bool simplify : {false, true})
    cases.run(
        simplify ? "full optimized two-map pipeline"
                 : "full unsimplified two-map pipeline",
        [&] {
          std::string declarations = R"mlir(
func.func private @affine(%x:!F,%y:!F)->!F {
  %r = algebra.field_add %x,%y : (!F,!F)->!F
  func.return %r : !F
}
"data.domain"() ({^entry(%s:!F,%xs:!V):
  %d = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
  "data.domain_yield"(%d) : (!data.domain<!F>)->()
}) {sym_name="second",sym_visibility="private",function_type=(!F,!V)->!data.domain<!F>} : ()->()
)mlir";
          declarations +=
              functionText("second_row", "%y:!F,%s:!F,%xs:!V", "!F",
                           invoke("exec.compute", "callee=@affine", "calculate",
                                  "%s,%y", "!F,!F", "%r", "!F") +
                               scopedReturn("%r", "!F"),
                           true);
          auto text = edit(fixture, " \"protocol.func\"",
                           declarations + " \"protocol.func\"");
          // Replace only the outer root's success continuation, after the first
          // collection. The second domain keeps scalar-before-vector
          // coordinates.
          auto start = text.find("func.func @work");
          auto prefix = text.substr(0, start), root = text.substr(start);
          root = edit(root, "%done = \"exec.returned\"(%r)",
                      invoke("exec.collect", "domain=@second,body=@second_row",
                             "second_map", "%a3,%r", "!F,!V", "%q", "!V") +
                          "%done = \"exec.returned\"(%q)");
          auto module = parse(prefix + root);
          PassManager manager(&context);
          manager.addPass(protocol::createProjectProtocolPass(simplify));
          manager.addPass(protocol::createLowerMathPass());
          manager.addPass(computation::createRealizeComputationsPass());
          manager.addPass(protocol::createSelectPhysicalPass());
          require(succeeded(manager.run(*module)),
                  "two collections failed physical selection");
          bool residual = false, scoped = false;
          module->walk([&](Operation *op) {
            auto name = op->getName().getStringRef();
            residual |=
                isa<exec::CollectOp, exec::FoldOp, exec::ComputeOp>(op) ||
                name.starts_with("local.") || name.starts_with("plan.") ||
                name.starts_with("kernel.");
            scoped |= isa<exec::ApplyOp>(op);
          });
          require(scoped && !residual,
                  "pending or replaced carrier escaped physical selection");
        });
  return cases.result();
}
