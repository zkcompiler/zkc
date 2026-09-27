#include "../lib/Frontend/Library/Internal.h"
#include "../lib/Frontend/Model/Module.h"
#include "../lib/Frontend/Static/Structural.h"
#include "Names.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Frontend/Analysis.h"
#include "zkc/Frontend/Library.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Protocol/Instantiation.h"
#include "zkc/Source/Codec.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace zkc;
using namespace zkc::frontend;
namespace lib = zkc::frontend::library;
namespace {
unsigned checks = 0, failures = 0;
void expect(bool condition, StringRef description) {
  ++checks;
  if (!condition) {
    ++failures;
    errs() << "FAIL: " << description << '\n';
  }
}
template <class T> T take(Expected<T> result) {
  if (!result) {
    errs() << toString(result.takeError()) << '\n';
    std::exit(1);
  }
  return std::move(*result);
}
bool complete(const Analysis &analysis) {
  expect(analysis.complete(), "source elaborates completely");
  if (!analysis.complete())
    for (const auto &diagnostic : analysis.diagnostics())
      errs() << diagnostic.code << ": " << diagnostic.message << '\n';
  return analysis.complete();
}
void refusedSource(StringRef text, StringRef code) {
  auto analysis = analyzeProtocol(text, "refused-structural.pir");
  expect(!analysis.complete(), "invalid source refuses");
  expect(llvm::any_of(
             analysis.diagnostics(),
             [&](const auto &diagnostic) { return diagnostic.code == code; }),
         "source refusal identifies the argument error");
  if (analysis.complete() ||
      llvm::none_of(analysis.diagnostics(),
                    [&](const auto &d) { return d.code == code; }))
    for (const auto &d : analysis.diagnostics())
      errs() << "expected " << code << ", got " << d.code << ": " << d.message
             << '\n';
}
void closedSource() {
  auto analysis = analyzeProtocol(R"(
    use zkc::algebra::{Vector, FixedVector as Sized, fixed_vector_from_vector,
                       fixed_vector_to_vector, fixed_vector_dot};
    const WIDTH: index = 4;
    fn Closed(value: Vector<"koala-bear"::Element>) -> "koala-bear"::Element {
      let fixed: Sized<"koala-bear"::Element, WIDTH> = fixed_vector_from_vector::<"koala-bear", WIDTH>(value);
      let vector = fixed_vector_to_vector(fixed);
      let again = fixed_vector_from_vector::<"koala-bear", 4>(vector);
      return fixed_vector_dot(again, again);
    }
    fn Keep<T: Type, N: nat>(value: Sized<T, N>) -> Sized<T, N> { return value; }
    fn Explicit(value: Sized<"koala-bear"::Element, 4>) -> Sized<"koala-bear"::Element, 4> {
      return Keep::<"koala-bear"::Element, 4>(value);
    }
    fn ExplicitNested(value: Sized<Sized<"koala-bear"::Element, 4>, 2>) -> Sized<Sized<"koala-bear"::Element, 4>, 2> {
      return Keep::<Sized<"koala-bear"::Element, 4>, 2>(value);
    }
    configure SelectedKeep = Keep(T = Sized<"koala-bear"::Element, WIDTH>, N = 2);
    protocol TypedSelection {
      roles (P);
      inputs (P value: Sized<Sized<"koala-bear"::Element, 4>, 2>);
      outputs (P Sized<Sized<"koala-bear"::Element, 4>, 2>);
      local [keep] P: let result = Keep::<Sized<"koala-bear"::Element, 4>, 2>(value);
      return result;
    }
    fn Nested(value: Sized<Sized<"koala-bear"::Element, 4>, 2>) -> Sized<Sized<"koala-bear"::Element, 4>, 2> { return value; }
    fn Array(value: Array<"koala-bear"::Element, 4>) -> Array<"koala-bear"::Element, 4> { return value; }
  )",
                                  "closed-structural.pir");
  if (!complete(analysis))
    return;
  auto content = take(analysis.lower());
  const auto &module = std::get<source::Module>(content);
  auto printed = take(printProtocol(content));
  expect(printed.find("FixedVector<") != std::string::npos,
         "readable structural constructors survive common-source printing");
  auto roundtrip =
      take(parseProtocolDocument(printed, "printed-structural.pir"));
  expect(
      source::encode(roundtrip.root()) == source::encode(content),
      "Type/Nat statics and nested signatures round-trip through the printer");
  bool from = false, to = false, dot = false;
  for (const auto &binding : module.bindings) {
    const auto &application = binding.application;
    if (!StringRef(application.contract).starts_with("fixed_vector."))
      continue;
    expect(application.arguments == source::Names({"koala-bear", "4"}),
           "operation roots are the field identity and canonical natural");
    auto signature = take(protocol::resolveBinding(application, false));
    if (application.contract == "fixed_vector.from_vector") {
      from = true;
      expect(signature.inputs.size() == 1 &&
                 signature.inputs[0].spelling() == "vector:koala-bear" &&
                 signature.outputs.size() == 1 &&
                 signature.outputs[0].spelling() ==
                     "fixed_vector<field:koala-bear,4>",
             "from_vector has exact one-port structural signature");
    } else if (application.contract == "fixed_vector.to_vector") {
      to = true;
      expect(signature.inputs.size() == 1 &&
                 signature.inputs[0].spelling() ==
                     "fixed_vector<field:koala-bear,4>" &&
                 signature.outputs.size() == 1 &&
                 signature.outputs[0].spelling() == "vector:koala-bear",
             "to_vector preserves the full inverse signature");
    } else if (application.contract == "fixed_vector.dot") {
      dot = true;
      expect(signature.inputs.size() == 2 &&
                 signature.inputs[0].spelling() ==
                     "fixed_vector<field:koala-bear,4>" &&
                 signature.inputs[0] == signature.inputs[1] &&
                 signature.outputs.size() == 1 &&
                 signature.outputs[0].spelling() == "field:koala-bear",
             "dot has two exact bulk inputs");
    }
  }
  expect(from && to && dot,
         "all declared operations elaborate without operator special cases");
  for (const auto &function : module.functions) {
    if (function.name == "Nested")
      expect(function.arguments.size() == 1 &&
                 function.arguments[0].type ==
                     "fixed_vector<fixed_vector<field:koala-bear,4>,2>",
             "nested constructors stay one nominal port");
    if (function.name == "Array")
      expect(function.arguments.size() == 4 && function.results.size() == 4,
             "source arrays retain four distinct ports");
  }
  auto named = analysis.lookup({0}, "Nested");
  expect(bool(named), "nested source declaration retained");
  if (named) {
    auto type = analysis.type(analysis.declaration(*named)->inputs[0].type);
    expect(type && type->arguments.size() == 2 &&
               type->arguments[0].kind == StaticArgument::Kind::Type &&
               type->arguments[1].kind == StaticArgument::Kind::Natural &&
               type->arguments[1].number == 2,
           "query model retains explicit Type and Natural argument kinds");
  }
}
void genericSource() {
  auto analysis = analyzeProtocol(R"(
    use zkc::algebra::{Vector, FixedVector, Field, fixed_vector_from_vector, fixed_vector_dot};
    fn Dot<F: Field, N: nat>(value: Vector<F::Element>) -> F::Element {
      let fixed: FixedVector<F::Element, N> = fixed_vector_from_vector::<F, N>(value);
      return fixed_vector_dot(fixed, fixed);
    }
    protocol Selected {
      roles (P); inputs (P value: Vector<"koala-bear"::Element>); outputs (P "koala-bear"::Element);
      local [dot] P: let result = Dot::<"koala-bear", 4>(value);
      return result;
    }
    instance run: Selected { roles (P = Prover); }
    entry main = run;
  )",
                                  "generic-structural.pir");
  if (!complete(analysis))
    return;
  const auto content = take(analysis.lower());
  const auto &module = std::get<source::Module>(content);
  expect(module.definitions.size() == 1 &&
             module.definitions[0].parameters.size() == 2 &&
             module.definitions[0].parameters[1].sort == "Nat",
         "generic natural is a distinct scope token");
  auto declaration = analysis.lookup({0}, "Dot");
  expect(bool(declaration), "generic declaration retained");
  bool natural = false;
  for (const auto &use : analysis.uses())
    for (const auto &binding : use.bindings)
      natural |= binding.argument.kind == StaticArgument::Kind::Natural;
  expect(natural,
         "operation and invocation query bindings retain natural kind");
  const auto closed = take(generic::elaborateLibrary(module));
  bool exact = false;
  for (const auto &binding : closed.bindings)
    if (binding.application.contract == "fixed_vector.from_vector") {
      auto signature =
          take(protocol::resolveBinding(binding.application, false));
      exact |=
          binding.application.arguments == source::Names({"koala-bear", "4"}) &&
          signature.outputs.size() == 1 &&
          signature.outputs[0].spelling() == "fixed_vector<field:koala-bear,4>";
    }
  expect(exact, "generic source specializes into an exact one-port binding");
}
void modelSubstitution() {
  model::Module model;
  auto function = model.add(Declaration::Kind::Function, {0}, "Generic");
  auto scope = model.declarations[function.index].members;
  auto field = model.add(Declaration::Kind::Parameter, scope, "F");
  auto count = model.add(Declaration::Kind::Parameter, scope, "N");
  model.declarations[field.index].sort = "Field";
  model.declarations[count.index].sort = "Nat";
  auto type = model.logical("fixed_vector<fixed_vector<field:F,N>,2>", scope);
  auto closed =
      model.substitute(type, {{field, model.internDomain("koala-bear", {0})},
                              {count, StaticArgument::natural(4)}});
  expect(model.spelling(type) == "fixed_vector<fixed_vector<field:F,N>,2>" &&
             model.spelling(closed) ==
                 "fixed_vector<fixed_vector<field:koala-bear,4>,2>",
         "recursive substitution preserves every constructor and natural");
  expect(model.leaves({"value", {}, closed, {}}).size() == 1,
         "structural logical application is one model port");
}
void coreCarriers() {
  model::Module model;
  auto unit = model.logical("resource_unit:slot", {0});
  expect(unit.valid(), "core resource slot is admitted by the source model");
  if (unit.valid())
    expect(model.spelling(unit) == "resource_unit:slot",
           "core resource slot retains its colon identity");
  auto variant = protocol::encodeVariant(
      {std::string(4096, 'a'),
       {{"Has", {"resource_unit:slot", "bool"}}, {"Empty", {}}}});
  expect(variant && variant->size() > 4096,
         "valid variant exceeds the ordinary application spelling bound");
  if (variant) {
    auto type = model.logical(*variant, {0});
    expect(type.valid(), "variant uses its own bounded common reader");
    if (type.valid()) {
      auto spelling = model.spelling(type);
      expect(spelling == *variant,
             "variant table identity survives source model reconstruction");
      auto bound = take(protocol::parseBoundType(spelling, false));
      expect(bound.arguments.empty() && bound.spelling() == spelling,
             "core carrier payload does not become a structural application");
    }
  }
  expect(!splitLogical("resource_unit:1bad") &&
             !splitLogical("resource_unit<slot>") &&
             !splitLogical("variant:00") &&
             !splitLogical("variant:" +
                           std::string(protocol::VariantSpellingBytes, '0')),
         "malformed and oversized core carriers still refuse");

  auto analysis = analyzeProtocol(R"(
    library(namespace="example", name="carriers", version="1", resolution="captured");
    use zkc::algebra::Element;
    interface Cell { type Value drop; local step(x: Value) -> Value; }
    component EmptyCell: Cell {
      type Value = ();
      local step(x: Value) -> Value { return Id(x); }
    }
    component ScalarCell<F: domain field>: Cell {
      type Value = Element<F>;
      local step(x: Value) -> Value { return x; }
    }
    fn Id(x: ()) -> () { return x; }
    fn Client<C: Cell>(x: C::Value) -> C::Value { return C::step(x); }
    link Empty = Client<EmptyCell>;
    link Scalar = Client<ScalarCell<"koala-bear">>;

    enum Holder { Has(((), bool)), Nothing(bool) }
    interface Inspect { type Value drop; local check(x: (Value, bool)) -> bool; }
    component Inspector: Inspect {
      type Value = ();
      local check(x: (Value, bool)) -> bool {
        let h: Holder = Holder::Has(x);
        return Check(h);
      }
    }
    fn Check(h: Holder) -> bool {
      match h capture() -> (r) {
        Has(p) => { yield(p.1); }, Nothing(q) => { yield(q); }
      }
      return r;
    }
    fn InspectClient<C: Inspect>(x: (C::Value, bool)) -> bool { return C::check(x); }
    link Inspected = InspectClient<Inspector>;
  )",
                                  "core-carrier-helpers.pir");
  if (!complete(analysis))
    return;
  auto content = take(analysis.lower());
  auto admitted = checkProtocolDocument(source::Document(content));
  expect(!admitted, "core carrier helpers pass common source admission");
  if (admitted) {
    errs() << toString(std::move(admitted)) << '\n';
    return;
  }
  bool empty = false, scalar = false;
  for (const auto &function : std::get<source::Module>(content).functions) {
    if (function.name == "Empty")
      empty =
          function.arguments.size() == 1 && function.results.size() == 1 &&
          StringRef(function.arguments[0].type).starts_with("resource_unit:") &&
          function.arguments[0].type == function.results[0];
    if (function.name == "Scalar")
      scalar = function.arguments.size() == 1 && function.results.size() == 1 &&
               function.arguments[0].type == "field:koala-bear" &&
               function.results[0] == "field:koala-bear";
  }
  expect(empty && scalar,
         "one checked client retains distinct empty and scalar layouts");
  auto encoded = source::encode(content);
  auto text = printJson(encoded);
  expect(StringRef(text).contains("resource_unit.consume") &&
             StringRef(text).contains("resource_unit.create") &&
             StringRef(text).contains("variant:"),
         "helpers preserve explicit resource bridges and nominal variants");
  auto document = take(parseProtocolDocument(text, "core-carriers.json"));
  admitted = checkProtocolDocument(document);
  expect(!admitted,
         "encoded core carriers independently pass common admission");
  if (admitted)
    errs() << toString(std::move(admitted)) << '\n';
  expect(source::encode(document.root()) == encoded,
         "core carrier source survives portable encoding exactly");
}
void libraryPermissions() {
  lib::LibraryId owner{"test", "structural", "1", "captured"};
  auto id = [&](StringRef name) {
    return lib::QualifiedDecl{owner, {}, name.str()};
  };
  lib::Environment environment;
  environment.libraries.push_back(
      {owner, {id("Field"), id("T"), id("Duplicate")}});
  environment.statics.push_back(
      {id("Field"), lib::Sort::domainOf("Field"), {}, {}, "koala-bear"});
  environment.statics.push_back(
      {id("T"), lib::Sort::type(), {}, {}, {}, {}, true});
  for (const auto &type : protocol::boundTypeConstructors())
    environment.logicalTypes.push_back(
        {type, protocol::discardable(type.name)});
  for (const auto &operation : protocol::boundOperationContracts())
    environment.operations.push_back(
        {operation, {protocol::operationEffect(operation.name).str()}});
  auto field = lib::StaticTerm::root(id("Field"));
  auto element =
      take(lib::logicalTypeTerm(lib::Type::logical("field", {field})));
  auto fixed = lib::Type::logical("fixed_vector",
                                  {element, lib::StaticTerm::natural(4)});
  const std::vector<lib::Import> imports;
  const std::vector<lib::TypeBound> bounds;
  lib::detail::TypeContext context{environment, imports, bounds};
  auto permission = take(lib::detail::permissions(fixed, context));
  expect(permission.copy && permission.drop,
         "concrete field element grants copy and drop conjunctions");
  expect(take(lib::resolvedLogicalType(fixed, environment)) ==
             "fixed_vector<field:koala-bear,4>",
         "checked-library lowering preserves complete structural type");
  auto signature = take(lib::detail::logicalSignature(
      {"fixed_vector.from_vector", {field, lib::StaticTerm::natural(4)}},
      environment));
  expect(signature.outputs.size() == 1 &&
             lib::sameType(signature.outputs[0].type, fixed),
         "checked-library operation instantiates the nested field application");
  auto abstract =
      lib::Type::logical("fixed_vector", {lib::StaticTerm::root(id("T")),
                                          lib::StaticTerm::natural(4)});
  permission = take(lib::detail::permissions(abstract, context));
  expect(!permission.copy && !permission.drop,
         "unbounded abstract Type root grants no implicit permissions");
  auto resource = lib::Type::logical(
      "fixed_vector",
      {take(lib::logicalTypeTerm(lib::Type::logical("rng", {field}))),
       lib::StaticTerm::natural(4)});
  permission = take(lib::detail::permissions(resource, context));
  expect(!permission.copy, "affine element makes its nominal container affine");
  lib::Body duplicate;
  duplicate.id = id("Duplicate");
  duplicate.signature.inputs = {{resource, {}}};
  duplicate.signature.outputs = {{resource, {}}, {resource, {}}};
  duplicate.inputs = {{ValueId{0}, {resource, {}}}};
  duplicate.returns = {{ValueId{0}, {}}, {ValueId{0}, {}}};
  auto checked = lib::checkBody(duplicate, environment);
  expect(!checked, "duplicate resource bulk value refuses");
  if (!checked)
    expect(
        namesIdentifier(toString(checked.takeError()), "library-resource-use"),
        "duplicate resource refusal is stable");
  expect(!protocol::serializable("fixed_vector<field:koala-bear,4>"),
         "public element does not confer container serialization");
  expect(
      take(lib::sortOf(lib::StaticTerm::natural(1048576), environment)).kind ==
          lib::Sort::Kind::Natural,
      "scalar natural maximum is independent of array expansion limits");
  auto oversized = lib::sortOf(lib::StaticTerm::natural(1048577), environment);
  expect(!oversized, "oversized natural refuses");
  if (!oversized)
    consumeError(oversized.takeError());
  auto wrongKind =
      lib::Type::logical("fixed_vector", {field, lib::StaticTerm::natural(4)});
  auto wrongPermission = lib::detail::permissions(wrongKind, context);
  expect(!wrongPermission, "domain argument cannot stand for a Type");
  if (!wrongPermission)
    consumeError(wrongPermission.takeError());
  expect(protocol::defaultCodec(take(protocol::parseBoundType(
                                    "fixed_vector<field:koala-bear,4>", false)))
             .empty(),
         "public field element does not grant a container codec");
}
void checkedSource() {
  auto analysis = analyzeProtocol(R"(
    use zkc::algebra::{FixedVector, Vector, fixed_vector_from_vector, fixed_vector_dot};
    const WIDTH: index = 4;
    interface BulkAPI {
      type Element copy drop;
      local keep(value: FixedVector<Element, WIDTH>) -> FixedVector<Element, WIDTH>;
      local dot(value: Vector<"koala-bear"::Element>) -> "koala-bear"::Element effects (local);
    }
    component Bulk: BulkAPI {
      type Element = "koala-bear"::Element;
      local keep(value: FixedVector<"koala-bear"::Element, WIDTH>) -> FixedVector<"koala-bear"::Element, WIDTH> { return value; }
      local dot(value: Vector<"koala-bear"::Element>) -> "koala-bear"::Element effects (local) {
        let fixed = fixed_vector_from_vector::<"koala-bear", WIDTH>(value);
        return fixed_vector_dot::<"koala-bear", WIDTH>(fixed, fixed);
      }
    }
    fn Keep<C: BulkAPI>(value: FixedVector<C::Element, WIDTH>) -> FixedVector<C::Element, WIDTH> { return C::keep(value); }
    fn Dot<C: BulkAPI>(value: Vector<"koala-bear"::Element>) -> "koala-bear"::Element effects (local) { return C::dot(value); }
    link SelectedKeep = Keep<Bulk>;
    link SelectedDot = Dot<Bulk>;
  )",
                                  "checked-structural.pir");
  if (!complete(analysis))
    return;
  const auto content = take(analysis.lower());
  const auto &module = std::get<source::Module>(content);
  bool structural = false, operation = false;
  for (const auto &function : module.functions)
    for (const auto &argument : function.arguments)
      structural |= argument.type == "fixed_vector<field:koala-bear,4>";
  for (const auto &binding : module.bindings)
    if (binding.application.contract == "fixed_vector.from_vector") {
      operation = true;
      expect(binding.application.arguments ==
                 source::Names({"koala-bear", "4"}),
             "checked library operation lowers typed root statics");
    }
  expect(structural && operation, "checked component links nested abstract "
                                  "Type arguments and logical calls");
}
void reexports() {
  auto project = take(ProjectInput::capture(
      {{{{{},
          Input(R"(
    mod types;
    use self::types::Bulk;
    fn Keep(value: Bulk<"koala-bear"::Element, 4>) -> Bulk<"koala-bear"::Element, 4> { return value; }
  )",
                "main.pir")},
         {{"types"},
          Input(" pub use zkc::algebra::FixedVector as Bulk; ",
                "types.pir")}}}}));
  auto analysis = analyzeProject(project);
  if (!complete(analysis))
    return;
  const auto content = take(analysis.lower());
  const auto &module = std::get<source::Module>(content);
  expect(module.functions.size() == 1 &&
             module.functions[0].arguments[0].type ==
                 "fixed_vector<field:koala-bear,4>",
         "arbitrary declared structural export aliases and reexports resolve");
}
} // namespace
int main() {
  closedSource();
  genericSource();
  modelSubstitution();
  coreCarriers();
  libraryPermissions();
  checkedSource();
  reexports();
  refusedSource(
      R"( use zkc::algebra::{FixedVector, Field}; fn Bad<F: Field>(x: FixedVector<F::Element, F>) -> () { return (); } )",
      "source-type-natural");
  refusedSource(
      R"( use zkc::algebra::FixedVector; fn Bad(x: FixedVector<"koala-bear"::Element, Missing>) -> () { return (); } )",
      "source-name-unresolved");
  refusedSource(
      R"( use zkc::algebra::{Vector, fixed_vector_from_vector}; fn Bad(x: Vector<"koala-bear"::Element>) -> () { let y = fixed_vector_from_vector::<"koala-bear", "koala-bear">(x); return (); } )",
      "source-static-sort");
  refusedSource(R"(
    use zkc::algebra::FixedVector;
    fn Keep<T: Type, N: Nat>(x: FixedVector<T, N>) -> FixedVector<T, N> { return x; }
    fn Bad(x: FixedVector<"koala-bear"::Element, 4>) -> FixedVector<"koala-bear"::Element, 4> {
      return Keep::<"koala-bear"::Element, "koala-bear">(x);
    }
  )",
                "source-static-sort");
  refusedSource(R"(
    use zkc::algebra::FixedVector;
    interface Resource { type Element; }
    fn Bad<C: Resource>(x: FixedVector<C::Element, 4>) -> (FixedVector<C::Element, 4>, FixedVector<C::Element, 4>) {
      return (x, x);
    }
  )",
                "library-resource-use");
  outs() << checks << " structural frontend checks, " << failures
         << " failures\n";
  return failures ? 1 : 0;
}
