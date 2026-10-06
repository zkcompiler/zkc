#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/ADT/StringSet.h"
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace {
void run(ModuleOp module, std::unique_ptr<Pass> pass) {
  PassManager manager(module.getContext());
  manager.addPass(std::move(pass));
  require(succeeded(manager.run(module)), "native policy test pass failed");
}
Operation *unit(ModuleOp module) { return &module.getBody()->front(); }
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  // Cross-check every installed nominal type against the explicit design table.
  const llvm::StringSet<> totals{"bool",    "field",  "group",  "index",
                                 "indices", "vector", "matrix", "groups"};
  const llvm::StringSet<> wires{
      "index", "indices", "vector", "matrix",     "polynomial",  "table",
      "point", "round",   "groups", "commitment", "commitments", "proof"};
  const llvm::StringSet<> locals{
      "opening_states", "prover_key", "verifier_key", "opening_state", "rng",
      "nonce",          "transcript", "resource_unit"};
  for (const auto &instance : protocol::installedDomains().allLogicalTypes()) {
    protocol::BoundType type{instance.kind, instance.domain, {}};
    cases.run(type.spelling(), [&] {
      auto native = protocol::decodeBoundType(&context, type);
      require(bool(native), "installed nominal type failed to decode");
      auto policy = mathematical::nativeTypePolicy(native);
      bool total = totals.contains(type.kind),
           shared = total || wires.contains(type.kind);
      require(bool(policy) == (shared || locals.contains(type.kind)),
              "native closed type table changed");
      if (policy) {
        require(policy->total == total && policy->shared == shared,
                "native use permission changed");
        require(policy->affine == protocol::affine(type.spelling()),
                "custody classification changed");
        require(policy->affine == !protocol::duplicable(type.spelling()),
                "native affine continuations disagree with consuming operands");
        require(policy->protocolPort &&
                    policy->wire ==
                        (shared && protocol::serializable(type.spelling()) &&
                         !protocol::defaultCodec(type).empty()),
                "nominal boundary or wire classification changed");
      }
    });
  }
  for (StringRef spelling :
       {"resource_unit:Guard", "fixed_vector<bool,2>",
        "fixed_vector<rng:bls12-381.fr,0>",
        "fixed_vector<fixed_vector<resource_unit:Guard,1>,2>"}) {
    cases.run(spelling, [&] {
      auto type = take(protocol::parseBoundType(spelling, false));
      auto policy = mathematical::nativeTypePolicy(
          protocol::decodeBoundType(&context, type));
      require(policy && !policy->total && !policy->shared &&
                  policy->affine == protocol::affine(spelling) &&
                  policy->protocolPort && !policy->wire,
              "recursive local policy changed");
    });
  }
  cases.run("closed message grammar checks inactive alternatives", [&] {
    for (auto [leaf, accepted] :
         std::initializer_list<std::pair<StringRef, bool>>{
             {"field:bls12-381.fr", true},
             {"groups:bls12-381.g1", true},
             {"proof:multilinear.kzg.bls12-381/1", true},
             {"vector:bn254.fr", true},
             {"groups:bn254.g2", true},
             {"groups:ristretto255.group", true},
             {"group:bn254.gt", true},
             {"matrix:koala-bear.ext8-binomial3", true},
             {"proof:rows.merkle-keccak256.koala-bear/1", true},
             {"proof:rows.merkle-keccak256.koala-bear.ext8-binomial3/1", true},
             {"opening_state:rows.merkle-keccak256.koala-bear/1", false},
             {"commitments:rows.merkle-keccak256.koala-bear/1", false},
             {"table:bls12-381.fr", false},
             {"rng:bls12-381.fr", false},
             {"verifier_key:multilinear.kzg.bls12-381/1", false}}) {
      auto encoded = protocol::encodeVariant(
          {"Optional", {{"None", {}}, {"Some", {leaf.str()}}}});
      require(bool(encoded), "closed grammar fixture failed");
      auto type = take(protocol::parseBoundType(*encoded, false));
      require(protocol::nativeMessageData(type) == accepted,
              "inactive leaf changed wire authority");
      if (accepted)
        require(protocol::duplicable(type.spelling()) &&
                    protocol::discardable(type.spelling()),
                "wire grammar admitted an owned resource");
      require(protocol::nativeSetupType(type) ==
                  leaf.contains("multilinear.kzg"),
              "inactive setup disappeared");
    }
  });
  cases.run("variant recursive policy", [&] {
    auto spelling = protocol::encodeVariant(
        {"Result", {{"Value", {"bool"}}, {"Guard", {"resource_unit:Guard"}}}});
    require(bool(spelling), "variant fixture failed");
    auto type = take(protocol::parseBoundType(*spelling, false));
    auto policy = mathematical::nativeTypePolicy(
        protocol::decodeBoundType(&context, type));
    require(policy && !policy->total && !policy->shared && policy->affine &&
                !policy->protocolPort && !policy->wire,
            "variant lost recursive affine custody");
  });
  cases.run("copyable variants retain non-affine custody recursively", [&] {
    auto inner = protocol::encodeVariant(
        {"Inner", {{"Empty", {}}, {"Value", {"bool"}}}});
    require(bool(inner), "copyable variant fixture failed");
    auto outer = protocol::encodeVariant({"Outer", {{"Nested", {*inner}}}});
    require(bool(outer), "nested variant fixture failed");
    for (const auto &spelling :
         {*inner, *outer, "fixed_vector<" + *inner + ",2>"}) {
      auto logical = take(protocol::parseBoundType(spelling, false));
      auto policy = mathematical::nativeTypePolicy(
          protocol::decodeBoundType(&context, logical));
      require(policy && !policy->affine &&
                  policy->affine == protocol::affine(spelling) &&
                  policy->protocolPort &&
                  policy->wire == (logical.kind == "variant"),
              "copyable variant policy disagrees with contract custody");
    }
  });
  cases.run("recursive native protocol boundaries", [&] {
    auto encoded = protocol::encodeVariant(
        {"Local", {{"Empty", {}}, {"Value", {"resource_unit:Guard"}}}});
    require(bool(encoded), "variant fixture failed");
    auto spelling = *encoded;
    for (const auto &text :
         {spelling, "fixed_vector<" + spelling + ",2>",
          "fixed_vector<fixed_vector<" + spelling + ",2>,0>"}) {
      auto type = protocol::decodeBoundType(
          &context, take(protocol::parseBoundType(text, false)));
      auto policy = mathematical::nativeTypePolicy(type);
      require(
          policy && !policy->protocolPort && !policy->wire,
          "variant acquired native boundary permission through a container");
      std::string printed;
      llvm::raw_string_ostream out(printed);
      type.print(out);
      auto commonText =
          "module { \"protocol.module\"() ({ \"protocol.func\"() ({ "
          "^entry(%x: " +
          printed + "): \"protocol.return\"(%x) : (" + printed +
          ") -> () }) {sym_name=\"main\", function_type=(" + printed + ")->(" +
          printed +
          "), roles=[\"P\"], input_roles=[[\"P\"]], output_roles=[[\"P\"]]} : "
          "() -> () }) {profile=#protocol.profile<protocol>} : () -> () }";
      bool boundary = false;
      ScopedDiagnosticHandler expected(&context, [&](Diagnostic &diagnostic) {
        boundary |=
            diagnostic.str().find("variant-boundary") != std::string::npos;
        return success();
      });
      require(!parseSourceString<ModuleOp>(commonText, &context) && boundary,
              "common variant boundary survived admission");
    }
  });
  cases.run("supplied participants cannot bypass native boundary policy", [&] {
    auto module =
        parseSourceString<ModuleOp>(R"mlir(module { "protocol.module"() ({
      "protocol.func"() ({ ^entry(%x: i1):
        "protocol.return"(%x) : (i1) -> ()
      }) {sym_name="main", function_type=(i1)->i1, roles=["P"],
          input_roles=[["P"]], output_roles=[["P"]]} : () -> ()
    }) {profile=#protocol.profile<protocol>} : () -> () })mlir",
                                    &context);
    require(bool(module), "boundary fixture refused");
    run(*module, protocol::createProjectProtocolPass());
    auto encoded = protocol::encodeVariant(
        {"Local", {{"Guard", {"resource_unit:Guard"}}}});
    require(bool(encoded), "variant fixture failed");
    for (bool bound : {false, true}) {
      if (bound)
        run(*module, protocol::createLowerMathPass());
      for (bool nested : {false, true}) {
        OwningOpRef<ModuleOp> invalid(cast<ModuleOp>(module->clone()));
        auto text = nested ? "fixed_vector<" + *encoded + ",2>" : *encoded;
        auto type = protocol::decodeBoundType(
            &context, take(protocol::parseBoundType(text, false)));
        invalid->walk([&](protocol_ir::ParticipantOp op) {
          op.setFunctionType(FunctionType::get(&context, {type}, {type}));
          op.getBody().front().getArgument(0).setType(type);
        });
        invalid->walk([&](protocol_ir::ProjectionOp op) {
          if (bound) {
            op.erase();
            return;
          }
          SmallVector<Attribute> interfaces;
          for (auto item : op.getInterfaces()) {
            NamedAttrList fields(cast<DictionaryAttr>(item));
            fields.set("original_type", TypeAttr::get(FunctionType::get(
                                            &context, {type}, {type})));
            interfaces.push_back(fields.getDictionary(&context));
          }
          op.setInterfacesAttr(ArrayAttr::get(&context, interfaces));
        });
        bool boundary = false;
        ScopedDiagnosticHandler expected(&context, [&](Diagnostic &diagnostic) {
          boundary |=
              diagnostic.str().find("variant-boundary") != std::string::npos;
          return success();
        });
        require(failed(verify(*invalid)) && boundary,
                "supplied participant did not refuse its variant boundary");
      }
    }
  });
  cases.run("unclassified native types", [&] {
    for (Type type :
         {Type(IntegerType::get(&context, 32)),
          Type(local::OpaqueType::get(&context, "arbitrary")),
          Type(local::CapabilityType::get(&context, "uninstalled:any")),
          Type(algebra::FieldType::get(&context, "unknown")),
          Type(algebra::FixedVectorType::get(
              &context, IntegerType::get(&context, 32), 2))})
      require(!mathematical::nativeTypePolicy(type),
              "unclassified type acquired permission");
  });
  cases.run("type argument constructors remain owner-local", [&] {
    for (const auto &constructor : protocol::boundTypeConstructors())
      if (llvm::is_contained(constructor.parameters, "Type"))
        require(constructor.name == "fixed_vector" ||
                    constructor.name == "sequence",
                "new structural constructor requires native policy review");
    for (StringRef spelling :
         {"vector<rng:bls12-381.fr>",
          "matrix<opening_state:multilinear.kzg.bls12-381/1>",
          "polynomial<rng:bls12-381.fr>"}) {
      auto value = protocol::parseBoundType(spelling, false);
      require(!value, "domain constructor accepted an arbitrary type leaf");
      consumeError(value.takeError());
    }
  });
  cases.run("shared type budget and repeated-type memoization", [&] {
    OwningOpRef<ModuleOp> anchor(ModuleOp::create(UnknownLoc::get(&context)));
    mathematical::NativeTypePolicies types(*anchor);
    auto make = [&](unsigned i) {
      auto spelling = protocol::encodeVariant(
          {"Type" + std::to_string(i),
           {{"Values", std::vector<std::string>(128, "bool")}}});
      require(bool(spelling), "budget fixture failed");
      return local::VariantType::get(&context, *spelling);
    };
    auto repeated = make(0);
    for (unsigned i = 0; i != 100000; ++i)
      require(bool(types.get(repeated)),
              "repeated type was charged repeatedly");
    bool limited = false, refused = false;
    ScopedDiagnosticHandler expected(&context, [&](Diagnostic &diagnostic) {
      limited |= diagnostic.str().find("native-type-policy-limit") !=
                 std::string::npos;
      return success();
    });
    for (unsigned i = 1; i != 2000 && !refused; ++i)
      refused = !types.get(make(i));
    require(refused && limited,
            "distinct complex types escaped the shared budget");
  });
  cases.run("authored local bodies frozen after application expansion", [&] {
    auto source = parseSourceFile<ModuleOp>(ZKC_MIXED_FIXTURE, &context);
    require(bool(source), "mixed fixture refused");
    run(*source, protocol::createPrepareProtocolPass());
    bool residual = false;
    source->walk([&](local::ApplyOp) { residual = true; });
    require(!residual, "preparation left local.apply");
    OwningOpRef<ModuleOp> prepared(cast<ModuleOp>(source->clone()));
    {
      OwningOpRef<ModuleOp> changed(cast<ModuleOp>(source->clone()));
      changed->walk([&](protocol_ir::LocalCallOp call) {
        if (call.getSite() == "first_check")
          call.erase();
      });
      require(succeeded(verify(*changed)),
              "deleted zero-result call must remain structurally valid");
      ScopedDiagnosticHandler expected(&context,
                                       [](Diagnostic &) { return success(); });
      require(failed(mathematical::verifyProtocolPreparationPreserved(
                  unit(*source), unit(*changed))),
              "prepare postcondition lost an authored call");
    }
    run(*source, protocol::createProjectProtocolPass());
    run(*source, protocol::createSimplifyParticipantPass());
    require(succeeded(mathematical::verifyAuthoredLocalsPreserved(
                unit(*prepared), unit(*source))),
            "math pass changed authored locals");
    OwningOpRef<ModuleOp> projected(cast<ModuleOp>(source->clone()));
    for (bool extraDefinition : {false, true}) {
      OwningOpRef<ModuleOp> changed(cast<ModuleOp>(projected->clone()));
      auto work = cast<local::FuncOp>(
          SymbolTable::lookupSymbolIn(unit(*changed), "work"));
      if (extraDefinition) {
        auto *extra = work->clone();
        extra->setAttr("sym_name", StringAttr::get(&context, "extra_work"));
        unit(*changed)->getRegion(0).front().push_back(extra);
      } else {
        auto result = cast<local::ReturnOp>(work.getBody().front().back());
        result->setOperand(0, work.getArgument(0));
      }
      require(succeeded(verify(*changed)),
              "local mutation must retain formation");
      ScopedDiagnosticHandler expected(&context,
                                       [](Diagnostic &) { return success(); });
      require(failed(mathematical::verifyAuthoredLocalsPreserved(
                  unit(*projected), unit(*changed))),
              "local freeze accepted new work or rewired return");
    }
    run(*source, protocol::createLowerMathPass());
    require(succeeded(mathematical::verifyAuthoredLocalsPreserved(
                unit(*prepared), unit(*source))),
            "lowering changed authored locals");
    for (bool retainAction : {true, false}) {
      OwningOpRef<ModuleOp> changed(cast<ModuleOp>(source->clone()));
      auto record = *unit(*changed)
                         ->getRegion(0)
                         .front()
                         .getOps<protocol_ir::ProjectionOp>()
                         .begin();
      Builder builder(&context);
      SmallVector<Attribute> interfaces;
      for (auto item : record.getInterfaces()) {
        NamedAttrList interface(cast<DictionaryAttr>(item));
        SmallVector<Attribute> actions;
        for (auto action : cast<ArrayAttr>(interface.get("actions")))
          if (retainAction || cast<DictionaryAttr>(action)
                                      .getAs<StringAttr>("site")
                                      .getValue() != "work")
            actions.push_back(action);
        interface.set("actions", builder.getArrayAttr(actions));
        interfaces.push_back(interface.getDictionary(&context));
      }
      record.setInterfacesAttr(builder.getArrayAttr(interfaces));
      SmallVector<Attribute> calculations(record.getCalculations().begin(),
                                          record.getCalculations().end());
      calculations.push_back(builder.getDictionaryAttr(
          {builder.getNamedAttr("participant",
                                FlatSymbolRefAttr::get(&context, "_math_0")),
           builder.getNamedAttr("callee",
                                FlatSymbolRefAttr::get(&context, "work")),
           builder.getNamedAttr("site", builder.getStringAttr("work"))}));
      record.setCalculationsAttr(builder.getArrayAttr(calculations));
      bool correct = false;
      ScopedDiagnosticHandler expected(&context, [&](Diagnostic &diagnostic) {
        correct |=
            diagnostic.str().find(retainAction ? "overlaps authored execution"
                                               : "non-total input type") !=
            std::string::npos;
        return success();
      });
      require(failed(verify(*changed)) && correct,
              "authored resource call was relabeled as generated total math");
    }
    auto work =
        cast<local::FuncOp>(SymbolTable::lookupSymbolIn(unit(*source), "work"));
    auto branch = *work.getBody().front().getOps<local::LocalIfOp>().begin();
    branch.setSite("changed_but_valid_site");
    require(succeeded(verify(*source)),
            "body mutation should be structurally valid");
    ScopedDiagnosticHandler expected(&context,
                                     [](Diagnostic &) { return success(); });
    require(
        failed(mathematical::verifyProjectionPreserved(*projected, *source)),
        "frozen postcondition accepted a changed local body");
  });
  cases.run("statement preservation refuses computed candidate operands", [&] {
    auto source = parseSourceString<ModuleOp>(R"mlir(module {
      "protocol.module"() ({
        relation.declare @r {kind="external", key="test/statement", revision="1", signature=(i1) -> i1, purposes=["statement"]}
        "protocol.func"() ({ ^entry(%a: i1, %b: i1):
          %computed = arith.andi %a, %b : i1
          protocol.statement @r(%a) {selectors=["P"], acceptance=0 : i64} : i1
          "protocol.return"(%a) : (i1) -> ()
        }) {sym_name="main", function_type=(i1, i1) -> i1, roles=["P"], input_roles=[["P"],["P"]], output_roles=[["P"]]} : () -> ()
      }) {profile=#protocol.profile<protocol>} : () -> ()
    })mlir",
                                              &context);
    require(bool(source), "statement fixture refused");
    OwningOpRef<ModuleOp> changed(cast<ModuleOp>(source->clone()));
    auto function = *unit(*changed)
                         ->getRegion(0)
                         .front()
                         .getOps<protocol_ir::MathematicalOp>()
                         .begin();
    changed->walk([&](protocol_ir::StatementOp statement) {
      statement->setOperand(0, function.getBody().front().front().getResult(0));
    });
    ScopedDiagnosticHandler expected(&context,
                                     [](Diagnostic &) { return success(); });
    require(failed(mathematical::verifyProtocolPreparationPreserved(
                unit(*source), unit(*changed))),
            "statement postcondition accepted a computed value or crashed");
  });
  return cases.result();
}
