#include "mlir/IR/Verifier.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Implementations.h"
#include "zkc/Contracts/NativeOrigin.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Interfaces/CatalogType.h"
#include "llvm/ADT/StringExtras.h"
#include <set>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Builder builder(&context);
  auto emit = [&] { return emitError(builder.getUnknownLoc()); };
  SmallVector<std::string> codes;
  ScopedDiagnosticHandler handler(&context, [&](Diagnostic &diagnostic) {
    for (const auto &refusal : diagnostics::refusals(diagnostic))
      codes.push_back(refusal.code);
    return success();
  });
  auto field = algebra::FieldType::get(&context, "bls12-381.fr");
  auto vector = data::FieldVectorType::get(&context, "bls12-381.fr");
  auto natural = [&](uint64_t value) {
    return builder.getIntegerAttr(
        IntegerType::get(&context, 64, IntegerType::Unsigned), value);
  };
  auto domain = builder.getStringAttr("bls12-381.fr");
  auto resolve = [&](StringRef contract, ArrayRef<Attribute> arguments) {
    auto signature =
        resolveLogicalSignature(emit, &context, contract, arguments);
    require(bool(signature), "native signature refused: " + contract.str());
    return signature;
  };
  auto refuse = [&](StringRef contract, ArrayRef<Attribute> arguments) {
    codes.clear();
    require(!resolveLogicalSignature(emit, &context, contract, arguments),
            "malformed native binding accepted");
    require(llvm::is_contained(codes, "binding-signature"),
            "signature refusal lost its diagnostic identity");
  };
  OwningOpRef<ModuleOp> installations(
      ModuleOp::create(builder.getUnknownLoc()));
  OpBuilder nativeBuilder(installations->getBody(),
                          installations->getBody()->end());
  unsigned nextBinding = 0;
  auto binding = [&](StringRef contract, ArrayRef<Attribute> arguments,
                     StringRef implementation, ArrayRef<Type> inputs,
                     ArrayRef<Type> outputs) {
    return runtime::BindingOp::create(
        nativeBuilder, installations->getLoc(),
        "binding_" + std::to_string(nextBinding++), contract,
        builder.getArrayAttr(arguments), implementation,
        executableBindingSignature(builder.getFunctionType(inputs, outputs)),
        ArrayAttr{}, ArrayAttr{});
  };
  auto acceptInstallation = [&](runtime::BindingOp declaration,
                                std::optional<bool> physical = std::nullopt) {
    codes.clear();
    auto checked = readNativeBinding(emit, declaration, physical);
    require(succeeded(checked),
            "native installation refused: " + llvm::join(codes, ","));
    require(succeeded(verify(declaration)),
            "Runtime verifier disagrees with native installation");
    return *checked;
  };
  auto refuseInstallation = [&](runtime::BindingOp declaration,
                                StringRef code) {
    codes.clear();
    require(failed(readNativeBinding(emit, declaration)),
            "invalid native installation admitted");
    require(llvm::is_contained(codes, code),
            "native installation lost its refusal identity: " + code.str() +
                " actual: " + llvm::join(codes, ","));
    require(failed(verify(declaration)),
            "Runtime verifier skipped installation restrictions");
  };
  auto represented = [&](Type logical, StringRef representation,
                         ArrayRef<Type> children = {}) -> Type {
    auto value = runtime::RepresentedType::getChecked(emit, &context, logical,
                                                      representation, children);
    require(bool(value), "invalid native layout fixture");
    return value;
  };
  Cases cases;
  cases.run("native default selection does not load missing type owners", [&] {
    MLIRContext local(registry);
    local.loadDialect<algebra::AlgebraDialect>();
    auto value = algebra::FieldType::get(&local, "bls12-381.fr");
    auto silent = [&] {
      auto diagnostic = emitError(UnknownLoc::get(&local));
      diagnostic.abandon();
      return diagnostic;
    };
    require(!defaultPhysicalType(silent, value) &&
                !local.getLoadedDialect<runtime::RuntimeDialect>(),
            "default selection loaded an absent representation owner");
  });
#ifdef NDEBUG
  cases.run(
      "native requests refuse missing value ports before inspection", [&] {
        for (bool missingInput : {false, true}) {
          NativeBindingApplication request;
          request.contract = "field.add";
          request.arguments = {domain};
          request.context = &context;
          request.valueType =
              builder.getFunctionType({missingInput ? Type{} : field, field},
                                      {missingInput ? field : Type{}});
          codes.clear();
          require(!resolveInstalledSignature(
                      emit, &context, request, false,
                      protocol::installedImplementations()) &&
                      llvm::is_contained(codes, "binding-signature"),
                  "missing proposed value port escaped native admission");
          auto declaration =
              binding("field.add", {domain}, "", {field, field}, {field});
          declaration.setFunctionType(
              executableBindingSignature(request.valueType));
          codes.clear();
          require(failed(readNativeBinding(emit, declaration)) &&
                      llvm::is_contained(codes, "binding-signature"),
                  "missing actual value port escaped native admission");
          declaration.erase();
        }
      });
#endif
  cases.run("logical meaning does not admit or erase a selected provider", [&] {
    auto declaration = binding("field.add", {domain}, "withheld/field.add",
                               {field, field}, {field});
    auto before = declaration.getFunctionType();
    require(readLogicalBindingSignature(emit, declaration) ==
                    builder.getFunctionType({field, field}, {field}) &&
                declaration.getImplementation() == "withheld/field.add" &&
                declaration.getFunctionType() == before,
            "signature inspection erased the pin or changed the declaration");
    refuseInstallation(declaration, "binding-implementation");
    declaration.setFunctionType(executableBindingSignature(
        builder.getFunctionType({field, vector}, {field})));
    codes.clear();
    require(!readLogicalBindingSignature(emit, declaration) &&
                llvm::is_contained(codes, "binding-signature"),
            "logical meaning admitted a mismatched actual port");
    declaration.setFunctionType(before);
    auto physical = defaultPhysicalType(emit, field);
    declaration.setFunctionType(executableBindingSignature(
        builder.getFunctionType({physical, physical}, {physical})));
    codes.clear();
    require(!readLogicalBindingSignature(emit, declaration) &&
                llvm::is_contained(codes, "binding-stage"),
            "logical meaning admitted represented ports");
  });
  cases.run("native provider selection checks all resolved nominal terms", [&] {
    auto declaration = binding("field.add", {domain}, "dalek/field.add",
                               {field, field}, {field});
    refuseInstallation(declaration, "binding-implementation");
    declaration.setImplementation("arkworks/field.add");
    auto logical = acceptInstallation(declaration, false);
    require(!logical.physical && logical.logicalType == logical.valueType,
            "logical pin changed its actual ports");
    declaration.setImplementation("arkworks/field.mul");
    refuseInstallation(declaration, "binding-implementation");
    declaration.setImplementation("");
    acceptInstallation(declaration);
    auto physical = defaultPhysicalType(emit, field);
    declaration.setFunctionType(executableBindingSignature(
        builder.getFunctionType({physical, physical}, {physical})));
    refuseInstallation(declaration, "binding-stage");
    declaration.setImplementation("arkworks/field.add");
    acceptInstallation(declaration, true);
    require(failed(readNativeBinding(emit, declaration, false)),
            "explicit logical consumer admitted physical ports");
  });
  cases.run("native provider selectors use associated scope terms", [&] {
    auto descriptor = *protocol::installedImplementations().find(
        "curve.msm", "dalek/curve.msm");
    descriptor.identity = "custom/projected-msm";
    descriptor.providerTerm = 1;
    descriptor.domains = {"ristretto255.scalar"};
    auto catalog =
        take(protocol::ImplementationCatalog::create({descriptor}, {}));
    auto arguments = builder.getStringAttr("ristretto255.group");
    auto ports = resolve("curve.msm", {arguments});
    auto declaration = binding("curve.msm", {arguments}, descriptor.identity,
                               ports.getInputs(), ports.getResults());
    require(succeeded(readNativeBinding(emit, declaration, false, catalog)),
            "provider selector used supplied-argument offsets");
    auto bls = builder.getStringAttr("bls12-381.g1");
    ports = resolve("curve.msm", {bls});
    declaration.setArgumentsAttr(builder.getArrayAttr({bls}));
    declaration.setFunctionType(executableBindingSignature(ports));
    codes.clear();
    require(failed(readNativeBinding(emit, declaration, false, catalog)) &&
                llvm::is_contained(codes, "binding-implementation"),
            "projected selector admitted an unsupported domain");
  });
  cases.run("exact implementations require every complete physical port", [&] {
    auto ordinary = defaultPhysicalType(emit, field);
    auto resident = represented(field, "blst/fr");
    auto declaration = binding("field.add", {domain}, "blst/resident/field.add",
                               {resident, resident}, {resident});
    acceptInstallation(declaration);
    declaration.setFunctionType(executableBindingSignature(
        builder.getFunctionType({resident, ordinary}, {resident})));
    refuseInstallation(declaration, "binding-signature");
    declaration.setImplementation("arkworks/field.add");
    refuseInstallation(declaration, "binding-signature");
  });
  cases.run("indexed layout overrides preserve port direction and index", [&] {
    auto ordinary = defaultPhysicalType(emit, vector);
    auto diagonal = represented(vector, "arkworks.fr-diagonal/0");
    auto scalar = defaultPhysicalType(emit, field);
    auto declaration =
        binding("vector.dot", {domain}, "arkworks-diagonal/vector.dot",
                {ordinary, diagonal}, {scalar});
    acceptInstallation(declaration);
    declaration.setFunctionType(executableBindingSignature(
        builder.getFunctionType({diagonal, ordinary}, {scalar})));
    refuseInstallation(declaration, "binding-signature");
  });
  cases.run("sequence family retains the selected nested element layout", [&] {
    auto resident = represented(field, "blst/fr");
    auto inner = data::SequenceType::get(&context, field);
    auto innerPhysical = represented(inner, "logical.sequence/0", {resident});
    auto outer = data::SequenceType::get(&context, inner);
    auto outerPhysical =
        represented(outer, "logical.sequence/0", {innerPhysical});
    auto declaration = binding("sequence.append", {TypeAttr::get(inner)},
                               "native/sequence.append",
                               {outerPhysical, innerPhysical}, {outerPhysical});
    acceptInstallation(declaration);
    declaration.setFunctionType(
        executableBindingSignature(builder.getFunctionType(
            {outerPhysical, defaultPhysicalType(emit, inner)},
            {outerPhysical})));
    refuseInstallation(declaration, "binding-signature");
  });
  cases.run("dense family binds container scalar and vector layouts", [&] {
    auto array = data::FieldArrayType::get(&context, "bls12-381.fr", 4);
    auto resident = represented(field, "blst/fr");
    auto arrayPhysical = represented(array, "blst/field-array", {resident});
    auto vectorPhysical = represented(vector, "blst/fr");
    auto declaration = binding("field_array.from_vector", {domain, natural(4)},
                               "blst/resident/field_array.from_vector",
                               {vectorPhysical}, {arrayPhysical});
    acceptInstallation(declaration);
    declaration.setFunctionType(
        executableBindingSignature(builder.getFunctionType(
            {defaultPhysicalType(emit, vector)}, {arrayPhysical})));
    refuseInstallation(declaration, "binding-signature");
    declaration.setFunctionType(executableBindingSignature(
        builder.getFunctionType({defaultPhysicalType(emit, vector)},
                                {defaultPhysicalType(emit, array)})));
    refuseInstallation(declaration, "binding-representation");
    auto fixed = data::FixedVectorType::get(&context, field, 4);
    auto fixedPhysical = represented(fixed, "blst/fixed-vector", {resident});
    auto dot = binding("fixed_vector.dot", {domain, natural(4)},
                       "blst/resident/fixed_vector.dot",
                       {fixedPhysical, fixedPhysical}, {resident});
    acceptInstallation(dot);
    dot.setFunctionType(executableBindingSignature(builder.getFunctionType(
        {fixedPhysical, fixedPhysical}, {defaultPhysicalType(emit, field)})));
    refuseInstallation(dot, "binding-signature");
  });
  cases.run("physical conversion checks both exact endpoints", [&] {
    auto ordinary = defaultPhysicalType(emit, field);
    auto resident = represented(field, "blst/fr");
    auto declaration =
        binding("representation.convert", {TypeAttr::get(field)},
                "native/representation.convert", {ordinary}, {resident});
    acceptInstallation(declaration);
    declaration.setFunctionType(executableBindingSignature(
        builder.getFunctionType({resident}, {ordinary})));
    acceptInstallation(declaration);
    declaration.setFunctionType(executableBindingSignature(
        builder.getFunctionType({ordinary}, {ordinary})));
    refuseInstallation(declaration, "binding-conversion");
    auto table = poly::MultilinearType::get(&context, "bls12-381.fr");
    auto lsb = represented(table, "arkworks.mle-lsb/0");
    auto msb = represented(table, "arkworks.mle-msb/0");
    auto relayout = binding("table.relayout", {domain},
                            "arkworks/table.relayout", {lsb}, {msb});
    acceptInstallation(relayout);
    relayout.setImplementation("native/representation.convert");
    refuseInstallation(relayout, "binding-conversion");
  });
  cases.run(
      "observation family admits complete frames independently of suite", [&] {
        auto suite = builder.getStringAttr("merlin3.bls12-381.fr64be/0");
        auto payload = data::SequenceType::get(&context, field);
        auto signature = resolve("transcript.native.indexed.observe.data",
                                 {suite, TypeAttr::get(payload)});
        auto state = defaultPhysicalType(emit, signature.getInput(0));
        auto indices = defaultPhysicalType(emit, signature.getInput(2));
        auto selected = represented(payload, "logical.sequence/0",
                                    {represented(field, "blst/fr")});
        auto declaration =
            binding("transcript.native.indexed.observe.data",
                    {suite, TypeAttr::get(payload)},
                    "arkworks/transcript.native.indexed.observe.data",
                    {state, selected, indices}, {state});
        acceptInstallation(declaration);
        declaration.setImplementation(
            "dalek/transcript.native.indexed.observe.data");
        refuseInstallation(declaration, "binding-implementation");
        declaration.setImplementation(
            "arkworks/transcript.native.indexed.observe.data");
        declaration.setArgumentsAttr(
            builder.getArrayAttr({suite, TypeAttr::get(vector)}));
        declaration.setFunctionType(
            executableBindingSignature(builder.getFunctionType(
                {state, represented(vector, "arkworks.fr-diagonal/0"), indices},
                {state})));
        refuseInstallation(declaration, "native-proof-wire-type");
        auto foreignField = algebra::FieldType::get(&context, "bn254.fr");
        declaration.setArgumentsAttr(
            builder.getArrayAttr({suite, TypeAttr::get(foreignField)}));
        declaration.setFunctionType(
            executableBindingSignature(builder.getFunctionType(
                {state, defaultPhysicalType(emit, foreignField), indices},
                {state})));
        acceptInstallation(declaration);
      });
  cases.run("native admission rechecks forged represented children", [&] {
    auto sequence = data::SequenceType::get(&context, field);
    auto ordinary = defaultPhysicalType(emit, field);
    auto forged = runtime::RepresentedType::get(
        &context, sequence, "logical.sequence/0", ArrayRef<Type>{vector});
    auto declaration =
        binding("sequence.append", {TypeAttr::get(field)},
                "native/sequence.append", {forged, ordinary}, {forged});
    refuseInstallation(declaration, "represented-type-formation");
  });
  cases.run("observation frames check inactive variant payloads", [&] {
    auto identity = data::IdentityAttr::get(
        &context, builder.getArrayAttr({builder.getStringAttr("atom"),
                                        builder.getStringAttr("Observation")}));
    auto payload = data::VariantType::get(
        &context, identity,
        {data::AlternativeAttr::get(&context, builder.getStringAttr("empty"),
                                    {}),
         data::AlternativeAttr::get(&context, builder.getStringAttr("value"),
                                    {field, vector})});
    auto suite = builder.getStringAttr("merlin3.bls12-381.fr64be/0");
    auto signature = resolve("transcript.native.indexed.observe.data",
                             {suite, TypeAttr::get(payload)});
    auto state = defaultPhysicalType(emit, signature.getInput(0));
    auto indices = defaultPhysicalType(emit, signature.getInput(2));
    auto selected =
        represented(payload, "logical.variant/0",
                    {represented(field, "blst/fr"),
                     represented(vector, "arkworks.fr-diagonal/0")});
    auto declaration =
        binding("transcript.native.indexed.observe.data",
                {suite, TypeAttr::get(payload)},
                "arkworks/transcript.native.indexed.observe.data",
                {state, selected, indices}, {state});
    refuseInstallation(declaration, "native-proof-wire-type");
    declaration.setFunctionType(
        executableBindingSignature(builder.getFunctionType(
            {state, defaultPhysicalType(emit, payload), indices}, {state})));
    acceptInstallation(declaration);
  });
  cases.run("declaration view checks administrative ABI context", [&] {
    auto declaration =
        binding("field.add", {domain}, "", {field, field}, {field});
    MLIRContext foreign(registry);
    foreign.loadAllAvailableDialects();
    auto scope = runtime::ScopeType::get(&foreign);
    auto outcome = exec::OutcomeType::get(&context, {field});
    declaration.setFunctionType(
        builder.getFunctionType({scope, field, field}, {outcome}));
    refuseInstallation(declaration, "binding-signature");
    declaration.setFunctionType(executableBindingSignature(
        builder.getFunctionType({field, field}, {field})));
    declaration.setImplementationAttr(StringAttr::get(&foreign, ""));
    refuseInstallation(declaration, "binding-signature");
    declaration.setImplementation("");
  });
  cases.run(
      "native installation does not inherit neutral byte depth limits", [&] {
        Type logical = field;
        for (unsigned i = 0; i < 12; ++i)
          logical = data::SequenceType::get(&context, logical);
        auto physical = defaultPhysicalType(emit, logical);
        require(bool(physical), "native default imposed a byte depth limit");
        auto container = data::SequenceType::get(&context, logical);
        auto selected =
            represented(container, "logical.sequence/0", {physical});
        auto declaration =
            binding("sequence.append", {TypeAttr::get(logical)},
                    "native/sequence.append", {selected, physical}, {selected});
        acceptInstallation(declaration);
        refuses(protocol::readBinding(declaration), "binding-type-limit");
      });
  cases.run(
      "neutral export checks native formation first and stays silent", [&] {
        auto declaration =
            binding("field.add", {domain}, "", {field, field}, {field});
        auto note = builder.getDictionaryAttr(
            {builder.getNamedAttr("test.note", builder.getUnitAttr())});
        declaration.setArgAttrsAttr(builder.getArrayAttr({note, note, note}));
        acceptInstallation(declaration);
        codes.clear();
        refuses(protocol::readBinding(declaration), "binding-attributes");
        require(codes.empty(),
                "neutral annotation refusal emitted a diagnostic");

        // Native bodylessness must fail before the independent neutral check
        // for annotations, even though the callable attributes are otherwise
        // formed.
        OperationState state(declaration.getLoc(),
                             runtime::BindingOp::getOperationName());
        state.addAttributes(declaration->getAttrs());
        state.addRegion();
        auto *malformed = nativeBuilder.create(state);
        codes.clear();
        refuses(protocol::readBinding(malformed), "binding-declaration");
        require(codes.empty(), "native export refusal leaked a diagnostic");
        malformed->erase();

        declaration.removeArgAttrsAttr();
        declaration.setImplementation("foreign/field.add");
        codes.clear();
        refuses(protocol::readBinding(declaration), "binding-implementation");
        require(codes.empty(), "native selection refusal leaked a diagnostic");
        declaration.erase();
      });
  cases.run("mathematical signature excludes execution bookkeeping", [&] {
    require(resolve("field.add", {domain}) ==
                builder.getFunctionType({field, field}, {field}),
            "scope or outcome leaked into mathematical ports");
  });
  cases.run("application terms construct complete nested ports", [&] {
    auto fixed = data::FixedVectorType::get(&context, field, 4);
    require(resolve("fixed_vector.dot", {domain, natural(4)}) ==
                builder.getFunctionType({fixed, fixed}, {field}),
            "nested Type application or Nat argument erased");
    auto array = data::FieldArrayType::get(&context, "bls12-381.fr", 4);
    require(resolve("field_array.from_vector", {domain, natural(4)}) ==
                builder.getFunctionType({vector}, {array}),
            "domain/Nat application changed");
  });
  cases.run("associated members determine actual challenge domain", [&] {
    const protocol::NominalDomain *selected = nullptr;
    for (const auto &candidate : protocol::installedDomains().allDomains())
      if (candidate.sort == "Transcript" &&
          protocol::associatedIdentity(candidate.identity, "ChallengeField") ==
              "bls12-381.fr") {
        selected = &candidate;
        break;
      }
    require(bool(selected), "missing transcript test installation");
    auto signature = resolve("transcript.native.indexed.challenge",
                             {builder.getStringAttr(selected->identity)});
    require(signature.getNumResults() == 2 && signature.getResult(0) == field &&
                signature.getInput(0) == signature.getResult(1),
            "associated field or affine successor changed");
  });
  cases.run("complete-Type ports retain native identity beyond byte limits",
            [&] {
              Type payload = field;
              for (unsigned i = 0; i < 12; ++i)
                payload = data::SequenceType::get(&context, payload);
              for (const auto &candidate :
                   protocol::installedDomains().allDomains()) {
                if (candidate.sort != "Transcript")
                  continue;
                auto signature = resolveLogicalSignature(
                    emit, &context, "transcript.native.indexed.observe.data",
                    {builder.getStringAttr(candidate.identity),
                     TypeAttr::get(payload)});
                if (!signature)
                  continue;
                require(signature.getInput(1) == payload,
                        "complete-Type payload was reconstructed or truncated");
                return;
              }
              require(false, "no native transcript signature formed");
            });
  cases.run("native block invocations have typed composite parameters", [&] {
    auto origin = take(protocol::encodeNativeOriginTemplate(
        "entry", {},
        {"query", "source", "block", "input_0",
         "random.koala-bear.ext4-binomial3/0", "indices", "V"}));
    for (StringRef suite :
         {"hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0",
          "hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0"}) {
      auto arguments = builder.getArrayAttr({builder.getStringAttr(suite)});
      for (StringRef contract : {"transcript.native.indexed.indices",
                                 "transcript.native.indexed.indices.search",
                                 "transcript.native.indexed.indices.gated"}) {
        auto signature = resolve(contract, arguments.getValue());
        bool search = contract.ends_with(".search"),
             gated = contract.ends_with(".gated");
        require(signature.getNumInputs() == (gated ? 3 : 2) &&
                    signature.getNumResults() == (search ? 3 : 2),
                "native block ports differ");
        std::vector<std::string> parameters{origin, "9223372036854775808",
                                            "1048576"};
        if (search || gated)
          parameters.push_back("0");
        auto typed = take(protocol::decodeInvocationParameters(
            contract, arguments, parameters,
            zkc::protocol::ParameterStage::Logical));
        require(take(protocol::encodeInvocationParameters(
                    contract, arguments, typed,
                    zkc::protocol::ParameterStage::Logical)) == parameters,
                "typed block parameter roundtrip differs");
        SmallVector<Attribute> wrong(typed.getValue());
        wrong[1] = builder.getI64IntegerAttr(8);
        codes.clear();
        require(failed(verifyInvocationParameters(
                    emit, contract, arguments, builder.getArrayAttr(wrong),
                    zkc::protocol::ParameterStage::Logical)) &&
                    llvm::is_contained(codes, "interactive-kernel-parameters"),
                "signed block natural admitted");
        wrong.assign(typed.begin(), typed.end());
        wrong[0] = builder.getStringAttr(origin);
        codes.clear();
        require(failed(verifyInvocationParameters(
                    emit, contract, arguments, builder.getArrayAttr(wrong),
                    zkc::protocol::ParameterStage::Logical)) &&
                    llvm::is_contained(codes, "interactive-native-origin"),
                "unstructured block origin admitted");
      }
    }
  });
  cases.run("numerical families preserve mixed and empty masks", [&] {
    auto mask = builder.getDenseBoolArrayAttr({true, false, true});
    require(resolve("numerical.map", {domain, mask}) ==
                builder.getFunctionType(
                    {natural(0).getType(), vector, field, vector}, {vector}),
            "numerical mask lost its positional ABI");
    require(
        resolve("numerical.sum", {domain, builder.getDenseBoolArrayAttr({})}) ==
            builder.getFunctionType({natural(0).getType()}, {field}),
        "empty numerical mask acquired a hidden operand");
  });
  cases.run(
      "slot scope derives resource successor without domain installation", [&] {
        auto slot = builder.getStringAttr("ticket");
        auto type = runtime::CapabilityType::get(
            &context, zkc::runtime::CapabilityKind::ResourceUnit, "ticket");
        require(
            resolve("resource_unit.pass", {slot}) ==
                builder.getFunctionType({type}, {type}),
            "resource slot changed or required a field-domain registration");
        refuse("resource_unit.pass", {builder.getStringAttr("bad:slot")});
      });
  cases.run("static kinds and numerical masks refuse substitutions", [&] {
    refuse("missing", {});
    refuse("field.add", {});
    refuse("field.add", {domain, domain});
    refuse("field.add", {TypeAttr::get(field)});
    refuse("field.add", {builder.getStringAttr("bls12-381.g1")});
    refuse("field_array.get", {domain, builder.getStringAttr("4")});
    refuse("field_array.get", {domain, builder.getI64IntegerAttr(4)});
    refuse("field_array.get", {domain, natural(1048577)});
    refuse("numerical.map", {domain, builder.getStringAttr("101")});
    refuse("numerical.map", {domain, natural(5)});
    refuse("numerical.map", {domain});
    SmallVector<bool> excessive(1024, false);
    refuse("numerical.map", {domain, builder.getDenseBoolArrayAttr(excessive)});
    MLIRContext foreign;
    refuse("field.add", {StringAttr::get(&foreign, "bls12-381.fr")});
    refuse("numerical.map", {domain, DenseBoolArrayAttr::get(&foreign, {})});
  });
  cases.run("native and neutral signatures agree for installed instances", [&] {
    std::set<std::string> covered;
    for (StringRef contract : {"representation.convert", "table.relayout"}) {
      auto table = poly::MultilinearType::get(&context, "bls12-381.fr");
      auto logical = contract == "table.relayout" ? Type(table) : Type(field);
      Attribute argument = contract == "table.relayout" ? Attribute(domain)
                                                        : TypeAttr::get(field);
      require(protocol::authoringStage(contract) ==
                      protocol::AuthoringStage::Physical &&
                  resolve(contract, {argument}) ==
                      builder.getFunctionType({logical}, {logical}),
              "physical adapter lost its declared erasure or stage");
      covered.insert(contract.str());
    }
    unsigned checked = 0, logicalSelections = 0, physicalSelections = 0;
    std::set<std::string> implementations;
    // Sample every installed root identity independently. Neutral resolution is
    // an independent boundary oracle; unsupported codec profiles may refuse
    // there even when mathematical formation succeeds.
    for (const auto &operation : protocol::executableOperationContracts()) {
      if (protocol::authoringStage(operation.name) ==
          protocol::AuthoringStage::Physical)
        continue;
      std::vector<std::vector<std::string>> choices;
      for (auto [i, term] : llvm::enumerate(operation.signature.scope.terms)) {
        if (term.parent || term.arguments ||
            operation.signature.scope.constants.count(i))
          continue;
        auto sort = operation.signature.scope.sorts[i];
        if (sort == "Type")
          choices.push_back({"field:bls12-381.fr"});
        else if (sort == "Nat")
          choices.push_back({"4"});
        else if (sort == "Slot")
          choices.push_back({"ticket"});
        else {
          choices.emplace_back();
          for (const auto &candidate :
               protocol::installedDomains().allDomains())
            if (candidate.sort == sort)
              choices.back().push_back(candidate.identity);
        }
      }
      if (llvm::any_of(choices,
                       [](const auto &values) { return values.empty(); }))
        continue;
      size_t samples = 1;
      for (const auto &values : choices)
        samples = std::max(samples, values.size());
      for (size_t sample = 0; sample < samples; ++sample) {
        protocol::BindingApplication binding{operation.name, {}, ""};
        SmallVector<Attribute> actuals;
        unsigned root = 0;
        for (auto [i, term] :
             llvm::enumerate(operation.signature.scope.terms)) {
          if (term.parent || term.arguments ||
              operation.signature.scope.constants.count(i))
            continue;
          auto &values = choices[root++];
          auto value = values[sample % values.size()];
          binding.arguments.push_back(value);
          auto sort = operation.signature.scope.sorts[i];
          actuals.push_back(sort == "Type" ? Attribute(TypeAttr::get(field))
                            : sort == "Nat"
                                ? Attribute(natural(4))
                                : Attribute(builder.getStringAttr(value)));
        }
        if (operation.numerical) {
          binding.arguments.push_back("101");
          actuals.push_back(builder.getDenseBoolArrayAttr({true, false, true}));
        }
        auto neutral = protocol::resolveLogicalBinding(binding);
        if (!neutral) {
          llvm::consumeError(neutral.takeError());
          continue;
        }
        auto native = resolve(operation.name, actuals);
        auto compare = [&](ArrayRef<Type> types,
                           ArrayRef<protocol::BoundType> expected) {
          require(types.size() == expected.size(), "signature arity changed");
          for (auto [type, port] : llvm::zip(types, expected))
            require(type == protocol::decodeBoundType(&context, port),
                    "native and neutral port disagree: " + operation.name);
        };
        compare(native.getInputs(), neutral->inputs);
        compare(native.getResults(), neutral->outputs);
        for (const auto &descriptor :
             protocol::installedImplementations().all()) {
          if (descriptor.contract != operation.name)
            continue;
          auto selected = binding;
          selected.implementation = descriptor.identity;
          auto logicalSelection = protocol::resolveBinding(selected, false);
          auto declaration = runtime::BindingOp::create(
              nativeBuilder, installations->getLoc(),
              "binding_" + std::to_string(nextBinding++), operation.name,
              builder.getArrayAttr(actuals), descriptor.identity,
              executableBindingSignature(native), ArrayAttr{}, ArrayAttr{});
          auto nativeSelection = readNativeBinding(emit, declaration, false);
          bool neutralAccepted = bool(logicalSelection);
          if (!neutralAccepted)
            llvm::consumeError(logicalSelection.takeError());
          require(neutralAccepted == succeeded(nativeSelection),
                  "native and neutral logical selections disagree: " +
                      descriptor.identity);
          ++logicalSelections;
          auto parameters = protocol::defaultPhysicalArguments(selected);
          if (!parameters) {
            llvm::consumeError(parameters.takeError());
            continue;
          }
          selected.physicalArguments = std::move(*parameters);
          auto physicalSelection = protocol::resolveBinding(selected, true);
          if (!physicalSelection) {
            llvm::consumeError(physicalSelection.takeError());
            continue;
          }
          auto imported = take(protocol::importBinding(
              nativeBuilder, installations->getLoc(),
              {"binding_" + std::to_string(nextBinding++), selected}, true));
          acceptInstallation(imported, true);
          ++physicalSelections;
          implementations.insert(descriptor.identity);
        }
        ++checked;
        covered.insert(operation.name);
      }
    }
    require(covered.size() == protocol::executableOperationContracts().size() &&
                checked >= 1000,
            "installed signature coverage unexpectedly shrank");
    llvm::outs() << "native signatures: " << covered.size() << " contracts, "
                 << checked
                 << " instances; installation selections: " << logicalSelections
                 << " logical, " << physicalSelections << " physical, "
                 << implementations.size() << " implementation identities\n";
    require(physicalSelections && logicalSelections,
            "no installed selections were compared");
  });
  return cases.result();
}
