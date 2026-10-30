#include "zkc/Target/CpuTarget.h"
#include "NativePlanTypes.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/ResourceUnit.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Support/Json.h"
#include "zkc/Target/Catalog.h"
#include "llvm/ADT/STLExtras.h"

using namespace llvm;
using namespace zkc::protocol;
namespace zkc::target {
namespace {
unsigned providerBit(StringRef provider) {
  const StringRef names[] = {"arkworks", "blst", "dalek", "halo2curves",
                             "plonky3"};
  for (auto [index, name] : enumerate(names))
    if (provider == name)
      return 1u << index;
  return 0;
}

// Actual CPU storage owners, maintained independently of Contracts' expected
// representations and default-provider preferences. In particular host.resource
// is not provider-independent, and native implementation families span domains.
StringRef domainOwner(StringRef domain) {
  const StringRef arkworks[] = {"bls12-381.fr",
                                "bls12-381.g1",
                                "bls12-381.g2",
                                "bls12-381.gt",
                                "bn254.fr",
                                "bn254.g1",
                                "bn254.g2",
                                "bn254.gt",
                                "multilinear.kzg.bls12-381/0",
                                "merlin3.bls12-381.fr64be/0",
                                "hash-chain.keccak256.bls12-381.fr64be/0",
                                "spongefish0.8.0.keccak.bls12-381.fr64be/0"};
  const StringRef dalek[] = {"ristretto255.scalar", "ristretto255.group",
                             "edwards25519.prime",
                             "merlin3.ristretto255.scalar64le/0"};
  const StringRef plonky3[] = {
      "koala-bear",
      "koala-bear.ext8-binomial3",
      "koala-bear.ext4-binomial3",
      "baby-bear",
      "baby-bear.ext4-binomial11",
      "goldilocks",
      "goldilocks.ext2-binomial7",
      "gf2-64.pentanomial-4-3-1",
      "gf2-64.pentanomial-4-3-1.ext3-trinomial1",
      "merlin3.koala-bear.ext8-binomial3.rejection31le/0",
      "merlin3.baby-bear.ext4-binomial11.rejection31le/0",
      "merlin3.goldilocks.ext2-binomial7.rejection64le/0",
      "hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0",
      "rows.merkle-keccak256.koala-bear/0",
      "rows.merkle-keccak256.koala-bear.ext8-binomial3/0",
      "rows.merkle-poseidon2-16.koala-bear/0",
      "rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0",
      "rows.merkle-poseidon2-16.baby-bear/0",
      "rows.merkle-poseidon2-16.baby-bear.ext4-binomial11/0",
      "rows.merkle-poseidon2-8.goldilocks/0",
      "rows.merkle-poseidon2-8.goldilocks.ext2-binomial7/0"};
  if (is_contained(arkworks, domain))
    return "arkworks";
  if (is_contained(dalek, domain))
    return "dalek";
  if (is_contained(plonky3, domain))
    return "plonky3";
  return {};
}

StringRef representationOwner(StringRef kind, StringRef identity,
                              StringRef rep) {
  const StringRef independent[] = {
      "native.bool/0",      "native.index/0",    "native.indices/0",
      "native.bytes/0",     "native.shake128/0", "native.quotient_matrix/0",
      "logical.sequence/0", "logical.variant/0", "logical.resource_unit/0"};
  if (is_contained(independent, rep))
    return "independent";
  const StringRef blst[] = {"blst/fr", "blst/g1", "blst/g2", "blst/field-array",
                            "blst/fixed-vector"};
  if (is_contained(blst, rep))
    return "blst";
  const StringRef halo[] = {"halo2curves-axiom/bn254.fr",
                            "halo2curves-axiom/bn254.g1",
                            "halo2curves-axiom/bn254.g2"};
  if (is_contained(halo, rep))
    return "halo2curves";
  if (rep == "plonky3.fixed-vector/0")
    return "plonky3";
  // Ordinary layouts are already independently admitted by Contracts. Their
  // exact nominal storage owner, not the spelling of an implementation or the
  // current canonical preference, determines the required contribution.
  return domainOwner(identity.empty() && kind == "field_array"
                         ? StringRef("bls12-381.fr")
                         : identity);
}

Error unavailable(StringRef detail) {
  return error("cpu-target-unavailable", detail);
}
} // namespace

Expected<CpuTarget> CpuTarget::parse(StringRef text) {
  auto parsed = parseNaturalJson(text, descriptorByteLimit, 4,
                                 "cpu-target-invalid", "cpu-target-limit");
  if (!parsed)
    return parsed.takeError();
  auto *object = parsed->getAsObject();
  if (!object || object->size() != 2 ||
      object->getString("format") != "zkc.cpu-target/0")
    return error("cpu-target-invalid");
  auto *names = object->getArray("providers");
  if (!names || names->size() > 5)
    return error("cpu-target-invalid");
  unsigned selected = 0;
  for (const auto &item : *names) {
    auto name = item.getAsString();
    auto bit = name ? providerBit(*name) : 0;
    if (!bit || (selected & bit))
      return error("cpu-target-invalid");
    selected |= bit;
  }
  return CpuTarget(selected);
}

bool CpuTarget::includes(StringRef provider) const {
  return (providers & providerBit(provider)) != 0;
}
std::string CpuTarget::descriptor() const {
  json::Array names;
  for (StringRef name : {"arkworks", "blst", "dalek", "halo2curves", "plonky3"})
    if (includes(name))
      names.push_back(name);
  return printJson(json::Object{{"format", "zkc.cpu-target/0"},
                                {"providers", std::move(names)}});
}

Error CpuTarget::checkType(const BoundType &type) const {
  auto owner =
      representationOwner(type.kind, type.identity, type.representation);
  if (owner.empty() || (owner != "independent" && !includes(owner)))
    return unavailable(type.spelling());
  if (type.physicalChildren)
    for (const auto &child : *type.physicalChildren)
      if (auto e = checkType(child))
        return e;
  return Error::success();
}

Error CpuTarget::checkImplementation(const BindingApplication &app) const {
  SmallVector<StringRef> identities(app.arguments.begin(), app.arguments.end());
  return checkImplementation(app.contract, app.implementation, identities);
}
Error CpuTarget::checkImplementation(StringRef contract,
                                     StringRef implementation,
                                     ArrayRef<StringRef> identities) const {
  // These are actual compiled handler owner families. Contracts must resolve
  // independently first: matching this table cannot install an operation.
  // The historical Arkworks names of these generic controls are wire identity,
  // not a numerical provider dependency (CPU backend/execute.rs).
  const StringRef controls[] = {"bool.and", "bool.not", "bool.or",
                                "control.require"};
  if (is_contained(controls, contract) &&
      implementation == ("arkworks/" + contract).str())
    return Error::success();
  const std::pair<StringRef, StringRef> families[] = {
      {"arkworks", "arkworks"},
      {"arkworks-msb", "arkworks"},
      {"arkworks-diagonal", "arkworks"},
      {"arkworks-pairwise", "arkworks"},
      {"dalek", "dalek"},
      {"dalek-diagonal", "dalek"},
      {"plonky3", "plonky3"},
      {"spongefish", "arkworks"},
      {"blst", "blst"},
      {"blst/resident", "blst"},
      {"halo2curves-axiom/resident", "halo2curves"}};
  for (auto [family, owner] : families)
    if (implementation == (family + "/" + contract).str())
      return includes(owner) ? Error::success() : unavailable(implementation);
  if (implementation == ("native/" + contract).str()) {
    // External transcript adapters have numerical dependencies even at an
    // init/hash call whose entire signature consists of generic indices.
    if (StringRef(contract).starts_with("external.monero."))
      return includes("dalek") ? Error::success() : unavailable(implementation);
    if (StringRef(contract).starts_with("external.openvm."))
      return includes("plonky3") ? Error::success()
                                 : unavailable(implementation);
    for (const auto &argument : identities) {
      auto owner = domainOwner(argument);
      if (!owner.empty() && !includes(owner))
        return unavailable(argument);
    }
    // Native sequence, observation and control families are constrained by
    // their fully resolved ports below, not granted all numerical domains.
    return Error::success();
  }
  if (resourceUnitContract(contract) &&
      implementation == ("logical/" + contract).str())
    return Error::success();
  return unavailable(implementation);
}

Error CpuTarget::checkBinding(const BindingApplication &app,
                              const BoundOperation &ports) const {
  if (auto e = checkImplementation(app))
    return e;
  for (const auto &type : ports.inputs)
    if (auto e = checkType(type))
      return e;
  for (const auto &type : ports.outputs)
    if (auto e = checkType(type))
      return e;
  // Codec payloads and service-like native families can erase their numerical
  // value from the signature. Static codec endpoints still require their
  // compiled default layout. Type arguments are covered by resolved ports.
  for (const auto &argument : app.arguments)
    if (auto e = checkCodec(argument))
      return e;
  return Error::success();
}
Error CpuTarget::checkCodec(StringRef identity) const {
  if (const auto *codec = installedDomains().codec(identity)) {
    auto logical = applyBoundType(
        codec->kind, codec->domain.empty() ? std::vector<std::string>{}
                                           : std::vector{codec->domain});
    if (!logical)
      return logical.takeError();
    auto physical = defaultRepresentation(*logical);
    if (!physical)
      return physical.takeError();
    return checkType(*physical);
  }
  return Error::success();
}
Error CpuTarget::checkType(mlir::Type type) const {
  if (auto e = checkPhysicalType(type))
    return e;
  // Formation above owns logical and represented validity. This traversal only
  // checks the CPU's immutable storage-owner facts, shared with neutral users.
  auto available = [&](auto &&self, mlir::Type value) -> Error {
    auto represented = mlir::cast<runtime::RepresentedType>(value);
    auto logical = represented.getLogical();
    StringRef identity;
    auto kind = planTypeConstructor(logical);
    if (auto interface = mlir::dyn_cast<CatalogTypeInterface>(logical)) {
      auto application = interface.getCatalogApplication();
      if (application && !application->arguments.empty())
        if (auto domain =
                mlir::dyn_cast<mlir::StringAttr>(application->arguments[0]))
          identity = domain.getValue();
    }
    auto owner =
        representationOwner(kind, identity, represented.getRepresentation());
    if (owner.empty() || (owner != "independent" && !includes(owner)))
      return unavailable(represented.getRepresentation());
    for (mlir::Type child : represented.getChildren())
      if (auto e = self(self, child))
        return e;
    return Error::success();
  };
  return available(available, type);
}
Error CpuTarget::checkBinding(const NativeBinding &binding) const {
  // Recheck the live declaration; a stale view cannot bypass installation or
  // stage validation. Native checking never consults the neutral serializer.
  auto declaration = binding.declaration;
  if (!declaration)
    return error("binding-declaration");
  auto emit = [&] {
    auto diagnostic = declaration.emitError();
    diagnostic.abandon();
    return diagnostic;
  };
  auto checked = readNativeBinding(emit, declaration, true);
  if (mlir::failed(checked))
    return error("binding-declaration");
  SmallVector<StringRef> identities;
  for (mlir::Attribute argument : declaration.getArguments())
    if (auto identity = mlir::dyn_cast<mlir::StringAttr>(argument))
      identities.push_back(identity.getValue());
  if (auto e = checkImplementation(declaration.getContract(),
                                   declaration.getImplementation(), identities))
    return e;
  for (auto types :
       {checked->valueType.getInputs(), checked->valueType.getResults()})
    for (mlir::Type type : types)
      if (auto e = checkType(type))
        return e;
  for (StringRef identity : identities)
    if (auto e = checkCodec(identity))
      return e;
  return Error::success();
}

Error CpuTarget::checkNativeImplementation(
    const NativeBindingApplication &application) const {
  SmallVector<StringRef> identities;
  for (mlir::Attribute argument : application.arguments)
    if (auto identity = mlir::dyn_cast<mlir::StringAttr>(argument))
      identities.push_back(identity.getValue());
  return checkImplementation(application.contract, application.implementation,
                             identities);
}
Error CpuTarget::checkNativeApplication(
    const NativeBindingApplication &application) const {
  auto ports = resolveNativeApplication(application);
  if (!ports)
    return ports.takeError();
  if (auto e = checkNativeImplementation(application))
    return e;
  for (auto types : {ports->getInputs(), ports->getResults()})
    for (mlir::Type type : types)
      if (auto e = checkType(type))
        return e;
  for (mlir::Attribute argument : application.arguments)
    if (auto identity = mlir::dyn_cast<mlir::StringAttr>(argument))
      if (auto e = checkCodec(identity.getValue()))
        return e;
  return Error::success();
}

Error CpuTarget::checkService(StringRef contract) const {
  auto draw = serviceMethod(contract, "draw");
  if (!draw)
    return unavailable(contract);
  auto physical = defaultRepresentation(draw->output);
  if (!physical)
    return physical.takeError();
  return checkType(*physical);
}
} // namespace zkc::target
