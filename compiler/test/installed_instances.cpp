// The installed owners are built from the generated installed-instance and
// native installation tables. The retained ordered dump records those owners
// and the facts their consumers derive, in declared order; its fixture makes
// every change visible. Regenerate it only deliberately, with
// `zkc-installed_instances-test --dump`.
//
// Differential evidence: consumers that still restate installed facts, and
// independent readers of them, agree with the generated tables. Every intended
// difference is listed below with its reason; any other difference, or a
// listed one that no longer occurs, fails.
#include "../lib/Language/DataRequirements.h"
#include "mlir/IR/Verifier.h"
#include "support/ResourceSources.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Implementations.h"
#include "zkc/Contracts/Instances.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/ResourceUnit.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/TypeRepresentations.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Commitment/IR/CommitmentTypes.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Evm/Evm.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/ResourceOrigins.h"
#include "zkc/Language/Builtins.h"
#include "zkc/Language/Project.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Target/CpuTarget.h"
#include "zkc/Target/Evm/Wire.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"
#include <algorithm>
#include <map>
#include <set>

using namespace llvm;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::test;
namespace generated = zkc::protocol::instances;
namespace physical = zkc::protocol::installation;

namespace {
// One difference between generated data and a hand-written owner.
struct Difference {
  std::string subject, reason;
};
// The listed differences must be exactly the found ones.
void agree(StringRef comparison, std::vector<std::string> found,
           ArrayRef<Difference> expected) {
  std::vector<std::string> listed;
  for (const auto &difference : expected) {
    listed.push_back(difference.subject);
    outs() << "expected difference, " << comparison << ": "
           << difference.subject << ": " << difference.reason << '\n';
  }
  sort(found);
  sort(listed);
  if (found == listed)
    return;
  std::string message = (comparison + " differs:").str();
  for (const auto &subject : found)
    if (!is_contained(listed, subject))
      message += " unexpected [" + subject + "]";
  for (const auto &subject : listed)
    if (!is_contained(found, subject))
      message += " no longer differs [" + subject + "]";
  throw std::runtime_error(message);
}
std::string code(Error error) {
  std::string result;
  handleAllErrors(
      std::move(error), [&](const Refusal &r) { result = r.code; },
      [&](const ErrorInfoBase &e) { result = e.message(); });
  return result;
}
template <typename T> std::string refusalCode(Expected<T> value) {
  return value ? std::string() : code(value.takeError());
}

const generated::Domain &row(StringRef identity) {
  const auto *found = generated::domain(identity);
  require(found, "missing generated domain " + identity);
  return *found;
}
const generated::Codec *codecFor(StringRef kind, StringRef identity) {
  for (const auto &codec : generated::codecs())
    if (codec.kind == kind && codec.domain == identity)
      return &codec;
  return nullptr;
}
std::vector<std::string> identities() {
  std::vector<std::string> result{""};
  for (const auto &domain : generated::domains())
    result.push_back(domain.identity);
  for (const auto &codec : generated::codecs())
    result.push_back(codec.identity);
  return result;
}
// The CPU target's storage owner of one physical type, measured through its
// public descriptor: provider-free storage passes with no unit selected.
std::string storageUnit(const BoundType &type) {
  const StringRef units[] = {"arkworks", "blst", "dalek", "halo2curves",
                             "plonky3"};
  auto target = [](StringRef selection) {
    return take(target::CpuTarget::parse(
        (R"({"format":"zkc.cpu-target/0","providers":[)" + selection + "]}")
            .str()));
  };
  if (auto error = target("").checkType(type))
    consumeError(std::move(error));
  else
    return "independent";
  std::vector<std::string> owners;
  for (auto unit : units)
    if (auto error = target(("\"" + unit + "\"").str()).checkType(type))
      consumeError(std::move(error));
    else
      owners.push_back(unit.str());
  return owners.size() == 1 ? owners.front() : "<" + join(owners, ",") + ">";
}
// The CPU target's owner of a nominal domain, measured by a provider-generic
// native implementation over that one static identity.
std::string domainUnit(StringRef identity) {
  const StringRef units[] = {"arkworks", "blst", "dalek", "halo2curves",
                             "plonky3"};
  BindingApplication probe{
      "installed.unit_probe", {identity.str()}, "native/installed.unit_probe"};
  auto admits = [&](StringRef selection) {
    auto target = take(target::CpuTarget::parse(
        (R"({"format":"zkc.cpu-target/0","providers":[)" + selection + "]}")
            .str()));
    if (auto error = target.checkImplementation(probe)) {
      consumeError(std::move(error));
      return false;
    }
    return true;
  };
  if (admits(""))
    return "";
  std::vector<std::string> owners;
  for (auto unit : units)
    if (admits(("\"" + unit + "\"").str()))
      owners.push_back(unit.str());
  return owners.size() == 1 ? owners.front() : "<" + join(owners, ",") + ">";
}

// Frame facts that the EVM wire generator emits for one complete type.
struct WireFrame {
  unsigned tag = 0;
  std::optional<uint64_t> frameBytes, stride, word;
  bool byteStride = false;
};
std::optional<uint64_t> numberAfter(StringRef text, StringRef prefix) {
  auto at = text.find(prefix);
  if (at == StringRef::npos)
    return std::nullopt;
  auto digits = text.drop_front(at + prefix.size()).take_while(isDigit);
  uint64_t value = 0;
  if (digits.empty() || digits.getAsInteger(10, value))
    return std::nullopt;
  return value;
}
StringRef functionBody(StringRef text, StringRef name) {
  auto start = text.find(("function " + name + "(").str());
  require(start != StringRef::npos, "missing generated wire function " + name);
  auto end = text.find("\nfunction ", start + 1);
  return text.slice(start, end);
}
WireFrame wireFrame(evm::NativeLayouts &layouts, mlir::Type type) {
  EvmLimits limits;
  evm::WireGenerator wire(layouts, limits);
  auto name = take(wire.decoder(type));
  StringRef decoder(name);
  require(decoder.consume_back("_decode"), "unexpected wire decoder name");
  auto definitions = wire.definitions();
  StringRef text(definitions);
  WireFrame result;
  auto scan = functionBody(text, (decoder + "_scan").str());
  auto header = scan.find("0x5a4b435600");
  require(header != StringRef::npos, "wire scan checks no frame header");
  require(!scan.substr(header + 12, 2).getAsInteger(16, result.tag),
          "unreadable frame tag");
  result.frameBytes = numberAfter(scan, "if iszero(eq(n, ");
  result.stride = numberAfter(scan, "let bytes := evm_wire_mul(count, ");
  if (!result.stride)
    result.stride =
        numberAfter(scan, "if iszero(eq(n, add(10, evm_wire_mul(count, ");
  result.byteStride = scan.contains("if iszero(eq(n, add(10, count)))");
  auto canonical = functionBody(text, (decoder + "_canonical").str());
  if (auto at = canonical.find("evm_le(add(add(p, "); at != StringRef::npos)
    result.word = numberAfter(canonical.drop_front(at), "mul(i, ");
  return result;
}
data::VariantType variantType(mlir::MLIRContext &context) {
  SmallVector<data::AlternativeAttr> alternatives;
  for (StringRef label : {"left", "right"})
    alternatives.push_back(data::AlternativeAttr::get(
        &context, mlir::StringAttr::get(&context, label), {}));
  return data::VariantType::get(
      &context, data::importVariantIdentity(&context, json::Value("Choice")),
      alternatives);
}

// Source declarations that name each finite definition or domain constructor
// with the signature its columns describe.
const char *sourcePrelude = R"(module m;
type Vector<F:Field>=builtin("vector",F);
type Groups<G:Group>=builtin("groups",G);
type Matrix<F:Field>=builtin("matrix",F);
type Sequence<T:Type+Copy+Drop>=builtin("sequence",T);
type Indices=builtin("indices");
type Array<F:Field,N:nat>=builtin("field_array",F,N);
domain Fr=field("koala-bear");
)";
Expected<language::CheckedProject> checkSource(StringRef source) {
  auto captured =
      language::capture({{"m", sourcePrelude + source.str(), "instances.zkc"}});
  if (!captured)
    return captured.takeError();
  return language::analyze(*captured).checkedProject();
}
const language::Declaration *declaration(const language::CheckedProject &p,
                                         StringRef name) {
  for (const auto &decl : p.declarations())
    if (decl.qualifiedName == name)
      return &decl;
  return nullptr;
}
std::string finiteSource(const generated::FiniteDefinition &definition,
                         StringRef identity) {
  const bool math = definition.mode == generated::FiniteMode::Math;
  const std::string callback = math ? "math fn" : "fn";
  const std::string effects = math ? "" : " effects(stop)";
  const std::string item = " where item_from(item, rows)";
  std::string generics = "I:Type+Copy+Drop", inputs = "rows:domain<I>", result;
  std::string body;
  if (definition.operation == generated::FiniteOperation::Fold) {
    generics += math ? ",S:Type+Copy+Drop" : ",S:Type";
    inputs += ",initial:S";
    body = "step:" + callback + "(S,item:I)->S" + effects + item;
    result = "S";
  } else {
    auto collection = *definition.collection;
    std::string element;
    if (collection == "vector")
      generics += ",F:Field", element = "F", result = "Vector<F>";
    else if (collection == "groups")
      generics += ",G:Group", element = "G", result = "Groups<G>";
    else if (collection == "sequence")
      generics += ",T:Type+Copy+Drop", element = "T", result = "Sequence<T>";
    else if (collection == "indices")
      element = "index", result = "Indices";
    else
      generics += ",N:nat", element = "Fr", result = "Array<Fr,N>";
    body = "body:" + callback + "(item:I)->" + element + effects + item;
  }
  if (definition.filtered)
    inputs += ",keep:" + callback + "(item:I)->bool" + effects + item;
  return (math ? "math fn" : "fn") + std::string(" defined<") + generics +
         ">(" + inputs + "," + body + ")->" + result + effects + "=finite(\"" +
         identity.str() + "\");\n";
}
std::string domainSource(const generated::DomainConstructor &constructor,
                         StringRef identity) {
  using K = generated::DomainConstructorKind;
  std::string signature;
  switch (constructor.kind) {
  case K::Elements:
    signature = "<F:Field>(xs:Vector<F>)->domain<F>";
    break;
  case K::Indices:
    signature = constructor.axis ? "<F:Field>(xs:Matrix<F>)->domain<index>"
                                 : "<F:Field>(xs:Vector<F>)->domain<index>";
    break;
  case K::Range:
    signature = "(lo:index,hi:index)->domain<index>";
    break;
  case K::Zip:
  case K::Product:
    signature = "<A:Type+Copy+Drop,B:Type+Copy+Drop>(a:domain<A>,b:domain<B>)"
                "->domain<(A,B)>";
    break;
  case K::MatrixRow:
  case K::MatrixColumn:
    signature = "<F:Field>(xs:Matrix<F>,i:index)->domain<F>";
    break;
  case K::MatrixCoordinates:
    signature = "<F:Field>(xs:Matrix<F>)->domain<(index,index)>";
    break;
  case K::SourceArray:
    signature = "<T:Type+Copy+Drop,N:nat>(xs:[T;N])->domain<T>";
    break;
  }
  return "domain fn defined" + signature + "=domain(\"" + identity.str() +
         "\");\n";
}
language::DomainBinding::Kind bindingKind(generated::DomainConstructorKind k) {
  using K = generated::DomainConstructorKind;
  using B = language::DomainBinding::Kind;
  switch (k) {
  case K::Elements:
    return B::Elements;
  case K::Indices:
    return B::Indices;
  case K::Range:
    return B::Range;
  case K::Zip:
    return B::Zip;
  case K::Product:
    return B::Product;
  case K::MatrixRow:
    return B::MatrixRow;
  case K::MatrixColumn:
    return B::MatrixColumn;
  case K::MatrixCoordinates:
    return B::MatrixCoordinates;
  case K::SourceArray:
    return B::SourceArray;
  }
  llvm_unreachable("domain constructor kind");
}
// The retained ordered dump: every installed owner row and the facts that
// the services, type properties, implementations and operation shapes derive
// from them, in declared order.
using Table = std::pair<std::string, json::Array>;
std::vector<Table> dump() {
  const auto &catalog = installedDomains();
  json::Array domains, types, codecs, representations;
  for (const auto &domain : catalog.allDomains()) {
    json::Array members, capabilities;
    for (const auto &member : domain.associated)
      members.push_back(json::Array{member.member, member.identity});
    for (const auto &capability : domain.capabilities)
      capabilities.push_back(capability);
    domains.push_back(
        json::Object{{"identity", domain.identity},
                     {"sort", domain.sort},
                     {"members", std::move(members)},
                     {"capabilities", std::move(capabilities)},
                     {"modulus", domain.modulus},
                     {"provider", catalog.defaultProvider(domain.identity)}});
  }
  for (const auto &type : catalog.allLogicalTypes())
    types.push_back(json::Array{type.kind, type.domain});
  for (const auto &codec : catalog.allCodecs())
    codecs.push_back(json::Array{codec.identity, codec.kind, codec.domain});
  for (const auto &row : catalog.allRepresentations())
    representations.push_back(json::Array{row.identity, row.kind, row.domain,
                                          row.isDefault, row.layout});
  json::Array fields;
  for (const auto &field : plonky3Fields())
    fields.push_back(json::Object{{"identity", field.identity},
                                  {"base", field.base},
                                  {"modulus", field.modulus},
                                  {"degree", field.degree},
                                  {"nonresidue", field.nonresidue},
                                  {"coordinateBytes", field.coordinateBytes},
                                  {"montgomery32", field.montgomery32}});
  json::Array services;
  for (const auto &service : randomServices())
    services.push_back(json::Array{service.contract, service.field});
  json::Array applied;
  for (const auto &entry : appliedTypeRepresentations()) {
    json::Array arguments;
    for (const auto &pattern : entry.arguments)
      if (pattern.argument.kind == TypeArgument::Kind::Nat)
        arguments.push_back(json::Array{pattern.minimum, pattern.maximum});
      else
        arguments.push_back(pattern.argument.spelling());
    applied.push_back(json::Object{{"constructor", entry.constructor},
                                   {"arguments", std::move(arguments)},
                                   {"representation", entry.representation},
                                   {"default", entry.isDefault},
                                   {"child", entry.childType.spelling()}});
  }
  // Constructor defaults, and the frames of array samples over every field.
  json::Array defaults, arrays;
  auto variant =
      *encodeVariant({"Choice", {{"left", {}}, {"right", {"bool"}}}});
  std::vector<std::string> samples = {"fixed_vector<field:koala-bear,0>",
                                      "fixed_vector<field:koala-bear,1048576>",
                                      "fixed_vector<field:bls12-381.fr,4>",
                                      "sequence<bool>",
                                      "sequence<field:koala-bear>",
                                      variant,
                                      "resource_unit:Slot.A"};
  for (const auto &domain : catalog.allDomains())
    if (domain.sort == "Field")
      for (StringRef size : {"0", "4", "1048576"})
        samples.push_back(
            ("field_array<" + domain.identity + "," + size + ">").str());
  for (const auto &spelling : samples) {
    auto logical = parseBoundType(spelling, false);
    if (!logical) {
      consumeError(logical.takeError());
      continue;
    }
    std::string selected = "<none>";
    if (auto physical = defaultRepresentation(*logical)) {
      selected = physical->spelling();
      arrays.push_back(json::Array{selected, nativeMessageData(*physical)});
    } else
      consumeError(physical.takeError());
    defaults.push_back(json::Array{spelling, selected});
    arrays.push_back(json::Array{spelling, nativeMessageData(*logical),
                                 nativeFieldArrayWire(*logical)});
    for (const auto &entry : appliedTypeRepresentations()) {
      if (entry.constructor != logical->kind || entry.isDefault)
        continue;
      auto physical = physicalType(*logical, entry.representation, {});
      if (!physical) {
        consumeError(physical.takeError());
        continue;
      }
      arrays.push_back(
          json::Array{physical->spelling(), nativeMessageData(*physical)});
    }
  }
  json::Array cosets, widths, atoms, setups, challenges, residents;
  for (const auto &identity : identities()) {
    if (const auto *convention = cosetConvention(identity))
      cosets.push_back(json::Array{
          identity, convention->identity, convention->rootField,
          convention->maximalRoot, convention->order, convention->maxLogSize});
    if (unsigned width = fieldBitPatternWidth(identity))
      widths.push_back(json::Array{identity, width});
    for (const auto &type : typeDeclarations())
      if (nativeMessageAtom(type.name, identity))
        atoms.push_back(json::Array{type.name, identity});
    if (auto field = nativeChallengeField(identity); !field.empty())
      challenges.push_back(json::Array{identity, field});
  }
  for (const auto &type : catalog.allLogicalTypes())
    if (nativeSetupType({type.kind, type.domain, ""}))
      setups.push_back(json::Array{type.kind, type.domain});
  for (const auto &row : catalog.allRepresentations()) {
    auto logical = applyBoundType(
        row.kind, row.domain.empty() ? std::vector<std::string>{}
                                     : std::vector<std::string>{row.domain});
    if (!logical) {
      consumeError(logical.takeError());
      continue;
    }
    auto represented = physicalType(*logical, row.identity, {});
    if (!represented) {
      consumeError(represented.takeError());
      continue;
    }
    residents.push_back(json::Array{row.identity, row.kind, row.domain,
                                    nativeMessageData(*represented)});
  }
  json::Array relation;
  for (StringRef provider : {"arkworks", "blst", "dalek", "halo2curves-axiom",
                             "plonky3", "spongefish", "native"})
    for (const auto &identity : identities())
      if (implementationProviderSupports(provider, identity))
        relation.push_back(json::Array{provider, identity});
  json::Array resourceUnits;
  for (const auto &operation : executableOperationContracts())
    if (resourceUnitContract(operation.name))
      resourceUnits.push_back(operation.name);
  json::Array implementations;
  for (const auto &entry : installedImplementations().all()) {
    json::Array ports;
    for (const auto &port : entry.representations)
      ports.push_back(json::Array{port.kind, port.domain, port.identity,
                                  port.port ? json::Value(int64_t(*port.port))
                                            : json::Value(nullptr),
                                  port.output});
    json::Value dense = nullptr;
    if (entry.denseLayout)
      dense =
          json::Array{entry.denseLayout->container, entry.denseLayout->vector};
    // The admitted domains are a set: only membership is meaningful.
    std::set<std::string> admitted(entry.domains.begin(), entry.domains.end());
    json::Array domainList;
    for (const auto &domain : admitted)
      domainList.push_back(domain);
    implementations.push_back(json::Array{
        entry.contract, entry.identity, entry.provider,
        int64_t(entry.compatibility), std::move(domainList), std::move(ports),
        int64_t(entry.providerTerm), int64_t(entry.family),
        entry.requiresExplicitSelection, std::move(dense)});
  }
  std::vector<Table> tables;
  tables.emplace_back("domains", std::move(domains));
  tables.emplace_back("logicalTypes", std::move(types));
  tables.emplace_back("codecs", std::move(codecs));
  tables.emplace_back("representations", std::move(representations));
  tables.emplace_back("plonky3Fields", std::move(fields));
  tables.emplace_back("randomServices", std::move(services));
  tables.emplace_back("appliedRepresentations", std::move(applied));
  tables.emplace_back("constructorDefaults", std::move(defaults));
  tables.emplace_back("arrayFrames", std::move(arrays));
  tables.emplace_back("cosetConventions", std::move(cosets));
  tables.emplace_back("bitPatternWidths", std::move(widths));
  tables.emplace_back("messageAtoms", std::move(atoms));
  tables.emplace_back("setupTypes", std::move(setups));
  tables.emplace_back("challengeFields", std::move(challenges));
  tables.emplace_back("residentFrames", std::move(residents));
  tables.emplace_back("providerRelation", std::move(relation));
  tables.emplace_back("implementations", std::move(implementations));
  tables.emplace_back("resourceUnitContracts", std::move(resourceUnits));
  return tables;
}
// One row per line, so a fixture change reads as a row diff.
void print(raw_ostream &os, ArrayRef<Table> tables) {
  os << "{\n";
  for (auto [index, table] : enumerate(tables)) {
    os << json::Value(table.first) << ": [\n";
    for (auto [row, value] : enumerate(table.second))
      os << "  " << value << (row + 1 < table.second.size() ? ",\n" : "\n");
    os << "]" << (index + 1 < tables.size() ? ",\n" : "\n");
  }
  os << "}\n";
}
} // namespace

int main(int argc, char **argv) {
  if (argc == 2 && StringRef(argv[1]) == "--dump") {
    print(outs(), dump());
    return 0;
  }
  Cases cases;

  cases.run("retained ordered dump equals its fixture", [&] {
    auto buffer = MemoryBuffer::getFile(ZKC_INSTALLED_INSTANCES_FIXTURE);
    require(bool(buffer), "missing installed-instance fixture");
    auto fixture = take(json::parse((*buffer)->getBuffer()));
    const auto *expected = fixture.getAsObject();
    require(expected, "malformed installed-instance fixture");
    auto tables = dump();
    std::vector<std::string> found;
    for (const auto &[name, rows] : tables) {
      const auto *recorded = expected->getArray(name);
      if (!recorded) {
        found.push_back(name + ": not recorded");
        continue;
      }
      for (size_t i = 0; i < std::max(rows.size(), recorded->size()); ++i)
        if (i >= rows.size() || i >= recorded->size() ||
            rows[i] != (*recorded)[i]) {
          std::string row;
          raw_string_ostream os(row);
          os << name << " row " << i << ": ";
          if (i < rows.size())
            os << rows[i];
          else
            os << "<absent>";
          os << " recorded ";
          if (i < recorded->size())
            os << (*recorded)[i];
          else
            os << "<absent>";
          found.push_back(row);
          break;
        }
    }
    if (expected->size() != tables.size())
      found.push_back("recorded tables differ");
    if (!found.empty())
      throw std::runtime_error("installed dump differs from its fixture: " +
                               join(found, "; "));
  });

  cases.run("resident canonical-frame representations", [&] {
    std::vector<std::string> found;
    for (const auto &row : physical::representations()) {
      if (!nativeMessageAtom(row.kind, row.domain))
        continue;
      auto logical = take(applyBoundType(
          row.kind, row.domain.empty() ? std::vector<std::string>{}
                                       : std::vector<std::string>{row.domain}));
      auto represented = take(physicalType(logical, row.identity, {}));
      if (nativeMessageData(represented) !=
          (row.frame == physical::ValueFrame::Canonical))
        found.push_back(row.identity + " " + row.kind + " " + row.domain);
    }
    agree("resident canonical frames", found, {});
  });

  cases.run("CPU storage units and default provider units", [&] {
    std::vector<std::string> found;
    for (const auto &row : physical::representations()) {
      BoundType type{row.kind, row.domain, row.identity};
      if (storageUnit(type) != row.unit)
        found.push_back("representation " + row.identity + " " + row.kind +
                        " " + row.domain);
    }
    for (const auto &row : physical::appliedRepresentations()) {
      BoundType type{row.constructor, "", row.identity};
      if (storageUnit(type) != row.unit)
        found.push_back("applied " + row.identity);
    }
    for (const auto &row : physical::providers())
      if (domainUnit(row.domain) != physical::providerUnit(row.defaultProvider))
        found.push_back("domain " + row.domain);
    agree("CPU storage units", found, {});
  });

  cases.run("EVM wire tags and widths", [&] {
    mlir::DialectRegistry registry;
    registerDialects(registry);
    registry.insert<evm::EvmDialect>();
    mlir::MLIRContext context(registry);
    context.loadAllAvailableDialects();
    mlir::ScopedDiagnosticHandler quiet(
        &context, [](mlir::Diagnostic &) { return mlir::success(); });
    auto emit = mlir::detail::getDefaultDiagnosticEmitFn(&context);
    evm::NativeLayouts layouts(context);
    std::vector<std::string> found;
    unsigned compared = 0;
    auto check = [&](mlir::Type type, StringRef subject, unsigned tag,
                     std::optional<uint64_t> width,
                     std::optional<uint64_t> word = std::nullopt) {
      if (!type)
        return;
      if (auto error = evm::verifyWireType(layouts, type)) {
        consumeError(std::move(error));
        return;
      }
      ++compared;
      auto frame = wireFrame(layouts, type);
      bool same = frame.tag == tag && (!word || frame.word == word);
      if (width)
        same &= frame.byteStride ? *width == 1
                : frame.stride   ? frame.stride == width
                                 : frame.frameBytes == 6 + *width;
      if (!same)
        found.push_back(subject.str());
    };
    for (const auto &codec : generated::codecs()) {
      if (!codec.frame)
        continue;
      mlir::Type type;
      auto *ctx = &context;
      if (codec.kind == "bool")
        type = mlir::IntegerType::get(ctx, 1);
      else if (codec.kind == "index")
        type = mlir::IntegerType::get(ctx, 64, mlir::IntegerType::Unsigned);
      else if (codec.kind == "indices")
        type = data::IndicesType::get(ctx);
      else if (codec.kind == "bytes")
        type = data::BytesType::get(ctx);
      else if (codec.kind == "field")
        type =
            algebra::FieldType::getChecked(emit, ctx, StringRef(codec.domain));
      else if (codec.kind == "vector")
        type = data::FieldVectorType::getChecked(emit, ctx,
                                                 StringRef(codec.domain));
      else if ((codec.kind == "commitment" || codec.kind == "proof") &&
               row(codec.domain).commitment->scheme !=
                   generated::CommitmentScheme::MultilinearKzg)
        type = commitment::VectorObjectType::get(ctx, codec.domain, codec.kind);
      else
        continue;
      std::optional<uint64_t> width = codec.frame->elementBytes;
      std::optional<uint64_t> word;
      if (const auto *domain = generated::domain(codec.domain);
          domain && domain->commitment) {
        width = domain->commitment->digestBytes;
        word = domain->commitment->digestWordBytes;
      }
      check(type, codec.identity, codec.frame->tag, width, word);
    }
    for (const auto &aggregate : generated::aggregateFrames()) {
      mlir::Type type;
      std::optional<uint64_t> width;
      if (aggregate.constructor == "sequence")
        type = data::SequenceType::get(&context,
                                       mlir::IntegerType::get(&context, 1));
      else if (aggregate.constructor == "variant")
        type = variantType(context);
      else {
        // Four scalars: the frame is 6 + 4 * w bytes.
        type = data::FieldArrayType::getChecked(
            emit, &context, StringRef(aggregate.domain), uint64_t(4));
        width = 4 * *codecFor("field", aggregate.domain)->frame->elementBytes;
      }
      check(type, aggregate.constructor + " " + aggregate.domain, aggregate.tag,
            width);
    }
    require(compared >= 30, "too few EVM frames compared");
    outs() << "EVM frames compared: " << compared << '\n';
    agree("EVM wire frames", found, {});
  });

  cases.run("succession facets and the exact-root analysis", [&] {
    std::vector<std::string> found;
    for (const auto &shape : operationShapes())
      if (shape.contracts.succession)
        found.push_back(
            shape.key.str() + " " +
            std::to_string(shape.contracts.succession->stateInput) + "->" +
            std::to_string(shape.contracts.succession->stateOutput));
    require(found == std::vector<std::string>{"resource_unit.pass 0->0"},
            "generated succession facets differ");
    // The exec root analysis transfers the received root only through pass;
    // fresh create and consume establish no successor.
    for (bool fresh : {false, true}) {
      resource_sources::Source source;
      source.binding("pass", "resource_unit.pass", {"Slot.A"});
      source.binding("create", "resource_unit.create", {"Slot.A"});
      source.binding("consume", "resource_unit.consume", {"Slot.A"});
      auto fn = source.function("step", source.unit, source.unit);
      exec::ScopedExecutionBuilder body(source.builder, fn);
      mlir::Value next;
      if (fresh) {
        source.invoke(body, "consume", fn.getArgument(1), {}, "consume");
        next = source.invoke(body, "create", {}, source.unit, "create")[0];
      } else
        next = source.invoke(body, "pass", fn.getArgument(1), source.unit,
                             "pass")[0];
      body.returned(next);
      require(succeeded(mlir::verify(*source.module)),
              "resource fixture must be formed");
      uint64_t work = 100000;
      auto closure = take(readSourceExecutionClosure(source.owner));
      auto analysis = take(exec::ResourceOriginAnalysis::create(
          source.owner, std::move(closure), work));
      auto roots = take(analysis->get(fn)).roots;
      const auto *pass = operationContracts("resource_unit.pass");
      std::map<unsigned, unsigned> expected;
      if (!fresh && pass->succession)
        expected = {
            {pass->succession->stateOutput, pass->succession->stateInput}};
      require(roots == expected,
              "the analysis successor differs from the Succession facet");
    }
    for (StringRef fresh : {"resource_unit.create", "resource_unit.consume"})
      require(!operationContracts(fresh)->succession,
              "fresh resource operations acquired a successor");
  });

  cases.run("physical-argument calling convention", [&] {
    // Binding resolution admits physical arguments for exactly the operations
    // the installation lists.
    std::set<std::string> declared;
    for (const auto &row : physical::physicalArguments())
      declared.insert(row.operation);
    std::vector<std::string> found;
    unsigned refused = 0;
    for (const auto &operation : executableOperationContracts()) {
      BindingApplication probe{operation.name,
                               {},
                               "installed.probe/" + operation.name,
                               {"bool@native.bool/0"}};
      auto refusal = refusalCode(resolveBinding(probe, true));
      bool admitted = refusal != "binding-representation";
      refused += !admitted;
      if (admitted != bool(declared.count(operation.name)))
        found.push_back(
            (admitted ? "admitted undeclared " : "refused declared ") +
            operation.name);
    }
    agree("physical arguments", found, {});
    outs() << "physical-argument rows: " << declared.size()
           << ", refused: " << refused << '\n';
  });

  cases.run("type columns against the source checker", [&] {
    std::vector<std::string> found;
    auto first = [](StringRef sort) -> std::string {
      if (sort == "Slot")
        return "Slot.A";
      for (const auto &domain : generated::domains())
        if (domain.sort == sort)
          return domain.identity;
      return {};
    };
    for (const auto &type : typeDeclarations()) {
      std::vector<language::Type> arguments;
      for (const auto &p : type.parameters) {
        if (p.kind == StaticKind::Type)
          arguments.emplace_back(language::Type::Kind::Index);
        else if (p.kind == StaticKind::Nat)
          arguments.emplace_back(language::Type::Kind::Natural);
        else if (p.sort == "Field")
          arguments.emplace_back(language::Type::Kind::Field, first("Field"));
        else if (p.sort == "Group")
          arguments.emplace_back(language::Type::Kind::Group, first("Group"));
        else
          arguments.push_back(language::domainType(p.sort, first(p.sort)));
      }
      auto formed = language::builtinType(type.name, arguments);
      std::string refusal;
      if (!formed)
        refusal = toString(formed.takeError());
      bool gated = StringRef(refusal).contains("not an admitted native data");
      if (type.sourceData == gated || (type.sourceData && !refusal.empty()))
        found.push_back("sourceData " + type.name);
      if (!type.sourceData || !formed)
        continue;
      // Collection rank against the source axis view. A byte element gives an
      // extent without source traversal.
      bool traversed = type.collection &&
                       type.collection->element != CollectionElement::Byte;
      unsigned rank = traversed ? type.collection->rank : 0;
      for (unsigned axis = 0; axis < 3; ++axis)
        if (language::detail::collectionAxis(*formed, axis) != (axis < rank))
          found.push_back("collection " + type.name + " axis " +
                          std::to_string(axis));
      // Rank-one elements use the constructor view; a rank-two collection is
      // traversed through its explicit matrix view.
      if (rank == 2) {
        auto element = language::detail::collectionElement(*formed, true);
        if (type.collection->element != CollectionElement::Parameter ||
            !element || *element != formed->arguments.front())
          found.push_back("element " + type.name);
        continue;
      }
      using E = language::detail::CollectionElementKind;
      auto element = language::detail::collectionElementKind(
          *formed, formed->arguments.size());
      auto expected = !traversed ? E::None
                      : type.collection->element == CollectionElement::Index
                          ? E::Index
                          : E::Parameter;
      if (element != expected)
        found.push_back("element " + type.name);
    }
    // Setup dependence over every instance: the setup-key constructors, and
    // every value over a commitment whose scheme requires an authorized setup.
    for (const auto &instance : generated::logicalTypes()) {
      const auto *declared = typeDeclaration(instance.kind);
      const auto *domain = generated::domain(instance.domain);
      bool authorized = domain && domain->commitment &&
                        domain->commitment->scheme ==
                            generated::CommitmentScheme::MultilinearKzg;
      BoundType type{instance.kind, instance.domain, ""};
      if (nativeSetupType(type) != (declared->setup.has_value() || authorized))
        found.push_back("setup " + instance.kind + " " + instance.domain);
    }
    agree("type columns", found, {});
  });

  cases.run("finite definitions against the source decoder", [&] {
    std::vector<std::string> found;
    for (const auto &definition : generated::finiteDefinitions()) {
      auto project = checkSource(finiteSource(definition, definition.identity));
      if (!project) {
        found.push_back("refused " + definition.identity + ": " +
                        code(project.takeError()));
        continue;
      }
      const auto *decl = declaration(*project, "m::defined");
      const auto *application =
          decl && decl->body && !decl->body->operations.empty()
              ? std::get_if<language::FiniteApplication>(
                    &decl->body->operations.front().action)
              : nullptr;
      bool fold = definition.operation == generated::FiniteOperation::Fold;
      if (!application || decl->finiteDefinition != definition.identity ||
          (application->kind == language::FiniteApplication::Kind::Fold) !=
              fold ||
          application->predicate.has_value() != definition.filtered)
        found.push_back("decoded " + definition.identity);
      // The same declaration under an identity outside the table refuses.
      auto unlisted =
          checkSource(finiteSource(definition, definition.identity + "_x"));
      if (unlisted)
        found.push_back("accepted unlisted " + definition.identity + "_x");
      else
        consumeError(unlisted.takeError());
    }
    outs() << "finite definitions decoded: "
           << generated::finiteDefinitions().size() << '\n';
    agree("finite definitions", found, {});
  });

  cases.run("domain constructors against the source decoder", [&] {
    std::vector<std::string> found;
    for (const auto &constructor : generated::domainConstructors()) {
      auto project =
          checkSource(domainSource(constructor, constructor.identity));
      if (!project) {
        found.push_back("refused " + constructor.identity + ": " +
                        code(project.takeError()));
        continue;
      }
      const auto *decl = declaration(*project, "m::defined");
      if (!decl || !decl->domainDefinition ||
          decl->domainDefinition->constructor !=
              bindingKind(constructor.kind) ||
          decl->domainDefinition->axis != constructor.axis)
        found.push_back("decoded " + constructor.identity);
      auto unlisted =
          checkSource(domainSource(constructor, constructor.identity + "_x"));
      if (unlisted)
        found.push_back("accepted unlisted " + constructor.identity + "_x");
      else
        consumeError(unlisted.takeError());
    }
    outs() << "domain constructors decoded: "
           << generated::domainConstructors().size() << '\n';
    agree("domain constructors", found, {});
  });

  cases.run("limits", [&] {
    static_assert(generated::protocolRoleLimit == 1024,
                  "the role roster ceiling is 1,024 roles");
    const auto *roles = generated::limit("protocol.roles");
    require(roles && roles->value == generated::protocolRoleLimit &&
                roles->unit == generated::LimitUnit::Roles &&
                roles->phase == generated::LimitPhase::Admission,
            "role limit row differs from its constant");
    // The source checker admits a protocol roster of exactly the ceiling.
    auto wide = [](uint64_t count) {
      std::string roles;
      for (uint64_t i = 0; i < count; ++i)
        roles += (i ? ",R" : "R") + std::to_string(i);
      return "protocol Wide roles(" + roles +
             ")(x:bool@R0)->(y:bool@R0){return(y=x);}\n";
    };
    take(checkSource(wide(generated::protocolRoleLimit)));
    auto refused = checkSource(wide(generated::protocolRoleLimit + 1));
    require(!refused, "a roster above the ceiling was admitted");
    auto message = toString(refused.takeError());
    require(StringRef(message).contains("participant roster exceeds"),
            "unexpected roster refusal: " + message);
  });

  return cases.result();
}
