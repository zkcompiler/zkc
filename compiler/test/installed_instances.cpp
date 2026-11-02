// Differential evidence: the generated installed-instance and native
// installation tables equal the hand-written owners they describe, in declared
// order. Every intended difference is listed below with its reason; any other
// difference, or a listed one that no longer occurs, fails.
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
std::optional<std::string> member(const generated::Domain &domain,
                                  StringRef name) {
  for (const auto &m : domain.members)
    if (m.member == name)
      return m.identity;
  return std::nullopt;
}
// Rows along BaseField extensions.
std::vector<const generated::Domain *> baseChain(StringRef identity) {
  std::vector<const generated::Domain *> chain{&row(identity)};
  while (chain.back()->field && chain.back()->field->extension &&
         chain.back()->field->extension->over ==
             generated::ExtensionBase::BaseField)
    chain.push_back(&row(*member(*chain.back(), "BaseField")));
  return chain;
}
const generated::Codec *codecFor(StringRef kind, StringRef identity) {
  for (const auto &codec : generated::codecs())
    if (codec.kind == kind && codec.domain == identity)
      return &codec;
  return nullptr;
}
// Field elements as GF(2) coordinates; zero for other characteristics.
unsigned binaryWidth(StringRef identity) {
  const auto &domain = row(identity);
  if (!domain.field || domain.field->characteristic != "2")
    return 0;
  if (!domain.field->extension)
    return 1;
  const auto &extension = *domain.field->extension;
  return extension.over == generated::ExtensionBase::PrimeSubfield
             ? extension.degree
             : extension.degree * binaryWidth(*member(domain, "BaseField"));
}
std::vector<std::string> identities() {
  std::vector<std::string> result{""};
  for (const auto &domain : generated::domains())
    result.push_back(domain.identity);
  for (const auto &codec : generated::codecs())
    result.push_back(codec.identity);
  return result;
}
BoundType treeType(const physical::TypeTree &tree) {
  std::vector<std::string> arguments;
  for (const auto &argument : tree.arguments)
    arguments.push_back(argument.kind ==
                                physical::TypeTreeArgument::Kind::Domain
                            ? argument.identity
                        : argument.kind == physical::TypeTreeArgument::Kind::Nat
                            ? argument.natural
                            : treeType(*argument.type).spelling());
  return take(applyBoundType(tree.constructor, arguments));
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
} // namespace

int main() {
  Cases cases;
  const auto &catalog = installedDomains();

  cases.run("domains in declared order", [&] {
    std::vector<std::string> found;
    auto handWritten = catalog.allDomains();
    auto rows = generated::domains();
    require(handWritten.size() == rows.size(), "domain count differs");
    for (auto [hand, row] : zip(handWritten, rows)) {
      bool same = hand.identity == row.identity && hand.sort == row.sort &&
                  hand.associated.size() == row.members.size() &&
                  hand.capabilities == row.capabilities &&
                  hand.modulus ==
                      (row.field ? row.field->characteristic : std::string());
      for (auto [a, m] : zip(hand.associated, row.members))
        same &= a.member == m.member && a.identity == m.identity;
      if (!same)
        found.push_back(row.identity);
    }
    agree("domains", found, {});
  });

  cases.run("logical types, codecs and representations in declared order", [&] {
    std::vector<std::string> found;
    auto types = catalog.allLogicalTypes();
    auto rows = generated::logicalTypes();
    require(types.size() == rows.size(), "logical type count");
    for (auto [hand, row] : zip(types, rows))
      if (hand.kind != row.kind || hand.domain != row.domain)
        found.push_back("type " + row.kind + " " + row.domain);
    auto codecs = catalog.allCodecs();
    require(codecs.size() == generated::codecs().size(), "codec count");
    for (auto [hand, row] : zip(codecs, generated::codecs()))
      if (hand.identity != row.identity || hand.kind != row.kind ||
          hand.domain != row.domain)
        found.push_back("codec " + row.identity);
    auto representations = catalog.allRepresentations();
    require(representations.size() == physical::representations().size(),
            "representation count");
    for (auto [hand, row] : zip(representations, physical::representations()))
      if (hand.identity != row.identity || hand.kind != row.kind ||
          hand.domain != row.domain || hand.isDefault != row.isDefault ||
          hand.layout != row.layout)
        found.push_back("representation " + row.identity);
    agree("logical types, codecs and representations", found, {});
  });

  cases.run("default providers", [&] {
    std::vector<std::string> found;
    require(physical::providers().size() == catalog.allDomains().size(),
            "provider rows do not cover the domains");
    for (const auto &row : physical::providers())
      if (catalog.defaultProvider(row.domain) != row.defaultProvider)
        found.push_back(row.domain);
    agree("default providers", found, {});
  });

  cases.run("Plonky3 fields from structures, codecs and field forms", [&] {
    std::vector<std::string> found, residue;
    for (const auto &form : physical::fieldForms())
      if (form.arithmetic)
        residue.push_back(form.field);
    std::vector<std::string> handWritten;
    for (const auto &field : plonky3Fields()) {
      handWritten.push_back(field.identity.str());
      const auto &domain = row(field.identity);
      const auto &facts = *domain.field;
      const auto *form = physical::fieldForm(field.identity);
      const auto *codec = codecFor("field", field.identity);
      const unsigned degree = facts.extension ? facts.extension->degree : 1;
      const auto &prime = *baseChain(field.identity).back();
      std::string nonresidue = "0";
      if (facts.extension) {
        const auto &terms = facts.extension->reduction;
        nonresidue = terms.size() == 1 && terms[0].exponent == 0
                         ? terms[0].coefficient
                         : "<not binomial>";
      }
      bool same =
          field.base == prime.identity &&
          field.modulus == facts.characteristic && field.degree == degree &&
          std::to_string(field.nonresidue) == nonresidue && codec &&
          codec->frame && codec->frame->elementBytes &&
          *codec->frame->elementBytes == field.coordinateBytes * degree &&
          form &&
          field.montgomery32 ==
              (form->montgomery && form->montgomery->radixBits == 32);
      if (facts.extension)
        same &= *member(domain, "BaseField") == field.base;
      if (!same)
        found.push_back(field.identity.str());
    }
    if (handWritten != residue)
      found.push_back("residue field set");
    agree("Plonky3 fields", found, {});
  });

  cases.run("random services", [&] {
    std::vector<std::string> found;
    auto rows = generated::randomServices();
    require(std::size(randomServices) == rows.size(), "service count");
    for (auto [hand, row] : zip(randomServices, rows))
      if (hand.contract != row.contract || hand.field != row.field)
        found.push_back(row.contract);
    agree("random services", found, {});
  });

  cases.run("applied and constructor default representations", [&] {
    std::vector<std::string> found;
    std::vector<const physical::AppliedRepresentation *> dense;
    for (const auto &row : physical::appliedRepresentations())
      if (row.constructor == "field_array" || row.constructor == "fixed_vector")
        dense.push_back(&row);
    auto handWritten = appliedTypeRepresentations();
    require(handWritten.size() == dense.size(), "applied representation count");
    for (auto [hand, row] : zip(handWritten, dense)) {
      bool same =
          hand.constructor == row->constructor &&
          hand.representation == row->identity &&
          hand.isDefault == row->isDefault && row->child &&
          hand.childType == BoundType{row->child->kind, row->child->domain,
                                      row->child->representation} &&
          hand.arguments.size() == row->arguments.size();
      for (auto [pattern, generatedPattern] :
           zip(hand.arguments, row->arguments)) {
        using P = physical::ArgumentPattern::Kind;
        switch (generatedPattern.kind) {
        case P::Domain:
          same &= pattern.argument ==
                  TypeArgument::domainArgument(generatedPattern.identity);
          break;
        case P::Type:
          same &= pattern.argument ==
                  TypeArgument::typeArgument(treeType(*generatedPattern.type));
          break;
        case P::NatRange:
          same &= pattern.argument.kind == TypeArgument::Kind::Nat &&
                  pattern.minimum == generatedPattern.minimum &&
                  pattern.maximum == generatedPattern.maximum;
          break;
        case P::Any:
          same = false;
          break;
        }
      }
      if (!same)
        found.push_back(row->identity);
    }
    // Constructor defaults of the remaining applied rows, on sample types.
    auto variant =
        *encodeVariant({"Choice", {{"left", {}}, {"right", {"bool"}}}});
    const std::map<std::string, std::vector<std::string>> samples = {
        {"field_array",
         {"field_array<bls12-381.fr,0>", "field_array<bls12-381.fr,1048576>"}},
        {"fixed_vector",
         {"fixed_vector<field:koala-bear,0>",
          "fixed_vector<field:koala-bear,1048576>"}},
        {"sequence", {"sequence<bool>", "sequence<field:koala-bear>"}},
        {"variant", {variant}},
        {"resource_unit", {"resource_unit:Slot.A"}}};
    for (const auto &row : physical::appliedRepresentations()) {
      auto sample = samples.find(row.constructor);
      if (sample == samples.end()) {
        found.push_back("unsampled " + row.constructor);
        continue;
      }
      for (const auto &spelling : sample->second) {
        if (!row.isDefault)
          continue;
        auto logical = take(parseBoundType(spelling, false));
        if (take(defaultRepresentation(logical)).representation != row.identity)
          found.push_back("default " + spelling);
      }
    }
    agree("applied representations", found, {});
  });

  cases.run("coset conventions for every domain", [&] {
    std::vector<std::string> found;
    for (const auto &identity : identities()) {
      const auto *hand = cosetConvention(identity);
      const generated::Domain *root = nullptr;
      if (const auto *domain = generated::domain(identity);
          domain && domain->field)
        for (const auto *link : baseChain(identity))
          if (link->field->twoAdic) {
            root = link;
            break;
          }
      bool same = bool(hand) == bool(root);
      if (hand && root) {
        const auto &facts = *root->field->twoAdic;
        same = hand->identity == facts.convention &&
               hand->rootField == root->identity &&
               hand->maximalRoot == facts.maximalRoot &&
               hand->maxLogSize == facts.twoAdicity &&
               facts.ordering == "powers" &&
               hand->order == "shift * root(size)^i; i = 0..size-1";
      }
      if (!same)
        found.push_back(identity);
    }
    agree("coset conventions", found, {});
  });

  cases.run("binary bit-pattern widths for every domain", [&] {
    std::vector<std::string> found;
    for (const auto &identity : identities())
      if (fieldBitPatternWidth(identity) !=
          (generated::domain(identity) ? binaryWidth(identity) : 0))
        found.push_back(identity);
    agree("bit-pattern widths", found, {});
  });

  cases.run("message atoms over every constructor and identity", [&] {
    std::vector<std::string> found;
    for (const auto &type : typeDeclarations())
      for (const auto &identity : identities()) {
        const auto *codec = codecFor(type.name, identity);
        bool framed = type.message && codec && codec->frame;
        if (nativeMessageAtom(type.name, identity) != framed)
          found.push_back(type.name + " " + identity);
      }
    agree("message atoms", found, {});
  });

  cases.run("native challenge fields", [&] {
    std::vector<std::string> found;
    for (const auto &identity : identities()) {
      std::string expected;
      if (const auto *domain = generated::domain(identity);
          domain && domain->transcript)
        expected = member(*domain, "ChallengeField").value_or("");
      if (nativeChallengeField(identity) != expected)
        found.push_back(identity);
    }
    agree("native challenge fields", found, {});
  });

  cases.run("implementation provider relation", [&] {
    std::vector<std::string> found;
    for (StringRef provider : {"arkworks", "blst", "dalek", "halo2curves-axiom",
                               "plonky3", "spongefish", "native"})
      for (const auto &identity : identities()) {
        const auto *row = physical::provider(identity);
        bool listed = row && (row->defaultProvider == provider ||
                              is_contained(row->alternatives, provider));
        if (implementationProviderSupports(provider, identity) != listed)
          found.push_back(provider.str() + " " + identity);
      }
    agree("provider relation", found, {});
  });

  cases.run("implementation field sets and field forms", [&] {
    std::vector<std::string> found;
    auto domains = [](StringRef contract) {
      const auto *entry = installedImplementations().find(
          contract, ("plonky3/" + contract).str());
      require(entry, "missing field-set implementation " + contract);
      std::set<std::string> result(entry->domains.begin(),
                                   entry->domains.end());
      return result;
    };
    std::set<std::string> residue, littleEndian, montgomery;
    for (const auto &form : physical::fieldForms()) {
      if (form.arithmetic)
        residue.insert(form.field);
      if (form.byteEncoding && form.byteEncoding->order == "littleEndian")
        littleEndian.insert(form.field);
      if (form.montgomery && form.montgomery->radixBits == 32)
        montgomery.insert(form.field);
    }
    if (domains("ring.point") != residue)
      found.push_back("residue");
    if (domains("encoding.field_le") != littleEndian)
      found.push_back("little-endian bytes");
    if (domains("encoding.field_montgomery_le") != montgomery)
      found.push_back("Montgomery words");
    agree("field sets", found, {});
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

  cases.run("succession facets and the by-name successor rule", [&] {
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
    std::set<std::string> declared;
    for (const auto &row : physical::physicalArguments())
      declared.insert(row.operation);
    std::vector<std::string> refused, admittedUndeclared, found;
    for (const auto &operation : executableOperationContracts()) {
      BindingApplication probe{operation.name,
                               {},
                               "installed.probe/" + operation.name,
                               {"bool@native.bool/0"}};
      auto refusal = refusalCode(resolveBinding(probe, true));
      bool admitted = refusal != "binding-representation";
      if (!admitted)
        refused.push_back(operation.name);
      if (declared.count(operation.name) && !admitted)
        found.push_back("declared but refused " + operation.name);
      if (!declared.count(operation.name) && admitted)
        admittedUndeclared.push_back(operation.name);
    }
    for (const auto &name : refused)
      if (!resourceUnitContract(name) && name != "table.relayout" &&
          !StringRef(name).starts_with("numerical."))
        found.push_back("refused " + name);
    // The C++ rule only excludes resource units, table relayout and the
    // numerical family; the declared rows are the convention's explicit list.
    std::vector<std::string> undeclared;
    for (const auto &operation : executableOperationContracts())
      if (!declared.count(operation.name) &&
          !resourceUnitContract(operation.name) &&
          operation.name != "table.relayout" &&
          !StringRef(operation.name).starts_with("numerical."))
        undeclared.push_back(operation.name);
    if (admittedUndeclared != undeclared)
      found.push_back("admitted undeclared set");
    else
      found.push_back("exclusion rule admits " +
                      std::to_string(undeclared.size()) +
                      " operations without a physicalArguments row");
    agree("physical arguments", found,
          {{"exclusion rule admits " + std::to_string(undeclared.size()) +
                " operations without a physicalArguments row",
            "Bindings.cpp refuses physical arguments only for resource units, "
            "table.relayout and the numerical family; the declared rows list "
            "the operations whose bindings actually carry them"}});
    outs() << "physical-argument rows: " << declared.size()
           << ", C++ rule refuses " << refused.size() << '\n';
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
      // Collection rank against the source axis view.
      unsigned rank = type.collection ? type.collection->rank : 0;
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
      auto expected = !type.collection ? E::None
                      : type.collection->element == CollectionElement::Index
                          ? E::Index
                      : type.collection->element == CollectionElement::Parameter
                          ? E::Parameter
                          : E::None;
      if (element != expected ||
          (type.collection &&
           type.collection->element == CollectionElement::Byte))
        found.push_back("element " + type.name);
    }
    // Setup keys against the native setup-type rule, over every instance.
    for (const auto &instance : generated::logicalTypes()) {
      const auto *declared = typeDeclaration(instance.kind);
      BoundType type{instance.kind, instance.domain, ""};
      if (nativeSetupType(type) != declared->setup.has_value())
        found.push_back("setup " + instance.kind + " " + instance.domain);
    }
    std::vector<Difference> expected = {
        {"collection bytes axis 0",
         "the source checker has no element traversal over bytes; its rank "
         "is an extent only"},
        {"element bytes", "bytes elements are bytes, which source collections "
                          "do not traverse"}};
    for (const auto &instance : generated::logicalTypes())
      if (instance.domain == "multilinear.kzg.bls12-381/0" &&
          !typeDeclaration(instance.kind)->setup)
        expected.push_back(
            {"setup " + instance.kind + " " + instance.domain,
             "nativeSetupType marks every value over the authorized-setup "
             "commitment, while the column marks only the key constructors"});
    agree("type columns", found, expected);
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
  });

  return cases.result();
}
