#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/TypeRepresentations.h"
#include "zkc/Contracts/Variant.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;
using namespace zkc::protocol;
namespace {
void check(bool condition, StringRef message) {
  if (!condition) {
    errs() << message << '\n';
    std::exit(1);
  }
}
BoundType accepts(StringRef spelling) {
  auto type = parseBoundType(spelling, false);
  if (!type) {
    errs() << spelling << ": " << toString(type.takeError()) << '\n';
    std::exit(1);
  }
  check(type->spelling() == spelling, "noncanonical successful parse");
  return *type;
}
void refuses(StringRef spelling, StringRef code = {}) {
  auto type = parseBoundType(spelling, false);
  check(!type, "malformed structural type accepted");
  auto error = toString(type.takeError());
  check(code.empty() || code == error, "unexpected structural refusal");
}
void representationPatterns() {
  using Kind = TypeArgument::Kind;
  auto validate = [](ArrayRef<AppliedTypeRepresentation> rows,
                     StringRef expected = {}) {
    auto result = validateAppliedTypeRepresentations(rows);
    check(bool(result) == !expected.empty(), "unexpected pattern validation");
    if (result)
      check(toString(std::move(result)) == expected,
            "unexpected representation refusal");
  };
  auto domain = [](StringRef name) {
    return TypeArgumentPattern{TypeArgument::domainArgument(name.str())};
  };
  auto type = [](BoundType value) {
    return TypeArgumentPattern{TypeArgument::typeArgument(std::move(value))};
  };
  auto range = [](uint64_t minimum, uint64_t maximum) {
    return TypeArgumentPattern{TypeArgument::naturalArgument(0), maximum,
                               minimum};
  };
  validate(appliedTypeRepresentations());
  BoundType blsChild{"field", "bls12-381.fr", "arkworks.fr/0"};
  const TypeArgumentPattern positive[] = {domain("bls12-381.fr"), range(1, 4)};
  const TypeArgumentPattern emptyRange[] = {domain("bls12-381.fr"),
                                            range(1, 0)};
  validate({{"field_array", positive, "test.array/0", true, blsChild}});
  validate({{"field_array", emptyRange, "test.array/0", true, blsChild}},
           "representation-pattern");
  const TypeArgumentPattern later[] = {domain("bls12-381.fr"), range(5, 8)};
  const TypeArgumentPattern overlap[] = {domain("bls12-381.fr"), range(4, 8)};
  validate({{"field_array", positive, "test.array/0", true, blsChild},
            {"field_array", later, "test.array/0", true, blsChild}});
  validate(
      {{"field_array", positive, "test.array/0", true, blsChild},
       {"field_array", overlap, "test.alternative-array/0", true, blsChild}},
      "representation-default");
  BoundType koala{"field", "koala-bear", {}};
  const TypeArgumentPattern arguments[] = {type(koala), range(0, 1048576)};
  AppliedTypeRepresentation row{
      "fixed_vector",
      arguments,
      "test.vector/0",
      true,
      {"field", "koala-bear", "plonky3.koala-bear/0"}};
  validate({row});
  for (BoundType child :
       {BoundType{}, koala, BoundType{"bool", {}, "arkworks.bool/0"},
        BoundType{"field", "koala-bear", "blst/fr"},
        BoundType{"field", "bls12-381.fr", "blst/fr"}}) {
    auto bad = row;
    bad.childType = child;
    validate({bad}, "representation-pattern");
  }
  auto bad = row;
  bad.childType.physicalChildren =
      std::make_shared<const std::vector<BoundType>>();
  validate({bad}, "representation-pattern");
  // Descriptor identities are opaque; child layout is an independent fact.
  validate({{"field_array",
             positive,
             "unrelated.array/0",
             false,
             {"field", "bls12-381.fr", "blst/fr"}}});
  for (StringRef constructor : {"missing", "field", "bool", "variant"}) {
    bad = row;
    bad.constructor = constructor;
    validate({bad}, "representation-constructor");
  }
  bad = row;
  bad.arguments = ArrayRef(arguments).take_front(1);
  validate({bad}, "representation-constructor");
  std::string tooLong(257, 'x');
  for (StringRef identity : {StringRef(), StringRef("bad@identity"),
                             StringRef("1bad"), StringRef(tooLong)}) {
    bad = row;
    bad.representation = identity;
    validate({bad}, "representation-identity");
  }
  auto missingType = TypeArgumentPattern{{Kind::Type, {}, {}, 0}};
  auto rangedType = type(koala);
  rangedType.maximum = 1;
  for (auto argument :
       {domain("koala-bear"), range(0, 4), missingType,
        type({"field", "missing", {}}),
        type({"field", "koala-bear", "plonky3.koala-bear/0"}), rangedType}) {
    TypeArgumentPattern malformed[] = {argument, arguments[1]};
    bad = row;
    bad.arguments = malformed;
    validate({bad}, "representation-pattern");
  }
  auto nonzeroNat = range(0, 4);
  nonzeroNat.argument.natural = 4;
  auto forgedNat = range(0, 4);
  forgedNat.argument.domain = "4";
  for (auto argument : {type({"bool", {}, {}}), nonzeroNat, forgedNat,
                        range(0, 1048577), range(0, UINT64_MAX)}) {
    TypeArgumentPattern malformed[] = {arguments[0], argument};
    bad = row;
    bad.arguments = malformed;
    validate({bad}, "representation-pattern");
  }
  for (StringRef name : {"koala-bear", "bls12-381.g1", "missing", ""}) {
    auto pattern = domain(name);
    validate({{"field", {pattern}, "test.field/0", true, blsChild}},
             "representation-constructor");
  }
  validate({row, row}, "representation-duplicate");
  auto alternative = row;
  alternative.representation = "test.alternative-vector/0";
  validate({row, alternative}, "representation-default");
  alternative.isDefault = false;
  validate({row, alternative});
  bad = row;
  bad.isDefault = false;
  validate({bad, bad}, "representation-duplicate");
  TypeArgumentPattern zero[] = {arguments[0], range(0, 0)};
  alternative.arguments = zero;
  validate({row, alternative});
  alternative.isDefault = true;
  validate({row, alternative}, "representation-default");
  alternative.representation = row.representation;
  validate({row, alternative}, "representation-duplicate");
  TypeArgumentPattern distinct[] = {type({"field", "bls12-381.fr", {}}),
                                    arguments[1]};
  alternative.arguments = distinct;
  alternative.childType = blsChild;
  validate({row, alternative});
  auto nested = accepts("fixed_vector<field:koala-bear,4>");
  distinct[0] = type(nested);
  auto physicalNested = defaultRepresentation(nested);
  check(bool(physicalNested), "missing nested representation");
  alternative.childType = *physicalNested;
  validate({row, alternative});
  for (const auto &entry : appliedTypeRepresentations()) {
    std::vector<std::string> args;
    for (const auto &pattern : entry.arguments)
      args.push_back(pattern.argument.kind == Kind::Nat
                         ? "4"
                         : pattern.argument.spelling());
    auto logical = applyBoundType(entry.constructor, args);
    check(bool(logical), "installed dense logical type refused");
    auto physical =
        physicalType(*logical, entry.representation, {entry.childType});
    check(bool(physical) && physical->physicalChildren &&
              physical->physicalChildren->front() == entry.childType,
          "exact descriptor child not preserved");
    for (StringRef wrong :
         {"field:bls12-381.fr@arkworks.fr/0", "field:bls12-381.fr@blst/fr",
          "field:koala-bear@plonky3.koala-bear/0"}) {
      auto other = parseBoundType(wrong, true);
      check(bool(other), "wrong-child fixture is not independently admitted");
      if (*other == entry.childType)
        continue;
      auto refused = physicalType(*logical, entry.representation, {*other});
      check(!refused &&
                toString(refused.takeError()) == "binding-representation",
            "dense representation accepted another child's layout");
    }
  }
}

} // namespace
int main() {
  representationPatterns();
  auto type = accepts("fixed_vector<field:koala-bear,4>");
  check(type.kind == "fixed_vector" && type.identity.empty() &&
            type.arguments.size() == 2 &&
            type.arguments[0].kind == TypeArgument::Kind::Type &&
            type.arguments[0].type->kind == "field" &&
            type.arguments[0].type->identity == "koala-bear" &&
            type.arguments[1].kind == TypeArgument::Kind::Nat &&
            type.arguments[1].natural == 4,
        "structural arguments were collapsed to a domain identity");
  accepts("fixed_vector<field:koala-bear,0>");
  accepts("fixed_vector<field:koala-bear,1048576>");
  accepts("fixed_vector<fixed_vector<bool,2>,3>");
  accepts("fixed_vector<field:bls12-381.fr,4>");
  check(duplicable(type.spelling()) && discardable(type.spelling()) &&
            !serializable(type.spelling()) && defaultCodec(type).empty(),
        "a public element granted its container a codec");
  auto physical = defaultRepresentation(type);
  check(bool(physical), "installed fixed-vector representation unavailable");
  check(physical->spelling() ==
            "fixed_vector<field:koala-bear,4>@plonky3.fixed-vector/0",
        "physical selection erased structural type arguments");
  auto resource = accepts("fixed_vector<rng:bls12-381.fr,2>");
  check(affine(resource.spelling()) && !duplicable(resource.spelling()) &&
            !discardable(resource.spelling()),
        "a container erased element resource permissions");
  auto wrongBackend =
      defaultRepresentation(accepts("fixed_vector<field:bls12-381.fr,4>"));
  check(!wrongBackend, "unsupported representation selected");
  check(toString(wrongBackend.takeError()) == "binding-representation",
        "unsupported realization was rejected as malformed logical type");
  for (auto spelling :
       {"fixed_vector<field:koala-bear,04>",
        "fixed_vector<field:koala-bear, 4>",
        "fixed_vector<field:koala-bear,+4>",
        "fixed_vector<field:koala-bear,-1>", "fixed_vector<field:koala-bear,>",
        "fixed_vector<field:koala-bear,4,5>", "fixed_vector<koala-bear,4>",
        "fixed_vector<field:missing,4>", "fixed_vector<field<koala-bear>,4>",
        "fixed_vector<field:koala-bear@plonky3.koala-bear/0,4>",
        "fixed_vector<field:koala-bear,4>>", "fixed_vector:koala-bear.4",
        "field<koala-bear>", "bool:"})
    refuses(spelling);
  refuses("fixed_vector<field:koala-bear,1048577>", "binding-type-limit");
  refuses("unknown_type<field:koala-bear,4>", "binding-type");
  std::string nested = "bool";
  for (unsigned i = 0; i < 8; ++i)
    nested = "fixed_vector<" + nested + ",1>";
  accepts(nested);
  refuses("fixed_vector<" + nested + ",1>", "binding-type-limit");
  nested = "index";
  for (unsigned i = 0; i < 8; ++i)
    nested = "sequence<" + nested + ">";
  auto sequence = accepts(nested);
  check(bool(defaultRepresentation(sequence)),
        "nested sequence representation");
  refuses("sequence<" + nested + ">", "binding-type-limit");
  for (unsigned i = 0; i < 40; ++i)
    nested = "sequence<" + nested + ">";
  refuses(nested, "binding-type-limit");
  refuses("sequence<rng:bls12-381.fr>", "sequence-element-permission");
  for (auto spelling :
       {"sequence<prover_key:multilinear.kzg.bls12-381/0>",
        "sequence<opening_state:multilinear.kzg.bls12-381/0>"}) {
    auto local = accepts(spelling);
    check(duplicable(local) && discardable(local) &&
              bool(defaultRepresentation(local)) && !nativeMessageData(local),
          "local immutable sequence acquired wire permission");
  }
  auto unsupported =
      defaultRepresentation(accepts("fixed_vector<sequence<index>,2>"));
  check(!unsupported, "fixed vector acquired a nested-value representation");
  consumeError(unsupported.takeError());
  auto applied = applyBoundType("fixed_vector", {"field:koala-bear", "4"});
  check(bool(applied), "kinded application failed");
  check(*applied == type, "direct application differs from parsed type");
  auto inner = encodeVariant({"Inner", {{"value", {"bool"}}}});
  check(bool(inner), "inner variant refused");
  auto outer =
      encodeVariant({"Outer", {{"value", {"fixed_vector<" + *inner + ",0>"}}}});
  check(bool(outer), "mixed variant and structural fixture refused");
  TypeParseBudget enough{5};
  auto mixed = parseBoundType(*outer, false, 0, &enough);
  check(bool(mixed) && enough.remaining == 0,
        "mixed parser did not share budget");
  TypeParseBudget shortBudget{4};
  auto exhausted = parseBoundType(*outer, false, 0, &shortBudget);
  check(!exhausted, "mixed parser reset its budget");
  consumeError(exhausted.takeError());
}
