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
  validate(appliedTypeRepresentations());
  const TypeArgumentPattern arguments[] = {{Kind::Type, "field:koala-bear"},
                                           {Kind::Nat, {}, 1048576}};
  AppliedTypeRepresentation row{"fixed_vector", arguments, "test.vector/1",
                                true};
  validate({row});
  for (StringRef constructor : {"missing", "resource_unit", "bool"}) {
    auto bad = row;
    bad.constructor = constructor;
    validate({bad}, "representation-constructor");
  }
  auto bad = row;
  bad.arguments = ArrayRef(arguments).take_front(1);
  validate({bad}, "representation-constructor");
  std::string tooLong(257, 'x');
  for (StringRef identity : {StringRef(), StringRef("bad@identity"),
                             StringRef("1bad"), StringRef(tooLong)}) {
    bad = row;
    bad.representation = identity;
    validate({bad}, "representation-identity");
  }
  for (TypeArgumentPattern argument :
       {TypeArgumentPattern{Kind::Domain, "koala-bear"},
        TypeArgumentPattern{Kind::Nat, {}, 4},
        TypeArgumentPattern{Kind::Type, {}},
        TypeArgumentPattern{Kind::Type, "field:missing"},
        TypeArgumentPattern{Kind::Type, "fixed_vector<bool,04>"},
        TypeArgumentPattern{Kind::Type,
                            "field:koala-bear@plonky3.koala-bear/1"},
        TypeArgumentPattern{Kind::Type, "field:koala-bear", 1}}) {
    TypeArgumentPattern malformed[] = {argument, arguments[1]};
    bad = row;
    bad.arguments = malformed;
    validate({bad}, "representation-pattern");
  }
  for (TypeArgumentPattern argument :
       {TypeArgumentPattern{Kind::Type, "bool"},
        TypeArgumentPattern{Kind::Nat, "4", 4},
        TypeArgumentPattern{Kind::Nat, {}, 1048577},
        TypeArgumentPattern{Kind::Nat, {}, UINT64_MAX}}) {
    TypeArgumentPattern malformed[] = {arguments[0], argument};
    bad = row;
    bad.arguments = malformed;
    validate({bad}, "representation-pattern");
  }
  // Atomic nominal carriers belong to the catalog. Applied registrations must
  // not shadow that separate key space, even with a valid Domain identity.
  for (StringRef domain : {"koala-bear", "bls12-381.g1", "missing", ""}) {
    TypeArgumentPattern pattern{Kind::Domain, domain};
    validate({{"field", {pattern}, "test.field/1", true}},
             "representation-constructor");
  }
  validate({row, row}, "representation-duplicate");
  auto alternative = row;
  alternative.representation = "test.vector/2";
  validate({row, alternative}, "representation-default");
  alternative.isDefault = false;
  validate({row, alternative});
  bad = row;
  bad.isDefault = false;
  validate({bad, bad}, "representation-duplicate");
  TypeArgumentPattern zero[] = {arguments[0], {Kind::Nat, {}, 0}};
  alternative.arguments = zero;
  validate({row, alternative});
  alternative.isDefault = true;
  validate({row, alternative}, "representation-default");
  alternative.representation = row.representation;
  validate({row, alternative}, "representation-duplicate");
  TypeArgumentPattern distinct[] = {{Kind::Type, "field:bls12-381.fr"},
                                    arguments[1]};
  alternative.arguments = distinct;
  validate({row, alternative});
  distinct[0].exact = "fixed_vector<field:koala-bear,4>";
  validate({row, alternative});
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
            "fixed_vector<field:koala-bear,4>@plonky3.fixed-vector/1",
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
        "fixed_vector<field:koala-bear@plonky3.koala-bear/1,4>",
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
