#include "support/NativeCases.h"
#include "zkc/Compiler/LanguagePackage.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
CompiledEntry compile(StringRef selected, const EntryOptions &options = {}) {
  auto capture = take(language::capture({{"sample",
                                          R"(module sample;
    protocol Check roles(P,V)(ok:bool@V)->(accepted:bool@V){return(accepted=ok);}
    entry Session=Check;
    entry Proof=Check{prover P;verifier V;public{ok};accept accepted;construction authored;}
    entry Alias=Proof;)",
                                          {}}}));
  auto checked = take(analyze(capture).checkedProject());
  return take(compileEntry(
      take(prepareOriginal(take(closeEntry(checked, selected)))), options));
}
} // namespace
int main() {
  zkc::test::Cases cases;
  for (StringRef job : {"sample::Session", "sample::Proof"})
    cases.run(job + ": package binds exact components and options", [&] {
      for (bool simplify : {false, true})
        for (bool release : {false, true}) {
          auto entry = compile(job, {simplify, release});
          auto package = take(packageEntry(entry));
          auto value = take(json::parse(package.bytes()));
          auto *root = value.getAsObject();
          require(root && root->size() == 5 &&
                      root->getString("format") == "zkc.entry" &&
                      root->getString("original") == entry.original().bytes() &&
                      root->getString("interface") ==
                          entry.original().interfaceJson() &&
                      root->getString("artifact") == entry.bytes(),
                  "package changed or omitted checked bytes");
          auto *options = root->getObject("options");
          require(options && options->size() == 2 &&
                      options->getBoolean("simplify") == simplify &&
                      options->getBoolean("release_storage") == release,
                  "package changed compilation choices");
          require(
              package.identity() ==
                  toHex(SHA256::hash(arrayRefFromStringRef(package.bytes())),
                        true),
              "package identity does not bind exact publication");
          auto same = take(packageEntry(entry, package.bytes().size()));
          require(same.bytes() == package.bytes(),
                  "boundary changed package bytes");
          refuses(packageEntry(entry, package.bytes().size() - 1),
                  "source.package-limit");
          refuses(packageEntry(entry, entryPackageByteLimit + 1),
                  "source.package-limit");
        }
    });
  cases.run(
      "complete aliases preserve executable but change publication Entry", [&] {
        auto original = compile("sample::Proof"),
             alias = compile("sample::Alias");
        require(original.bytes() == alias.bytes(), "alias changed executable");
        require(take(packageEntry(original)).identity() !=
                    take(packageEntry(alias)).identity(),
                "selected Entry identity was erased from publication");
      });
  return cases.result();
}
