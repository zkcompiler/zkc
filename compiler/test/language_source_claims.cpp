#include "../lib/Compiler/ComponentContracts.h"
#include "../lib/Compiler/SourceView.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectRegistry.h"
#include "mlir/IR/MLIRContext.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/SourceClaims.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/StructuredData.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Language/Names.h"
#include "zkc/Support/Json.h"
#include "llvm/Support/MemoryBuffer.h"
using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
std::string fixture(StringRef name) {
  auto file = MemoryBuffer::getFile(
      (Twine(ZKC_CLAIM_FIXTURES) + "/" + name + ".zkc").str());
  require(bool(file), "fixture cannot be read");
  return (*file)->getBuffer().str();
}
Expected<CheckedProject> check(StringRef text) {
  auto captured = capture({{"claims", text.str(), {}}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
Expected<CheckedProject> checkSources(std::vector<SourceBuffer> sources) {
  auto captured = capture(std::move(sources));
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
Expected<ClosedEntry> close(StringRef text, StringRef name = "claims::Demo") {
  auto project = check(text);
  if (!project)
    return project.takeError();
  return closeEntry(*project, name);
}
std::string editSource(std::string source, StringRef before, StringRef after) {
  auto at = source.find(before.str());
  require(at != std::string::npos, "replacement text is absent");
  source.replace(at, before.size(), after);
  return source;
}
json::Value report(StringRef text) {
  return take(json::parse(take(inspectSourceClaims(take(close(text))))));
}
json::Value request(json::Value &value, unsigned index = 0) {
  return *(*value.getAsObject()->getArray("claims"))[index].getAsObject()->get(
      "request");
}
StringRef cardinalityDomain(json::Value &value) {
  auto *r =
      value.getAsObject()->getArray("claims")->front().getAsObject()->getObject(
          "request");
  return *r->getObject("quantity")
              ->getObject("expression")
              ->getObject("right")
              ->getArray("arguments")
              ->front()
              .getAsObject()
              ->getObject("value")
              ->getString("name");
}
void refused(Error error) {
  require(bool(error), "expected claim export refusal");
  auto message = toString(std::move(error));
  require(message.find("source.claim.export") != std::string::npos, message);
}
std::string importedContracts(StringRef rootClause, StringRef childClause,
                              bool callChild = true) {
  return ("module claims;"
          "relation Equal(statement x:bool,witness y:bool){return x==y;}"
          "protocol Child roles(P,V)(x:bool@(P,V))->(ok:bool@V) spec{" +
          childClause +
          "}{let ok@V=true;return(ok=ok);}"
          "protocol Run roles(P,V)(x:bool@(P,V))->(ok:bool@V) spec{" +
          rootClause + "}{" +
          (callChild ? "let ok=Child roles(P,V)(x);" : "let ok@V=true;") +
          "return(ok=ok);}"
          "proof Demo=Run{prover P;verifier V;public{x};accept ok;"
          "construction authored;}"
          "spec Claims for Demo{sound:soundness@0("
          "imported_language(languages.guess@0()),model=models.example@0(),"
          "accept=out.ok,stage=executable_bytes,error=0);}")
      .str();
}
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run(
      "cardinality aliases and associated Scalar normalize request identity",
      [] {
        auto original = report(fixture("cardinality"));
        require(cardinalityDomain(original) == "bls12-381.fr",
                "lexical field not resolved");
        for (StringRef alias : {"Alias", "Scalar", "G.Scalar", "G::Scalar"}) {
          auto normalized =
              report(editSource(fixture("cardinality"), "cardinality(Fr)",
                                ("cardinality(" + alias + ")").str()));
          require(request(original) == request(normalized),
                  "alias changed normalized request");
        }
        auto group = report(editSource(fixture("cardinality"),
                                       "cardinality(Fr)", "cardinality(G)"));
        require(cardinalityDomain(group) == "bls12-381.g1",
                "group domain not bound");
        auto entry = take(close(fixture("cardinality")));
        const auto &authored = entry.project()
                                   .declarations()[entry.entry().module.index]
                                   .sourceClaims[0]
                                   .claims[0]
                                   .property;
        const auto &builtin = authored.arguments.back().arguments[1];
        require(builtin.cardinalityDomain &&
                    builtin.cardinalityDomain->domain == "bls12-381.fr" &&
                    builtin.arguments[0].text == "Fr",
                "authored domain spelling or checked provenance lost");
      });
  cases.run(
      "generic Entry bindings never replace an unrelated lexical domain", [] {
        auto source =
            editSource(fixture("cardinality"), "Run<Alias>", "Run<Other>");
        auto entry = take(close(source));
        require(entry.protocol().inputs[0].type.domain == "koala-bear",
                "Entry did not specialize");
        auto value = report(source);
        require(cardinalityDomain(value) == "bls12-381.fr",
                "protocol type binding captured lexical Fr");
        auto selected =
            report(editSource(source, "cardinality(Fr)", "cardinality(Other)"));
        require(cardinalityDomain(selected) == "koala-bear",
                "selected actual field not resolved");
        refuses(check(editSource(source, "cardinality(Fr)", "cardinality(F)")),
                "source.claim.domain");
      });
  cases.run(
      "selected generic Entry and associated Scalar use the actual group", [] {
        auto source =
            editSource(fixture("cardinality"), "bls12-381.g1", "bn254.g1");
        source = editSource(source, "Run<Alias>", "Run<Scalar>");
        source = editSource(source, "cardinality(Fr)", "cardinality(G.Scalar)");
        auto entry = take(close(source));
        require(entry.protocol().parameters.empty() &&
                    entry.protocol().staticArguments[0].domain == "bn254.fr" &&
                    entry.protocol().inputs[0].type.domain == "bn254.fr",
                "selected Entry retained an unresolved generic type");
        auto value = take(json::parse(take(inspectSourceClaims(entry))));
        require(cardinalityDomain(value) == "bn254.fr",
                "Scalar did not follow the actual selected group");
      });
  cases.run("cardinality follows the nearest lexical domain declaration", [] {
    auto source = editSource(
        fixture("cardinality"), "module claims;",
        "module claims;domain Fr=field(\"koala-bear\");module Inner{");
    source += "}";
    auto entry = take(close(source, "claims::Inner::Demo"));
    auto value = take(json::parse(take(inspectSourceClaims(entry))));
    require(cardinalityDomain(value) == "bls12-381.fr",
            "outer same-spelled domain captured the claim");
  });
  for (StringRef path :
       {"Imported.Fr", "Imported::Fr", "ImportedFr", "Imported.G.Scalar"}) {
    cases.run("cardinality resolves imported namespace " + path, [&] {
      auto source = editSource(fixture("cardinality"), "module claims;",
                               "module claims;use library as Imported;use "
                               "library::{ImportedFr};");
      source = editSource(source, "cardinality(Fr)",
                          ("cardinality(" + path + ")").str());
      auto project = take(
          checkSources({{"claims", source, {}},
                        {"library",
                         "module library;pub domain Fr=field(\"koala-bear\");"
                         "pub type ImportedFr=Fr;"
                         "pub domain G=group(\"bls12-381.g1\");",
                         {}}}));
      auto entry = take(closeEntry(project, "claims::Demo"));
      auto value = take(json::parse(take(inspectSourceClaims(entry))));
      require(cardinalityDomain(value) ==
                  (path == "Imported.G.Scalar" ? "bls12-381.fr" : "koala-bear"),
              "imported type resolved in wrong module");
    });
  }
  cases.run(
      "external claim uses its owner scope rather than the imported subject "
      "scope",
      [] {
        auto subject = fixture("cardinality");
        subject = subject.substr(0, subject.find("spec Claims"));
        subject = editSource(subject, "module claims;", "module library;");
        subject = editSource(subject, "field(\"bls12-381.fr\")",
                             "field(\"koala-bear\")");
        subject = editSource(subject, "proof Demo=", "pub proof Demo=");
        auto project = take(checkSources(
            {{"library", subject, {}},
             {"claims",
              "module claims;use library as Subject;domain "
              "Fr=field(\"bls12-381.fr\");"
              "spec Claims for Subject::Demo{sound:soundness@0(target.claim,"
              "model=models.example@0(),accept=out.ok,stage=executable_bytes,"
              "error=1/cardinality(Fr));}",
              {}}}));
        auto entry = take(closeEntry(project, "library::Demo"));
        require(entry.protocol().inputs[0].type.domain == "koala-bear",
                "imported subject changed");
        auto value = take(json::parse(take(inspectSourceClaims(entry))));
        require(cardinalityDomain(value) == "bls12-381.fr",
                "subject module captured claim owner's Fr");
      });
  for (StringRef argument : {"Missing", "bool", "index", "Run", "Demo",
                             "claims", "out.ok", "Fr.Scalar"}) {
    cases.run("cardinality refuses non-domain " + argument, [&] {
      refuses(check(editSource(fixture("cardinality"), "cardinality(Fr)",
                               ("cardinality(" + argument + ")").str())),
              "source.claim.domain");
    });
  }
  for (StringRef malformed :
       {"cardinality()", "cardinality(Fr,Other)", "cardinality(domain=Fr)",
        "cardinality(0)", "cardinality([Fr])", "cardinality(Fr+Other)",
        "cardinality(Fr())"}) {
    cases.run("cardinality refuses malformed builtin " + malformed, [&] {
      refuses(check(editSource(fixture("cardinality"), "cardinality(Fr)",
                               malformed)),
              "source.claim.domain");
    });
  }
  for (StringRef malformed : {"cardinality@01(Fr)", "cardinality@-1(Fr)",
                              "cardinality@4294967296(Fr)", "cardinality@1"}) {
    cases.run("cardinality refuses malformed registry syntax " + malformed,
              [&] {
                refuses(check(editSource(fixture("cardinality"),
                                         "cardinality(Fr)", malformed)),
                        "source.claim.syntax");
              });
  }
  cases.run("cardinality duplicate labels remain a syntax refusal", [] {
    refuses(check(editSource(fixture("cardinality"), "cardinality(Fr)",
                             "cardinality(domain=Fr,domain=Other)")),
            "source.claim.duplicate-field");
  });
  cases.run("cardinality refuses an alias of a non-domain type", [] {
    auto source = editSource(fixture("cardinality"), "type Alias=Fr;",
                             "type Alias=Fr;type Flags=(bool,bool);");
    refuses(check(editSource(source, "cardinality(Fr)", "cardinality(Flags)")),
            "source.claim.domain");
  });
  cases.run(
      "an unrelated symbolic claim owner cannot borrow subject bindings", [] {
        auto subject = fixture("cardinality");
        subject = subject.substr(0, subject.find("spec Claims"));
        subject = editSource(subject, "module claims;", "module library;");
        subject = editSource(subject, "proof Demo=", "pub proof Demo=");
        auto project = take(checkSources({
            {"library", subject, {}},
            {"claims",
             "module claims<F:Field>;use library as Subject;"
             "spec Claims for Subject::Demo{sound:soundness@0(target.claim,"
             "model=models.example@0(),accept=out.ok,stage=executable_bytes,"
             "error=1/cardinality(F));}",
             {}},
        }));
        auto entry = take(closeEntry(project, "library::Demo"));
        refuses(inspectSourceClaims(entry), "source.claim.domain");
      });
  cases.run("cardinality cannot reach a private imported domain", [] {
    auto source = editSource(fixture("cardinality"), "cardinality(Fr)",
                             "cardinality(library.Fr)");
    refuses(checkSources({{"claims", source, {}},
                          {"library",
                           "module library;domain Fr=field(\"koala-bear\");",
                           {}}}),
            "source.claim.domain");
  });
  cases.run(
      "conflicting imported domains cannot select an arbitrary carrier", [] {
        auto source = editSource(fixture("cardinality"), "module claims;",
                                 "module claims;use a::{D};use b::{D};");
        source = editSource(source, "cardinality(Fr)", "cardinality(D)");
        refuses(checkSources({
                    {"claims", source, {}},
                    {"a", "module a;pub domain D=field(\"koala-bear\");", {}},
                    {"b", "module b;pub domain D=field(\"bls12-381.fr\");", {}},
                }),
                "source.duplicate");
      });
  cases.run("a missing local domain never falls back to another module", [] {
    auto source = editSource(fixture("cardinality"), "cardinality(Fr)",
                             "cardinality(Foreign)");
    refuses(checkSources({
                {"claims", source, {}},
                {"library",
                 "module library;pub domain Foreign=field(\"koala-bear\");",
                 {}},
            }),
            "source.claim.domain");
  });
  for (StringRef extension :
       {"cardinality@999(Missing,x=7)", "user.cardinality@19(Missing)",
        "cardinality@0()", "user.cardinality(Missing)"}) {
    cases.run("cardinality preserves extension application " + extension, [&] {
      auto source =
          editSource(fixture("cardinality"), "cardinality(Fr)", extension);
      auto value = report(source);
      auto r = request(value);
      auto *app = r.getAsObject()
                      ->getObject("quantity")
                      ->getObject("expression")
                      ->getObject("right");
      require(app->getString("name") == (extension.starts_with("user.")
                                             ? "user.cardinality"
                                             : "cardinality"),
              "extension name changed");
      require(!app->getArray("arguments")->empty() ||
                  extension == "cardinality@0()",
              "extension arguments lost");
      if (extension == "user.cardinality(Missing)")
        require(app->get("version")->getAsNull().has_value(),
                "extension acquired a version");
      else
        require(app->getInteger("version") ==
                    (extension == "cardinality@999(Missing,x=7)" ? 999
                     : extension == "cardinality@0()"            ? 0
                                                                 : 19),
                "extension version changed");
      if (!app->getArray("arguments")->empty()) {
        const auto &args = *app->getArray("arguments");
        require(args[0].getAsObject()->getObject("value")->getString("name") ==
                    "Missing",
                "opaque reference was resolved");
        if (extension == "cardinality@999(Missing,x=7)")
          require(args.size() == 2 &&
                      args[1].getAsObject()->getString("label") == "x" &&
                      args[1].getAsObject()->getObject("value")->getString(
                          "value") == "7",
                  "opaque labeled argument changed");
      }
      auto entry = take(close(source));
      auto wire = take(inspectSourceClaims(entry));
      require(!checkSourceClaims(entry, wire),
              "opaque extension comparison refused");
    });
  }
  cases.run(
      "explicit nested builtins normalize across the expression envelope", [] {
        auto source =
            editSource(fixture("cardinality"), "models.example@0()",
                       "models.example@0(cost=cardinality(G.Scalar))");
        source =
            editSource(source, "error=1/cardinality(Fr)",
                       "error=1/cardinality(Fr),parameters=cardinality(Alias),"
                       "capabilities=[caps.example@23(cardinality(Scalar))]");
        source +=
            "verify Claims.sound=methods.example@17(cardinality(G::Scalar));";
        auto value = report(source);
        auto r = request(value);
        const auto &model = *r.getAsObject()->getObject("model");
        const auto &parameters =
            *r.getAsObject()->getObject("property")->get("parameters");
        const auto &capability =
            r.getAsObject()->getArray("capabilities")->front();
        const auto &method = *value.getAsObject()
                                  ->getArray("claims")
                                  ->front()
                                  .getAsObject()
                                  ->get("method");
        for (const auto *builtin :
             {model.getArray("arguments")->front().getAsObject()->get("value"),
              &parameters,
              capability.getAsObject()
                  ->getArray("arguments")
                  ->front()
                  .getAsObject()
                  ->get("value"),
              method.getAsObject()
                  ->getArray("arguments")
                  ->front()
                  .getAsObject()
                  ->get("value")})
          require(builtin->getAsObject()
                          ->getArray("arguments")
                          ->front()
                          .getAsObject()
                          ->getObject("value")
                          ->getString("name") == "bls12-381.fr",
                  "nested builtin was not normalized");
        auto entry = take(close(source));
        require(!checkSourceClaims(entry, take(inspectSourceClaims(entry))),
                "nested normalized wire refused");
        refuses(check(editSource(source,
                                 "methods.example@17(cardinality(G::Scalar))",
                                 "methods.example@17(cardinality(Missing))")),
                "source.claim.domain");
      });
  cases.run(
      "normalized cardinality identity participates in exact JSON comparison",
      [] {
        auto entry = take(close(fixture("cardinality")));
        auto wire = take(inspectSourceClaims(entry));
        require(!checkSourceClaims(entry, wire),
                "canonical domain wire refused");
        refused(
            checkSourceClaims(entry, editSource(wire, "bls12-381.fr", "Fr")));
        refused(checkSourceClaims(
            entry, editSource(wire, "bls12-381.fr", "koala-bear")));
        auto original = take(prepareOriginal(entry));
        auto exported = take(exportSourceClaims(original));
        require(!checkSourceClaims(original, exported),
                "admitted canonical wire refused");
        refused(checkSourceClaims(original,
                                  editSource(exported, "bls12-381.fr", "Fr")));
      });
  cases.run("Schnorr forking wire and exact original binding", [] {
    auto entry = take(close(fixture("schnorr")));
    auto original = take(prepareOriginal(entry));
    auto bytes = take(exportSourceClaims(original));
    auto value = take(json::parse(bytes));
    require(value.getAsObject()->getString("format") == "zkc.source-claims/0",
            "format");
    auto *admission = value.getAsObject()->getObject("admission");
    require(!admission->get("original_identity") &&
                admission->getString("original_sha256") ==
                    ("sha256:" + original.identity()).str(),
            "canonical original hash");
    require(admission->getString("protocol_symbol") == entry.protocol().symbol,
            "protocol symbol");
    auto r = request(value);
    require(r.getAsObject()->getObject("quantity")->getString("kind") ==
                "guarantee",
            "guarantee");
    require(!checkSourceClaims(original, bytes), "exact export refused");
    auto renamed = editSource(fixture("schnorr"), "know:", "renamed:");
    renamed =
        editSource(renamed, "SchnorrClaims.know=", "SchnorrClaims.renamed=");
    auto changed = take(prepareOriginal(take(close(renamed))));
    require(changed.bytes() == original.bytes(),
            "claim nickname changed executable original");
    auto modifiedRelation = editSource(
        fixture("schnorr"), "return point==base*scalar;", "return false;");
    auto changedSubject = take(prepareOriginal(take(close(modifiedRelation))));
    require(changedSubject.identity() != original.identity(),
            "changed relation did not detach the original subject reference");
  });
  cases.run("adaptive per-site charges and an external registry extension", [] {
    auto value = report(fixture("sumcheck"));
    require(value.getAsObject()->getArray("claims")->size() == 2,
            "extension omitted");
    auto r = request(value);
    auto *quantity = r.getAsObject()->getObject("quantity");
    require(quantity->getString("kind") == "charged", "charge bundle omitted");
    require((*quantity->getArray("charges"))[0].getAsObject()->getString(
                "site") == "round_challenge",
            "site binding");
    auto extension = request(value, 1);
    require(
        extension.getAsObject()->getObject("property")->getInteger("version") ==
            7,
        "external version lost");
  });
  cases.run("inline and external normalization and label independence", [] {
    auto external = fixture("schnorr");
    auto inlined = editSource(external, "spec SchnorrClaims for Demo", "spec");
    inlined =
        editSource(inlined, "verify SchnorrClaims.know", "verify Demo.know");
    auto a = report(external), b = report(inlined);
    require(request(a) == request(b), "inline request differs");
    auto renamed = editSource(external, "know:", "other:");
    renamed =
        editSource(renamed, "SchnorrClaims.know=", "SchnorrClaims.other=");
    auto c = report(renamed);
    require(request(a) == request(c), "label altered request");
  });
  cases.run("targetless Guess imports a language and the proof acceptance", [] {
    auto source = fixture("guess");
    auto entry = take(close(source));
    require(entry.protocol().specifications.empty() &&
                !entry.entry().proof()->target,
            "Guess gained a fabricated target");
    auto original = take(prepareOriginal(entry));
    auto wire = take(inspectSourceClaims(entry));
    auto value = take(json::parse(wire));
    auto r = request(value);
    auto *target = r.getAsObject()->getObject("target");
    require(target->size() == 2 &&
                target->getString("protocol") == entry.protocol().symbol &&
                !target->get("clause") && !target->get("name"),
            "imported target shape differs");
    auto *language = target->getObject("language");
    require(language->getString("kind") == "application" &&
                language->getString("name") == "languages.guess" &&
                language->getInteger("version") == 0 &&
                language->getArray("arguments")->empty(),
            "language registry application changed");
    auto *accept = r.getAsObject()->getObject("accept");
    require(accept->getBoolean("output") == true &&
                accept->getInteger("port") ==
                    entry.entry().proof()->acceptance.port &&
                accept->getInteger("role") == entry.entry().proof()->verifier &&
                accept->getArray("path")->empty(),
            "proof Entry acceptance changed");
    require(!checkSourceClaims(entry, wire), "closed imported export refused");
    require(!checkSourceClaims(original, take(exportSourceClaims(original))),
            "admitted imported export refused");
    auto without = source.substr(0, source.find("spec GuessClaims"));
    require(take(prepareOriginal(take(close(without)))).bytes() ==
                original.bytes(),
            "imported claim changed executable original");
    auto inlined = editSource(source, "spec GuessClaims for Demo", "spec");
    auto other = report(inlined);
    require(request(value) == request(other),
            "inline imported request differs");
  });
  cases.run("retained target wire remains unchanged", [] {
    auto entry = take(close(fixture("schnorr")));
    auto value = report(fixture("schnorr"));
    auto r = request(value);
    auto expected =
        json::Value(json::Object{{"protocol", entry.protocol().symbol},
                                 {"clause", 0},
                                 {"name", "knowledge"}});
    require(*r.getAsObject()->get("target") == expected,
            "retained wire shape changed");
  });
  cases.run("unknown imported language preserves extension arguments", [] {
    auto value = report(
        editSource(fixture("guess"), "languages.guess@0()",
                   "user::languages.future@4294967295(offset,budget=2^64,"
                   "options=[nested@19(x=7),-1])"));
    auto r = request(value);
    auto *language =
        r.getAsObject()->getObject("target")->getObject("language");
    require(language->getString("name") == "user::languages.future" &&
                language->getInteger("version") == 4294967295LL,
            "unknown language identifier or version changed");
    auto *arguments = language->getArray("arguments");
    require(arguments->size() == 3 &&
                (*arguments)[0].getAsObject()->get("label")->getAsNull() &&
                (*arguments)[1].getAsObject()->getString("label") == "budget" &&
                (*arguments)[2]
                        .getAsObject()
                        ->getObject("value")
                        ->getArray("items")
                        ->size() == 2,
            "language argument tree changed");
    require(value.getAsObject()->getString("registry_resolution") ==
                "deferred-to-lean",
            "native frontend resolved language semantics");
  });
  for (StringRef clause : {"input initial=Equal(in.x@V,in.x@P);",
                           "output final=Equal(in.x@V,out.ok);",
                           "target claim=Equal(in.x@V,in.x@P) accept out.ok;",
                           "continuation reduce=Equal(in.x@V,in.x@P) residual "
                           "Equal(in.x@V,out.ok) accept out.ok;"}) {
    cases.run("imported language refuses root " + clause, [&] {
      refuses(check(importedContracts(clause, "")), "source.claim.target");
    });
    cases.run("imported language refuses unlabelled child " + clause, [&] {
      refuses(close(importedContracts("", clause)), "source.claim.target");
    });
    cases.run(
        "imported language checks child clauses in zero-trip loops " + clause,
        [&] {
          auto source = editSource(
              importedContracts("", clause), "let ok=Child roles(P,V)(x);",
              "for _ in 0..0 roles(P,V) max 1 {let unused=Child roles(P,V)(x);}"
              "let ok@V=true;");
          refuses(close(source), "source.claim.target");
        });
    cases.run("unused contracts are outside the emitted unit " + clause, [&] {
      take(prepareOriginal(take(close(importedContracts("", clause, false)))));
    });
  }
  cases.run(
      "empty specification blocks compare and allow imported language", [] {
        auto source = importedContracts("", "");
        auto entry = take(close(source));
        require(entry.protocol().specificationBlock.has_value(),
                "empty spec lost");
        auto original = take(prepareOriginal(entry));
        auto interface =
            take(readInterface(original.bytes(), original.interfaceJson()));
        require(!compareInterface(entry, interface),
                "empty spec comparison refused");
        auto &clauses = interface.protocols[interface.selected].clauses;
        clauses.emplace_back();
        auto error = compareInterface(entry, interface);
        require(bool(error), "invented clause accepted for empty spec");
        require(toString(std::move(error)).find("source.correspondence") !=
                    std::string::npos,
                "wrong empty spec diagnostic");
      });
  for (const auto &edit : std::vector<std::pair<std::string, std::string>>{
           {"imported_language()", "source.claim.target"},
           {"imported_language(languages.guess@0(),languages.guess@0())",
            "source.claim.target"},
           {"imported_language(language=languages.guess@0())",
            "source.claim.target"},
           {"imported_language@0(languages.guess@0())", "source.claim.target"},
           {"imported_language(languages.guess())", "source.claim.identifier"},
           {"imported_language(languages.guess)", "source.claim.identifier"},
           {"imported_language(0)", "source.claim.identifier"},
           {"imported_language([languages.guess@0()])",
            "source.claim.identifier"},
           {"imported_language(languages.guess@00())", "source.claim.syntax"},
           {"imported_language(languages.guess@4294967296())",
            "source.claim.syntax"},
           {"imported_language(languages.guess@0)", "source.claim.syntax"},
           {"imported_language(languages.guess@0(x=1,x=2))",
            "source.claim.duplicate-field"},
           {"languages.guess@0()", "source.claim.target"},
           {"Guess(offset,guess)", "source.claim.target"}}) {
    cases.run("imported target refuses " + edit.first, [&] {
      refuses(check(editSource(fixture("guess"),
                               "imported_language(languages.guess@0())",
                               edit.first)),
              edit.second);
    });
  }
  cases.run("imported acceptance is the checked proof Boolean decision", [] {
    auto source =
        editSource(fixture("guess"), "-> (accepted: bool @V)",
                   "-> (accepted: bool @V, other: bool @V, scalar: F @V)");
    source = editSource(
        source, "return (accepted = accepted);",
        "return (accepted = accepted, other = true, scalar = challenge);");
    for (StringRef result : {"other", "scalar", "missing"})
      refuses(check(editSource(source, "accept=out.accepted",
                               ("accept=out." + result).str())),
              "source.claim.accept");
  });
  cases.run("imported language requires a proof Entry", [] {
    auto source = editSource(importedContracts("", ""),
                             "proof Demo=Run{prover P;verifier "
                             "V;public{x};accept ok;construction authored;}",
                             "");
    source = editSource(source, "for Demo", "for Run");
    source = editSource(source, "stage=executable_bytes", "stage=interactive");
    refuses(check(source), "source.claim.target");
  });
  cases.run(
      "imported comparison refuses mixed shapes and changed registry data", [] {
        auto original = take(prepareOriginal(take(close(fixture("guess")))));
        auto wire = take(exportSourceClaims(original));
        for (const auto &changed :
             {editSource(wire, "\"language\":", "\"clause\":0,\"language\":"),
              editSource(wire,
                         "\"language\":", "\"name\":\"fake\",\"language\":"),
              editSource(wire,
                         "\"language\":", "\"language\":null,\"language\":"),
              editSource(wire, "\"protocol\":",
                         "\"protocol\":\"wrong\",\"protocol\":"),
              editSource(wire, "languages.guess", "languages.other"),
              editSource(wire, "\"version\":0", "\"version\":999")})
          refused(checkSourceClaims(original, changed));
        for (StringRef field : {"protocol", "version", "arguments", "accept"}) {
          auto changed = take(json::parse(wire));
          auto *r = changed.getAsObject()
                        ->getArray("claims")
                        ->front()
                        .getAsObject()
                        ->getObject("request");
          auto *target = r->getObject("target");
          if (field == "protocol")
            (*target)["protocol"] = "wrong";
          else if (field == "accept")
            (*r->getObject("accept"))["port"] = 999;
          else if (field == "version")
            (*target->getObject("language"))["version"] = 999;
          else
            target->getObject("language")
                ->getArray("arguments")
                ->push_back(
                    json::Object{{"label", nullptr},
                                 {"value", json::Object{{"kind", "natural"},
                                                        {"value", "1"}}}});
          refused(checkSourceClaims(original, zkc::printJson(changed)));
        }
      });
  for (const auto &edit :
       std::vector<std::tuple<std::string, std::string, std::string>>{
           {"target.knowledge", "target.missing", "source.claim.target"},
           {"target.knowledge", "DLog(base,point,scalar)",
            "source.claim.target"},
           {"accept=out.accepted", "accept=out.missing", "source.claim.accept"},
           {"for Demo", "for Missing", "source.claim.subject"},
           {"for Demo", "for Schnorr", "source.generic"},
           {"model=models.fiat_shamir@0", "model=models.fiat_shamir",
            "source.claim.identifier"},
           {"knowledge@0(", "knowledge(", "source.claim.identifier"},
           {"accept=out.accepted", "accept=out.accepted,accept=out.accepted",
            "source.claim.duplicate-field"},
           {"queries=2^64", "queries=1,queries=2",
            "source.claim.duplicate-field"},
           {"accept=out.accepted", "typo=0,accept=out.accepted",
            "source.claim.field"},
           {"stage=executable_bytes", "stage=wrong", "source.claim.stage"},
           {"cost=prover_runs(2)", "cost=\"Lean.evil\"", "source.claim.syntax"},
           {"fs.forking@0()", "fs.forking()", "source.claim.identifier"},
           {"SchnorrClaims.know=", "SchnorrClaims.absent=",
            "source.claim.verify"},
           {"knowledge@0", "knowledge@00", "source.claim.syntax"}}) {
    cases.run("refuse " + std::get<2>(edit) + " " + std::get<1>(edit), [&] {
      refuses(check(editSource(fixture("schnorr"), std::get<0>(edit),
                               std::get<1>(edit))),
              std::get<2>(edit));
    });
  }
  cases.run("empty charges retain the exact charged request", [] {
    auto value = report(
        editSource(fixture("sumcheck"),
                   "charge=[per_site(sites.round_challenge,2/cardinality(Fr))]",
                   "charge=[]"));
    auto selected = request(value);
    auto *quantity = selected.getAsObject()->getObject("quantity");
    require(quantity->getString("kind") == "charged" &&
                quantity->getArray("charges")->empty(),
            "empty charge schedule changed request kind or entries");
  });
  cases.run("unexported and duplicated charges", [] {
    refuses(check(editSource(fixture("sumcheck"), "sites.round_challenge",
                             "sites.missing")),
            "source.claim.site");
    refuses(check(editSource(
                fixture("sumcheck"),
                "charge=[per_site(sites.round_challenge,2/cardinality(Fr))]",
                "charge=[per_site(sites.round_challenge,0),per_site(sites."
                "round_challenge,1)]")),
            "source.claim.field");
  });
  cases.run("duplicate labels and plans", [] {
    auto text = fixture("schnorr");
    auto begin = text.find("  know:");
    auto end = text.find("\n}", begin);
    text.insert(end, "\n" + text.substr(begin, end - begin));
    refuses(check(text), "source.claim.duplicate-label");
    refuses(
        check(fixture("schnorr") + "verify SchnorrClaims.know=fs.forking@0();"),
        "source.claim.verify");
  });
  cases.run(
      "unknown registry version is retained without native semantic resolution",
      [] {
        auto value =
            report(editSource(fixture("schnorr"), "models.fiat_shamir@0",
                              "models.fiat_shamir@999"));
        auto r = request(value);
        require(r.getAsObject()->getObject("model")->getInteger("version") ==
                    999,
                "unknown model silently normalized");
      });
  cases.run("strict JSON exact shape and Entry", [] {
    auto entry = take(close(fixture("schnorr")));
    auto bytes = take(inspectSourceClaims(entry));
    require(!checkSourceClaims(entry, bytes), "valid wire export");
    for (auto edit :
         {editSource(bytes, "\"format\":", "\"unknown\":0,\"format\":"),
          editSource(bytes, "\"format\":", "\"format\":0,\"format\":"),
          editSource(bytes, "claims::Demo", "claims::Other"),
          editSource(bytes, "\"version\":0", "\"version\":0.0")})
      refused(checkSourceClaims(entry, edit));
  });
  cases.run("claim envelope and registry application shapes", [] {
    for (const auto &edit :
         std::vector<std::tuple<std::string, std::string, std::string>>{
             {"guarantee=guarantees.forking@0",
              "error=0,guarantee=guarantees.forking@0", "source.claim.field"},
             {"guarantee=guarantees.forking@0", "guarantee=guarantees.forking",
              "source.claim.identifier"},
             {"model=models.fiat_shamir@0",
              "model=models.fiat_shamir@4294967296", "source.claim.syntax"},
             {"queries=2^64", "queries=01", "source.claim.syntax"},
             {"queries=2^64", "queries=2^", "source.claim.syntax"},
             {"fs.forking@0()", "fs.forking@0(at=sites.missing)",
              "source.claim.site"}})
      refuses(check(editSource(fixture("schnorr"), std::get<0>(edit),
                               std::get<1>(edit))),
              std::get<2>(edit));
    refuses(
        check(editSource(fixture("sumcheck"),
                         "capabilities=[capabilities.charged_reduction@0()]",
                         "capabilities=[capabilities.charged_reduction()]")),
        "source.claim.identifier");
    refuses(
        check(editSource(fixture("sumcheck"),
                         "capabilities=[capabilities.charged_reduction@0()]",
                         "capabilities=0")),
        "source.claim.field");
  });
  cases.run("wrong retained Entry target and acceptance", [] {
    auto source = fixture("schnorr");
    source = editSource(
        source,
        "target knowledge=DLog<H>(in.base@V,in.point@V,in.scalar) accept "
        "out.accepted;",
        "target knowledge=DLog<H>(in.base@V,in.point@V,in.scalar) accept "
        "out.accepted; target other=DLog<H>(in.base@V,in.point@V,in.scalar) "
        "accept out.accepted;");
    refuses(check(editSource(source, "knowledge@0(target.knowledge",
                             "knowledge@0(target.other")),
            "source.claim.target");
    auto nonbool = editSource(fixture("sumcheck"), "->(accepted:bool@V)",
                              "->(accepted:bool@V,scalar:Fr@V)");
    nonbool = editSource(nonbool, "return(accepted=accepted);",
                         "return(accepted=accepted,scalar=challenge);");
    refuses(
        check(editSource(nonbool, "accept=out.accepted", "accept=out.scalar")),
        "source.claim.accept");
    auto wrong = editSource(fixture("schnorr"), "for Demo", "for Other");
    wrong += "protocol OtherRun "
             "roles(P,V)()->(accepted:bool@V){return(accepted=true);} proof "
             "Other=OtherRun{prover P;verifier V;public{};accept "
             "accepted;construction authored;}";
    refuses(check(wrong), "source.claim.target");
  });
  cases.run("only the selected Entry owns exported claims", [] {
    auto source = fixture("schnorr") + "proof Alias=Demo;";
    auto alias = take(close(source, "claims::Alias"));
    auto exported = take(json::parse(take(inspectSourceClaims(alias))));
    require(exported.getAsObject()->getArray("claims")->empty(),
            "Entry alias inherited another subject's claims");
    auto without = source.substr(0, source.find("spec SchnorrClaims for Demo"));
    auto a = take(prepareOriginal(take(close(source))));
    auto b = take(prepareOriginal(take(close(without))));
    require(a.bytes() == b.bytes(), "claims changed executable original bytes");
    auto changed = report(editSource(fixture("schnorr"), "fs.forking@0()",
                                     "user.external_method@19()"));
    auto before = report(fixture("schnorr"));
    require(request(before) == request(changed),
            "method changed request meaning");
  });
  cases.run(
      "nested JSON shape, duplicate keys, nonfinite tokens and admission "
      "checks",
      [] {
        auto original = take(prepareOriginal(take(close(fixture("schnorr")))));
        auto bytes = take(exportSourceClaims(original));
        refused(checkSourceClaims(original,
                                  editSource(bytes, "\"property\":{",
                                             "\"property\":{\"unknown\":0,")));
        refused(checkSourceClaims(
            original,
            editSource(bytes, "\"version\":0", "\"version\":0,\"version\":0")));
        refused(checkSourceClaims(
            original, editSource(bytes, "\"version\":0", "\"version\":NaN")));
        refused(checkSourceClaims(
            original, editSource(bytes, "\"protocol_symbol\":",
                                 "\"invented\":0,\"protocol_symbol\":")));
      });
  cases.run("nested site paths resolve exact labelled call occurrences", [] {
    auto source = fixture("nested");
    auto value = report(source);
    auto *claim = (*value.getAsObject()->getArray("claims"))[0].getAsObject();
    auto *binding = (*claim->getArray("site_bindings"))[0].getAsObject();
    auto *path = binding->getArray("native_path");
    require(path->size() == 2 &&
                (*path)[0].getAsString() == nativeSiteName("inner", 0) &&
                (*path)[1].getAsString() == nativeSiteName("challenge", 0),
            "native path mismatch");
    take(prepareOriginal(take(close(source))));
    refuses(
        check(editSource(source, "sites.inner.challenge", "sites.challenge")),
        "source.claim.site");
    refuses(check(editSource(source, "#[site(inner)] ", "")),
            "source.claim.site");
  });
  cases.run(
      "interactive protocol claims are retained independently of proof plans",
      [] {
        auto source = fixture("nested");
        source += "spec InteractiveClaims for "
                  "Wrapper {complete: "
                  "completeness@0(target.valid,model=models.honest_interactive@"
                  "0(),accept=out.ok,stage=interactive,error=0);}";
        auto entry = take(closeSubject(take(check(source)), "claims::Wrapper"));
        auto value = take(json::parse(take(inspectSourceClaims(entry))));
        require(value.getAsObject()->getArray("claims")->size() == 1,
                "interactive claim ignored");
        auto r = request(value);
        require(r.getAsObject()->getObject("subject")->getString("stage") ==
                    "interactive",
                "interactive stage changed");
        refuses(check(editSource(source, "stage=interactive",
                                 "stage=executable_bytes")),
                "source.claim.stage");
      });
  cases.run(
      "closed protocol claims match normalized arguments and not proof aliases",
      [] {
        auto source =
            editSource(fixture("cardinality"), "for Demo", "for Run<Alias>");
        source =
            editSource(source, "stage=executable_bytes", "stage=interactive");
        auto project = take(check(source));
        auto first = take(closeSubject(project, "claims::Run<claims::Fr>"));
        auto same = take(closeSubject(project, "Run<Scalar>"));
        auto other = take(closeSubject(project, "Run<Other>"));
        auto a = take(json::parse(take(inspectSourceClaims(first))));
        auto b = take(json::parse(take(inspectSourceClaims(same))));
        auto c = take(json::parse(take(inspectSourceClaims(other))));
        auto inventory =
            take(json::parse(take(inspectSourceClaimInventory(project))));
        require(inventory.getAsArray()->size() == 1,
                "unselected claim disappeared from the project inventory");
        auto *item = inventory.getAsArray()->front().getAsObject();
        require(item->getObject("subject")->getString("declaration") ==
                        "claims::Run" &&
                    item->getObject("subject")->getString("kind") ==
                        "protocol" &&
                    *item->getObject("subject")->getArray("arguments") ==
                        json::Array{json::Array{"field", "bls12-381.fr"}},
                "inventory lost the normalized closed subject");
        require(*item->getObject("node") == *a.getAsObject()
                                                 ->getArray("claims")
                                                 ->front()
                                                 .getAsObject()
                                                 ->getObject("attachment")
                                                 ->getObject("node"),
                "inventory does not identify the exported claim");
        Limits small;
        small.interfaceBytes = 1;
        refuses(inspectSourceClaimInventory(project, small), "source.limit");
        require(a.getAsObject()->getArray("claims")->size() == 1 &&
                    request(a) == request(b),
                "equivalent closed arguments changed the claim");
        require(c.getAsObject()->getArray("claims")->empty(),
                "another specialization inherited the claim");
        auto proof = take(closeSubject(project, "Demo"));
        auto exported = take(json::parse(take(inspectSourceClaims(proof))));
        require(exported.getAsObject()->getArray("claims")->empty(),
                "proof inherited a protocol subject claim");
        auto host = take(closeEntry(project, "Run<Fr>"));
        require(!host.protocolOrNull(),
                "ordinary Entry selection changed meaning");
        refuses(inspectSourceClaims(host), "source.claim.subject");
        refuses(closeSubject(project, "Run<index>"), "source.generic");
        refuses(closeSubject(project, "Run<_>"), "source.inference");
        refuses(closeSubject(project, "Run<Fr>trailing"), "source.syntax");
        refuses(closeSubject(project, ""), "source.subject");
        auto original = take(prepareOriginal(first));
        cantFail(
            checkSourceClaims(original, take(exportSourceClaims(original))));
      });
  cases.run("Host inventory cardinality never grants a protocol subject", [] {
    auto source = fixture("cardinality");
    source += R"(
      entry fn Twice(inputs: Run<Fr>::Inputs) {
        let first = Run<Fr>::run(inputs);
        let second = Run<Fr>::run(inputs);
        return (first,second);
      }
      entry fn Conditional(inputs: Run<Fr>::Inputs, enabled:bool) {
        return if enabled {let result=Run<Fr>::run(inputs);true} else {false};
      }
      entry fn Changed(inputs: Run<Fr>::Inputs) {
        let result=Run<Fr>::run(inputs); return false;
      }
      entry fn Never(inputs: Run<Fr>::Inputs) {
        for _ in 0..0 { let result=Run<Fr>::run(inputs); }
        return false;
      }
      entry fn Guarded(inputs: Run<Fr>::Inputs, enabled:bool) {
        require enabled; return Run<Fr>::run(inputs);
      }
    )";
    auto project = take(check(source));
    for (StringRef name :
         {"Twice", "Conditional", "Changed", "Never", "Guarded"}) {
      auto host = take(closeEntry(project, name));
      require(host.invocations().size() == 1,
              "control must have one static deployment despite different "
              "execution");
      refuses(closeSubject(project, name), "source.subject");
      refuses(inspectSourceClaims(host), "source.claim.subject");
      refuses(check(source + "spec Host for " + name.str() +
                    "{x:completeness@0(target.claim,model=models.example@0(),"
                    "accept=out.ok,stage=interactive,error=0);}"),
              "source.claim.subject");
    }
  });
  cases.run(
      "component occurrences, zero-case routes and checked proposals", [] {
        auto project = take(check(fixture("components")));
        auto original =
            take(prepareOriginal(take(closeSubject(project, "claims::Run"))));
        auto bytes = take(exportSourceClaims(original));
        cantFail(checkSourceClaims(original, bytes));
        auto value = take(json::parse(bytes));
        auto &root = *value.getAsObject();
        auto &calls = *root.getArray("proposals");
        require(calls.size() == 3,
                "two ordinary calls and one loop call required");
        for (auto &call : calls) {
          const auto &slots = *(*call.getAsArray())[5].getAsArray();
          require(slots.size() == 1 &&
                      (*slots[0].getAsArray())[0] == json::Value("parameter"),
                  "logical slot must use the retained input purpose");
        }
        require((*calls[0].getAsArray())[1] != (*calls[1].getAsArray())[1],
                "repeated callee occurrences collapsed");
        unsigned init = 0, yielded = 0, zero = 0, exits = 0;
        for (auto &row : *root.getArray("seams")) {
          auto &fields = *row.getAsArray();
          auto &endpoint = *fields[1].getAsArray();
          init += endpoint[0] == json::Value("repeat_init");
          yielded += endpoint[0] == json::Value("yield");
          if (endpoint[0] == json::Value("repeat_result")) {
            ++zero;
            require(fields[3].getAsArray()->size() == 2,
                    "loop result must retain initial and yielded alternatives");
          }
          exits += fields[2] == json::Value("terminal");
        }
        require(init == 1 && yielded == 1 && zero == 1 && exits == 1,
                "missing invariant or actual terminal exit");
        auto encode = [](const json::Value &v) {
          std::string result;
          raw_string_ostream out(result);
          out << v;
          return result;
        };
        auto choose = [&](unsigned call, json::Value source) {
          auto changed = take(json::parse(bytes));
          auto &proposal =
              *(*changed.getAsObject()->getArray("proposals"))[call]
                   .getAsArray();
          (*(*proposal[5].getAsArray())[0].getAsArray())[2] = std::move(source);
          return changed;
        };
        StringRef role = "role00000000";
        for (json::Value source :
             {json::Value(json::Array{"operand", 0, role}),
              json::Value(
                  json::Array{"parameter", json::Array{"input", 0, role}})})
          cantFail(checkSourceClaims(original,
                                     encode(choose(0, std::move(source)))));
        auto earlier = (*calls[0].getAsArray())[1];
        cantFail(checkSourceClaims(
            original,
            encode(choose(1, json::Array{"result", earlier, 1, role}))));
        auto interface = take(json::parse(original.interfaceJson()));
        auto formula = *interface.getAsObject()
                            ->getArray("relations")
                            ->front()
                            .getAsObject()
                            ->getObject("definition")
                            ->getString("function");
        cantFail(checkSourceClaims(
            original,
            encode(choose(
                0,
                json::Array{"math", formula, 0,
                            json::Array{json::Array{"operand", 0, role},
                                        json::Array{"operand", 0, role}}}))));
        for (json::Value source :
             {json::Value(json::Array{"operand", 0, "absent"}),
              json::Value(json::Array{"operand", 99, role}),
              json::Value(
                  json::Array{"witness", json::Array{"input", 0, role}}),
              json::Value(
                  json::Array{"parameter", json::Array{"output", 0, role}}),
              json::Value(
                  json::Array{"result", (*calls[1].getAsArray())[1], 0, role}),
              json::Value(json::Array{"result", earlier, 99, role}),
              json::Value(json::Array{"math", "missing", 0, json::Array{}}),
              json::Value(
                  json::Array{"math", formula, 0,
                              json::Array{json::Array{"open"},
                                          json::Array{"operand", 0, role}}}),
              json::Value(json::Array{"open", "extra"})}) {
          auto error =
              checkSourceClaims(original, encode(choose(0, std::move(source))));
          require(bool(error), "bad logical source accepted");
          require(namesIdentifier(toString(std::move(error)),
                                  "component-instantiation"),
                  "wrong logical refusal");
        }
        for (unsigned variant = 0; variant != 5; ++variant) {
          auto changed = take(json::parse(bytes));
          auto &object = *changed.getAsObject();
          if (variant == 0)
            object.getArray("proposals")->push_back(calls[0]);
          if (variant == 1)
            (*(*object.getArray("proposals"))[0].getAsArray())[2] =
                "wrong-callee";
          if (variant == 2)
            (*(*object.getArray("proposals"))[0].getAsArray())[4] =
                json::Array{"wrong-role"};
          if (variant == 3)
            object.getArray("seams")->pop_back();
          if (variant == 4)
            (*object.getArray("seams"))[0].getAsArray()->push_back("unknown");
          auto error = checkSourceClaims(original, encode(changed));
          require(bool(error), "wrong call or seam accepted");
          consumeError(std::move(error));
        }
        auto unknown = take(json::parse(bytes));
        (*unknown.getAsObject())["unknown"] = true;
        auto error = checkSourceClaims(original, encode(unknown));
        require(bool(error), "unknown export field accepted");
        consumeError(std::move(error));
        auto duplicate = bytes;
        duplicate.insert(1, "\"seams\":[],");
        error = checkSourceClaims(original, duplicate);
        require(bool(error), "duplicate export field accepted");
        consumeError(std::move(error));
      });
  cases.run("pending vector declarations retain their source representation",
            [] {
              auto original = take(prepareOriginal(take(closeSubject(
                  take(check(fixture("components-vectors"))), "claims::Run"))));
              cantFail(checkSourceClaims(original,
                                         take(exportSourceClaims(original))));
            });
  cases.run("selected library root retains linear residual ownership", [] {
    auto source = fixture("components-local-fields") +
                  "protocol Library roles(V)(reference:bool@V,value:bool@V)"
                  "->(claim:Pending@V,ok:bool@V) spec{output result=Truth("
                  "in.reference,out.claim.first,out.claim.second);}{"
                  "let initial@V=pending(value);"
                  "let(next,ok)=Reduce roles(V)(reference,initial);"
                  "return(claim=next,ok=ok);}";
    auto original = take(prepareOriginal(
        take(closeSubject(take(check(source)), "claims::Library"))));
    auto bytes = take(exportSourceClaims(original));
    cantFail(checkSourceClaims(original, bytes));
    auto claims = take(json::parse(bytes));
    require(claims.getAsObject()->getArray("claims")->empty(),
            "library association invented a property claim");
    auto symbol = *claims.getAsObject()
                       ->getObject("admission")
                       ->getString("protocol_symbol");
    auto baseline = take(zkc::language::detail::OriginalAccess::read(original));
    auto derived = take(deriveComponentContracts(baseline));
    require(!derived.getArray("seams")->empty(), "missing library residual");
    cantFail(checkComponentContracts(baseline, *claims.getAsObject()));
    using A = json::Array;
    using J = json::Value;
    for (unsigned variant = 0; variant != 8; ++variant) {
      auto snapshot =
          take(zkc::language::detail::OriginalAccess::read(original));
      auto &function = snapshot.definitions.at(snapshot.names.at(symbol.str()));
      auto *operation = function.operation;
      auto *context = operation->getContext();
      mlir::Builder builder(context);
      unsigned mutation = variant < 5 ? variant : variant - 5;
      if (variant >= 5)
        operation->setAttr("contracts", builder.getArrayAttr({}));
      if (mutation < 2) {
        auto from = mutation == 0 ? 0 : 2;
        function.body.returned[1] = function.body.returned[from];
        function.body.terminal->setOperand(
            1, function.body.terminal->getOperand(from));
      } else if (mutation == 2) {
        auto *unit = &snapshot.native.get().getBody()->front();
        auto declarations = take(
            zkc::exportDeclarationData(unit->getAttr("source_declarations")));
        auto &owners = *(*declarations.getAsArray())[1].getAsArray();
        for (auto &value : owners) {
          auto &owner = *value.getAsArray();
          if (owner[0] == J(symbol))
            (*(*owner[2].getAsArray())[0].getAsArray())[2] = A{};
        }
        unit->setAttr("source_declarations",
                      take(zkc::importDeclarationData(context, declarations)));
      } else {
        auto clauses = operation->getAttrOfType<mlir::ArrayAttr>("contracts");
        SmallVector<mlir::Attribute> terms(clauses.begin(), clauses.end());
        auto clause = mlir::cast<mlir::ArrayAttr>(terms[0]);
        SmallVector<mlir::Attribute> parts(clause.begin(), clause.end());
        auto application = mlir::cast<mlir::ArrayAttr>(parts[2]);
        SmallVector<mlir::Attribute> arguments(application.begin(),
                                               application.end());
        if (mutation == 3)
          arguments[1] = builder.getArrayAttr({builder.getArrayAttr(
              {builder.getStringAttr("input"), builder.getI64IntegerAttr(0),
               builder.getStringAttr("role00000000")})});
        else
          arguments[0] =
              mlir::FlatSymbolRefAttr::get(context, "different-relation");
        parts[2] = builder.getArrayAttr(arguments);
        terms[0] = builder.getArrayAttr(parts);
        operation->setAttr("contracts", builder.getArrayAttr(terms));
      }
      // Isolate ownership analysis after admission by mutating actual native
      // declarations and the corresponding derived SSA coordinates together.
      refuses(deriveComponentContracts(snapshot),
              mutation < 2    ? "component-seam-coverage"
              : mutation == 2 ? "component-claim-role"
                              : "component-claim-relation");
    }
    auto declarations = (*baseline.publication.getAsArray())[10];
    auto &records = *(*declarations.getAsArray())[0].getAsArray();
    (*records[0].getAsArray())[2] = false;
    auto error = checkComponentDeclarations(declarations);
    require(bool(error), "unsealed linear record accepted");
    require(StringRef(toString(std::move(error)))
                .contains("component-declaration-record"),
            "wrong unsealed linear record diagnostic");
    auto changed = take(json::parse(bytes));
    auto &row = *changed.getAsObject()->getArray("seams")->front().getAsArray();
    (*row[1].getAsArray())[1] = 999;
    std::string changedBytes;
    raw_string_ostream(changedBytes) << changed;
    auto associationError = checkSourceClaims(original, changedBytes);
    require(bool(associationError), "wrong library residual endpoint accepted");
    require(StringRef(toString(std::move(associationError)))
                .contains("component-seam-association"),
            "wrong library endpoint diagnostic");
  });
  cases.run("clause-free library wrapper keeps its residual open", [] {
    auto source = fixture("components-local-fields") +
                  "protocol Library roles(V)(reference:bool@V,value:bool@V)"
                  "->(claim:Pending@V){let initial@V=pending(value);"
                  "let(next,ok)=Reduce roles(V)(reference,initial);"
                  "require @V ok;return(claim=next);}";
    auto original = take(prepareOriginal(
        take(closeSubject(take(check(source)), "claims::Library"))));
    auto bytes = take(exportSourceClaims(original));
    cantFail(checkSourceClaims(original, bytes));
    auto claims = take(json::parse(bytes));
    require(claims.getAsObject()->getArray("claims")->empty(),
            "wrapper association invented a property claim");
    require(!claims.getAsObject()->getArray("seams")->empty(),
            "wrapper association lost resource coverage");
    // A structural library subject supplies no target for a property request.
    refuses(check(source +
                  "spec LibraryClaims for Library{sound:soundness@0("
                  "target.missing,model=models.example@0(),accept=out.claim,"
                  "stage=interactive,error=0);}"),
            "source.claim.target");
    refuses(closeSubject(take(check(fixture("components-local-fields"))),
                         "claims::Reduce"),
            "source.ingress");
  });
  cases.run("pending output requires an actual residual relation", [] {
    auto source = editSource(
        fixture("components"),
        "continuation step=Truth(in.reference,in.claim.value)\n      residual "
        "Truth(in.reference,out.claim.value) accept out.ok;",
        "input step=Truth(in.reference,in.claim.value);");
    auto original = take(prepareOriginal(
        take(closeSubject(take(check(source)), "claims::Run"))));
    refuses(exportSourceClaims(original), "component-claim-relation");
  });
  cases.run("component local stops leave mathematical adequacy open", [] {
    auto source = fixture("components-stop");
    auto original = take(prepareOriginal(
        take(closeSubject(take(check(source)), "claims::Run"))));
    auto stoppedClaims = take(exportSourceClaims(original));
    cantFail(checkSourceClaims(original, stoppedClaims));
    source =
        editSource(fixture("components"), "return payload.0;", "return false;");
    original = take(prepareOriginal(
        take(closeSubject(take(check(source)), "claims::Run"))));
    // A deterministic terminal still needs an authored adequacy law in Lean.
    cantFail(checkSourceClaims(original, take(exportSourceClaims(original))));
    refused(checkSourceClaims(original, stoppedClaims));
    source = editSource(fixture("components"), "return payload.0;",
                        "return !payload.0;");
    original = take(prepareOriginal(
        take(closeSubject(take(check(source)), "claims::Run"))));
    // Boolean negation is outside the current native structured Local fragment.
    refuses(exportSourceClaims(original), "structured-source-binding");
  });
  cases.run(
      "Local nested loops branches and helper calls retain association", [] {
        auto original = take(prepareOriginal(take(closeSubject(
            take(check(fixture("components-local-control"))), "claims::Run"))));
        cantFail(
            checkSourceClaims(original, take(exportSourceClaims(original))));
      });
  cases.run(
      "Boolean Pending identity remains pure through calls and repeat", [] {
        auto original = take(prepareOriginal(take(closeSubject(
            take(check(fixture("components-local-pending"))), "claims::Run"))));
        auto bytes = take(exportSourceClaims(original));
        cantFail(checkSourceClaims(original, bytes));
        auto claims = take(json::parse(bytes));
        unsigned conversions = 0;
        for (const auto &value : *claims.getAsObject()->getArray("seams")) {
          const auto &row = *value.getAsArray();
          if ((*row[1].getAsArray())[0] != json::Value("argument"))
            continue;
          for (const auto &value : *row[3].getAsArray()) {
            const auto &route = *value.getAsArray();
            require(route[0] != json::Value("terminal"),
                    "handoff discharged a Boolean Pending conversion");
            conversions += route[0] == json::Value("pure");
          }
        }
        require(conversions != 0, "identity lost its actual helper route");
        auto negated = editSource(fixture("components-local-pending"),
                                  "firstOk && secondOk && finished",
                                  "firstOk && secondOk && !finished");
        auto rejected = take(prepareOriginal(
            take(closeSubject(take(check(negated)), "claims::Run"))));
        refuses(exportSourceClaims(rejected), "component-seam-acceptance");
      });
  cases.run("multi-field Local conversion covers every output projection", [] {
    auto original = take(prepareOriginal(take(closeSubject(
        take(check(fixture("components-local-fields"))), "claims::Run"))));
    auto claims = take(json::parse(take(exportSourceClaims(original))));
    std::string bytes;
    raw_string_ostream(bytes) << claims;
    cantFail(checkSourceClaims(original, bytes));
    auto symbol = *claims.getAsObject()
                       ->getObject("admission")
                       ->getString("protocol_symbol");
    using namespace zkc::protocol;
    for (unsigned maximum : {0, 2}) {
      auto text = editSource(
          fixture("components-local-fields"), "let initial@V=pending(value);",
          ("for _ in 0..n roles(V) max " + std::to_string(maximum) +
           " {} let initial@V=pending(value);")
              .c_str());
      auto emptyRepeat = take(prepareOriginal(
          take(closeSubject(take(check(text)), "claims::Run"))));
      take(deriveComponentContracts(
          take(zkc::language::detail::OriginalAccess::read(emptyRepeat))));
    }
    for (unsigned variant = 0; variant != 7; ++variant) {
      auto snapshot =
          take(zkc::language::detail::OriginalAccess::read(original));
      for (auto &function : snapshot.definitions) {
        if (function.kind != "protocol")
          continue;
        if (function.name != symbol) {
          if (variant < 2) {
            unsigned from = variant == 0 ? 0 : 2;
            function.body.returned[1] = function.body.returned[from];
            function.body.terminal->setOperand(
                1, function.body.terminal->getOperand(from));
          }
          continue;
        }
        for (auto &instruction : function.body.instructions) {
          auto *op = instruction.operation;
          mlir::Builder builder(op->getContext());
          if (auto repeat = mlir::dyn_cast<zkc::protocol_ir::RepeatOp>(op)) {
            if (variant == 2) {
              instruction.operands[2] = instruction.operands[1];
              op->setOperand(2, op->getOperand(1));
            }
            if (variant == 3)
              repeat.setCarried(
                  1); // The other Pending field becomes a capture.
            if (variant == 6)
              instruction.regions[0].terminator = SourceTerminator::Stop;
          }
          if (variant == 4 && mlir::isa<zkc::protocol_ir::LocalCallOp>(op))
            op->setAttr("role", builder.getStringAttr("absent"));
        }
        if (variant == 5) {
          auto &last = function.body.instructions.back();
          mlir::OpBuilder builder(last.operation);
          auto replacement = mlir::arith::CmpIOp::create(
              builder, last.operation->getLoc(), mlir::arith::CmpIPredicate::eq,
              last.operation->getOperand(0), last.operation->getOperand(1));
          last.operation->replaceAllUsesWith(replacement);
          last.operation->erase();
          last.operation = replacement;
          snapshot.descriptors.insert_or_assign(replacement.getOperation(),
                                                json::Array{"bool.equal"});
        }
      }
      // Scanner controls are intentionally separate from whole-unit admission.
      refuses(deriveComponentContracts(snapshot),
              variant < 3                    ? "component-seam-coverage"
              : variant == 3 || variant == 6 ? "component-seam-control"
              : variant == 4                 ? "component-seam-role"
                                             : "component-seam-acceptance");
    }
  });
  cases.run("malformed seam descriptors refuse exact source association", [] {
    auto original = take(prepareOriginal(take(closeSubject(
        take(check(fixture("components-repeat-values"))), "claims::Run"))));
    auto bytes = take(exportSourceClaims(original));
    for (json::Array descriptor :
         {json::Array{}, json::Array{"draw"}, json::Array{"future"},
          json::Array{"bool.constant", 0}, json::Array{"product.get", 512}}) {
      auto changed = take(json::parse(bytes));
      bool replaced = false;
      for (auto &value : *changed.getAsObject()->getArray("seams")) {
        for (auto &value : *(*value.getAsArray())[3].getAsArray()) {
          auto &route = *value.getAsArray();
          if (!replaced && (route[0] == json::Value("pure") ||
                            route[0] == json::Value("action") ||
                            route[0] == json::Value("terminal"))) {
            route[1] = std::move(descriptor);
            replaced = true;
          }
        }
      }
      require(replaced, "missing operation descriptor control");
      std::string encoded;
      raw_string_ostream(encoded) << changed;
      auto error = checkSourceClaims(original, encoded);
      require(bool(error), "malformed descriptor accepted");
      require(namesIdentifier(toString(std::move(error)),
                              "component-seam-association"),
              "wrong descriptor association refusal");
    }
  });
  cases.run("Local callback effect inventory inspects every stored path", [] {
    auto original = take(prepareOriginal(
        take(closeSubject(take(check(fixture("components"))), "claims::Run"))));
    using namespace zkc::protocol;
    // These unit controls deliberately exercise the post-admission effect
    // inventory, including paths that produce no result. Operations are native
    // owned objects; synthetic views only isolate that analysis from formation.
    auto operation = [](SourceView &view, StringRef name,
                        ArrayRef<mlir::NamedAttribute> attributes = {}) {
      auto *context = view.native.get().getContext();
      mlir::OperationState state(mlir::UnknownLoc::get(context), name);
      state.addAttributes(attributes);
      auto *op = mlir::Operation::create(state);
      view.native.get().getBody()->front().getRegion(0).front().push_back(op);
      return op;
    };
    auto instruction = [](mlir::Operation *op,
                          std::vector<SourceBlock> regions = {}) {
      return SourceInstruction{op, {}, {}, std::move(regions), "inventory"};
    };
    auto block = [](std::vector<SourceInstruction> instructions,
                    SourceTerminator end = SourceTerminator::Return) {
      SourceBlock result;
      result.instructions = std::move(instructions);
      result.terminator = end;
      return result;
    };
    auto mutate = [](SourceView &view, const SourceBlock &body) {
      for (auto &function : view.definitions)
        if (function.kind == "local")
          function.body = body;
    };
    const std::vector<std::pair<StringRef, StringRef>> effects{
        {"protocol.query", "component-seam-sampling"},
        {"protocol.exchange", "component-seam-message"},
        {"protocol.oracle_query", "component-seam-oracle"},
        {"protocol.apply", "component-seam-effect"},
        {"exec.compute", "component-seam-call"}};
    for (StringRef control : {"exec.test", "exec.range"}) {
      auto view = take(zkc::language::detail::OriginalAccess::read(original));
      auto *branch = operation(view, control);
      mutate(view, block({instruction(
                       branch, {block({}, SourceTerminator::Stop),
                                block({}, SourceTerminator::Condition)})}));
      take(deriveComponentContracts(view));
      for (const auto &[effect, code] : effects)
        for (unsigned arm : {0u, 1u}) {
          std::vector<SourceBlock> regions{block({}), block({})};
          regions[arm] = block({instruction(operation(view, effect))},
                               SourceTerminator::Stop);
          mutate(view, block({instruction(branch, std::move(regions))}));
          refuses(deriveComponentContracts(view), code);
        }
    }
    for (StringRef call : {"func.call", "exec.compute", "exec.fold",
                           "exec.collect", "data.finite_fold"}) {
      bool finite = call == "exec.fold" || call == "exec.collect" ||
                    call == "data.finite_fold";
      auto callbacks = [&](StringRef effect, bool inPredicate,
                           bool missingDomain = false) {
        auto view = take(zkc::language::detail::OriginalAccess::read(original));
        auto *context = view.native.get().getContext();
        mlir::Builder builder(context);
        SmallVector<mlir::NamedAttribute> attributes;
        auto reference = [&](StringRef key, StringRef target) {
          attributes.push_back(builder.getNamedAttr(
              key, mlir::FlatSymbolRefAttr::get(context, target)));
        };
        if (finite) {
          reference("domain", "effect.domain");
          reference(call == "exec.collect" ? "body" : "step",
                    "effect.callback");
          reference("predicate", "effect.predicate");
        } else
          reference("callee", "effect.callback");
        mutate(view, block({instruction(operation(view, call, attributes))}));
        for (StringRef name : {"effect.callback", "effect.predicate"}) {
          SourceDefinition helper;
          helper.name = name.str();
          helper.kind = "local";
          helper.hasBody = true;
          helper.operation = operation(
              view, "func.func",
              {builder.getNamedAttr("sym_name", builder.getStringAttr(name))});
          if (!effect.empty() && ((name == "effect.predicate") == inPredicate))
            helper.body = block({instruction(
                operation(view, "exec.test"),
                {block({}), block({instruction(operation(view, effect))},
                                  SourceTerminator::Stop)})});
          view.definitions.push_back(std::move(helper));
        }
        if (!missingDomain)
          operation(view, "data.domain",
                    {builder.getNamedAttr(
                        "sym_name", builder.getStringAttr("effect.domain"))});
        return view;
      };
      take(deriveComponentContracts(callbacks({}, false)));
      for (const auto &[effect, code] : effects) {
        refuses(deriveComponentContracts(callbacks(effect, false)), code);
        if (finite)
          refuses(deriveComponentContracts(callbacks(effect, true)), code);
      }
      if (finite)
        refuses(deriveComponentContracts(callbacks({}, false, true)),
                "component-seam-call");
    }
    auto view = take(zkc::language::detail::OriginalAccess::read(original));
    auto *branch = operation(view, "exec.test");
    auto deep = block({});
    for (unsigned depth = 0; depth < 64; ++depth)
      deep = block({instruction(branch, {std::move(deep)})});
    mutate(view, deep);
    take(deriveComponentContracts(view));
    deep = block({instruction(branch, {std::move(deep)})});
    mutate(view, deep);
    refuses(deriveComponentContracts(view), "component-seam-depth");
    auto *constant = operation(view, "exec.boolean");
    mutate(view, block(std::vector<SourceInstruction>(100001,
                                                      instruction(constant))));
    refuses(deriveComponentContracts(view), "component-seam-limit");
  });
  cases.run("bounded parser and exporter", [] {
    auto entry = take(close(fixture("schnorr")));
    Limits limits;
    limits.interfaceBytes = 1;
    refuses(inspectSourceClaims(entry, limits), "source.limit");
    auto source = editSource(fixture("schnorr"), "queries=2^64",
                             "queries=" + std::string(70, '(') + "1" +
                                 std::string(70, ')'));
    refuses(check(source), "source.limit");
  });
  return cases.result();
}
