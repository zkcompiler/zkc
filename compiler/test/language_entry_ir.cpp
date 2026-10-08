#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SHA256.h"
using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
CheckedOriginal original(StringRef source, StringRef entry = "sample::Demo") {
  auto capture =
      take(language::capture({{"sample", source.str(), "proof.zkc"}}));
  auto checked = take(analyze(capture).checkedProject());
  return take(prepareOriginal(take(closeEntry(checked, entry))));
}
} // namespace
int main(int argc, char **argv) {
  require(argc == 2, "source fixture argument");
  auto buffer = MemoryBuffer::getFile(argv[1]);
  require(bool(buffer), "source fixture missing");
  const auto source = (*buffer)->getBuffer().str();
  zkc::test::Cases cases;
  mlir::DialectRegistry registry;
  registerNativeDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto parse = [&](StringRef bytes) {
    auto module = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
    require(bool(module), "invalid mathematical original");
    return module;
  };
  cases.run("source proof compilation retains exact Entry selections", [&] {
    auto checked = original(source);
    const auto &view = checked.interface();
    require(view.proof && view.proof->target == 0 && view.proof->service == 1 &&
                view.proof->publicInputs == std::vector<unsigned>({0, 1}),
            "Entry choices not retained");
    auto module = parse(checked.bytes());
    unsigned statements = 0;
    module->walk([&](protocol_ir::StatementOp statement) {
      ++statements;
      require(statement.getSelectors() ==
                  mlir::ArrayAttr::get(&context,
                                       {mlir::StringAttr::get(&context, "V"),
                                        mlir::StringAttr::get(&context, "V"),
                                        mlir::StringAttr::get(&context, "P")}),
              "statement participants differ");
      require(statement.getAcceptance() == 0 &&
                  statement.getInputs().size() == 3,
              "statement layout differs");
    });
    require(statements == 1, "target did not emit one entry-only statement");
    take(admitOriginal(checked.entry(), checked.bytes(),
                       checked.interfaceJson()));
    for (bool simplify : {false, true})
      for (bool release : {false, true}) {
        auto compiled = take(compileEntry(checked, {simplify, release}));
        require(
            std::holds_alternative<CompiledNativeProof>(compiled.artifact()),
            "proof Entry compiled as run");
        auto artifact = take(json::parse(compiled.bytes()));
        const auto &deployment = *artifact.getAsArray();
        require(deployment[0].getAsString() == "zkc.native-proof/4" &&
                    deployment[1].getAsString() == checked.identity(),
                "deployment source identity differs");
        auto &policy = *(*deployment[2].getAsArray())[1].getAsArray();
        require(policy[1].getAsString() == checked.entry().protocol().symbol &&
                    policy[6].getAsString() == "4" &&
                    policy[8].getAsArray()->size() == 1,
                "derived native policy differs");
        require(compiled.options().simplify == simplify &&
                    compiled.options().releaseStorage == release,
                "compile options were not retained");
      }
    auto alias = original(source, "sample::Release");
    require(alias.bytes() == checked.bytes(),
            "complete alias changed original meaning");
    require(take(compileEntry(alias)).bytes() ==
                take(compileEntry(checked)).bytes(),
            "complete alias changed native deployment");
  });
  cases.run("standalone admission pins the statement before execution", [&] {
    auto checked = original(source);
    auto module = parse(checked.bytes());
    protocol_ir::StatementOp statement;
    module->walk([&](protocol_ir::StatementOp op) { statement = op; });
    require(bool(statement) && statement->getNextNode(),
            "statement fixture missing");
    auto readReprinted = [&] {
      std::string bytes;
      raw_string_ostream out(bytes);
      module->print(out);
      auto value = take(json::parse(checked.interfaceJson()));
      (*value.getAsObject())["original"] =
          toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
      return readInterface(bytes, printJson(value));
    };
    take(readReprinted());
    statement->moveAfter(statement->getNextNode());
    require(succeeded(mlir::verify(*module)),
            "late statement must be structurally valid native IR");
    refuses(readReprinted(), "unexpected native Entry statement");
  });
  cases.run("another installed suite preserves original but changes explicit "
            "construction",
            [&] {
              auto text = source;
              auto position = text.find("merlin3.bls12-381.fr64be/1");
              text.replace(position,
                           StringRef("merlin3.bls12-381.fr64be/1").size(),
                           "spongefish0.7.4.keccak.bls12-381.fr64be/1");
              auto first = original(source), second = original(text);
              require(first.bytes() == second.bytes(),
                      "construction choice changed authored protocol");
              require(take(compileEntry(first)).bytes() !=
                          take(compileEntry(second)).bytes(),
                      "suite choice was lost");
            });
  cases.run("authored proof and joint run are distinct artifact variants", [&] {
    const auto text =
        R"(module sample;protocol Verify roles(P,V)(ok:bool@V)->(accepted:bool@V){return(accepted=ok);}
      entry Demo=Verify{prover P;verifier V;public{ok};accept accepted;construction authored;}
      entry Session=Verify;)";
    auto proof = take(compileEntry(original(text)));
    require(std::holds_alternative<CompiledNativeProof>(proof.artifact()),
            "authored proof became run");
    auto run = take(compileEntry(original(text, "sample::Session")));
    require(std::holds_alternative<CompiledRun>(run.artifact()),
            "run became proof");
  });
  cases.run(
      "source composition and repetition use native occurrence selection", [&] {
        auto definitions =
            source.substr(0, source.find("entry Demo")) +
            R"(math fn both(a:bool,b:bool)->bool{return intrinsic("bool.and",a,b);})";
        for (bool repeated : {false, true}) {
          auto text = definitions + R"(
        protocol Wrapper roles(P,V)(base:G@(P,V),point:G@(P,V),scalar:G::Scalar@P,n:index@(P,V))
        using(nonces:Random<G::Scalar>@P,challenges:Random<G::Scalar>@V)->(accepted:bool@V){
      )";
          if (repeated)
            text += R"(
          let initial@V=true;
          let valid=repeat roles(P,V)(i<n,max 3) carry(valid=initial@V)
              capture(base,point,scalar) using(nonces,challenges){
            let ok=apply Schnorr<G>(base,point,scalar) using(nonces,challenges);
            yield(valid=both(valid,ok));
          };
          return(accepted=valid);
        )";
          else
            text += R"(
          let first=apply Schnorr<G>(base,point,scalar) using(nonces,challenges);
          let second=apply Schnorr<G>(base,point,scalar) using(nonces,challenges);
          return(accepted=both(first,second));
        )";
          text += R"(}
        entry Demo=Wrapper{prover P;verifier V;public{base,point,n};accept accepted;
          construction fiat_shamir("merlin3.bls12-381.fr64be/1"){derive challenges;}}
      )";
          auto compiled = take(compileEntry(original(text)));
          auto artifact = take(json::parse(compiled.bytes()));
          auto &descriptor = *(*artifact.getAsArray())[2].getAsArray();
          auto &policy = *descriptor[1].getAsArray();
          require(
              policy[8].getAsArray()->size() == (repeated ? 1u : 2u),
              "nested source occurrences were lost or enumerated dynamically");
        }
      });
  cases.run("structured acceptance retains its actual native result index",
            [&] {
              auto checked = original(R"(module sample;
      struct Result{pub extra:index,pub accepted:bool}
      protocol Verify roles(P,V)(r:Result@V)->(r:Result@V){return(r=r);}
      entry Demo=Verify{prover P;verifier V;public{r};accept r.accepted;construction authored;})");
              require(checked.interface().proof->acceptance.native ==
                          std::vector<unsigned>{1},
                      "acceptance was flattened to the first result");
              auto compiled = take(compileEntry(checked));
              auto artifact = take(json::parse(compiled.bytes()));
              auto &descriptor = *(*artifact.getAsArray())[2].getAsArray();
              require((*descriptor[1].getAsArray())[4].getAsString() == "1",
                      "proof policy changed structural acceptance");
            });
  cases.run("source construction refuses transformed challenge delivery", [&] {
    auto text = source;
    auto at = text.find("send V->P(challenge)");
    require(at != std::string::npos, "challenge delivery missing");
    text.replace(at, StringRef("send V->P(challenge)").size(),
                 "send V -> P(challenge + challenge)");
    auto checked = original(text);
    auto result = compileEntry(checked);
    require(!result, "changed challenge delivery compiled");
    unsigned line =
        1 + std::count(text.begin(),
                       text.begin() + checked.entry().entry().span.begin, '\n');
    bool located = false;
    auto remaining =
        handleErrors(result.takeError(), [&](const CompilationError &e) {
          located =
              namesIdentifier(e.message, "native-proof-reverse-message") &&
              any_of(e.locations, [&](const DiagnosticLocation &location) {
                return location.filename == "proof.zkc" &&
                       location.line == line;
              });
        });
    if (remaining)
      throw std::runtime_error(toString(std::move(remaining)));
    require(located, "selection refusal lost its Entry coordinate");
  });
  cases.run(
      "long declaration paths use bounded native instance identities", [&] {
        std::string name(125, 'a');
        auto text =
            "module sample;protocol " + name +
            " roles(P,V)(ok:bool@V)->(accepted:bool@V){return(accepted=ok);}"
            "entry Demo=" +
            name +
            "{prover P;verifier V;public{ok};accept accepted;construction "
            "authored;}entry Session=" +
            name + ";";
        for (StringRef entry : {"sample::Demo", "sample::Session"}) {
          auto checked = original(text, entry);
          require(StringRef(checked.entry().protocol().symbol)
                          .starts_with("zkl_") &&
                      checked.entry().protocol().symbol.size() == 68,
                  "long native symbol was not bounded");
          take(compileEntry(checked));
        }
      });
  cases.run("native compilation failures retain source coordinates", [&] {
    std::string text = "module sample;domain F=field(\"bls12-381.fr\");\n"
                       "math fn f0()->F{return 1;}\n";
    for (unsigned i = 1; i <= 14; ++i) {
      auto previous = std::to_string(i - 1);
      text += "math fn f" + std::to_string(i) + "()->F{return f" + previous +
              "()+f" + previous + "();}\n";
    }
    text += "protocol Round roles(P,V)(ok:bool@V)->(accepted:bool@V,x:F@P)"
            "{return(accepted=ok,x=f14());}\n"
            "entry Demo=Round{prover P;verifier V;public{ok};accept accepted;"
            "construction authored;}entry Session=Round;";
    for (StringRef entry : {"sample::Demo", "sample::Session"}) {
      auto result = compileEntry(original(text, entry), {false, false});
      require(!result, "oversized projection succeeded");
      bool mapped = false;
      auto remaining =
          handleErrors(result.takeError(), [&](const CompilationError &e) {
            mapped =
                namesIdentifier(e.message, "mathematical-projection-limit") &&
                any_of(e.locations, [](const DiagnosticLocation &location) {
                  return location.filename == "proof.zkc" &&
                         location.line == 17;
                });
          });
      if (remaining)
        throw std::runtime_error(toString(std::move(remaining)));
      require(mapped, "native refusal did not map to source declaration");
    }
  });
  cases.run("long local names retain executable origins", [&] {
    // Encoded template symbols are exactly 128 and 129 bytes at the first
    // two lengths. Both sides of the native boundary must compile.
    for (unsigned length : {115, 116, 125}) {
      std::string name(length, 'b');
      auto text =
          "module sample;fn " + name +
          "(x:bool)->bool{return x;}protocol Round roles(P,V)(x:bool@V)"
          "->(ok:bool@V){local V let ok=" +
          name +
          "(x);return(ok=ok);}entry Demo=Round{prover P;verifier V;"
          "public{x};accept ok;construction authored;}entry Session=Round;";
      for (StringRef entry : {"sample::Demo", "sample::Session"})
        take(compileEntry(original(text, entry)));
    }
  });
  cases.run(
      "independent comparison rejects omitted and changed statements", [&] {
        auto checked = original(source);
        for (unsigned change = 0; change < 3; ++change) {
          auto module = parse(checked.bytes());
          protocol_ir::StatementOp statement;
          module->walk([&](protocol_ir::StatementOp op) { statement = op; });
          require(bool(statement), "statement missing");
          if (change == 0)
            statement.erase();
          else if (change == 1)
            statement.setOperand(0, statement.getInputs()[1]);
          else
            statement.setSelectorsAttr(mlir::ArrayAttr::get(
                &context, {mlir::StringAttr::get(&context, "P"),
                           mlir::StringAttr::get(&context, "V"),
                           mlir::StringAttr::get(&context, "P")}));
          require(succeeded(mlir::verify(*module)),
                  "statement mutation is ill-formed");
          refuses(compareOriginal(checked.entry(), *module),
                  "source.correspondence");
        }
      });
  cases.run("every source location budget boundary retains a limit refusal",
            [&] {
              auto checked = original(source);
              require(!checked.locations().empty(), "missing source map");
              for (uint64_t n = 0; n < checked.locations().size(); ++n) {
                Limits limits;
                limits.locationBytes = n * 5 * sizeof(uint64_t);
                refuses(admitOriginal(checked.entry(), checked.bytes(),
                                      checked.interfaceJson(), limits),
                        "source.limit");
              }
            });
  cases.run(
      "statement admission rejects extra attributes and selector counts", [&] {
        auto checked = original(source);
        mlir::ScopedDiagnosticHandler handler(
            &context, [](mlir::Diagnostic &) { return mlir::success(); });
        for (unsigned change = 0; change < 3; ++change) {
          auto module = parse(checked.bytes());
          protocol_ir::StatementOp statement;
          module->walk([&](protocol_ir::StatementOp op) { statement = op; });
          require(bool(statement), "statement missing");
          if (change == 0)
            statement->setAttr("extra", mlir::UnitAttr::get(&context));
          else {
            SmallVector<mlir::Attribute> selectors(
                statement.getSelectors().getValue());
            if (change == 1)
              selectors.pop_back();
            else
              selectors.push_back(mlir::StringAttr::get(&context, "P"));
            statement.setSelectorsAttr(
                mlir::ArrayAttr::get(&context, selectors));
          }
          refuses(compareOriginal(checked.entry(), *module),
                  "target.admission");
        }
      });
  cases.run(
      "structural and source job comparison reject changed selections", [&] {
        auto checked = original(source);
        for (StringRef field :
             {"public", "acceptance", "target", "construction"}) {
          auto value = take(json::parse(checked.interfaceJson()));
          auto &job = *value.getAsObject()->getObject("job");
          if (field == "public")
            job["public"] = json::Array{};
          else if (field == "acceptance")
            (*job.getObject("acceptance"))["role"] = "P";
          else if (field == "target")
            job["target"] = nullptr;
          else
            job["construction"] = json::Object{{"kind", "authored"}};
          refuses(readInterface(checked.bytes(), printJson(value)),
                  "source.interface");
        }
        auto value = take(json::parse(checked.interfaceJson()));
        (*value.getAsObject()->getObject("job")->getObject(
            "construction"))["suite"] =
            "spongefish0.7.4.keccak.bls12-381.fr64be/1";
        auto view = take(readInterface(checked.bytes(), printJson(value)));
        auto error = compareInterface(checked.entry(), view);
        require(bool(error),
                "structurally valid different suite gained source authority");
        consumeError(std::move(error));
        auto changed = checkInterface(checked, printJson(value));
        require(bool(changed), "changed job passed retained interface check");
        require(
            namesIdentifier(toString(std::move(changed)), "source.interface"),
            "changed job refused with another code");
      });

  cases.run(
      "completion metadata retains the source choice and exact native leaf",
      [] {
        auto checked = original(R"(module sample;
      struct Result{pub first:bool,pub second:bool,pub count:index}
      protocol Run roles(P,V)(n:index@P,r:Result@(P,V),ok:bool@V)->(padding:index@P,result:Result@(P,V),accepted:bool@V){return(padding=n,result=r,accepted=ok);}
      entry Demo=Run{prover P;verifier V;public{r,ok};accept accepted;complete result.second;construction authored;}
    )");
        require(checked.interface().proof->completion->native ==
                    std::vector<unsigned>{2},
                "completion used its logical port as a native leaf");
        take(compileEntry(checked));
        auto value = take(json::parse(checked.interfaceJson()));
        auto &job = *value.getAsObject()->getObject("job");
        auto &completion = *job.getObject("completion");
        completion["path"] = json::Array{0};
        auto view = take(readInterface(checked.bytes(), printJson(value)));
        auto mismatch = compareInterface(checked.entry(), view);
        require(bool(mismatch),
                "another same-typed completion gained source authority");
        require(namesIdentifier(toString(std::move(mismatch)),
                                "source.correspondence"),
                "unexpected completion refusal");
        completion["path"] = json::Array{2};
        refuses(readInterface(checked.bytes(), printJson(value)),
                "source.interface");
        completion["path"] = json::Array{1};
        completion["role"] = "V";
        refuses(readInterface(checked.bytes(), printJson(value)),
                "source.interface");
        job.erase("completion");
        refuses(readInterface(checked.bytes(), printJson(value)),
                "source.interface");
      });

  return cases.result();
}
