#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Host.h"
#include "zkc/Compiler/LanguagePackage.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Names.h"
#include "zkc/Program/Admission.h"
#include "zkc/Program/Codec.h"
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
CheckedOriginal original(StringRef source) {
  auto captured = take(capture({{"sample", source.str(), "sample.zkc"}}));
  auto checked = take(analyze(captured).checkedProject());
  auto closed =
      take(closeEntry(checked, "sample::Demo", {}, EntryKind::Function));
  return take(prepareOriginal(closed));
}
void rejects(Error e, StringRef code) {
  require(bool(e), "expected refusal");
  auto message = toString(std::move(e));
  require(message.find(code) != std::string::npos,
          "unexpected refusal: " + message);
}
constexpr StringLiteral source = R"(module sample;
  fn add(x:index,y:index)->index{return x+y;}
  run Twice(x:index)->index{return add(x,x);}
  run Demo(x:index)->index{return Twice(Twice(x));})";
CompiledEntry compiled() { return take(compileEntry(original(source))); }
} // namespace
int main() {
  zkc::test::Cases cases;
  cases.run("standalone typed static calls and native numerical Program", [] {
    auto entry = compiled();
    auto artifact = take(json::parse(entry.bytes()));
    auto &a = *artifact.getAsObject();
    require(a.getString("format") == "zkc.host/0", "wrong Host artifact");
    require(entry.original().interface().host.has_value() &&
                entry.original().interface().protocols.empty(),
            "Host requires protocol interface");
    require(a.getArray("functions")->size() == 2 &&
                a.getArray("deployments")->empty(),
            "wrong Entry closure");
    require(entry.original().bytes().find("protocol.func") == StringRef::npos &&
                entry.original().bytes().find("protocol.participant") ==
                    StringRef::npos,
            "standalone fakes a protocol/participant");
    for (const auto &c : *a.getArray("calculations")) {
      auto &calculation = *c.getAsObject();
      auto program = take(program::parse(*calculation.getString("program")));
      if (auto e = protocol::admit(program))
        throw std::runtime_error(toString(std::move(e)));
      require(program.participants.empty() && program.entries.empty() &&
                  !program.functions.empty(),
              "numeric Program is not role free");
    }
    auto package = take(packageEntry(entry));
    auto p = take(json::parse(package.bytes()));
    require(p.getAsObject()->getString("artifact") == entry.bytes(),
            "package changed artifact");
    auto admitted =
        take(admitOriginal(entry.original().entry(), entry.original().bytes(),
                           entry.original().interfaceJson()));
    require(admitted.identity() == entry.original().identity(),
            "canonical re-admission changed identity");
  });
  cases.run("Host control uses actual func/scf and typed captures", [] {
    auto entry = take(compileEntry(original(R"(module sample;
      run Identity(x:bool)->bool{return x;}
      run Demo(x:bool)->bool{return if x {Identity(x)} else {false};})")));
    require(entry.original().bytes().contains("scf.if"), "if did not use scf");
    if (auto e = checkHostArtifact(entry.bytes(), entry.original().interface()))
      throw std::runtime_error(toString(std::move(e)));
  });
  cases.run("stopped branches retain valid structured continuations", [] {
    auto entry = take(compileEntry(original(R"(module sample;
      run Demo(go:bool)->bool {
        return if go {stop "abort";} else {true};
      })")));
    if (auto e = checkHostArtifact(entry.bytes(), entry.original().interface()))
      throw std::runtime_error(toString(std::move(e)));
    mlir::DialectRegistry registry;
    registerDialects(registry);
    mlir::MLIRContext context(registry);
    context.loadAllAvailableDialects();
    auto module = mlir::parseSourceString<mlir::ModuleOp>(
        entry.original().bytes(), &context);
    require(bool(module), "stopped original failed to parse");
    SmallVector<mlir::Operation *> continuations;
    module->walk([&](mlir::Operation *op) {
      if (op->getName().getStringRef() == "entry.stop") {
        require(op->getNumResults() == 1 &&
                    op->getNextNode()->getName().getStringRef() == "scf.yield",
                "stop did not close its unreachable structured continuation");
        continuations.push_back(op->getNextNode());
      }
    });
    require(!continuations.empty(), "no stopped branch");
    for (auto *continuation : continuations)
      continuation->erase();
    refuses(compareOriginal(entry.original().entry(), *module),
            "target.admission");
  });
  for (StringRef kind :
       {"dangling", "signature", "closure", "scope", "unknown", "duplicate"})
    cases.run("Host artifact refuses " + kind, [=] {
      auto entry = compiled();
      auto value = take(json::parse(entry.bytes()));
      auto &a = *value.getAsObject();
      auto &functions = *a.getArray("functions");
      auto *target = &*functions.back()
                           .getAsObject()
                           ->getObject("body")
                           ->getArray("operations")
                           ->front()
                           .getAsObject();
      StringRef code = "entry.reference";
      if (kind == "dangling") {
        auto operation = target->getString("op");
        if (operation == "call")
          (*target)["callee"] = "missing";
        else if (operation == "numeric")
          (*target)["calculation"] = "missing";
        else
          throw std::runtime_error("expected a statically referenced call");
      }
      if (kind == "signature") {
        target->getArray("operands")->clear();
        code = "entry.signature";
      }
      if (kind == "closure") {
        a.getArray("calculations")
            ->push_back(a.getArray("calculations")->front());
        code = "entry.closure";
      }
      if (kind == "scope") {
        (*target->getArray("operands"))[0] = 99999;
        code = "entry.scope";
      }
      if (kind == "unknown") {
        (*target)["hidden"] = true;
        code = "entry.operation";
      }
      auto bytes = printJson(value);
      if (kind == "duplicate") {
        bytes.insert(1, "\"format\":\"zkc.host/0\",");
        code = "entry.artifact";
      }
      rejects(checkHostArtifact(bytes, entry.original().interface()), code);
    });
  cases.run("Host call depth includes cached callee suffixes", [] {
    auto entry = take(compileEntry(original(R"(module sample;
      run A(x:bool)->bool{return x;}
      run B(x:bool)->bool{return A(x);}
      run C(x:bool)->bool{return B(x);}
      run Demo(x:bool)->bool{let a=A(x);let b=B(a);return C(b);})")));
    Limits limits;
    limits.callDepth = 3;
    if (auto e = checkHostArtifact(entry.bytes(), entry.original().interface(),
                                   limits))
      throw std::runtime_error(toString(std::move(e)));
    limits.callDepth = 2;
    rejects(
        checkHostArtifact(entry.bytes(), entry.original().interface(), limits),
        "entry.cycle");
  });
  for (StringRef operation : {"require", "numeric", "invoke"})
    cases.run("original admission checks malformed " + operation, [=] {
      auto checked =
          original("module sample; run Demo(x:index)->index{return x;}");
      mlir::DialectRegistry registry;
      registerDialects(registry);
      mlir::MLIRContext context(registry);
      context.loadAllAvailableDialects();
      auto module =
          mlir::parseSourceString<mlir::ModuleOp>(checked.bytes(), &context);
      auto function = *module->getOps<mlir::func::FuncOp>().begin();
      auto body = take(json::parse(
          function->getAttrOfType<mlir::StringAttr>("entry.body").getValue()));
      auto &b = *body.getAsObject();
      auto id =
          *b.getArray("arguments")->front().getAsObject()->getInteger("id");
      b.getArray("operations")
          ->push_back(json::Object{{"op", operation.str()},
                                   {"operands", json::Array{id}},
                                   {"results", json::Array{}}});
      function->setAttr("entry.body",
                        mlir::StringAttr::get(&context, printJson(body)));
      mlir::OpBuilder builder(&context);
      builder.setInsertionPointToStart(&function.getBody().front());
      mlir::OperationState state(function.getLoc(), "entry." + operation.str());
      state.addOperands(function.getArgument(0));
      state.addAttribute("descriptor",
                         builder.getStringAttr(
                             printJson(json::Object{{"op", operation.str()}})));
      builder.create(state);
      std::string bytes;
      raw_string_ostream stream(bytes);
      module->print(stream);
      auto iface = take(json::parse(checked.interfaceJson()));
      (*iface.getAsObject())["original"] =
          toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
      refuses(readInterface(bytes, printJson(iface)),
              operation == "require" ? "entry.operation" : "entry.reference");
    });
  cases.run("joint deployment binds the closed static specialization", [] {
    auto compile = [](StringRef field) {
      std::string text = R"(module sample;
        domain F=field(")" +
                         field.str() + R"(");
        protocol Work<T:Field> roles(P)(x:bool@P)->(value:bool@P){return(value=x);}
        run Demo(inputs:Work<F>::Inputs){return Work<F>::run(inputs);})";
      return take(compileEntry(original(text)));
    };
    auto first = compile("koala-bear");
    auto second = compile("bls12-381.fr");
    auto artifact = take(json::parse(first.bytes()));
    auto replacement = take(json::parse(second.bytes()));
    (*artifact.getAsObject()->getArray("deployments"))[0]
        .getAsObject()
        ->get("package")
        ->operator=(*(*replacement.getAsObject()->getArray("deployments"))[0]
                         .getAsObject()
                         ->get("package"));
    rejects(
        checkHostArtifact(printJson(artifact), first.original().interface()),
        "entry.signature");
  });
  cases.run("Host dropped values cannot be returned", [] {
    auto entry = take(compileEntry(
        original("module sample; run Demo(x:bool)->bool{return x;}")));
    auto artifact = take(json::parse(entry.bytes()));
    auto &body = *artifact.getAsObject()
                      ->getArray("functions")
                      ->front()
                      .getAsObject()
                      ->getObject("body");
    auto id =
        *body.getArray("arguments")->front().getAsObject()->getInteger("id");
    body.getArray("operations")
        ->push_back(json::Object{{"op", "drop"},
                                 {"operands", json::Array{id}},
                                 {"results", json::Array{}}});
    rejects(
        checkHostArtifact(printJson(artifact), entry.original().interface()),
        "entry.scope");
  });
  cases.run("joint child admits nested protocol instances", [] {
    auto entry = take(compileEntry(original(R"(module sample;
      protocol Step roles(P)(x:bool@P)->(value:bool@P){return(value=x);}
      protocol Work roles(P,V)(x:bool@P)->(value:bool@P,ok:bool@V){
        let value=Step(x);let ok@V=true;return(value=value,ok=ok);}
      run Demo(inputs:Work::Inputs){return Work::run(inputs);})")));
    if (auto e = checkHostArtifact(entry.bytes(), entry.original().interface()))
      throw std::runtime_error(toString(std::move(e)));
  });
  cases.run("source correspondence catches changed SSA actual operand", [] {
    auto checked = original(source);
    mlir::DialectRegistry registry;
    registerDialects(registry);
    mlir::MLIRContext context(registry);
    context.loadAllAvailableDialects();
    auto module =
        mlir::parseSourceString<mlir::ModuleOp>(checked.bytes(), &context);
    require(bool(module), "original parse");
    bool changed = false;
    module->walk([&](mlir::Operation *op) {
      if (!changed && op->getName().getStringRef() == "func.call" &&
          op->getNumOperands() && op->getNumResults() &&
          op->getParentOp()->getName().getStringRef() == "func.func") {
        auto &block = *op->getBlock();
        if (block.getNumArguments() &&
            op->getOperand(0) != block.getArgument(0)) {
          op->setOperand(0, block.getArgument(0));
          changed = true;
        }
      }
    });
    require(changed, "test found no actual operand to change");
    refuses(compareOriginal(checked.entry(), *module), "source.correspondence");
  });
  cases.run("joint child keeps the legitimate participant deployment", [] {
    auto entry = take(compileEntry(original(R"(module sample;
      protocol Work roles(P,V)(x:bool@(P,V))->(value:bool@P,ok:bool@V){
        let ok@V=x;return(value=x,ok=ok);}
      run Demo(inputs:Work::Inputs){return Work::run(inputs);})")));
    auto artifact = take(json::parse(entry.bytes()));
    const auto &deployments = *artifact.getAsObject()->getArray("deployments");
    require(deployments.size() == 1, "joint deployment inventory");
    auto package =
        take(json::parse(*deployments[0].getAsObject()->getString("package")));
    auto run = take(json::parse(*package.getAsObject()->getString("artifact")));
    auto program =
        take(program::parse(*run.getAsObject()->getString("candidate")));
    require(program.participants.size() == 2,
            "joint deployment lost a participant");
  });
  for (StringRef operation : {"prove", "verify"})
    cases.run("operation-specific proof child " + operation, [=] {
      std::string definition = R"(module sample;
      protocol Work roles(P,V)(x:bool@(P,V),y:bool@P)->(value:bool@P,ok:bool@V){
        let ok@V=x;return(value=y,ok=ok);}
      proof Family=Work{prover P;verifier V;public{x};accept ok;construction authored;}
    )";
      auto signature = operation == "verify" ? "candidate:Family::Proof"
                                             : "witness:Family::Witness";
      auto argument = operation == "verify" ? "candidate" : "witness";
      auto source = definition + "run Demo(public:Family::Public," + signature +
                    "){return Family::" + operation.str() + "(public," +
                    argument + ");}";
      auto entry = take(compileEntry(original(source)));
      auto artifact = take(json::parse(entry.bytes()));
      const auto &deployments =
          *artifact.getAsObject()->getArray("deployments");
      require(deployments.size() == 1 &&
                  deployments[0].getAsObject()->getString("operation") ==
                      operation,
              "proof deployment inventory");
      auto package = take(
          json::parse(*deployments[0].getAsObject()->getString("package")));
      auto proof = take(parseJson(*package.getAsObject()->getString("artifact"),
                                  16 * 1024 * 1024));
      auto &payload = *proof.getAsArray();
      require(payload.size() == 9 &&
                  payload[0].getAsString() == "zkc.native-proof/0",
              "native proof framing changed");
      auto program = take(program::parse(*payload[4].getAsString()));
      require(program.participants.size() == 1 &&
                  program.participants[0].role == (operation == "verify"
                                                       ? nativeRoleName(1)
                                                       : nativeRoleName(0)),
              "proof child retained the opposite operation");
      auto capture =
          take(language::capture({{"sample", source, "sample.zkc"}}));
      auto checked = take(analyze(capture).checkedProject());
      auto closed =
          take(closeEntry(checked, "sample::Family", {}, EntryKind::Proof));
      auto combined = take(compileEntry(take(prepareOriginal(closed))));
      auto combinedPayload =
          take(parseJson(combined.bytes(), 16 * 1024 * 1024));
      require(payload[2] == (*combinedPayload.getAsArray())[2] &&
                  payload[8] == (*combinedPayload.getAsArray())[8],
              "operation selection changed the proof descriptor or canonical "
              "wire occurrences");
    });
  cases.run("Host loops retain actual scf carried values", [] {
    auto entry = take(compileEntry(original(R"(module sample;
      run Identity(x:index){return x;}
      run Demo(n:index){let mut sum:index=0;for _ in 0..n{sum=Identity(sum)+1;}return sum;})")));
    require(entry.original().bytes().contains("scf.for"), "loop lost scf");
  });
  return cases.result();
}
