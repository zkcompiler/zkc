#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Host.h"
#include "zkc/Compiler/LanguagePackage.h"
#include "zkc/Compiler/NativeLanguage.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Names.h"
#include "zkc/Program/Admission.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Entry.h"
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
constexpr StringLiteral sourceText = R"(module sample;
  fn add(x:index,y:index)->index{return x+y;}
  entry fn Twice(x:index)->index{return add(x,x);}
  entry fn Demo(x:index)->index{return Twice(Twice(x));})";
CompiledEntry compiled() { return take(compileEntry(original(sourceText))); }
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
  cases.run("Host artifacts reconstruct from SSA without body hints", [] {
    auto entry = compiled();
    require(!entry.original().bytes().contains("entry.body") &&
                !entry.original().bytes().contains("entry.signature"),
            "Host original retained a second body or signature carrier");
    json::Array functions;
    {
      mlir::DialectRegistry registry;
      registerDialects(registry);
      mlir::MLIRContext context(registry);
      auto module = mlir::parseSourceString<mlir::ModuleOp>(
          entry.original().bytes(), &context);
      require(bool(module), "native Host roundtrip refused");
      functions = take(readHostFunctions(*module));
      auto function = *module->getOps<mlir::func::FuncOp>().begin();
      auto name = functions.front()
                      .getAsObject()
                      ->getObject("signature")
                      ->getString("symbol");
      require(name && name->data() != function.getSymName().data(),
              "exported Host symbol borrows MLIR storage");
      Limits limited;
      limited.work = 0;
      refuses(readHostFunctions(*module, limited), "source.correspondence");
      function->setAttr("entry.body", mlir::StringAttr::get(&context, "{}"));
      refuses(readHostFunctions(*module), "source.correspondence");
    }
    auto artifact = take(json::parse(entry.bytes()));
    require(functions == *artifact.getAsObject()->getArray("functions"),
            "SSA-only reconstruction changed after MLIR context destruction");
  });
  cases.run("Host conditional captures are explicit and checked", [] {
    auto checked = original(R"(module sample;
      entry fn Demo(go:bool,left:bool,right:bool)->bool {
        return if go {left} else {right};
      })");
    mlir::DialectRegistry registry;
    registerDialects(registry);
    mlir::MLIRContext context(registry);
    auto module =
        mlir::parseSourceString<mlir::ModuleOp>(checked.bytes(), &context);
    require(bool(module), "conditional native roundtrip refused");
    mlir::cf::CondBranchOp branch;
    module->walk([&](mlir::cf::CondBranchOp op) { branch = op; });
    require(branch && branch.getTrueDestOperands().size() >= 2 &&
                branch.getTrueDest()->getNumArguments() ==
                    branch.getTrueDestOperands().size(),
            "conditional erased capture ports");
    take(readHostFunctions(*module));
    branch.getTrueDestOperandsMutable()[0].set(branch.getTrueDestOperands()[1]);
    require(mlir::succeeded(mlir::verify(*module)),
            "capture mutation should retain structural MLIR validity");
    refuses(readHostFunctions(*module), "source.correspondence");
    // Matching duplicated captures describe a different, formed Host program.
    // Its reconstructed artifact is valid, but source correspondence must fail.
    branch.getFalseDestOperandsMutable()[0].set(
        branch.getFalseDestOperands()[1]);
    take(readHostFunctions(*module));
    refuses(compareHostOriginal(checked.entry(), *module),
            "source.correspondence");
  });
  cases.run("Host zero-state loops and terminal arms retain their structure",
            [] {
              for (StringRef source : {
                       R"(module sample;entry fn Demo(n:index)->bool {
                  for _ in 0..n {require true;} return true;
                })",
                       R"(module sample;
                  entry fn Check(go:bool)->(){require go;return ();}
                  entry fn Demo(go:bool,n:index)->bool {
                    for _ in 0..n {Check(go);} return true;
                  })",
                       R"(module sample;
                  entry fn Next(x:index)->index{return x+1;}
                  entry fn Demo(seed:index,n:index)->(index,index) {
                    let mut a=seed;let mut b=seed;
                    for i in 0..n {a=Next(a);b=b+i+seed;} return(a,b);
                  })",
                       R"(module sample;entry fn Demo(go:bool)->bool {
                  return if go {stop "abort";} else {stop "abort";};
                })"}) {
                auto entry = take(compileEntry(original(source)));
                if (auto failure = checkHostArtifact(
                        entry.bytes(), entry.original().interface()))
                  throw std::runtime_error(toString(std::move(failure)));
              }
            });
  cases.run("Host numerical selection retains the requested finite policy", [] {
    auto checked = original(R"(module sample;
      domain Fr=field("koala-bear");
      type Vector<F:Field>=builtin("vector",F);
      domain fn elements<F:Field>(xs:Vector<F>)->domain<F>=domain("elements");
      math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
      math fn sum(xs:Vector<Fr>)->Fr{return fold(elements(xs),0,fn(state,item)=>state+item);}
      fn work(xs:Vector<Fr>)->Fr{return sum(xs);}
      entry fn Demo(xs:Vector<Fr>)->Fr{return work(xs);})");
    auto loops = [&](bool optimize) {
      EntryOptions options;
      options.mathematicalSelection.finiteBulk = optimize;
      auto compiled = take(compileEntry(checked, options));
      auto artifact = take(json::parse(compiled.bytes()));
      unsigned count = 0;
      std::function<void(const program::Body &)> walk;
      walk = [&](const program::Body &body) {
        for (const auto &instruction : body) {
          if (auto loop = instruction.get<program::For>()) {
            ++count;
            walk(loop->body);
          } else if (auto condition = instruction.get<program::Conditional>()) {
            walk(condition->thenBody);
            walk(condition->elseBody);
          }
        }
      };
      for (const auto &calculation :
           *artifact.getAsObject()->getArray("calculations")) {
        auto program = take(
            program::parse(*calculation.getAsObject()->getString("program")));
        for (const auto &function : program.functions)
          walk(function.body);
      }
      take(packageEntry(compiled));
      return count;
    };
    require(loops(false) > loops(true),
            "disabled finite selection did not retain its ordered traversal");
  });
  cases.run("Host control exposes outcomes with standard control flow", [] {
    auto entry = take(compileEntry(original(R"(module sample;
      entry fn Identity(x:bool)->bool{return x;}
      entry fn Demo(x:bool)->bool{return if x {Identity(x)} else {false};})")));
    require(entry.original().bytes().contains("cf.cond_br") &&
                entry.original().bytes().contains("exec.dispatch"),
            "control or fallible call did not expose its outcome");
    if (auto e = checkHostArtifact(entry.bytes(), entry.original().interface()))
      throw std::runtime_error(toString(std::move(e)));
  });
  for (StringRef disposal : {"drop", "consume"})
    for (bool reuse : {false, true})
      cases.run(
          "source disposal publishes with Copy reuse " + disposal +
              (reuse ? " reused" : " discarded"),
          [=] {
            auto type = disposal == "drop" ? "bool" : "Item";
            auto fallback = disposal == "drop" ? "false" : "Item{bit:false}";
            auto text =
                "module sample;struct Item{pub bit:bool}entry fn Demo(x:" +
                std::string(type) + ")->" + type + "{" + disposal.str() +
                " x;return " + (reuse ? "x" : fallback) + ";}";
            auto entry = take(compileEntry(original(text)));
            auto artifact = take(json::parse(entry.bytes()));
            auto &body = *artifact.getAsObject()
                              ->getArray("functions")
                              ->front()
                              .getAsObject()
                              ->getObject("body");
            auto input = *body.getArray("arguments")
                              ->front()
                              .getAsObject()
                              ->getInteger("id");
            auto &operations = *body.getArray("operations");
            require(operations.size() >= 3,
                    "disposal omitted copy, drop or logical unit");
            auto &copy = *operations[0].getAsObject();
            auto &drop = *operations[1].getAsObject();
            auto &unit = *operations[2].getAsObject();
            auto temporary =
                *copy.getArray("results")->front().getAsObject()->getInteger(
                    "id");
            require(copy.getString("op") == "project" &&
                        copy.getArray("path")->empty() &&
                        *copy.getArray("operands") == json::Array{input} &&
                        temporary != input && drop.getString("op") == "drop" &&
                        *drop.getArray("operands") == json::Array{temporary} &&
                        drop.getArray("results")->empty() &&
                        unit.getString("op") == "construct" &&
                        unit.getArray("operands")->empty() &&
                        unit.getArray("results")
                                ->front()
                                .getAsObject()
                                ->getObject("schema")
                                ->getString("kind") == "unit",
                    "disposal does not preserve source Copy/unit semantics");
            if (reuse)
              require(*body.getArray("returns") == json::Array{input},
                      "disposal removed the original Copy value");
            take(packageEntry(entry));
            auto admitted = take(admitOriginal(
                entry.original().entry(), entry.original().bytes(),
                entry.original().interfaceJson()));
            require(admitted.identity() == entry.original().identity(),
                    "disposal changed original re-admission");
            drop["operands"] = json::Array{input};
            if (reuse)
              rejects(checkHostArtifact(printJson(artifact),
                                        entry.original().interface()),
                      "entry.scope");
            else {
              drop["results"] = json::Array(*unit.getArray("results"));
              rejects(checkHostArtifact(printJson(artifact),
                                        entry.original().interface()),
                      "entry.operation");
            }
          });
  cases.run("non-Copy disposal stays inside numerical helpers", [] {
    auto entry = take(compileEntry(original(R"(module sample;
      #[affine] struct Disposable {value:bool}
      #[linear] struct Required {value:bool}
      fn dispose(x:bool)->bool {
        let a=Disposable{value:x};drop a;
        let b=Required{value:x};consume b;
        return x;
      }
      entry fn Demo(x:bool)->bool{return dispose(x);})")));
    take(packageEntry(entry));
  });
  cases.run("owner-module opaque factories and numerical pass-through publish",
            [] {
              auto entry = take(compileEntry(original(R"(module sample;
      module Vault {
        pub type Item:Copy+Drop=bool;
        pub fn make(x:bool)->Item{return Item(x);}
        pub fn read(x:Item)->bool{return unpack(x);}
      }
      fn retain(x:Vault::Item)->Vault::Item{return x;}
      entry fn Demo(x:bool)->bool{return Vault::read(retain(Vault::make(x)));}
    )")));
              auto artifact = take(json::parse(entry.bytes()));
              bool opaqueResult = false, opaquePass = false;
              for (const auto &value :
                   *artifact.getAsObject()->getArray("calculations")) {
                auto &calculation = *value.getAsObject();
                auto &result =
                    *calculation.getArray("results")->front().getAsObject();
                if (result.getString("kind") != "associated")
                  continue;
                opaqueResult |= !*result.getBoolean("constructible");
                auto &parameter = calculation.getArray("parameters")->front();
                opaquePass |= parameter == json::Value(json::Object(result));
              }
              require(opaqueResult && opaquePass,
                      "opaque factory or pass-through lost its logical schema");
              take(packageEntry(entry));
            });
  cases.run(
      "stopped branches carry a terminal cause without fabricated values", [] {
        auto entry = take(compileEntry(original(R"(module sample;
      entry fn Demo(go:bool)->bool {
        return if go {stop "abort";} else {true};
      })")));
        if (auto e =
                checkHostArtifact(entry.bytes(), entry.original().interface()))
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
          if (op->getName().getStringRef() == "exec.stop") {
            require(op->getNumResults() == 1 &&
                        op->getResult(0).getType() !=
                            mlir::IntegerType::get(&context, 1) &&
                        op->getNextNode()->getName().getStringRef() == "cf.br",
                    "stop fabricated a Boolean or lost its terminal edge");
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
  cases.run("Host publication shares Rust lexical resource bounds", [] {
    auto entry = compiled();
    auto check = [&](StringRef bytes, StringRef code) {
      rejects(checkHostArtifact(bytes, entry.original().interface()), code);
    };
    // One array and 199999 scalar tokens reach structural admission. One more
    // token must refuse before shape checks, just as the independent reader.
    std::string nodes = "[0";
    for (unsigned i = 1; i < 199999; ++i)
      nodes += ",0";
    nodes += ']';
    check(nodes, "entry.artifact");
    nodes.insert(nodes.size() - 1, ",0");
    check(nodes, "source.limit");
    check("{\"x\":12345678901}", "source.limit");
    // Resource refusal precedes invalid numeric spelling throughout the scan.
    check("[-0,12345678901]", "source.limit");
    check("[-0," + std::string(256, '[') + "0" + std::string(256, ']') + "]",
          "source.limit");
    check("[-0]", "entry.artifact");
    // Host carriers embed programs larger than an interface metadata string.
    // That allowance does not bypass the document's fixed 16 MiB ceiling.
    check("{\"program\":\"" + std::string(2 * 1024 * 1024, 'x') + "\"}",
          "entry.artifact");
    check(std::string(16 * 1024 * 1024 + 1, ' '), "source.limit");
  });
  cases.run("Host call depth includes cached callee suffixes", [] {
    auto entry = take(compileEntry(original(R"(module sample;
      entry fn A(x:bool)->bool{return x;}
      entry fn B(x:bool)->bool{return A(x);}
      entry fn C(x:bool)->bool{return B(x);}
      entry fn Demo(x:bool)->bool{let a=A(x);let b=B(a);return C(b);})")));
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
          original("module sample; entry fn Demo(x:index)->index{return x;}");
      mlir::DialectRegistry registry;
      registerDialects(registry);
      mlir::MLIRContext context(registry);
      context.loadAllAvailableDialects();
      auto module =
          mlir::parseSourceString<mlir::ModuleOp>(checked.bytes(), &context);
      auto function = *module->getOps<mlir::func::FuncOp>().begin();
      mlir::OpBuilder builder(&context);
      builder.setInsertionPointToStart(&function.getBody().front());
      mlir::OperationState state(function.getLoc(), "exec." + operation.str());
      state.addTypes(exec::OutcomeType::get(&context, {}));
      state.addOperands(function.getArgument(0));
      builder.create(state);
      std::string bytes;
      raw_string_ostream stream(bytes);
      module->print(stream);
      auto iface = take(json::parse(checked.interfaceJson()));
      (*iface.getAsObject())["original"] =
          toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
      refuses(readInterface(bytes, printJson(iface)), "target.admission");
    });
  cases.run("joint deployment binds the closed static specialization", [] {
    auto compile = [](StringRef field) {
      std::string text = R"(module sample;
        domain F=field(")" +
                         field.str() + R"(");
        protocol Work<T:Field> roles(P)(x:bool@P)->(value:bool@P){return(value=x);}
        entry fn Demo(inputs:Work<F>::Inputs){return Work<F>::run(inputs);})";
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
        original("module sample; entry fn Demo(x:bool)->bool{return x;}")));
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
      entry fn Demo(inputs:Work::Inputs){return Work::run(inputs);})")));
    if (auto e = checkHostArtifact(entry.bytes(), entry.original().interface()))
      throw std::runtime_error(toString(std::move(e)));
  });
  cases.run("source correspondence catches changed SSA actual operand", [] {
    auto checked = original(sourceText);
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
        auto &block = mlir::cast<mlir::func::FuncOp>(op->getParentOp()).front();
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
      entry fn Demo(inputs:Work::Inputs){return Work::run(inputs);})")));
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
      auto result = operation == "verify" ? "Family::VerifyResult"
                                          : "Family::ProveResult";
      auto source = definition + "fn retain(x:" + result + ")->" + result +
                    "{return x;}entry fn Demo(public:Family::Public," +
                    signature + "){return retain(Family::" + operation.str() +
                    "(public," + argument + "));}";
      auto entry = take(compileEntry(original(source)));
      auto artifact = take(json::parse(entry.bytes()));
      const auto &deployments =
          *artifact.getAsObject()->getArray("deployments");
      require(deployments.size() == 1 &&
                  deployments[0].getAsObject()->getString("operation") ==
                      operation,
              "proof deployment inventory");
      require(!artifact.getAsObject()->getArray("calculations")->empty(),
              "native result did not cross the numerical helper");
      take(packageEntry(entry));
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
  cases.run("Host loops retain actual CFG carried values", [] {
    auto entry = take(compileEntry(original(R"(module sample;
      entry fn Identity(x:index){return x;}
      entry fn Demo(n:index){let mut sum:index=0;for _ in 0..n{sum=Identity(sum)+1;}return sum;})")));
    require(entry.original().bytes().contains("cf.cond_br") &&
                entry.original().bytes().contains("arith.cmpi"),
            "loop lost unsigned CFG condition");
  });
  cases.run("terminal failure cannot be replaced by returned false", [] {
    auto checked = original(R"(module sample;
      entry fn Demo(go:bool)->bool{require go;return true;})");
    mlir::DialectRegistry registry;
    registerDialects(registry);
    mlir::MLIRContext context(registry);
    context.loadAllAvailableDialects();
    auto module =
        mlir::parseSourceString<mlir::ModuleOp>(checked.bytes(), &context);
    require(bool(module), "outcome original did not parse");
    exec::FailureOp failed;
    module->walk([&](exec::FailureOp op) {
      auto function = op->getParentOfType<mlir::func::FuncOp>();
      if (function && function->getParentOp() == module->getOperation())
        failed = op;
    });
    require(bool(failed), "missing failure carrier");
    mlir::OpBuilder builder(failed);
    auto value =
        mlir::arith::ConstantIntOp::create(builder, failed.getLoc(), 0, 1);
    auto returned = exec::ReturnOp::create(builder, failed.getLoc(),
                                           failed.getOutcome().getType(),
                                           mlir::ValueRange{value});
    failed.getOutcome().replaceAllUsesWith(returned.getOutcome());
    failed.erase();
    require(mlir::succeeded(mlir::verify(*module)),
            "mutation should remain well typed");
    refuses(compareOriginal(checked.entry(), *module), "source.correspondence");
  });
  cases.run("unread dead control blocks are not source correspondence", [] {
    auto checked =
        original("module sample;entry fn Demo(x:bool)->bool{return x;}");
    mlir::DialectRegistry registry;
    registerDialects(registry);
    mlir::MLIRContext context(registry);
    context.loadAllAvailableDialects();
    auto module =
        mlir::parseSourceString<mlir::ModuleOp>(checked.bytes(), &context);
    require(bool(module), "original did not parse");
    auto function = *module->getOps<mlir::func::FuncOp>().begin();
    mlir::IRMapping mapping;
    auto *dead = new mlir::Block;
    function.getBody().push_back(dead);
    auto &terminal = *std::next(function.getBody().begin());
    auto argument =
        dead->addArgument(terminal.getArgument(0).getType(), function.getLoc());
    mapping.map(terminal.getArgument(0), argument);
    for (auto &op : terminal)
      dead->push_back(op.clone(mapping));
    require(mlir::succeeded(mlir::verify(*module)),
            "dead block should be well typed");
    refuses(compareOriginal(checked.entry(), *module), "source.correspondence");
  });
  for (StringRef operation :
       {"return", "require", "drop", "numeric", "invoke", "dispatch"})
    cases.run("Exec formation refuses invalid " + operation, [=] {
      mlir::DialectRegistry registry;
      registerDialects(registry);
      mlir::MLIRContext context(registry);
      std::string diagnostic;
      mlir::ScopedDiagnosticHandler handler(&context, [&](mlir::Diagnostic &d) {
        raw_string_ostream stream(diagnostic);
        d.print(stream);
        return mlir::success();
      });
      std::string instruction;
      if (operation == "return")
        instruction =
            R"(%r = "exec.returned"(%x) : (i64) -> !exec.outcome<(i1)>)";
      if (operation == "require")
        instruction = R"(%r = "exec.require"(%x)  : (i64) -> !exec.outcome<>)";
      if (operation == "drop")
        instruction = R"(%r = "exec.drop"()  : () -> !exec.outcome<>)";
      if (operation == "numeric")
        instruction =
            R"(%r = "exec.numeric"() {calculation = ""} : () -> !exec.outcome<>)";
      if (operation == "invoke")
        instruction =
            R"(%r = "exec.invoke"() {deployment = "work"} : () -> !exec.outcome<>)";
      std::string text = "module { func.func @test(%x: i64) {" + instruction +
                         "\nfunc.return } }";
      if (operation == "dispatch")
        text = R"(module {func.func @test(%x: !exec.outcome<(i1)>) {
        "exec.dispatch"(%x)[^returned, ^stopped] : (!exec.outcome<(i1)>) -> ()
        ^returned(%bad:i64): func.return
        ^stopped(%stop:!exec.stop): func.return
      }})";
      auto parsed = mlir::parseSourceString<mlir::ModuleOp>(text, &context);
      require(!parsed && StringRef(diagnostic).contains("execution-formation"),
              "invalid outcome accepted or wrong diagnostic: " + diagnostic);
    });
  for (StringRef change : {"alternative", "payload", "projection", "unpack"})
    cases.run("logical operation refuses changed " + change, [=] {
      auto checked = original(R"(module sample;
        struct Pair { pub flag:bool, pub count:index }
        entry fn Demo(x:bool,n:index)->bool {
          let pair=Pair{flag:x,count:n};return pair.flag;
        })");
      mlir::DialectRegistry registry;
      registerDialects(registry);
      mlir::MLIRContext context(registry);
      context.loadAllAvailableDialects();
      auto module =
          mlir::parseSourceString<mlir::ModuleOp>(checked.bytes(), &context);
      require(bool(module), "logical original did not parse");
      data::ConstructOp construct;
      data::ProjectOp project;
      module->walk([&](data::ConstructOp op) { construct = op; });
      module->walk([&](data::ProjectOp op) { project = op; });
      require(construct && project, "missing logical value operations");
      if (change == "alternative")
        construct.setAlternative("invented");
      else if (change == "payload")
        construct->setOperand(0, construct.getInputs()[1]);
      else if (change == "projection")
        project.setPath(llvm::ArrayRef<int64_t>{-1});
      else {
        mlir::OpBuilder builder(&context);
        builder.setInsertionPointAfter(construct);
        mlir::OperationState state(construct.getLoc(), "data.unpack");
        state.addOperands(construct.getOutput());
        state.addTypes(builder.getI1Type());
        builder.create(state);
      }
      std::string diagnostic;
      mlir::ScopedDiagnosticHandler handler(&context, [&](mlir::Diagnostic &d) {
        raw_string_ostream stream(diagnostic);
        d.print(stream);
        return mlir::success();
      });
      require(mlir::failed(mlir::verify(*module)) &&
                  StringRef(diagnostic).contains("data-value-formation"),
              "malformed logical operation accepted: " + diagnostic);
    });
  for (StringRef change : {"predicate", "increment", "back-edge"})
    cases.run("Host loop rejects changed " + change, [=] {
      auto checked = original(R"(module sample;
        entry fn Demo(n:index){let mut sum:index=0;for _ in 0..n{sum=sum+1;}return sum;})");
      mlir::DialectRegistry registry;
      registerDialects(registry);
      mlir::MLIRContext context(registry);
      context.loadAllAvailableDialects();
      auto module =
          mlir::parseSourceString<mlir::ModuleOp>(checked.bytes(), &context);
      require(bool(module), "loop original did not parse");
      auto function = *module->getOps<mlir::func::FuncOp>().begin();
      mlir::arith::CmpIOp compare;
      mlir::arith::AddIOp increment;
      function.walk([&](mlir::arith::CmpIOp op) { compare = op; });
      function.walk([&](mlir::arith::AddIOp op) { increment = op; });
      require(compare && increment, "missing loop structure");
      if (change == "predicate")
        compare.setPredicate(mlir::arith::CmpIPredicate::ule);
      else if (change == "increment")
        increment.setOperand(1, increment.getLhs());
      else {
        auto edge = mlir::cast<mlir::cf::BranchOp>(
            increment->getBlock()->getTerminator());
        edge.setOperand(1, edge.getDest()->getArgument(1));
      }
      require(mlir::succeeded(mlir::verify(*module)),
              "mutation should remain well typed");
      refuses(compareOriginal(checked.entry(), *module),
              "source.correspondence");
    });
  cases.run("Data match refuses duplicate alternatives", [] {
    auto checked = original(R"(module sample;
      enum Choice { First(bool), Second(bool) }
      entry fn Demo(x:Choice)->bool{return match x {First(v)=>{v},Second(v)=>{v}};})");
    mlir::DialectRegistry registry;
    registerDialects(registry);
    mlir::MLIRContext context(registry);
    context.loadAllAvailableDialects();
    auto module =
        mlir::parseSourceString<mlir::ModuleOp>(checked.bytes(), &context);
    require(bool(module), "match original did not parse");
    data::MatchOp match;
    module->walk([&](data::MatchOp op) { match = op; });
    require(bool(match), "missing sum elimination");
    auto label = match.getAlternatives()[0];
    match.setAlternativesAttr(mlir::ArrayAttr::get(&context, {label, label}));
    std::string diagnostic;
    mlir::ScopedDiagnosticHandler handler(&context, [&](mlir::Diagnostic &d) {
      raw_string_ostream stream(diagnostic);
      d.print(stream);
      return mlir::success();
    });
    require(mlir::failed(mlir::verify(*module)) &&
                StringRef(diagnostic).contains("data-match-formation"),
            "duplicate alternatives accepted or wrong diagnostic: " +
                diagnostic);
  });
  cases.run(
      "Host match reads every successor's source capture association", [] {
        auto checked = original(R"(module sample;
      enum Choice { First(bool), Second(bool) }
      entry fn Demo(x:Choice,y:bool,z:bool)->bool {
        return match x {First(v)=>{y},Second(v)=>{z}};
      })");
        mlir::DialectRegistry registry;
        registerDialects(registry);
        mlir::MLIRContext context(registry);
        auto module =
            mlir::parseSourceString<mlir::ModuleOp>(checked.bytes(), &context);
        require(bool(module), "match original did not parse");
        take(readHostFunctions(*module));
        data::MatchOp match;
        module->walk([&](data::MatchOp op) { match = op; });
        require(match && match.getForwarded()[1].size() == 2,
                "fixture must carry two common source captures");
        auto values = match.getForwarded()[1];
        mlir::Value first = values[0], second = values[1];
        match.getForwardedMutable()[1].assign({second, first});
        require(mlir::succeeded(mlir::verify(*module)),
                "independent edge mutation should remain structurally valid");
        refuses(readHostFunctions(*module), "source.correspondence");
      });
  cases.run("Host admission does not ignore extra dispatch forwarding", [] {
    auto entry = compiled();
    mlir::DialectRegistry registry;
    registerDialects(registry);
    mlir::MLIRContext context(registry);
    auto module = mlir::parseSourceString<mlir::ModuleOp>(
        entry.original().bytes(), &context);
    require(bool(module), "Host original did not parse");
    exec::DispatchOp edge;
    module->walk([&](exec::DispatchOp op) {
      if (!edge)
        edge = op;
    });
    require(bool(edge), "missing Host outcome dispatch");
    auto function = edge->getParentOfType<mlir::func::FuncOp>();
    auto argument = function.getArgument(0);
    edge.getSuccessorOperands(0).append(mlir::ValueRange{argument});
    edge.getReturned()->addArgument(argument.getType(), edge.getLoc());
    require(mlir::succeeded(mlir::verify(*module)),
            "extra generic forwarding should remain structurally valid");
    refuses(readHostFunctions(*module), "source.correspondence");
  });
  return cases.result();
}
