#include "mlir/IR/Verifier.h"
#include "zkc/Compiler/Compilation.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/LanguageInspection.h"
#include "zkc/Compiler/LanguageInterface.h"
#include "zkc/Compiler/LanguagePackage.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Compiler/PublicCoin.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"

int main(int argc, char **argv) {
  auto captured = zkc::language::capture({{"m", R"(module m;
    relation Same(statement x:bool,witness y:bool){return x==y;}
    protocol Step roles(P)(x:bool@P)->(r:bool@P)
      spec {output contract=Same(in.x,out.r);}{return(r=x);}
    protocol Run roles(P)(x:bool@P)->(r:bool@P){let r=apply Step(x);return(r=r);}
    entry Demo=Run;
    protocol Send roles(P,V)(x:bool@P)->(accepted:bool@V){
      let received=send P->V(x);return(accepted=received);
    }
    entry Proof=Send{prover P;verifier V;public{};accept accepted;construction authored;})",
                                           "consumer.zkc"}});
  if (!captured) {
    llvm::errs() << llvm::toString(captured.takeError());
    return 30;
  }
  auto languageChecked = zkc::language::analyze(*captured).checkedProject();
  if (!languageChecked) {
    llvm::errs() << llvm::toString(languageChecked.takeError());
    return 31;
  }
  auto entry = zkc::language::closeEntry(*languageChecked, "m::Demo");
  if (!entry) {
    llvm::errs() << llvm::toString(entry.takeError());
    return 32;
  }
  auto original = zkc::language::prepareOriginal(*entry);
  if (!original) {
    llvm::errs() << llvm::toString(original.takeError());
    return 33;
  }
  auto admitted = zkc::language::admitOriginal(*entry, original->bytes(),
                                               original->interfaceJson());
  if (!admitted) {
    llvm::errs() << llvm::toString(admitted.takeError());
    return 40;
  }
  if (admitted->identity() != original->identity() ||
      admitted->interfaceJson() != original->interfaceJson())
    return 41;
  auto execution = zkc::language::compileEntry(*admitted);
  if (!execution) {
    llvm::errs() << llvm::toString(execution.takeError());
    return 34;
  }
  auto package = zkc::language::packageEntry(*execution);
  if (!package) {
    llvm::errs() << llvm::toString(package.takeError());
    return 42;
  }
  if (package->bytes().empty() || package->identity().size() != 64)
    return 43;
  if (auto error =
          zkc::language::checkInterface(*original, original->interfaceJson())) {
    llvm::errs() << llvm::toString(std::move(error));
    return 35;
  }
  auto interface = zkc::language::readInterface(original->bytes(),
                                                original->interfaceJson());
  if (!interface) {
    llvm::errs() << llvm::toString(interface.takeError());
    return 36;
  }
  if (interface->selectedProtocol().symbol != entry->protocol().symbol ||
      interface->selectedProtocol().inputs.size() != 1 ||
      original->interface().selectedProtocol().symbol !=
          interface->selectedProtocol().symbol ||
      original->interface().selectedProtocol().inputs.size() != 1)
    return 37;
  unsigned applications = 0;
  if (auto error = zkc::language::inspectApplications(
          original->bytes(), original->interfaceJson(),
          [&](const zkc::language::ApplicationOccurrence &call) -> llvm::Error {
            ++applications;
            if (call.clauses.size() != 1 ||
                call.clauses[0].subject[1].values[0] !=
                    call.operation->getResult(0))
              return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                             "application binding differs");
            return llvm::Error::success();
          })) {
    llvm::errs() << llvm::toString(std::move(error));
    return 38;
  }
  if (applications != 1)
    return 39;
  if (argc > 2)
    return 15;
  mlir::DialectRegistry registry;
  auto native = zkc::compileRun(R"(module { "protocol.module"() ({
    "protocol.func"() ({
    ^entry(%value: i1):
      "protocol.return"(%value) : (i1) -> ()
    }) {sym_name="main", function_type=(i1) -> i1, roles=["Solo"],
        input_roles=[["Solo"]], output_roles=[["Solo"]]} : () -> ()
  }) {profile=#protocol.profile<protocol>} : () -> () })",
                                "native-consumer.mlir", {}, registry);
  if (!native) {
    llvm::consumeError(native.takeError());
    return 6;
  }
  if (mlir::failed(mlir::verify(native->compilation.module())))
    return 7;
  auto bundle = llvm::json::parse(native->bundle);
  if (!bundle) {
    llvm::consumeError(bundle.takeError());
    return 8;
  }
  if (bundle->getAsObject()->getString("format") != "zkc.run/1")
    return 9;
  // Installed NativeCompiler exports both view APIs, retaining ordinary source
  // admission even when a caller presents a compiled physical module.
  auto view = zkc::analyzePublicCoin(native->compilation.module(), "{}");
  if (view)
    return 10;
  llvm::consumeError(view.takeError());
  auto checked = zkc::checkPublicCoin(native->compilation.module(), "{}", "{}");
  if (!checked)
    return 11;
  llvm::consumeError(std::move(checked));
  zkc::NativeProofOptions proofOptions;
  proofOptions.policy =
      R"(["zkc.native-proof-policy/4","main","P","V","0","","",[],[]])";
  auto proof =
      zkc::compileNativeProof(R"(module { "protocol.module"() ({
    "protocol.func"() ({
    ^entry(%value: i1):
      %received = protocol.exchange %value {site="message", sender="P", receiver="V"} : i1
      "protocol.return"(%received) : (i1) -> ()
    }) {sym_name="main", function_type=(i1) -> i1, roles=["P","V"],
        input_roles=[["P"]], output_roles=[["V"]]} : () -> ()
  }) {profile=#protocol.profile<protocol>} : () -> () })",
                              "proof-consumer.mlir", proofOptions, registry);
  if (!proof) {
    llvm::consumeError(proof.takeError());
    return 12;
  }
  auto deployment = llvm::json::parse(proof->deployment);
  if (!deployment) {
    llvm::consumeError(deployment.takeError());
    return 13;
  }
  if ((*deployment->getAsArray())[0].getAsString() != "zkc.native-proof/4" ||
      mlir::failed(mlir::verify(proof->compilation.module())))
    return 14;
  auto proofEntry = zkc::language::closeEntry(*languageChecked, "m::Proof");
  if (!proofEntry) {
    llvm::errs() << llvm::toString(proofEntry.takeError());
    return 50;
  }
  auto proofOriginal = zkc::language::prepareOriginal(*proofEntry);
  if (!proofOriginal) {
    llvm::errs() << llvm::toString(proofOriginal.takeError());
    return 51;
  }
  auto proofExecution = zkc::language::compileEntry(*proofOriginal);
  if (!proofExecution) {
    llvm::errs() << llvm::toString(proofExecution.takeError());
    return 52;
  }
  auto proofPackage = zkc::language::packageEntry(*proofExecution);
  if (!proofPackage) {
    llvm::errs() << llvm::toString(proofPackage.takeError());
    return 53;
  }
  if (argc == 2) {
    auto write = [&](llvm::StringRef name, llvm::StringRef bytes) {
      llvm::SmallString<256> path(argv[1]);
      llvm::sys::path::append(path, name);
      std::error_code error;
      llvm::raw_fd_ostream stream(path, error, llvm::sys::fs::OF_None);
      if (error)
        return false;
      stream << bytes;
      stream.flush();
      return !stream.has_error();
    };
    if (!write("run.bundle", native->bundle) ||
        !write("proof.deployment", proof->deployment) ||
        !write("run.entry", package->bytes()) ||
        !write("proof.entry", proofPackage->bytes()))
      return 16;
  }
  return 0;
}
