#include "TableGen/Declarations.h"
#include "TableGen/Mathematical.h"
#include "TableGen/Recipes.h"
#include "TableGen/TypeBindings.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TableGen/Error.h"
#include "llvm/TableGen/Main.h"
#include "llvm/TableGen/Record.h"
#include <algorithm>
#include <map>
#include <string>
#include <tuple>
#include <vector>

using namespace llvm;

namespace {
enum class Action {
  Declarations,
  Inventory,
  TypeBindings,
  Mathematics,
  Recipes
};
cl::opt<Action> action(
    cl::desc("Generation action (required):"), cl::Required,
    cl::values(
        clEnumValN(Action::Recipes, "gen-mathematical-recipes",
                   "Generate checked private realization recipes"),
        clEnumValN(Action::Mathematics, "gen-mathematical-declarations",
                   "Generate mathematical identities, intrinsics and laws"),
        clEnumValN(Action::TypeBindings, "gen-type-bindings",
                   "Generate native type bindings and check coverage"),
        clEnumValN(Action::Declarations, "gen-contract-declarations",
                   "Generate neutral contract descriptors"),
        clEnumValN(Action::Inventory, "dump-contract-declarations",
                   "Inspect neutral declarations as JSON")));
bool generate(raw_ostream &os, const RecordKeeper &records) {
  switch (action) {
  case Action::Recipes:
    return emitMathematicalRecipes(os, records);
  case Action::Mathematics:
    return emitMathematicalDeclarations(os, records);
  case Action::TypeBindings:
    return emitTypeBindings(os, records);
  case Action::Declarations:
    return emitContractDeclarations(os, records);
  case Action::Inventory:
    return emitContractInventory(os, records);
  }
  llvm_unreachable("unknown generation action");
}
} // namespace

int main(int argc, char **argv) {
  InitLLVM init(argc, argv);
  cl::ParseCommandLineOptions(argc, argv, "zkc contract generator\n");
  return TableGenMain(argv[0], &generate);
}
