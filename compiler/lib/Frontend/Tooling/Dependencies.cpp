#include "zkc/Frontend/Dependencies.h"
#include "../Syntax/Tree.h"
#include <set>

using namespace llvm;
namespace zkc::frontend {
namespace {
LibraryIdentityDeclaration identity(const syntax::LibraryIdentity &value) {
  return {value.nameSpace, value.name, value.version, value.resolution,
          value.location};
}
bool moduleName(StringRef name) {
  return !name.empty() && name.size() <= 128 && name != "." && name != ".." &&
         !name.contains('/') && !name.contains('\\') && !name.contains('\0');
}
} // namespace

DependencyDeclarations inspectDependencies(const Input &input, uint32_t file) {
  auto parsed = syntax::parseRecoverable(input.text(), input.filename(), file);
  DependencyDeclarations result;
  for (const auto &d : parsed.diagnostics)
    result.diagnostics.push_back({d.code, d.message, d.location});
  if (!parsed.content)
    return result;
  result.recoverable = true;
  auto fail = [&](const source::Node &node, StringRef code, StringRef message) {
    result.recoverable = false;
    result.diagnostics.push_back({code.str(), message.str(), node.location});
  };
  if (const auto *module = std::get_if<syntax::Module>(&*parsed.content)) {
    result.form =
        module->carrier ? SourceForm::CarrierModule : SourceForm::Module;
    result.location = module->location;
    result.profile = module->profile;
    std::set<std::string> modules, relations, libraries;
    for (const auto &child : module->modules) {
      result.modules.push_back({child.name, child.location});
      if (!moduleName(child.name))
        fail(child, "project-module-name", "invalid logical module name");
      if (!modules.insert(child.name).second)
        fail(child, "project-module-duplicate",
             "duplicate logical module name");
    }
    for (const auto &import : module->imports) {
      result.relations.push_back(
          {import.name, import.family, import.path, import.location});
      if (!relations.insert(import.name).second)
        fail(import, "relation-duplicate-alias", "duplicate relation alias");
      if (import.family != "r1cs" && import.family != "air")
        fail(import, "relation-import-family", "unsupported relation family");
    }
    for (const auto &declaration : module->libraryIdentities)
      result.libraryIdentities.push_back(identity(declaration));
    if (module->libraryIdentities.size() > 1)
      fail(module->libraryIdentities[1], "source-library-identity",
           "a library root requires one identity");
    for (const auto &dependency : module->dependencies) {
      result.libraries.push_back({dependency.name,
                                  identity(dependency.identity),
                                  dependency.location});
      if (!libraries.insert(dependency.name).second)
        fail(dependency, "source-dependency-duplicate",
             "duplicate library dependency alias");
    }
  } else {
    result.form = SourceForm::Construction;
    result.location = std::get<source::Construction>(*parsed.content).location;
  }
  result.complete = parsed.complete() && result.recoverable;
  return result;
}
} // namespace zkc::frontend
