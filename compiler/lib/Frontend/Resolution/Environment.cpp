#include "Project.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::frontend::resolution {
library::Environment
Context::environment(const library::Environment &input,
                     const library::QualifiedDecl &owner) const {
  auto out = input;
  const auto *declaration = lookup(owner);
  if (!declaration || declaration->owner >= available.size())
    return {};
  const auto &allowed = available[declaration->owner];
  auto visible = [&](const library::QualifiedDecl &id) {
    if (const auto *d = lookup(id))
      return allowed.count(uint32_t(d - declarations.data())) != 0;
    // Installed declarations have a fixed owner and are independent of the
    // application graph. They are supplied by the compiler's contract catalog.
    return id.library.nameSpace == "zkc" &&
           id.library.name == "installed-contracts" &&
           id.library.version == "1" && id.library.resolution == "builtin";
  };
  for (auto &library : out.libraries) {
    llvm::erase_if(library.declarations,
                   [&](const auto &d) { return !visible(d); });
    llvm::sort(library.declarations, [&](const auto &a, const auto &b) {
      return library::identity(a) < library::identity(b);
    });
  }
  llvm::erase_if(out.libraries,
                 [](const auto &l) { return l.declarations.empty(); });
  llvm::sort(out.libraries, [](const auto &a, const auto &b) {
    return library::identity({a.id, {}, ""}) <
           library::identity({b.id, {}, ""});
  });
  llvm::erase_if(out.statics, [&](const auto &d) { return !visible(d.id); });
  llvm::sort(out.statics, [](const auto &a, const auto &b) {
    return library::identity(a.id) < library::identity(b.id);
  });
  return out;
}
} // namespace zkc::frontend::resolution
