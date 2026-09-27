#ifndef ZKC_FRONTEND_LIBRARY_CALLABLE_H
#define ZKC_FRONTEND_LIBRARY_CALLABLE_H
#include "Internal.h"

namespace zkc::frontend::library::detail {
// Simultaneous substitution: actuals belong to the caller's scope, including
// when caller and callee use the same parameter declaration.
inline llvm::Expected<StaticTerm> actual(const StaticTerm &t,
                                         const Substitution &s) {
  for (const auto &a : s.statics)
    if (identity(t) == identity(a.first))
      return a.second;
  if (t.kind == StaticTerm::Kind::Root)
    for (const auto &a : s.types)
      if (identity(t.declaration) == identity(a.first))
        return logicalTypeTerm(a.second);
  StaticTerm out = t;
  for (auto &a : out.arguments) {
    auto selected = actual(a, s);
    if (!selected)
      return selected.takeError();
    a = *selected;
  }
  return out;
}
inline llvm::Expected<Type> actual(const Type &t, const Substitution &s) {
  if (t.kind == Type::Kind::Parameter)
    for (const auto &a : s.types)
      if (identity(t.declaration) == identity(a.first))
        return a.second;
  Type out = t;
  for (auto &a : out.arguments) {
    auto selected = actual(a, s);
    if (!selected)
      return selected.takeError();
    a = *selected;
  }
  for (auto &a : out.elements) {
    auto selected = actual(a, s);
    if (!selected)
      return selected.takeError();
    a = *selected;
  }
  return out;
}
inline llvm::Expected<Signature> actual(Signature s, const Substitution &sub) {
  for (auto *ps : {&s.inputs, &s.outputs})
    for (auto &p : *ps) {
      auto selected = actual(p.type, sub);
      if (!selected)
        return selected.takeError();
      p.type = *selected;
    }
  for (auto *rs : {&s.preconditions, &s.postconditions})
    for (auto &r : *rs)
      for (auto &a : r.arguments) {
        auto selected = actual(a, sub);
        if (!selected)
          return selected.takeError();
        a = *selected;
      }
  return s;
}
inline std::string callableShape(const CallableDecl &d) {
  Body b;
  b.id = d.id;
  b.signature = d.signature;
  b.typeBounds = d.typeBounds;
  Writer w;
  w.add(encode(b));
  w.list(d.parameters, [&](const auto &p) { w.add(identity(p)); });
  w.list(d.imports, [&](const auto &i) {
    w.add(identity(i.parameter));
    w.add(i.interface.identity());
  });
  return w.bytes;
}
} // namespace zkc::frontend::library::detail
#endif
