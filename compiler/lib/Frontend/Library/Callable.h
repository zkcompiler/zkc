#ifndef ZKC_FRONTEND_LIBRARY_CALLABLE_H
#define ZKC_FRONTEND_LIBRARY_CALLABLE_H
#include "Internal.h"

namespace zkc::frontend::library::detail {
// Simultaneous substitution: actuals belong to the caller's scope, including
// when caller and callee use the same parameter declaration.
inline StaticTerm actual(const StaticTerm &t, const Substitution &s) {
  for (const auto &a : s.statics)
    if (identity(t) == identity(a.first))
      return a.second;
  StaticTerm out = t;
  for (auto &a : out.arguments)
    a = actual(a, s);
  return out;
}
inline Type actual(const Type &t, const Substitution &s) {
  if (t.kind == Type::Kind::Parameter)
    for (const auto &a : s.types)
      if (identity(t.declaration) == identity(a.first))
        return a.second;
  Type out = t;
  for (auto &a : out.arguments)
    a = actual(a, s);
  for (auto &a : out.elements)
    a = actual(a, s);
  return out;
}
inline Signature actual(Signature s, const Substitution &sub) {
  for (auto *ps : {&s.inputs, &s.outputs})
    for (auto &p : *ps)
      p.type = actual(p.type, sub);
  for (auto *rs : {&s.preconditions, &s.postconditions})
    for (auto &r : *rs)
      for (auto &a : r.arguments)
        a = actual(a, sub);
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
