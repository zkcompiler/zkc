#include "BodyCheck.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
namespace {
bool prefix(ArrayRef<unsigned> a, ArrayRef<unsigned> b) {
  return a.size() <= b.size() && std::equal(a.begin(), a.end(), b.begin());
}
} // namespace
bool BodyChecker::use(ValueId value, Span span, ArrayRef<unsigned> path) {
  if (!checker.types.charge(path.size() + 1, span))
    return false;
  auto type = projected(body.values[value.index].type, path, span);
  if (!type)
    return false;
  auto caps = checker.types.permissions(*type, span, &decl);
  if (!caps)
    return false;
  auto &state = uses[value.index];
  for (auto &moved : state.moved) {
    if (!checker.types.charge(moved.size() + 1, span))
      return false;
    if (prefix(moved, path) || prefix(path, moved))
      return fail("source.move", "value or overlapping field was already moved",
                  span);
  }
  state.used.emplace_back(path.begin(), path.end());
  if (!caps->copy)
    state.moved.emplace_back(path.begin(), path.end());
  return true;
}
bool BodyChecker::finish(Span span) {
  if (body.stopped)
    return true;
  for (unsigned i = 0; i < body.values.size(); ++i)
    if (!finishValue(ValueId{i}, span))
      return false;
  return true;
}
bool BodyChecker::finishValue(ValueId value, Span span) {
  auto &state = uses[value.index];
  std::function<bool(const Type &, std::vector<unsigned>, unsigned)> check =
      [&](const Type &t, std::vector<unsigned> path, unsigned depth) {
        if (depth > checker.work.limits.typeDepth ||
            !checker.types.charge(1, span))
          return checker.types.diagnostic
                     ? false
                     : fail("source.limit", "resource obligation depth", span);
        auto caps = checker.types.permissions(t, span, &decl);
        if (!caps)
          return false;
        if (caps->drop)
          return true;
        for (auto &used : state.used) {
          if (!checker.types.charge(used.size() + 1, span))
            return false;
          if (prefix(used, path))
            return true;
        }
        if (!restricted(t) &&
            (t.kind == Type::Kind::Record || t.kind == Type::Kind::Tuple ||
             (t.kind == Type::Kind::Array && t.dimension.isClosed()))) {
          auto fs = checker.types.fields(t, span);
          if (!fs)
            return false;
          if (!fs->empty()) {
            for (unsigned j = 0; j < fs->size(); ++j) {
              auto child = path;
              child.push_back(j);
              if (!check((*fs)[j].type, std::move(child), depth + 1))
                return false;
            }
            return true;
          }
        }
        return fail("source.drop",
                    "value without Drop remains unused on a continuing path",
                    body.values[value.index].span);
      };
  return check(body.values[value.index].type, {}, 1);
}
bool BodyChecker::available(ValueId value, ArrayRef<unsigned> path) {
  for (const auto &moved : uses[value.index].moved) {
    if (!checker.types.charge(moved.size() + path.size() + 1,
                              body.values[value.index].span) ||
        prefix(moved, path) || prefix(path, moved))
      return false;
  }
  return true;
}
bool BodyChecker::intersectUses(Uses &common, const Uses &other, Span span) {
  std::vector<std::vector<unsigned>> paths;
  for (const auto &a : common.used)
    for (const auto &b : other.used) {
      if (!checker.types.charge(a.size() + b.size() + 1, span))
        return false;
      if (prefix(a, b))
        paths.push_back(b);
      else if (prefix(b, a))
        paths.push_back(a);
    }
  std::sort(paths.begin(), paths.end());
  common.used.clear();
  for (auto &path : paths)
    if (common.used.empty() || !prefix(common.used.back(), path))
      common.used.push_back(std::move(path));
  return true;
}
} // namespace zkc::language::detail
