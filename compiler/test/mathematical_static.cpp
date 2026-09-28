#include "zkc/Mathematical/Static.h"
#include "llvm/Support/raw_ostream.h"
#include <limits>

using namespace llvm;
using namespace zkc::mathematical;
namespace {
bool sameNormalForm(const Static &left, const Static &right, uint64_t arity) {
  AdmissionBudget budget;
  auto a = normalize(left, arity, budget), b = normalize(right, arity, budget);
  if (!a) {
    errs() << toString(a.takeError());
    return false;
  }
  if (!b) {
    errs() << toString(b.takeError());
    return false;
  }
  return *a == *b;
}
template <class T> bool refused(Expected<T> value) {
  if (value)
    return false;
  consumeError(value.takeError());
  return true;
}
} // namespace
int main() {
  auto x = Static::parameter(0), y = Static::parameter(1),
       z = Static::parameter(2);
  if (!sameNormalForm(
          Static::multiply(x, Static::add(y, z)),
          Static::add(Static::multiply(y, x), Static::multiply(x, z)), 3) ||
      !sameNormalForm(Static::add(x, x),
                      Static::multiply(Static::literal(2), x), 1) ||
      !sameNormalForm(Static::multiply(Static::literal(0), x),
                      Static::literal(0), 1) ||
      !sameNormalForm(Static::pow2(Static::add(x, y)),
                      Static::pow2(Static::add(y, x)), 2) ||
      !sameNormalForm(Static::pow2(Static::literal(3)), Static::literal(8), 0))
    return 1;
  AdmissionBudget budget;
  auto applied = evaluate(Static::add(Static::pow2(x), y), {4, 3}, budget);
  if (!applied) {
    errs() << toString(applied.takeError());
    return 1;
  }
  if (*applied != 19)
    return 1;
  if (!refused(normalize(x, 0, budget)) ||
      !refused(evaluate(Static::pow2(Static::literal(64)), {}, budget)) ||
      !refused(evaluate(
          Static::add(Static::literal(std::numeric_limits<uint64_t>::max()),
                      Static::literal(1)),
          {}, budget)) ||
      !refused(evaluate(Static::multiply(Static::literal(uint64_t(1) << 63),
                                         Static::literal(2)),
                        {}, budget)))
    return 1;
  // Malformed syntax is checked even when multiplication would erase it.
  if (!refused(normalize(Static::multiply(Static::literal(0), y), 1, budget)))
    return 1;
  Static expanding = Static::literal(1);
  for (uint64_t i = 0; i < 20; ++i)
    expanding =
        Static::multiply(std::move(expanding),
                         Static::add(Static::parameter(i), Static::literal(1)));
  AdmissionBudget limited{2000};
  if (!refused(normalize(expanding, 20, limited)))
    return 1;
  // Long symbolic exponent keys remain bounded when substituted into a
  // multiplication. Counting only atoms would admit these repeated byte copies.
  Static exponent = Static::literal(0);
  for (uint64_t i = 0; i < 32; ++i)
    exponent = Static::add(std::move(exponent), Static::parameter(i));
  AdmissionBudget atomBudget;
  auto atom = normalize(Static::pow2(std::move(exponent)), 32, atomBudget);
  if (!atom) {
    errs() << toString(atom.takeError());
    return 1;
  }
  auto key = atom->key(atomBudget);
  if (!key) {
    errs() << toString(key.takeError());
    return 1;
  }
  AdmissionBudget copyBudget{2 * key->size() + 64};
  if (!refused(normalize(Static::multiply(x, x), {*atom}, copyBudget)))
    return 1;
  AdmissionBudget hugeArity;
  if (!refused(normalize(x, std::numeric_limits<uint64_t>::max(), hugeArity)))
    return 1;
  outs() << "scoped substitution, polynomial normalization and overflow/work "
            "controls passed\n";
}
