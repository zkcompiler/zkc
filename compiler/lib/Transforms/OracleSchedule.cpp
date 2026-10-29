#include "OracleSchedule.h"

namespace zkc::protocol {
OracleObservationSummary::OracleObservationSummary()
    : normal{1, 2, 4}, stopped{} {}
OracleObservationSummary OracleObservationSummary::query() {
  return {{2, 2, 4}, {}};
}
OracleObservationSummary OracleObservationSummary::draw() {
  return {{1, 4, 4}, {}};
}
OracleObservationSummary OracleObservationSummary::stop() {
  return {{}, {1, 2, 4}};
}
OracleObservationSummary
OracleObservationSummary::either(const OracleObservationSummary &other) const {
  auto result = *this;
  for (unsigned state = 0; state < normal.size(); ++state) {
    result.normal[state] |= other.normal[state];
    result.stopped[state] |= other.stopped[state];
  }
  return result;
}
OracleObservationSummary
OracleObservationSummary::then(const OracleObservationSummary &other) const {
  OracleObservationSummary result({}, stopped);
  for (unsigned state = 0; state < normal.size(); ++state)
    for (unsigned next = 0; next < normal.size(); ++next)
      if (normal[state] & (1u << next)) {
        result.normal[state] |= other.normal[next];
        result.stopped[state] |= other.stopped[next];
      }
  return result;
}
OracleObservationSummary
OracleObservationSummary::repeat(uint64_t count) const {
  OracleObservationSummary result, power = *this;
  // Boolean relation composition is associative. Exponentiation bounds the
  // analysis work even when a checked runtime count has a large maximum.
  while (count) {
    if (count & 1)
      result = result.then(power);
    count >>= 1;
    if (count)
      power = power.then(power);
  }
  return result;
}
OracleObservationSummary
OracleObservationSummary::repeatAtMost(uint64_t maximum) const {
  // Choosing empty work independently in each slot generates every count
  // 0..maximum. Termination remains absorbing under sequential composition.
  return OracleObservationSummary().either(*this).repeat(maximum);
}
bool OracleObservationSummary::queryBeforeDraw() const {
  return (normal[0] | stopped[0]) & 4;
}
} // namespace zkc::protocol
