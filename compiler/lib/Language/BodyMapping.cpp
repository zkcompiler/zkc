#include "BodyMapping.h"
using namespace llvm;
namespace zkc::language::detail {
void mapBodyValues(Body &body, const std::function<ValueId(ValueId)> &map) {
  auto list = [&](std::vector<ValueId> &values) {
    for (auto &value : values)
      value = map(value);
  };
  list(body.results);
  for (auto &[id, value] : body.expressionValues)
    value = map(value);
  for (auto &domain : body.domainBindings)
    list(domain.operands);
  for (auto &binding : body.scopedBindings)
    list(binding.captures);
  for (auto &op : body.operations) {
    list(op.results);
    if (op.binding)
      list(op.binding->operands);
    // Reduction expression witnesses refer to the extracted helper's SSA,
    // which has a separate value space from this enclosing body.
    std::visit(
        [&](auto &action) {
          using T = std::decay_t<decltype(action)>;
          if constexpr (std::is_same_v<T, MathValue> ||
                        std::is_same_v<T, HelperCall> ||
                        std::is_same_v<T, BulkApplication> ||
                        std::is_same_v<T, ProtocolApplication> ||
                        std::is_same_v<T, Construct> ||
                        std::is_same_v<T, LocalPrimitive> ||
                        std::is_same_v<T, LocalControl> ||
                        std::is_same_v<T, ScopedInvoke>)
            list(action.operands);
          else if constexpr (std::is_same_v<T, Projection> ||
                             std::is_same_v<T, Consume> ||
                             std::is_same_v<T, Restriction>)
            action.input = map(action.input);
          else if constexpr (std::is_same_v<T, Require>)
            action.condition = map(action.condition);
          else if constexpr (std::is_same_v<T, ProtocolCompletion>) {
            action.condition = map(action.condition);
            list(action.values);
          } else if constexpr (std::is_same_v<T, Exchange>)
            action.payload = map(action.payload);
          else if constexpr (std::is_same_v<T, ProtocolRepeat>) {
            action.count = map(action.count);
            list(action.carried);
            list(action.captures);
          }
        },
        op.action);
  }
}
std::vector<ValueId> appendBodyInputs(Body &body, ArrayRef<Value> inputs) {
  auto prior = body.inputs;
  auto count = unsigned(inputs.size());
  mapBodyValues(body, [&](ValueId value) {
    return ValueId{value.index < prior ? value.index : value.index + count};
  });
  body.values.insert(body.values.begin() + prior, inputs.begin(), inputs.end());
  std::vector<ValueId> result;
  for (unsigned i = 0; i < count; ++i) {
    result.push_back({prior + i});
    if (body.mode == Body::Mode::Math)
      body.values[prior + i].components = {prior + i};
  }
  body.inputs += count;
  return result;
}
} // namespace zkc::language::detail
