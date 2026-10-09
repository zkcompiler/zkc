#include "zkc/Program/Codec.h"
#include "llvm/Support/ErrorHandling.h"
#include <type_traits>

using namespace llvm;
namespace zkc::program {
namespace {
using A = json::Array;
using V = json::Value;
class Encoder {
  template <typename T, typename F> A list(const T &values, F f) {
    A result;
    result.reserve(values.size());
    for (size_t i = 0; i < values.size(); ++i)
      result.push_back(f(values[i]));
    return result;
  }
  A names(const Names &values) {
    return list(values, [](const std::string &s) -> V { return s; });
  }
  A pairs(const protocol::Assignments &values) {
    return list(values,
                [](const auto &p) -> V { return A{p.first, p.second}; });
  }
  A parameters(const std::vector<Parameter> &values) {
    return list(values,
                [](const Parameter &p) -> V { return A{p.name, p.type}; });
  }
  A body(const Body &values) {
    return list(values, [&](const Instruction &i) { return instruction(i); });
  }
  V instruction(const Instruction &i) {
    return std::visit(
        [&](const auto &op) -> V {
          using T = std::decay_t<decltype(op)>;
          if constexpr (std::is_same_v<T, Return> || std::is_same_v<T, Yield> ||
                        std::is_same_v<T, Release>) {
            return A{i.kind().str(), names(op.values)};
          } else if constexpr (std::is_same_v<T, BooleanConstant>) {
            return A{"bool_constant", i.site, op.output, op.value};
          } else if constexpr (std::is_same_v<T, ServiceQuery>) {
            return A{"query",   i.site,           op.port,
                     op.method, names(op.inputs), names(op.outputs)};
          } else if constexpr (std::is_same_v<T, ReturnIf>) {
            return A{"return_if", i.site, op.condition, names(op.values),
                     names(op.continuations)};
          } else if constexpr (std::is_same_v<T, Operation>) {
            A result{"op", i.site, op.callee};
            result.push_back(names(op.attributes));
            result.push_back(names(op.inputs));
            result.push_back(names(op.outputs));
            return result;
          } else if constexpr (std::is_same_v<T, LocalCall>) {
            A result{"local", i.site};
            result.push_back(op.callee);
            result.push_back(names(op.inputs));
            result.push_back(names(op.outputs));
            return result;
          } else if constexpr (std::is_same_v<T, LocalApply>) {
            report_fatal_error("algorithm-call-context: unexpanded program");
          } else if constexpr (std::is_same_v<T, Send>) {
            return A{"send", i.site, op.schema, op.peer, op.input};
          } else if constexpr (std::is_same_v<T, Receive>) {
            return A{"receive", i.site, op.schema, op.peer, op.output, op.type};
          } else if constexpr (std::is_same_v<T, Stop>) {
            return A{"stop", i.site, op.reason};
          } else if constexpr (std::is_same_v<T, VariantConstruct>) {
            return A{"variant",         i.site,   op.type, op.alternative,
                     names(op.payload), op.output};
          } else if constexpr (std::is_same_v<T, Match>) {
            return A{"match",
                     i.site,
                     op.input,
                     names(op.captures),
                     list(op.arms,
                          [&](const MatchArm &arm) -> V {
                            return A{arm.alternative, names(arm.payload),
                                     body(arm.body)};
                          }),
                     names(op.outputs)};
          } else if constexpr (std::is_same_v<T, Conditional>) {
            return A{"if",
                     i.site,
                     op.condition,
                     names(op.captures),
                     body(op.thenBody),
                     body(op.elseBody),
                     names(op.outputs)};
          } else if constexpr (std::is_same_v<T, For>) {
            return A{op.conditional ? "for_while" : "for",
                     i.site,
                     op.induction,
                     op.lower,
                     op.upper,
                     pairs(op.carried),
                     names(op.captures),
                     body(op.body),
                     names(op.outputs)};
          } else {
            V count = A{"value", op.count.value,
                        std::to_string(op.count.maximum), op.count.induction};
            return A{"loop",
                     i.site,
                     std::move(count),
                     pairs(op.carried),
                     names(op.captures),
                     body(op.body),
                     names(op.outputs)};
          }
        },
        i.value);
  }
  V function(const Function &f) {
    A out{"function", f.name, parameters(f.arguments), names(f.results),
          body(f.body)};
    if (f.origin)
      out.push_back(A{f.origin->definition, pairs(f.origin->arguments)});
    return out;
  }
  V binding(const protocol::OperationBinding &b) {
    return A{b.name, b.application.contract, names(b.application.arguments),
             b.application.implementation};
  }
  template <typename T> V environment(const T &m) {
    return list(m.bindings, [&](const auto &b) { return binding(b); });
  }

public:
  V run(const Participants &m) {
    if (m.stage != Participants::Stage::Physical)
      report_fatal_error("native-physical-required: unchecked program");

    auto participants = list(m.participants, [&](const Participant &p) -> V {
      A record{"participant",           p.name,           p.instance,  p.role,
               parameters(p.arguments), names(p.results), body(p.body)};
      record.push_back(list(p.services, [](const ServicePort &port) -> V {
        return A{port.name, port.contract, std::to_string(port.inputIndex)};
      }));
      return record;
    });
    auto entries = list(m.entries, [&](const ParticipantEntry &e) -> V {
      return A{"entry", e.name, pairs(e.participants)};
    });
    return A{"zkc.program/0", environment(m),
             list(m.functions, [&](const auto &f) { return function(f); }),
             std::move(participants), std::move(entries)};
  }
};
} // namespace
json::Value encode(const Participants &m) { return Encoder().run(m); }
} // namespace zkc::program
