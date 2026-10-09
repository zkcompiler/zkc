#include "Structure.h"
#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include <type_traits>

using namespace llvm;
namespace zkc::program {
namespace {
/// Count the exact compact interchange encoding without constructing JSON.
/// The same traversal checks UTF-8, bounded containers and non-serializable
/// combinations that a programmatic author could otherwise create.
class Structure {
  static constexpr size_t byteLimit = 1024 * 1024;
  std::string problem;
  bool projected = false;
  bool nativeIR = false;

  void fail(StringRef code) {
    if (problem.empty())
      problem = code.str();
  }
  size_t add(size_t a, size_t b) {
    if (a > byteLimit || b > byteLimit - a) {
      fail("source-limit");
      return byteLimit + 1;
    }
    return a + b;
  }
  size_t text(StringRef value) {
    if (!json::isUTF8(value))
      fail("source-string");
    size_t bytes = 2;
    for (unsigned char c : value.bytes()) {
      size_t length = 1;
      if (c == '"' || c == '\\' || c == '\n' || c == '\r' || c == '\t')
        length = 2;
      else if (c < 32)
        length = 6;
      bytes = add(bytes, length);
      if (bytes > byteLimit)
        break;
    }
    return bytes;
  }
  size_t fields(std::initializer_list<size_t> values) {
    size_t bytes = 2 + (values.size() ? values.size() - 1 : 0);
    for (size_t value : values)
      bytes = add(bytes, value);
    return bytes;
  }
  template <typename T, typename F> size_t list(const T &values, F f) {
    if (values.size() > 32768) {
      fail("source-limit");
      return byteLimit + 1;
    }
    size_t bytes = 2 + (values.empty() ? 0 : values.size() - 1);
    for (const auto &value : values) {
      if (!problem.empty())
        break;
      bytes = add(bytes, f(value));
    }
    return bytes;
  }
  size_t names(const Names &values) {
    return list(values, [&](const auto &s) { return text(s); });
  }
  size_t pairs(const protocol::Assignments &values) {
    return list(values, [&](const auto &p) {
      return fields({text(p.first), text(p.second)});
    });
  }
  size_t parameters(const std::vector<Parameter> &values) {
    return list(values, [&](const auto &p) {
      return fields({text(p.name), text(p.type)});
    });
  }
  size_t body(const Body &value, unsigned depth = 0) {
    if (depth > 64) {
      fail("interactive-body");
      return byteLimit + 1;
    }
    return list(value, [&](const Instruction &i) {
      if ((i.get<Return>() || i.get<Yield>() || i.get<Release>()) &&
          !i.site.empty())
        fail("source-model-shape");
      return std::visit(
          [&](const auto &op) -> size_t {
            using T = std::decay_t<decltype(op)>;
            size_t tag = text(i.kind());
            if constexpr (std::is_same_v<T, Return> ||
                          std::is_same_v<T, Yield> ||
                          std::is_same_v<T, Release>)
              return fields({tag, names(op.values)});
            else if constexpr (std::is_same_v<T, ReturnIf>) {
              if (!projected)
                fail("interactive-return-type");
              return fields({tag, text(i.site), text(op.condition),
                             names(op.values), names(op.continuations)});
            } else if constexpr (std::is_same_v<T, Operation>) {
              return fields({tag, text(i.site), text(op.callee),
                             names(op.attributes), names(op.inputs),
                             names(op.outputs)});
            } else if constexpr (std::is_same_v<T, BooleanConstant>) {
              return fields(
                  {tag, text(i.site), text(op.output), op.value ? 4u : 5u});
            } else if constexpr (std::is_same_v<T, ServiceQuery>) {
              return fields({tag, text(i.site), text(op.port), text(op.method),
                             names(op.inputs), names(op.outputs)});
            } else if constexpr (std::is_same_v<T, LocalCall>) {
              return fields({tag, text(i.site), text(op.callee),
                             names(op.inputs), names(op.outputs)});
            } else if constexpr (std::is_same_v<T, LocalApply>) {
              if (projected)
                fail("algorithm-call-context");
              return fields({tag, text(i.site), text(op.callee),
                             names(op.inputs), names(op.outputs)});
            } else if constexpr (std::is_same_v<T, Send>)
              return fields({tag, text(i.site), text(op.schema), text(op.peer),
                             text(op.input)});
            else if constexpr (std::is_same_v<T, Receive>)
              return fields({tag, text(i.site), text(op.schema), text(op.peer),
                             text(op.output), text(op.type)});
            else if constexpr (std::is_same_v<T, Stop>) {
              return fields({tag, text(i.site), text(op.reason)});
            } else if constexpr (std::is_same_v<T, VariantConstruct>)
              return fields({tag, text(i.site), text(op.type),
                             text(op.alternative), names(op.payload),
                             text(op.output)});
            else if constexpr (std::is_same_v<T, Match>)
              return fields({tag, text(i.site), text(op.input),
                             names(op.captures),
                             list(op.arms,
                                  [&](const MatchArm &arm) {
                                    return fields({text(arm.alternative),
                                                   names(arm.payload),
                                                   body(arm.body, depth + 1)});
                                  }),
                             names(op.outputs)});
            else if constexpr (std::is_same_v<T, Conditional>)
              return fields({tag, text(i.site), text(op.condition),
                             names(op.captures), body(op.thenBody, depth + 1),
                             body(op.elseBody, depth + 1), names(op.outputs)});
            else if constexpr (std::is_same_v<T, For>) {
              return fields({text(op.conditional ? "for_while" : "for"),
                             text(i.site), text(op.induction), text(op.lower),
                             text(op.upper), pairs(op.carried),
                             names(op.captures), body(op.body, depth + 1),
                             names(op.outputs)});
            } else {
              if (!projected || op.count.maximum > 1048576)
                fail("interactive-loop-count");
              size_t count = fields({text("value"), text(op.count.value),
                                     text(std::to_string(op.count.maximum)),
                                     text(op.count.induction)});
              return fields({tag, text(i.site), count, pairs(op.carried),
                             names(op.captures), body(op.body, depth + 1),
                             names(op.outputs)});
            }
          },
          i.value);
    });
  }
  size_t function(const Function &f) {
    if (!f.origin)
      fail("binding-logical-origin");
    size_t out =
        fields({text("function"), text(f.name), parameters(f.arguments),
                names(f.results), body(f.body)});
    if (f.origin)
      out = add(out, 1 + fields({text(f.origin->definition),
                                 pairs(f.origin->arguments)}));
    return out;
  }
  template <typename T> size_t environment(const T &m) {
    return list(m.bindings, [&](const protocol::OperationBinding &b) {
      return fields({text(b.name), text(b.application.contract),
                     names(b.application.arguments),
                     text(b.application.implementation)});
    });
  }
  size_t measure(const LocalDefinitions &m) {
    return fields({environment(m), list(m.functions, [&](const auto &f) {
                     return function(f);
                   })});
  }
  size_t measure(const Participants &m) {
    projected = true;
    if (!nativeIR && m.stage == Participants::Stage::Logical)
      fail("native-physical-required");
    if (m.stage != Participants::Stage::Logical &&
        m.stage != Participants::Stage::Physical)
      fail("source-model-shape");
    return fields(
        {text("zkc.program/0"), environment(m),
         list(m.functions, [&](const auto &f) { return function(f); }),
         list(m.participants,
              [&](const Participant &p) {
                auto bytes =
                    fields({text("participant"), text(p.name), text(p.instance),
                            text(p.role), parameters(p.arguments),
                            names(p.results), body(p.body)});
                bytes = add(bytes,
                            1 + list(p.services, [&](const ServicePort &port) {
                              return fields(
                                  {text(port.name), text(port.contract),
                                   text(std::to_string(port.inputIndex))});
                            }));
                return bytes;
              }),
         list(m.entries, [&](const ParticipantEntry &e) {
           return fields({text("entry"), text(e.name), pairs(e.participants)});
         })});
  }

public:
  // Reconstructed IR may precede physical selection. Interchange accepts only
  // physical programs; local.apply remains internal to local definitions.
  explicit Structure(bool allowNativeIR = false) : nativeIR(allowNativeIR) {}
  template <typename T> Error run(const T &value) {
    measure(value);
    return problem.empty() ? Error::success() : error(problem);
  }
};
} // namespace
Error checkStructure(const Participants &m) { return Structure().run(m); }
Error detail::checkNativeIRStructure(const LocalDefinitions &m) {
  return Structure(true).run(m);
}
Error detail::checkNativeIRStructure(const Participants &m) {
  return Structure(true).run(m);
}
} // namespace zkc::program
