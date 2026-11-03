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
  using RC = RefusalClass;
  static constexpr size_t byteLimit = artifactByteLimit;
  std::string problem;
  std::string detail;
  RefusalClass problemClass = RC::Syntax;
  size_t nodes = 0;
  bool projected = false;
  bool nativeIR = false;
  // Selected-control tags share names across body kinds but differ in their
  // capture field. A record is serializable only within its own body kind.
  bool participantBody = false;

  void fail(RefusalClass kind, StringRef code, StringRef reason = {}) {
    if (problem.empty()) {
      problem = code.str();
      detail = reason.str();
      problemClass = kind;
    }
  }
  size_t add(size_t a, size_t b) {
    if (a > byteLimit || b > byteLimit - a) {
      fail(RC::Capacity, "source-limit",
           "compact program exceeds artifact byte limit");
      return byteLimit + 1;
    }
    return a + b;
  }
  void node() {
    if (++nodes > artifactNodeLimit)
      fail(RC::Capacity, "source-limit", "program exceeds artifact node limit");
  }
  size_t text(StringRef value, size_t limit = stringByteLimit) {
    node();
    if (value.size() > limit)
      fail(RC::Capacity, "source-limit",
           "program string exceeds its field byte limit");
    if (!json::isUTF8(value))
      fail(RC::Syntax, "source-string");
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
    node();
    size_t bytes = 2 + (values.size() ? values.size() - 1 : 0);
    for (size_t value : values)
      bytes = add(bytes, value);
    return bytes;
  }
  /// Counts a list against its own bound before measuring its elements.
  template <typename T, typename F>
  size_t list(const T &values, size_t limit, F f) {
    node();
    if (values.size() > arrayElementLimit) {
      fail(RC::Capacity, "source-limit",
           "program container exceeds 32768 elements");
      return byteLimit + 1;
    }
    if (values.size() > limit) {
      fail(RC::Capacity, "interactive-list-limit",
           "program list exceeds its entry bound");
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
  size_t names(const Names &values, size_t limit = listEntryLimit,
               size_t bytes = stringByteLimit) {
    return list(values, limit, [&](const auto &s) { return text(s, bytes); });
  }
  size_t pairs(const protocol::Assignments &values,
               size_t limit = listEntryLimit) {
    return list(values, limit, [&](const auto &p) {
      return fields({text(p.first), text(p.second)});
    });
  }
  size_t captures(const Names &values) { return names(values); }
  size_t captures(const protocol::Assignments &values) { return pairs(values); }
  size_t parameters(const std::vector<Parameter> &values) {
    return list(values, listEntryLimit, [&](const auto &p) {
      return fields({text(p.name), text(p.type)});
    });
  }
  size_t body(const Body &value, unsigned depth = 0) {
    if (depth > bodyNestingLimit) {
      fail(RC::Capacity, "interactive-body-depth");
      return byteLimit + 1;
    }
    return list(value, arrayElementLimit, [&](const Instruction &i) {
      if ((i.get<Return>() || i.get<Yield>() || i.get<Release>()) &&
          !i.site.empty())
        fail(RC::Syntax, "source-model-shape");
      return std::visit(
          [&](const auto &op) -> size_t {
            using T = std::decay_t<decltype(op)>;
            size_t tag = 0;
            if constexpr (std::is_same_v<T, For>)
              tag = text(op.conditional ? "for_while" : "for");
            else
              tag = text(i.kind());
            if constexpr (std::is_same_v<T, Return> ||
                          std::is_same_v<T, Yield> ||
                          std::is_same_v<T, Release>)
              return fields({tag, names(op.values)});
            else if constexpr (std::is_same_v<T, ReturnIf>) {
              if (!projected)
                fail(RC::Syntax, "interactive-return-type");
              return fields({tag, text(i.site), text(op.condition),
                             names(op.values), names(op.continuations)});
            } else if constexpr (std::is_same_v<T, Operation>) {
              return fields(
                  {tag, text(i.site), text(op.callee),
                   names(op.attributes, attributeLimit, parameterByteLimit),
                   names(op.inputs), names(op.outputs)});
            } else if constexpr (std::is_same_v<T, BooleanConstant>) {
              node();
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
                fail(RC::Syntax, "algorithm-call-context");
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
            else if constexpr (std::is_same_v<T, Match> ||
                               std::is_same_v<T, ParticipantMatch>) {
              if (participantBody != std::is_same_v<T, ParticipantMatch>)
                fail(RC::Syntax, "source-model-shape");
              if (op.arms.size() > matchAlternativeLimit)
                fail(RC::Capacity, participantBody ? "interactive-match-shape"
                                                   : "local-match-shape");
              return fields({tag, text(i.site), text(op.input),
                             captures(op.captures),
                             list(op.arms, matchAlternativeLimit,
                                  [&](const MatchArm &arm) {
                                    return fields({text(arm.alternative),
                                                   names(arm.payload),
                                                   body(arm.body, depth + 1)});
                                  }),
                             names(op.outputs)});
            } else if constexpr (std::is_same_v<T, Conditional> ||
                                 std::is_same_v<T, ParticipantConditional>) {
              if (participantBody != std::is_same_v<T, ParticipantConditional>)
                fail(RC::Syntax, "source-model-shape");
              return fields({tag, text(i.site), text(op.condition),
                             captures(op.captures),
                             body(op.thenBody, depth + 1),
                             body(op.elseBody, depth + 1), names(op.outputs)});
            } else if constexpr (std::is_same_v<T, For>) {
              return fields({tag, text(i.site), text(op.induction),
                             text(op.lower), text(op.upper), pairs(op.carried),
                             names(op.captures), body(op.body, depth + 1),
                             names(op.outputs)});
            } else {
              static_assert(std::is_same_v<T, Loop>);
              if (!projected)
                fail(RC::Syntax, "interactive-loop-count");
              if (op.count.maximum > loopMaximumLimit)
                fail(RC::Capacity, "interactive-loop-count");
              size_t count = fields({text("value"), text(op.count.value),
                                     text(std::to_string(op.count.maximum)),
                                     text(op.count.induction)});
              return fields({tag, text(i.site), count, pairs(op.carried),
                             pairs(op.captures), body(op.body, depth + 1),
                             names(op.outputs)});
            }
          },
          i.value);
    });
  }
  size_t function(const Function &f) {
    if (!f.origin)
      fail(RC::Syntax, "binding-logical-origin");
    size_t out =
        fields({text("function"), text(f.name), parameters(f.arguments),
                names(f.results), body(f.body)});
    if (f.origin)
      out = add(
          out, 1 + fields({text(f.origin->definition),
                           pairs(f.origin->arguments, originAssignmentLimit)}));
    return out;
  }
  template <typename T> size_t environment(const T &m) {
    return list(
        m.bindings, bindingLimit, [&](const protocol::OperationBinding &b) {
          return fields(
              {text(b.name), text(b.application.contract),
               names(b.application.arguments, bindingArgumentLimit),
               text(b.application.implementation),
               names(b.application.physicalArguments, bindingArgumentLimit)});
        });
  }
  size_t measure(const LocalDefinitions &m) {
    return fields(
        {environment(m), list(m.functions, definitionLimit,
                              [&](const auto &f) { return function(f); })});
  }
  size_t measure(const Participants &m) {
    projected = true;
    if (!nativeIR && m.stage == Participants::Stage::Logical)
      fail(RC::UnsupportedProfile, "native-physical-required");
    if (m.stage != Participants::Stage::Logical &&
        m.stage != Participants::Stage::Physical)
      fail(RC::Syntax, "source-model-shape");
    if (m.functions.size() + m.participants.size() > definitionLimit)
      fail(RC::Capacity, "interactive-definition-limit");
    return fields(
        {text("zkc.program/0"), environment(m),
         list(m.functions, definitionLimit,
              [&](const auto &f) { return function(f); }),
         list(m.participants, definitionLimit,
              [&](const Participant &p) {
                participantBody = true;
                auto bytes =
                    fields({text("participant"), text(p.name), text(p.instance),
                            text(p.role), parameters(p.arguments),
                            names(p.results), body(p.body)});
                participantBody = false;
                bytes =
                    add(bytes,
                        1 + list(p.services, listEntryLimit,
                                 [&](const ServicePort &port) {
                                   return fields(
                                       {text(port.name), text(port.contract),
                                        text(std::to_string(port.inputIndex))});
                                 }));
                return bytes;
              }),
         list(m.entries, entryLimit, [&](const ParticipantEntry &e) {
           return fields({text("entry"), text(e.name), pairs(e.participants)});
         })});
  }

public:
  // Reconstructed IR may precede physical selection. Interchange accepts only
  // physical programs. Participant programs reject unresolved LocalApply edges.
  explicit Structure(bool allowNativeIR = false) : nativeIR(allowNativeIR) {}
  template <typename T> Error run(const T &value) {
    measure(value);
    return problem.empty() ? Error::success()
                           : refuse(problemClass, problem, detail);
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
