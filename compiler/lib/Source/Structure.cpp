#include "zkc/Source/Codec.h"
#include "zkc/Source/Relations.h"
#include "zkc/Support/Json.h"
#include <type_traits>

using namespace llvm;
namespace zkc::source {
namespace {
/// Count the exact compact interchange encoding without constructing JSON.
/// The same traversal checks UTF-8, bounded containers and non-serializable
/// combinations that a programmatic author could otherwise create.
class Structure {
  static constexpr size_t byteLimit = 1024 * 1024;
  std::string problem;
  bool projected = false, generic = false;

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
      if (c == '"' || c == '\\' || c == '\b' || c == '\f' || c == '\n' ||
          c == '\r' || c == '\t')
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
  size_t pairs(const Assignments &values) {
    return list(values, [&](const auto &p) {
      return fields({text(p.first), text(p.second)});
    });
  }
  size_t pairs(const ParameterBindings &values) {
    return list(values, [&](const auto &p) {
      if (const auto *constant = std::get_if<std::string>(&p.second))
        return fields({text(p.first), text(*constant)});
      const auto &ingress = std::get<FamilyIngress>(p.second);
      return fields(
          {text(p.first),
           fields({text("ingress"), text(ingress.bound),
                   list(ingress.selectors, [&](const FamilySelector &s) {
                     return fields(
                         {text(s.role), text(s.function), names(s.arguments)});
                   })})});
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
            else if constexpr (std::is_same_v<T, Operation>) {
              if (!generic && !op.staticArguments.empty())
                fail("source-model-shape");
              if (generic)
                return fields({tag, text(i.site), text(op.callee),
                               names(op.staticArguments), names(op.attributes),
                               names(op.inputs), names(op.outputs)});
              return fields({tag, text(i.site), text(op.callee),
                             names(op.attributes), names(op.inputs),
                             names(op.outputs)});
            } else if constexpr (std::is_same_v<T, LocalCall>) {
              if (projected) {
                if (!op.role.empty())
                  fail("source-model-shape");
                return fields({tag, text(i.site), text(op.callee),
                               names(op.inputs), names(op.outputs)});
              }
              return fields({tag, text(i.site), text(op.role), text(op.callee),
                             names(op.inputs), names(op.outputs)});
            } else if constexpr (std::is_same_v<T, AlgorithmCall>)
              return fields({tag, text(i.site), text(op.callee),
                             names(op.staticArguments), names(op.inputs),
                             names(op.outputs)});
            else if constexpr (std::is_same_v<T, ProtocolCall>)
              return fields({tag, text(i.site), text(op.callee),
                             names(op.inputs), names(op.outputs)});
            else if constexpr (std::is_same_v<T, Message>)
              return fields({tag, text(i.site), text(op.schema),
                             text(op.sender), text(op.receiver), text(op.input),
                             text(op.output)});
            else if constexpr (std::is_same_v<T, Send>)
              return fields({tag, text(i.site), text(op.schema), text(op.peer),
                             text(op.input)});
            else if constexpr (std::is_same_v<T, Receive>)
              return fields({tag, text(i.site), text(op.schema), text(op.peer),
                             text(op.output), text(op.type)});
            else if constexpr (std::is_same_v<T, Stop>) {
              if (projected) {
                if (!op.role.empty())
                  fail("source-model-shape");
                return fields({tag, text(i.site), text(op.reason)});
              }
              return fields(
                  {tag, text(i.site), text(op.role), text(op.reason)});
            } else if constexpr (std::is_same_v<T, Incomplete>)
              return fields({tag, text(i.site)});
            else if constexpr (std::is_same_v<T, VariantConstruct>)
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
            else if constexpr (std::is_same_v<T, For>)
              return fields({tag, text(i.site), text(op.induction),
                             text(op.lower), text(op.upper), pairs(op.carried),
                             names(op.captures), body(op.body, depth + 1),
                             names(op.outputs)});
            else {
              if (op.count.kind != LoopCount::Kind::Constant &&
                  op.count.kind != LoopCount::Kind::Parameter)
                fail("source-model-shape");
              size_t count =
                  projected && op.count.kind == LoopCount::Kind::Constant
                      ? text(op.count.value)
                      : fields({text(op.count.kind == LoopCount::Kind::Parameter
                                         ? "parameter"
                                         : "constant"),
                                text(op.count.value)});
              return fields({tag, text(i.site), count, pairs(op.carried),
                             names(op.captures), body(op.body, depth + 1),
                             names(op.outputs)});
            }
          },
          i.value);
    });
  }
  size_t optionalBody(const std::optional<Body> &value) {
    return value ? body(*value) : text("external");
  }
  size_t function(const Function &f) {
    if (!f.origin)
      fail("binding-logical-origin");
    size_t out =
        fields({text("function"), text(f.name), parameters(f.arguments),
                names(f.results), optionalBody(f.body)});
    if (f.origin)
      out = add(out, 1 + fields({text(f.origin->definition),
                                 pairs(f.origin->arguments)}));
    return out;
  }
  template <typename T> size_t environment(const T &m) {
    return list(m.bindings, [&](const OperationBinding &b) {
      return fields({text(b.name), text(b.application.contract),
                     names(b.application.arguments),
                     text(b.application.implementation)});
    });
  }
  size_t definition(const GenericFunction &f) {
    size_t params = list(f.parameters, [&](const StaticParameter &p) {
      return fields({text(p.name), text(p.sort)});
    });
    size_t requirements = list(f.requirements, [&](const Requirement &r) {
      return fields({text(r.predicate), names(r.arguments)});
    });
    generic = true;
    size_t contents = body(f.body);
    generic = false;
    return fields({text("generic_function"), text(f.name), params, requirements,
                   parameters(f.arguments), names(f.results), contents});
  }
  size_t measure(const Module &m) {
    if (!m.relations.empty() || !m.relationViews.empty()) {
      auto authored = relation::authoredSource(m);
      if (!authored) {
        fail(toString(authored.takeError()));
        return byteLimit + 1;
      }
      return measure(*authored);
    }
    size_t common = fields(
        {text("zkc.protocol/1"), environment(m),
         list(m.functions, [&](const auto &f) { return function(f); }),
         list(m.protocols,
              [&](const Protocol &p) {
                return fields(
                    {text("protocol"), text(p.name), names(p.roles),
                     names(p.parameters),
                     list(p.arguments,
                          [&](const OwnedParameter &v) {
                            return fields(
                                {text(v.name), text(v.role), text(v.type)});
                          }),
                     list(p.results,
                          [&](const OwnedResult &v) {
                            return fields({text(v.role), text(v.type)});
                          }),
                     list(p.dependencies,
                          [&](const Dependency &d) {
                            return fields({text(d.name), text(d.protocol),
                                           pairs(d.agreements)});
                          }),
                     optionalBody(p.body)});
              }),
         list(m.instances,
              [&](const Instance &i) {
                return fields({text("instance"), text(i.name), text(i.protocol),
                               pairs(i.parameters), pairs(i.dependencies),
                               pairs(i.roles)});
              }),
         list(m.entries, [&](const Entry &e) {
           return fields({text("entry"), text(e.name), text(e.instance)});
         })});
    if (!m.isLibrary())
      return common;
    return fields(
        {text("zkc.library/1"),
         list(m.definitions, [&](const auto &f) { return definition(f); }),
         list(m.configurations,
              [&](const Configuration &c) {
                return fields({text("configure"), text(c.name), text(c.base),
                               pairs(c.arguments), pairs(c.implementations)});
              }),
         common});
  }
  size_t measure(const Participants &m) {
    projected = true;
    if (m.stage != Participants::Stage::Logical &&
        m.stage != Participants::Stage::Physical)
      fail("source-model-shape");
    return fields(
        {text("zkc.participants/1"), environment(m),
         text(m.stage == Participants::Stage::Physical ? "physical"
                                                       : "logical"),
         list(m.functions, [&](const auto &f) { return function(f); }),
         list(m.participants,
              [&](const Participant &p) {
                return fields({text("participant"), text(p.name),
                               text(p.instance), text(p.role),
                               pairs(p.parameters), parameters(p.arguments),
                               names(p.results), body(p.body)});
              }),
         list(m.entries, [&](const ParticipantEntry &e) {
           return fields({text("entry"), text(e.name), pairs(e.participants)});
         })});
  }
  size_t measure(const Construction &c) {
    if (c.identity != Construction::Identity::Exact &&
        c.identity != Construction::Identity::Normalized)
      fail("source-model-shape");
    return fields(
        {text("zkc.construction/1"), text(c.entry), text(c.producer),
         text(c.validator),
         list(c.publicBindings,
              [&](const PublicBinding &b) {
                return fields({text(b.name), pairs(b.ports)});
              }),
         fields({text(c.randomness), pairs(c.draws)}), text(c.acceptance),
         text(c.suite),
         text(c.identity == Construction::Identity::Normalized ? "normalized"
                                                               : "exact")});
  }

public:
  template <typename T> Error run(const T &value) {
    measure(value);
    return problem.empty() ? Error::success() : error(problem);
  }
};
} // namespace
Error checkStructure(const Content &content) {
  return std::visit([](const auto &root) { return Structure().run(root); },
                    content);
}
Error checkStructure(const Module &m) { return Structure().run(m); }
Error checkStructure(const Participants &m) { return Structure().run(m); }
Error checkStructure(const Construction &c) { return Structure().run(c); }
} // namespace zkc::source
