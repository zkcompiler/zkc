#include "zkc/Relation/Authoring.h"
#include "zkc/Source/Codec.h"
#include "llvm/Support/ErrorHandling.h"
#include <type_traits>

using namespace llvm;
namespace zkc::source {
namespace {
using A = json::Array;
using V = json::Value;
class Encoder {
  RecordMap *records;
  Path path;
  bool projected = false;
  bool generic = false;

  void origin(const Node &node) {
    if (records)
      records->emplace(path, &node);
  }
  template <typename F> auto at(size_t index, F f) {
    path.push_back(index);
    auto result = f();
    path.pop_back();
    return result;
  }
  template <typename T, typename F> A list(const T &values, F f) {
    A result;
    result.reserve(values.size());
    for (size_t i = 0; i < values.size(); ++i)
      result.push_back(at(i, [&] { return f(values[i]); }));
    return result;
  }
  A names(const Names &values) {
    return list(values, [](const std::string &s) -> V { return s; });
  }
  A pairs(const Assignments &values) {
    return list(values,
                [](const auto &p) -> V { return A{p.first, p.second}; });
  }
  A pairs(const ParameterBindings &values) {
    return list(values, [&](const auto &p) -> V {
      if (const auto *constant = std::get_if<std::string>(&p.second))
        return A{p.first, *constant};
      const auto &ingress = std::get<FamilyIngress>(p.second);
      return A{p.first,
               A{"ingress", ingress.bound,
                 list(ingress.selectors, [&](const FamilySelector &s) -> V {
                   return A{s.role, s.function, names(s.arguments)};
                 })}};
    });
  }
  A parameters(const std::vector<Parameter> &values) {
    return list(values,
                [](const Parameter &p) -> V { return A{p.name, p.type}; });
  }
  A body(const Body &values) {
    return list(values, [&](const Instruction &i) { return instruction(i); });
  }
  V optionalBody(const std::optional<Body> &value) {
    return value ? V(body(*value)) : V("external");
  }
  V instruction(const Instruction &i) {
    origin(i);
    return std::visit(
        [&](const auto &op) -> V {
          using T = std::decay_t<decltype(op)>;
          if constexpr (std::is_same_v<T, Return> || std::is_same_v<T, Yield> ||
                        std::is_same_v<T, Release>) {
            return A{i.kind().str(), names(op.values)};
          } else if constexpr (std::is_same_v<T, Operation>) {
            A result{"op", i.site, op.callee};
            if (generic)
              result.push_back(names(op.staticArguments));
            result.push_back(names(op.attributes));
            result.push_back(names(op.inputs));
            result.push_back(names(op.outputs));
            return result;
          } else if constexpr (std::is_same_v<T, LocalCall>) {
            A result{"local", i.site};
            if (!projected)
              result.push_back(op.role);
            result.push_back(op.callee);
            result.push_back(names(op.inputs));
            result.push_back(names(op.outputs));
            return result;
          } else if constexpr (std::is_same_v<T, AlgorithmCall>) {
            return A{"apply",          i.site,
                     op.callee,        names(op.staticArguments),
                     names(op.inputs), names(op.outputs)};
          } else if constexpr (std::is_same_v<T, ProtocolCall>) {
            return A{i.kind().str(), i.site, op.callee, names(op.inputs),
                     names(op.outputs)};
          } else if constexpr (std::is_same_v<T, Message>) {
            return A{"message",   i.site,   op.schema, op.sender,
                     op.receiver, op.input, op.output};
          } else if constexpr (std::is_same_v<T, Send>) {
            return A{"send", i.site, op.schema, op.peer, op.input};
          } else if constexpr (std::is_same_v<T, Receive>) {
            return A{"receive", i.site, op.schema, op.peer, op.output, op.type};
          } else if constexpr (std::is_same_v<T, Stop>) {
            if (projected)
              return A{"stop", i.site, op.reason};
            return A{"stop", i.site, op.role, op.reason};
          } else if constexpr (std::is_same_v<T, Incomplete>) {
            return A{"incomplete", i.site};
          } else if constexpr (std::is_same_v<T, VariantConstruct>) {
            return A{"variant",         i.site,   op.type, op.alternative,
                     names(op.payload), op.output};
          } else if constexpr (std::is_same_v<T, Match>) {
            return A{"match",
                     i.site,
                     op.input,
                     names(op.captures),
                     at(4,
                        [&] {
                          return list(op.arms, [&](const MatchArm &arm) -> V {
                            return A{arm.alternative, names(arm.payload),
                                     at(2, [&] { return body(arm.body); })};
                          });
                        }),
                     names(op.outputs)};
          } else if constexpr (std::is_same_v<T, Conditional>) {
            return A{"if",
                     i.site,
                     op.condition,
                     names(op.captures),
                     at(4, [&] { return body(op.thenBody); }),
                     at(5, [&] { return body(op.elseBody); }),
                     names(op.outputs)};
          } else if constexpr (std::is_same_v<T, For>) {
            return A{"for",
                     i.site,
                     op.induction,
                     op.lower,
                     op.upper,
                     pairs(op.carried),
                     names(op.captures),
                     at(7, [&] { return body(op.body); }),
                     names(op.outputs)};
          } else {
            V count = projected && op.count.kind == LoopCount::Kind::Constant
                          ? V(op.count.value)
                          : V(A{op.count.kind == LoopCount::Kind::Parameter
                                    ? "parameter"
                                    : "constant",
                                op.count.value});
            return A{"loop",
                     i.site,
                     std::move(count),
                     pairs(op.carried),
                     names(op.captures),
                     at(5, [&] { return body(op.body); }),
                     names(op.outputs)};
          }
        },
        i.value);
  }
  V function(const Function &f) {
    origin(f);
    A out{"function", f.name, parameters(f.arguments), names(f.results),
          at(4, [&] { return optionalBody(f.body); })};
    if (f.origin)
      out.push_back(A{f.origin->definition, pairs(f.origin->arguments)});
    return out;
  }
  V protocol(const Protocol &p) {
    origin(p);
    A arguments = list(p.arguments, [](const OwnedParameter &x) -> V {
      return A{x.name, x.role, x.type};
    });
    A results = list(
        p.results, [](const OwnedResult &x) -> V { return A{x.role, x.type}; });
    A dependencies = at(6, [&] {
      return list(p.dependencies, [&](const Dependency &d) -> V {
        origin(d);
        return A{d.name, d.protocol, pairs(d.agreements)};
      });
    });
    return A{"protocol",
             p.name,
             names(p.roles),
             names(p.parameters),
             std::move(arguments),
             std::move(results),
             std::move(dependencies),
             at(7, [&] { return optionalBody(p.body); })};
  }
  V instance(const Instance &i) {
    origin(i);
    return A{"instance",
             i.name,
             i.protocol,
             pairs(i.parameters),
             pairs(i.dependencies),
             pairs(i.roles)};
  }
  V entry(const Entry &e) {
    origin(e);
    return A{"entry", e.name, e.instance};
  }
  V binding(const OperationBinding &b) {
    origin(b);
    return A{b.name, b.contract, names(b.arguments), b.implementation};
  }
  V definition(const GenericFunction &f) {
    origin(f);
    A parameters = list(f.parameters, [](const StaticParameter &p) -> V {
      return A{p.name, p.sort};
    });
    A requirements = at(3, [&] {
      return list(f.requirements, [&](const Requirement &r) -> V {
        origin(r);
        return A{r.predicate, names(r.arguments)};
      });
    });
    generic = true;
    A contents = at(6, [&] { return body(f.body); });
    generic = false;
    return A{"generic_function",
             f.name,
             std::move(parameters),
             std::move(requirements),
             this->parameters(f.arguments),
             names(f.results),
             std::move(contents)};
  }
  V configuration(const Configuration &c) {
    origin(c);
    return A{"configure", c.name, c.base, pairs(c.arguments),
             pairs(c.implementations)};
  }
  template <typename T> V environment(const T &m) {
    return at(1, [&] {
      return list(m.bindings, [&](const auto &b) { return binding(b); });
    });
  }
  V common(const Module &m, bool root = true) {
    if (root)
      origin(m);
    return A{"zkc.protocol/1",
             environment(m),
             at(2,
                [&] {
                  return list(m.functions,
                              [&](const auto &f) { return function(f); });
                }),
             at(3,
                [&] {
                  return list(m.protocols,
                              [&](const auto &p) { return protocol(p); });
                }),
             at(4,
                [&] {
                  return list(m.instances,
                              [&](const auto &i) { return instance(i); });
                }),
             at(5, [&] {
               return list(m.entries, [&](const auto &e) { return entry(e); });
             })};
  }

public:
  explicit Encoder(RecordMap *records) : records(records) {
    if (records)
      records->clear();
  }
  V run(const GenericFunction &f) { return definition(f); }
  V run(const Module &m) {
    if (!m.relations.empty() || !m.relationViews.empty()) {
      auto authored = relation::authoredSource(m);
      if (!authored)
        report_fatal_error(Twine("encode requires checked relation source: ") +
                           toString(authored.takeError()));
      // The compact envelope is reconstructed from a temporary authored copy.
      // Never publish borrowed node pointers into that temporary as source
      // maps.
      auto *saved = records;
      records = nullptr;
      auto common = run(*authored);
      records = saved;
      return A{"zkc.relations/1", relation::encodeDeclarations(m),
               std::move(common)};
    }
    if (!m.isLibrary())
      return common(m);
    origin(m);
    return A{"zkc.library/1",
             at(1,
                [&] {
                  return list(m.definitions,
                              [&](const auto &f) { return definition(f); });
                }),
             at(2,
                [&] {
                  return list(m.configurations,
                              [&](const auto &c) { return configuration(c); });
                }),
             at(3, [&] { return common(m, false); })};
  }
  V run(const Participants &m) {
    origin(m);
    projected = true;
    auto participants = at(4, [&] {
      return list(m.participants, [&](const Participant &p) -> V {
        origin(p);
        return A{"participant",       p.name,
                 p.instance,          p.role,
                 pairs(p.parameters), parameters(p.arguments),
                 names(p.results),    at(7, [&] { return body(p.body); })};
      });
    });
    auto entries = at(5, [&] {
      return list(m.entries, [&](const ParticipantEntry &e) -> V {
        origin(e);
        return A{"entry", e.name, pairs(e.participants)};
      });
    });
    return A{"zkc.participants/1",
             environment(m),
             m.stage == Participants::Stage::Physical ? "physical" : "logical",
             at(3,
                [&] {
                  return list(m.functions,
                              [&](const auto &f) { return function(f); });
                }),
             std::move(participants),
             std::move(entries)};
  }
  V run(const Construction &c) {
    origin(c);
    A bindings = at(4, [&] {
      return list(c.publicBindings, [&](const PublicBinding &b) -> V {
        origin(b);
        return A{b.name, pairs(b.ports)};
      });
    });
    return A{"zkc.construction/1",
             c.entry,
             c.producer,
             c.validator,
             std::move(bindings),
             A{c.randomness, pairs(c.draws)},
             c.acceptance,
             c.suite,
             c.identity == Construction::Identity::Normalized ? "normalized"
                                                              : "exact"};
  }
};
} // namespace
json::Value encode(const Content &content, RecordMap *records) {
  Encoder encoder(records);
  return std::visit([&](const auto &root) { return encoder.run(root); },
                    content);
}
json::Value encode(const Module &m, RecordMap *records) {
  return Encoder(records).run(m);
}
json::Value encode(const Participants &m, RecordMap *records) {
  return Encoder(records).run(m);
}
json::Value encode(const Construction &c, RecordMap *records) {
  return Encoder(records).run(c);
}
json::Value encode(const GenericFunction &f, RecordMap *records) {
  return Encoder(records).run(f);
}
} // namespace zkc::source
