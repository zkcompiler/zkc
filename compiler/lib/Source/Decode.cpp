#include "zkc/Source/Codec.h"
#include "zkc/Source/Relations.h"
#include "zkc/Support/Json.h"

using namespace llvm;
namespace zkc::source {
namespace {
using A = json::Array;
using V = json::Value;

class Decoder {
  const SourceMap &locations;
  std::optional<Span> *failure;
  std::optional<Span> current;
  Path path;
  std::string problem;
  bool projected = false;
  bool generic = false;

  void locate(const V &value) {
    auto found = locations.find(path);
    current = value.getAsArray() && found != locations.end()
                  ? std::optional<Span>(found->second)
                  : std::nullopt;
  }
  void fail(StringRef code) {
    if (problem.empty()) {
      problem = code.str();
      if (failure)
        *failure = current;
    }
  }
  const A *array(const V &v, std::optional<size_t> size = {},
                 StringRef code = "interactive-shape") {
    const auto *a = v.getAsArray();
    if (!a || (size && a->size() != *size) || a->size() > 32768) {
      fail(code);
      return nullptr;
    }
    return a;
  }
  const A *record(const V &v, StringRef tag, size_t size,
                  StringRef code = "interactive-record") {
    locate(v);
    const auto *r = array(v, size, code);
    if (!r || (*r)[0].getAsString() != tag) {
      fail(code);
      return nullptr;
    }
    return r;
  }
  std::string string(const V &v) {
    auto s = v.getAsString();
    if (!s) {
      fail("interactive-shape");
      return {};
    }
    return s->str();
  }
  void origin(Node &node) {
    if (auto it = locations.find(path); it != locations.end())
      node.location = it->second;
  }
  template <typename F> auto at(size_t index, F f) {
    auto enclosing = current;
    path.push_back(index);
    auto result = f();
    path.pop_back();
    current = enclosing;
    return result;
  }
  template <typename F> auto list(const V &v, F f) {
    using T = decltype(f(v));
    std::vector<T> out;
    if (const auto *a = array(v)) {
      out.reserve(a->size());
      for (size_t i = 0; i < a->size() && problem.empty(); ++i)
        out.push_back(at(i, [&] { return f((*a)[i]); }));
    }
    return out;
  }
  Names names(const V &v) {
    return list(v, [&](const V &x) { return string(x); });
  }
  Assignments pairs(const V &v) {
    return list(v, [&](const V &x) -> std::pair<std::string, std::string> {
      const auto *p = array(x, 2);
      return p ? std::make_pair(string((*p)[0]), string((*p)[1]))
               : std::pair<std::string, std::string>{};
    });
  }
  ParameterBindings parameterBindings(const V &v) {
    return list(
        v, [&](const V &item) -> std::pair<std::string, ParameterBinding> {
          const auto *p = array(item, 2);
          if (!p)
            return {};
          auto key = string((*p)[0]);
          if ((*p)[1].getAsString())
            return {key, string((*p)[1])};
          const auto *ingress =
              record((*p)[1], "ingress", 3, "interactive-family-binding");
          if (!ingress)
            return {};
          return {key,
                  FamilyIngress{
                      string((*ingress)[1]),
                      list((*ingress)[2], [&](const V &item) -> FamilySelector {
                        const auto *selector = array(item, 3);
                        if (!selector)
                          return {};
                        return {string((*selector)[0]), string((*selector)[1]),
                                names((*selector)[2])};
                      })}};
        });
  }
  std::vector<Parameter> parameters(const V &v) {
    return list(v, [&](const V &x) {
      const auto *p = array(x, 2);
      return p ? Parameter{string((*p)[0]), string((*p)[1])} : Parameter{};
    });
  }
  Body body(const V &v, unsigned depth = 0) {
    if (depth > 64) {
      fail("interactive-body");
      return {};
    }
    return list(v, [&](const V &x) { return instruction(x, depth); });
  }
  std::optional<Body> optionalBody(const V &v) {
    if (auto s = v.getAsString()) {
      if (*s != "external")
        fail("interactive-external-body");
      return {};
    }
    return body(v);
  }
  Instruction instruction(const V &v, unsigned depth) {
    Instruction out;
    origin(out);
    locate(v);
    const auto *r = array(v);
    if (!r || r->empty()) {
      fail("interactive-instruction");
      return out;
    }
    std::string tag = string((*r)[0]);
    auto fields = [&](size_t count, StringRef code) {
      if (r->size() == count)
        return true;
      fail(code);
      return false;
    };
    if (tag == "release") {
      if (!projected)
        fail("interactive-release-context");
      if (fields(2, "interactive-release-shape"))
        out.value = Release{names((*r)[1])};
      return out;
    }
    if (tag == "return" || tag == "yield") {
      if (fields(2, "interactive-return")) {
        auto values = names((*r)[1]);
        if (tag == "return")
          out.value = Return{std::move(values)};
        else
          out.value = Yield{std::move(values)};
      }
      return out;
    }
    if (r->size() < 2) {
      fail("interactive-instruction");
      return out;
    }
    out.site = string((*r)[1]);
    if (tag == "op") {
      if (fields(generic ? 7 : 6, "interactive-operation")) {
        size_t offset = generic ? 1 : 0;
        out.value =
            Operation{string((*r)[2]), generic ? names((*r)[3]) : Names{},
                      names((*r)[3 + offset]), names((*r)[4 + offset]),
                      names((*r)[5 + offset])};
      }
    } else if (tag == "local") {
      if (fields(projected ? 5 : 6, "interactive-local-call")) {
        size_t offset = projected ? 0 : 1;
        out.value = LocalCall{projected ? "" : string((*r)[2]),
                              string((*r)[2 + offset]), names((*r)[3 + offset]),
                              names((*r)[4 + offset])};
      }
    } else if (tag == "apply") {
      if (fields(6, "algorithm-call-shape"))
        out.value = AlgorithmCall{string((*r)[2]), names((*r)[4]),
                                  names((*r)[5]), names((*r)[3])};
    } else if (tag == "call") {
      if (fields(5, "interactive-call"))
        out.value =
            ProtocolCall{string((*r)[2]), names((*r)[3]), names((*r)[4])};
    } else if (tag == "message") {
      if (fields(7, "interactive-message"))
        out.value = Message{string((*r)[2]), string((*r)[3]), string((*r)[4]),
                            string((*r)[5]), string((*r)[6])};
    } else if (tag == "send") {
      if (fields(5, "interactive-send"))
        out.value = Send{string((*r)[2]), string((*r)[3]), string((*r)[4])};
    } else if (tag == "receive") {
      if (fields(6, "interactive-receive"))
        out.value = Receive{string((*r)[2]), string((*r)[3]), string((*r)[4]),
                            string((*r)[5])};
    } else if (tag == "stop") {
      if (fields(projected ? 3 : 4, "interactive-stop"))
        out.value = Stop{projected ? "" : string((*r)[2]), string(r->back())};
    } else if (tag == "incomplete") {
      if (fields(2, "interactive-incomplete"))
        out.value = Incomplete{};
    } else if (tag == "variant") {
      if (fields(6, "variant-shape"))
        out.value = VariantConstruct{string((*r)[2]), string((*r)[3]),
                                     names((*r)[4]), string((*r)[5])};
    } else if (tag == "match") {
      if (fields(6, "local-match-shape")) {
        Match match;
        match.input = string((*r)[2]);
        match.captures = names((*r)[3]);
        match.arms = at(4, [&] {
          return list((*r)[4], [&](const V &v) {
            MatchArm arm;
            if (const auto *a = array(v, 3, "local-match-arm")) {
              arm.alternative = string((*a)[0]);
              arm.payload = names((*a)[1]);
              arm.body = at(2, [&] { return body((*a)[2], depth + 1); });
            }
            return arm;
          });
        });
        match.outputs = names((*r)[5]);
        out.value = std::move(match);
      }
    } else if (tag == "if") {
      if (fields(7, "local-if-shape"))
        out.value = Conditional{string((*r)[2]), names((*r)[3]),
                                at(4, [&] { return body((*r)[4], depth + 1); }),
                                at(5, [&] { return body((*r)[5], depth + 1); }),
                                names((*r)[6])};
    } else if (tag == "for") {
      if (fields(9, "local-for-shape"))
        out.value = For{
            string((*r)[2]), string((*r)[3]),
            string((*r)[4]), pairs((*r)[5]),
            names((*r)[6]),  at(7, [&] { return body((*r)[7], depth + 1); }),
            names((*r)[8])};
    } else if (tag == "loop") {
      if (fields(7, "interactive-loop")) {
        Loop loop;
        if (projected && (*r)[2].getAsString())
          loop.count.value = string((*r)[2]);
        else if (const auto *count = array((*r)[2], 2)) {
          auto kind = string((*count)[0]);
          if (kind != "constant" && kind != "parameter")
            fail("interactive-loop-count");
          loop.count.kind = kind == "parameter" ? LoopCount::Kind::Parameter
                                                : LoopCount::Kind::Constant;
          loop.count.value = string((*count)[1]);
        }
        loop.carried = pairs((*r)[3]);
        loop.captures = names((*r)[4]);
        loop.body = at(5, [&] { return body((*r)[5], depth + 1); });
        loop.outputs = names((*r)[6]);
        out.value = std::move(loop);
      }
    } else
      fail(generic ? "generic-operation" : "interactive-instruction");
    return out;
  }
  Function function(const V &v) {
    Function out;
    origin(out);
    const auto *r = record(v, "function", 6);
    if (!r)
      return out;
    out.name = string((*r)[1]);
    out.arguments = parameters((*r)[2]);
    out.results = names((*r)[3]);
    out.body = at(4, [&] { return optionalBody((*r)[4]); });
    if (const auto *o = array((*r)[5], 2, "binding-logical-origin"))
      out.origin = LogicalOrigin{string((*o)[0]), pairs((*o)[1])};
    return out;
  }
  Protocol protocol(const V &v) {
    Protocol out;
    origin(out);
    const auto *r = record(v, "protocol", 8);
    if (!r)
      return out;
    out.name = string((*r)[1]);
    out.roles = names((*r)[2]);
    out.parameters = names((*r)[3]);
    out.arguments = list((*r)[4], [&](const V &x) {
      const auto *p = array(x, 3);
      return p ? OwnedParameter{string((*p)[0]), string((*p)[1]),
                                string((*p)[2])}
               : OwnedParameter{};
    });
    out.results = list((*r)[5], [&](const V &x) {
      const auto *p = array(x, 2);
      return p ? OwnedResult{string((*p)[0]), string((*p)[1])} : OwnedResult{};
    });
    out.dependencies = at(6, [&] {
      return list((*r)[6], [&](const V &x) {
        Dependency d;
        origin(d);
        if (const auto *p = array(x, 3)) {
          d.name = string((*p)[0]);
          d.protocol = string((*p)[1]);
          d.agreements = pairs((*p)[2]);
        }
        return d;
      });
    });
    out.body = at(7, [&] { return optionalBody((*r)[7]); });
    return out;
  }
  Instance instance(const V &v) {
    Instance out;
    origin(out);
    const auto *r = record(v, "instance", 6, "interactive-instance");
    if (!r)
      return out;
    out.name = string((*r)[1]);
    out.protocol = string((*r)[2]);
    out.parameters = parameterBindings((*r)[3]);
    out.dependencies = pairs((*r)[4]);
    out.roles = pairs((*r)[5]);
    return out;
  }
  Entry entry(const V &v) {
    Entry out;
    origin(out);
    if (const auto *r = record(v, "entry", 3, "interactive-entry-name")) {
      out.name = string((*r)[1]);
      out.instance = string((*r)[2]);
    }
    return out;
  }
  OperationBinding binding(const V &v) {
    OperationBinding out;
    origin(out);
    locate(v);
    if (const auto *r = array(v, 4, "binding-declaration")) {
      out.name = string((*r)[0]);
      out.application.contract = string((*r)[1]);
      out.application.arguments = names((*r)[2]);
      out.application.implementation = string((*r)[3]);
    }
    return out;
  }
  GenericFunction definition(const V &v) {
    GenericFunction out;
    origin(out);
    const auto *r = record(v, "generic_function", 7, "generic-definition");
    if (!r)
      return out;
    out.name = string((*r)[1]);
    out.parameters = list((*r)[2], [&](const V &x) {
      const auto *p = array(x, 2);
      return p ? StaticParameter{string((*p)[0]), string((*p)[1])}
               : StaticParameter{};
    });
    out.requirements = at(3, [&] {
      return list((*r)[3], [&](const V &x) {
        Requirement requirement;
        origin(requirement);
        if (const auto *p = array(x, 2)) {
          requirement.predicate = string((*p)[0]);
          requirement.arguments = names((*p)[1]);
        }
        return requirement;
      });
    });
    out.arguments = parameters((*r)[4]);
    out.results = names((*r)[5]);
    generic = true;
    out.body = at(6, [&] { return body((*r)[6]); });
    generic = false;
    return out;
  }
  Configuration configuration(const V &v) {
    Configuration out;
    origin(out);
    if (const auto *r = record(v, "configure", 5, "generic-configuration")) {
      out.name = string((*r)[1]);
      out.base = string((*r)[2]);
      out.arguments = pairs((*r)[3]);
      out.implementations = pairs((*r)[4]);
    }
    return out;
  }
  template <typename T> void environment(const A &r, T &out) {
    out.bindings = at(
        1, [&] { return list(r[1], [&](const V &v) { return binding(v); }); });
  }
  Module module(const V &v) {
    locate(v);
    Module out;
    origin(out);
    const auto *r = array(v, 6);
    if (!r)
      return out;
    if (string((*r)[0]) != "zkc.protocol/1") {
      fail("interactive-format");
      return out;
    }
    environment(*r, out);
    out.functions = at(2, [&] {
      return list((*r)[2], [&](const V &x) { return function(x); });
    });
    out.protocols = at(3, [&] {
      return list((*r)[3], [&](const V &x) { return protocol(x); });
    });
    out.instances = at(4, [&] {
      return list((*r)[4], [&](const V &x) { return instance(x); });
    });
    out.entries = at(
        5, [&] { return list((*r)[5], [&](const V &x) { return entry(x); }); });
    return out;
  }
  Participants participants(const V &v) {
    Participants out;
    origin(out);
    const auto *r = array(v, 6);
    if (!r)
      return out;
    projected = true;
    std::string stage = string((*r)[2]);
    if (stage != "logical" && stage != "physical")
      fail("interactive-stage");
    out.stage = stage == "physical" ? Participants::Stage::Physical
                                    : Participants::Stage::Logical;
    environment(*r, out);
    out.functions = at(3, [&] {
      return list((*r)[3], [&](const V &x) { return function(x); });
    });
    out.participants = at(4, [&] {
      return list((*r)[4], [&](const V &x) {
        Participant p;
        origin(p);
        if (const auto *r = record(x, "participant", 8)) {
          p.name = string((*r)[1]);
          p.instance = string((*r)[2]);
          p.role = string((*r)[3]);
          p.parameters = parameterBindings((*r)[4]);
          p.arguments = parameters((*r)[5]);
          p.results = names((*r)[6]);
          p.body = at(7, [&] { return body((*r)[7]); });
        }
        return p;
      });
    });
    out.entries = at(5, [&] {
      return list((*r)[5], [&](const V &x) {
        ParticipantEntry e;
        origin(e);
        if (const auto *r = record(x, "entry", 3)) {
          e.name = string((*r)[1]);
          e.participants = pairs((*r)[2]);
        }
        return e;
      });
    });
    return out;
  }
  Construction construction(const V &v) {
    Construction out;
    origin(out);
    const auto *r = array(v, 9, "construction-descriptor");
    if (!r)
      return out;
    // The identity policy is a field, not a version: both policies are current
    // (docs/spec/profiles/compiler/local-algorithms.md).
    auto identity = string((*r)[8]);
    if (identity == "normalized")
      out.identity = Construction::Identity::Normalized;
    else if (identity == "exact")
      out.identity = Construction::Identity::Exact;
    else
      fail("construction-descriptor");
    out.entry = string((*r)[1]);
    out.producer = string((*r)[2]);
    out.validator = string((*r)[3]);
    out.publicBindings = at(4, [&] {
      return list((*r)[4], [&](const V &x) {
        PublicBinding binding;
        origin(binding);
        if (const auto *p = array(x, 2)) {
          binding.name = string((*p)[0]);
          binding.ports = pairs((*p)[1]);
        }
        return binding;
      });
    });
    if (const auto *random = array((*r)[5], 2)) {
      out.randomness = string((*random)[0]);
      out.draws = pairs((*random)[1]);
    }
    out.acceptance = string((*r)[6]);
    out.suite = string((*r)[7]);
    return out;
  }

public:
  Decoder(const SourceMap &locations, std::optional<Span> *failure)
      : locations(locations), failure(failure) {
    if (failure)
      failure->reset();
  }
  Expected<Content> run(const V &v) {
    locate(v);
    const auto *r = array(v);
    if (!r || r->empty())
      return error("interactive-shape");
    auto tag = string((*r)[0]);
    Content result;
    if (tag == "zkc.relations/1") {
      if (r->size() != 3)
        return error("relation-source-shape");
      auto *inner = (*r)[2].getAsArray();
      if (!inner || inner->empty() ||
          ((*inner)[0].getAsString() != "zkc.protocol/1" &&
           (*inner)[0].getAsString() != "zkc.library/1"))
        return error("relation-source-shape");
      auto base = decode((*r)[2]);
      if (!base)
        return base.takeError();
      auto *module = std::get_if<Module>(&*base);
      if (!module || !module->relations.empty() ||
          !module->relationViews.empty())
        return error("relation-source-shape");
      if (auto e = relation::decodeDeclarations((*r)[1], *module))
        return std::move(e);
      if (auto e = relation::checkEmbeddedRelations((*r)[2], *module))
        return std::move(e);
      if (auto e = relation::materializeViews(*module))
        return std::move(e);
      result = std::move(*base);
    } else if (tag == "zkc.library/1") {
      if (r->size() != 4)
        return error("generic-library-shape");
      auto common = at(3, [&] { return module((*r)[3]); });
      common.library = true;
      // A library is one semantic root. Its location denotes the whole input,
      // not both the envelope and its inner common-module array.
      common.location.reset();
      origin(common);
      common.definitions = at(1, [&] {
        return list((*r)[1], [&](const V &x) { return definition(x); });
      });
      common.configurations = at(2, [&] {
        return list((*r)[2], [&](const V &x) { return configuration(x); });
      });
      result = std::move(common);
    } else if (tag == "zkc.protocol/1")
      result = module(v);
    else if (tag == "zkc.participants/1")
      result = participants(v);
    else if (tag == "zkc.construction/1")
      result = construction(v);
    else
      fail("interactive-format");
    if (!problem.empty())
      return error(problem);
    if (auto e = checkStructure(result))
      return std::move(e);
    return result;
  }
};
} // namespace
Expected<Content> decode(const json::Value &v, const SourceMap &locations,
                         std::optional<Span> *failure) {
  return Decoder(locations, failure).run(v);
}
} // namespace zkc::source
