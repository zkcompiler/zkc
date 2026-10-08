#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"

using namespace llvm;
namespace zkc::program {
namespace {
using A = json::Array;
using V = json::Value;

class Decoder {
  std::string problem;

  void fail(StringRef code) {
    if (problem.empty()) {
      problem = code.str();
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
  template <typename F> auto list(const V &v, F f) {
    using T = decltype(f(v));
    std::vector<T> out;
    if (const auto *a = array(v)) {
      out.reserve(a->size());
      for (size_t i = 0; i < a->size() && problem.empty(); ++i)
        out.push_back(f((*a)[i]));
    }
    return out;
  }
  Names names(const V &v) {
    return list(v, [&](const V &x) { return string(x); });
  }
  protocol::Assignments pairs(const V &v) {
    return list(v, [&](const V &x) -> std::pair<std::string, std::string> {
      const auto *p = array(x, 2);
      return p ? std::make_pair(string((*p)[0]), string((*p)[1]))
               : std::pair<std::string, std::string>{};
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
  Body functionBody(const V &v) {
    if (!v.getAsArray()) {
      fail("interactive-external-body");
      return {};
    }
    return body(v);
  }
  Instruction instruction(const V &v, unsigned depth) {
    Instruction out;

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
      if (fields(6, "interactive-operation"))
        out.value = Operation{string((*r)[2]), names((*r)[3]), names((*r)[4]),
                              names((*r)[5])};
    } else if (tag == "return_if") {
      if (fields(5, "interactive-return-type"))
        out.value = ReturnIf{string((*r)[2]), names((*r)[3]), names((*r)[4])};
    } else if (tag == "bool_constant") {
      if (fields(4, "native-boolean-shape")) {
        auto value = (*r)[3].getAsBoolean();
        if (!value)
          fail("native-boolean-value");
        else
          out.value = BooleanConstant{string((*r)[2]), *value};
      }
    } else if (tag == "query") {
      if (fields(6, "service-query-shape"))
        out.value = ServiceQuery{string((*r)[2]), string((*r)[3]),
                                 names((*r)[4]), names((*r)[5])};
    } else if (tag == "local") {
      if (fields(5, "interactive-local-call"))
        out.value = LocalCall{string((*r)[2]), names((*r)[3]), names((*r)[4])};
    } else if (tag == "send") {
      if (fields(5, "interactive-send"))
        out.value = Send{string((*r)[2]), string((*r)[3]), string((*r)[4])};
    } else if (tag == "receive") {
      if (fields(6, "interactive-receive"))
        out.value = Receive{string((*r)[2]), string((*r)[3]), string((*r)[4]),
                            string((*r)[5])};
    } else if (tag == "stop") {
      if (fields(3, "interactive-stop"))
        out.value = Stop{string(r->back())};
    } else if (tag == "variant") {
      if (fields(6, "variant-shape"))
        out.value = VariantConstruct{string((*r)[2]), string((*r)[3]),
                                     names((*r)[4]), string((*r)[5])};
    } else if (tag == "match") {
      if (fields(6, "local-match-shape")) {
        Match match;
        match.input = string((*r)[2]);
        match.captures = names((*r)[3]);
        match.arms = list((*r)[4], [&](const V &v) {
          MatchArm arm;
          if (const auto *a = array(v, 3, "local-match-arm")) {
            arm.alternative = string((*a)[0]);
            arm.payload = names((*a)[1]);
            arm.body = body((*a)[2], depth + 1);
          }
          return arm;
        });
        match.outputs = names((*r)[5]);
        out.value = std::move(match);
      }
    } else if (tag == "if") {
      if (fields(7, "local-if-shape"))
        out.value = Conditional{string((*r)[2]), names((*r)[3]),
                                body((*r)[4], depth + 1),
                                body((*r)[5], depth + 1), names((*r)[6])};
    } else if (tag == "for" || (tag == "for_while")) {
      if (fields(9, "local-for-shape"))
        out.value =
            For{string((*r)[2]), string((*r)[3]),   string((*r)[4]),
                pairs((*r)[5]),  names((*r)[6]),    body((*r)[7], depth + 1),
                names((*r)[8]),  tag == "for_while"};
    } else if (tag == "loop") {
      if (fields(7, "interactive-loop")) {
        Loop loop;
        if (const auto *count = array((*r)[2])) {
          if (count->size() == 4 && (*count)[0].getAsString() == "value") {
            loop.count.value = string((*count)[1]);
            auto bound = string((*count)[2]);
            if (bound.empty() || (bound.size() > 1 && bound.front() == '0') ||
                !llvm::all_of(bound,
                              [](char c) { return c >= '0' && c <= '9'; }) ||
                StringRef(bound).getAsInteger(10, loop.count.maximum) ||
                loop.count.maximum > 1048576)
              fail("interactive-loop-count");
            loop.count.induction = string((*count)[3]);
          } else {
            fail("interactive-loop-count");
          }
        }
        loop.carried = pairs((*r)[3]);
        loop.captures = names((*r)[4]);
        loop.body = body((*r)[5], depth + 1);
        loop.outputs = names((*r)[6]);
        out.value = std::move(loop);
      }
    } else
      fail("interactive-instruction");
    return out;
  }
  Function function(const V &v) {
    Function out;

    const auto *r = record(v, "function", 6);
    if (!r)
      return out;
    out.name = string((*r)[1]);
    out.arguments = parameters((*r)[2]);
    out.results = names((*r)[3]);
    out.body = functionBody((*r)[4]);
    if (const auto *o = array((*r)[5], 2, "binding-logical-origin"))
      out.origin = LogicalOrigin{string((*o)[0]), pairs((*o)[1])};
    return out;
  }
  protocol::OperationBinding binding(const V &v) {
    protocol::OperationBinding out;

    if (const auto *r = array(v, 4, "binding-declaration")) {
      out.name = string((*r)[0]);
      out.application.contract = string((*r)[1]);
      out.application.arguments = names((*r)[2]);
      out.application.implementation = string((*r)[3]);
    }
    return out;
  }
  template <typename T> void environment(const A &r, T &out) {
    out.bindings = list(r[1], [&](const V &v) { return binding(v); });
  }
  Participants participants(const V &v) {
    Participants out;

    const auto *r = array(v, 6);
    if (!r)
      return out;
    std::string stage = string((*r)[2]);
    if (stage != "logical" && stage != "physical")
      fail("interactive-stage");
    out.stage = Participants::Stage::Physical;
    if (stage != "physical")
      fail("native-physical-required");
    environment(*r, out);
    out.functions = list((*r)[3], [&](const V &x) { return function(x); });
    out.participants = list((*r)[4], [&](const V &x) {
      Participant p;

      if (const auto *r = record(x, "participant", 9)) {
        p.name = string((*r)[1]);
        p.instance = string((*r)[2]);
        p.role = string((*r)[3]);
        array((*r)[4], 0);
        p.arguments = this->parameters((*r)[5]);
        p.results = names((*r)[6]);
        p.body = body((*r)[7]);
        p.services = list((*r)[8], [&](const V &v) {
          ServicePort port;
          if (const auto *row = array(v, 3)) {
            port.name = string((*row)[0]);
            port.contract = string((*row)[1]);
            auto index = string((*row)[2]);
            if (StringRef(index).getAsInteger(10, port.inputIndex) ||
                std::to_string(port.inputIndex) != index)
              fail("service-port-index");
          }
          return port;
        });
      }
      return p;
    });
    out.entries = list((*r)[5], [&](const V &x) {
      ParticipantEntry e;

      if (const auto *r = record(x, "entry", 3)) {
        e.name = string((*r)[1]);
        e.participants = pairs((*r)[2]);
      }
      return e;
    });
    return out;
  }

public:
  Expected<Participants> run(const V &v) {
    const auto *r = array(v);
    if (!r || r->empty())
      return error("interactive-shape");
    auto tag = string((*r)[0]);
    if (tag != "zkc.program/1")
      return error("interactive-format");
    auto result = participants(v);
    if (!problem.empty())
      return error(problem);
    if (auto e = checkStructure(result))
      return std::move(e);
    return result;
  }
};
} // namespace
Expected<Participants> decode(const json::Value &v) { return Decoder().run(v); }
} // namespace zkc::program
