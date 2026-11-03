#include "zkc/Program/Codec.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"

using namespace llvm;
namespace zkc::program {
char ProgramRefusal::ID;
StringRef refusalClassName(RefusalClass kind) {
  switch (kind) {
  case RefusalClass::Syntax:
    return "syntax";
  case RefusalClass::Capacity:
    return "capacity";
  case RefusalClass::NamesAndSsa:
    return "names-and-ssa";
  case RefusalClass::Types:
    return "types";
  case RefusalClass::AffineUse:
    return "affine-use";
  case RefusalClass::UnsupportedProfile:
    return "unsupported-profile";
  }
  llvm_unreachable("unknown refusal class");
}
Error refuse(RefusalClass kind, StringRef code, const Twine &detail) {
  return make_error<ProgramRefusal>(kind, code.str(), detail.str());
}
bool isIdentifier(StringRef value) {
  return !value.empty() && value.size() <= identifierByteLimit &&
         (isAlpha(value.front()) || value.front() == '_') &&
         all_of(value, [](char c) {
           return isAlnum(c) || c == '_' || c == '.' || c == '-';
         });
}
namespace {
using RC = RefusalClass;
/// Count arrays, strings and Boolean literals and the array nesting of the
/// raw text before any JSON value is allocated. Only those values occur in the
/// grammar; string escapes and trailing input remain the parser's checks.
Error preflight(StringRef text) {
  if (text.size() > artifactByteLimit)
    return refuse(RC::Capacity, "byte-limit");
  size_t depth = 0, nodes = 0;
  for (size_t i = 0; i < text.size(); ++i) {
    char c = text[i];
    if (c == '"') {
      ++nodes;
      bool closed = false;
      for (++i; i < text.size(); ++i) {
        if (text[i] == '\\')
          ++i;
        else if (text[i] == '"') {
          closed = true;
          break;
        }
      }
      if (!closed)
        return refuse(RC::Syntax, "invalid-json", "unterminated string");
    } else if (c == '[') {
      ++depth;
      ++nodes;
    } else if (c == ']') {
      if (!depth)
        return refuse(RC::Syntax, "invalid-json", "unbalanced array");
      --depth;
    } else if (c == 't' || c == 'f') {
      StringRef token = c == 't' ? "true" : "false";
      if (!text.substr(i).starts_with(token))
        return refuse(RC::Syntax, "invalid-json", "invalid Boolean token");
      i += token.size() - 1;
      ++nodes;
    } else if (c != ',' && c != ' ' && c != '\t' && c != '\r' && c != '\n') {
      return refuse(RC::Syntax, "invalid-shape",
                    "only arrays, strings and Boolean literals are permitted");
    }
    if (depth > jsonDepthLimit)
      return refuse(RC::Capacity, "interactive-json-depth");
    if (nodes > artifactNodeLimit)
      return refuse(RC::Capacity, "source-limit", "JSON node ceiling");
  }
  if (depth)
    return refuse(RC::Syntax, "invalid-json", "unterminated array");
  return Error::success();
}
/// The same measures over an already allocated JSON value.
Error preflight(const json::Value &value) {
  size_t nodes = 0;
  std::vector<std::pair<const json::Value *, size_t>> pending{{&value, 1}};
  while (!pending.empty()) {
    auto [v, level] = pending.back();
    pending.pop_back();
    if (++nodes > artifactNodeLimit)
      return refuse(RC::Capacity, "source-limit", "JSON node ceiling");
    if (const auto *a = v->getAsArray()) {
      if (level > jsonDepthLimit)
        return refuse(RC::Capacity, "interactive-json-depth");
      for (const auto &child : *a)
        pending.push_back({&child, level + 1});
    }
  }
  return Error::success();
}
} // namespace
Expected<Participants> parse(StringRef text) {
  if (auto e = preflight(text))
    return std::move(e);
  auto json = parseJson(text, artifactByteLimit);
  if (!json) {
    // Preflight has bounded bytes, depth and nodes and admitted only arrays,
    // strings and Boolean literals; what remains is JSON syntax.
    std::string code;
    handleAllErrors(json.takeError(), [&](const Refusal &r) { code = r.code; });
    return refuse(RC::Syntax, code.empty() ? "invalid-json" : code);
  }
  return decode(*json);
}
namespace {
using A = json::Array;
using V = json::Value;

class Decoder {
  std::string problem;
  RefusalClass problemClass = RC::Syntax;

  void fail(RefusalClass kind, StringRef code) {
    if (problem.empty()) {
      problem = code.str();
      problemClass = kind;
    }
  }
  /// An array, refused as a shape error unless it exceeds the element bound.
  const A *array(const V &v, std::optional<size_t> size = {},
                 StringRef code = "interactive-shape") {
    const auto *a = v.getAsArray();
    if (a && a->size() > arrayElementLimit) {
      fail(RC::Capacity, "source-limit");
      return nullptr;
    }
    if (!a || (size && a->size() != *size)) {
      fail(RC::Syntax, code);
      return nullptr;
    }
    return a;
  }
  const A *record(const V &v, StringRef tag, size_t size,
                  StringRef code = "interactive-record") {
    const auto *r = array(v, size, code);
    if (!r || (*r)[0].getAsString() != tag) {
      fail(RC::Syntax, code);
      return nullptr;
    }
    return r;
  }
  std::string string(const V &v, size_t limit = stringByteLimit) {
    auto s = v.getAsString();
    if (!s) {
      fail(RC::Syntax, "interactive-shape");
      return {};
    }
    if (s->size() > limit) {
      fail(RC::Capacity, "source-limit");
      return {};
    }
    return s->str();
  }
  /// Every list is counted before its elements are decoded or reserved.
  template <typename F> auto list(const V &v, size_t limit, F f) {
    using T = decltype(f(v));
    std::vector<T> out;
    if (const auto *a = array(v)) {
      if (a->size() > limit) {
        fail(RC::Capacity, "interactive-list-limit");
        return out;
      }
      out.reserve(a->size());
      for (size_t i = 0; i < a->size() && problem.empty(); ++i)
        out.push_back(f((*a)[i]));
    }
    return out;
  }
  /// A name or site, checked against the identifier grammar while decoding,
  /// as every independent reader does.
  std::string name(const V &v) {
    auto s = v.getAsString();
    if (!s) {
      fail(RC::Syntax, "interactive-shape");
      return {};
    }
    // An ordinary string bound first, then the identifier's own.
    if (s->size() > stringByteLimit) {
      fail(RC::Capacity, "source-limit");
      return {};
    }
    if (s->size() > identifierByteLimit) {
      fail(RC::Capacity, "interactive-name-limit");
      return {};
    }
    if (!isIdentifier(*s)) {
      fail(RC::Syntax, "interactive-name");
      return {};
    }
    return s->str();
  }
  /// A list of strings other than names, such as types or attributes.
  Names strings(const V &v, size_t limit = listEntryLimit,
                size_t bytes = stringByteLimit) {
    return list(v, limit, [&](const V &x) { return string(x, bytes); });
  }
  Names names(const V &v) {
    return list(v, listEntryLimit, [&](const V &x) { return name(x); });
  }
  /// Rows of two names: capture rows, carried rows and entry role maps.
  protocol::Assignments pairs(const V &v) {
    return list(v, listEntryLimit,
                [&](const V &x) -> std::pair<std::string, std::string> {
                  const auto *p = array(x, 2);
                  return p ? std::make_pair(name((*p)[0]), name((*p)[1]))
                           : std::pair<std::string, std::string>{};
                });
  }
  std::vector<Parameter> parameters(const V &v) {
    return list(v, listEntryLimit, [&](const V &x) {
      const auto *p = array(x, 2);
      return p ? Parameter{name((*p)[0]), string((*p)[1])} : Parameter{};
    });
  }
  /// A canonical natural within `limit`. Overflowing digits exceed every
  /// natural bound of the carrier.
  uint64_t natural(const V &v, uint64_t limit, StringRef code) {
    auto text = string(v);
    if (!problem.empty())
      return 0;
    uint64_t value = 0;
    if (text.empty() || (text.size() > 1 && text.front() == '0') ||
        !llvm::all_of(text, [](char c) { return c >= '0' && c <= '9'; }))
      fail(RC::Syntax, code);
    else if (StringRef(text).getAsInteger(10, value) || value > limit)
      fail(RC::Capacity, code);
    return value;
  }
  // Local and participant bodies are distinct closed grammars. Their shared
  // selected-control tags differ in the capture field, so a reader decodes
  // them by body kind and never by guessing the field's shape.
  enum class BodyKind { Local, Participant };
  Body body(const V &v, BodyKind kind, unsigned depth = 0) {
    if (depth > bodyNestingLimit) {
      fail(RC::Capacity, "interactive-body-depth");
      return {};
    }
    return list(v, arrayElementLimit,
                [&](const V &x) { return instruction(x, kind, depth); });
  }
  Body functionBody(const V &v) {
    if (!v.getAsArray()) {
      fail(RC::Syntax, "interactive-external-body");
      return {};
    }
    return body(v, BodyKind::Local);
  }
  Instruction instruction(const V &v, BodyKind kind, unsigned depth) {
    Instruction out;

    const auto *r = array(v, {}, "interactive-instruction");
    if (!r)
      return out;
    if (r->empty()) {
      fail(RC::Syntax, "interactive-instruction");
      return out;
    }
    std::string tag = string((*r)[0]);
    auto fields = [&](size_t count, StringRef code) {
      if (r->size() == count)
        return true;
      fail(RC::Syntax, code);
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
      fail(RC::Syntax, "interactive-instruction");
      return out;
    }
    out.site = name((*r)[1]);
    if (tag == "op") {
      if (fields(6, "interactive-operation"))
        out.value = Operation{
            name((*r)[2]), strings((*r)[3], attributeLimit, parameterByteLimit),
            names((*r)[4]), names((*r)[5])};
    } else if (tag == "return_if") {
      if (fields(5, "interactive-return-type"))
        out.value = ReturnIf{name((*r)[2]), names((*r)[3]), names((*r)[4])};
    } else if (tag == "bool_constant") {
      if (fields(4, "native-boolean-shape")) {
        auto value = (*r)[3].getAsBoolean();
        if (!value)
          fail(RC::Syntax, "native-boolean-value");
        else
          out.value = BooleanConstant{name((*r)[2]), *value};
      }
    } else if (tag == "query") {
      if (fields(6, "service-query-shape"))
        out.value = ServiceQuery{name((*r)[2]), name((*r)[3]), names((*r)[4]),
                                 names((*r)[5])};
    } else if (tag == "local") {
      if (fields(5, "interactive-local-call"))
        out.value = LocalCall{name((*r)[2]), names((*r)[3]), names((*r)[4])};
    } else if (tag == "send") {
      if (fields(5, "interactive-send"))
        out.value = Send{name((*r)[2]), name((*r)[3]), name((*r)[4])};
    } else if (tag == "receive") {
      if (fields(6, "interactive-receive"))
        out.value = Receive{name((*r)[2]), name((*r)[3]), name((*r)[4]),
                            string((*r)[5])};
    } else if (tag == "stop") {
      if (fields(3, "interactive-stop"))
        out.value = Stop{string(r->back())};
    } else if (tag == "variant") {
      if (fields(6, "variant-shape"))
        out.value = VariantConstruct{string((*r)[2]), name((*r)[3]),
                                     names((*r)[4]), name((*r)[5])};
    } else if (tag == "match") {
      bool participant = kind == BodyKind::Participant;
      if (fields(6, participant ? "interactive-match-shape"
                                : "local-match-shape")) {
        // One arm per alternative, within the program's match limit.
        auto arms = [&] {
          const auto *items = (*r)[4].getAsArray();
          if (items && items->size() > matchAlternativeLimit) {
            fail(RC::Capacity,
                 participant ? "interactive-match-shape" : "local-match-shape");
            return std::vector<MatchArm>{};
          }
          return list((*r)[4], matchAlternativeLimit, [&](const V &v) {
            MatchArm arm;
            if (const auto *a = array(v, 3, "local-match-arm")) {
              arm.alternative = name((*a)[0]);
              arm.payload = names((*a)[1]);
              arm.body = body((*a)[2], kind, depth + 1);
            }
            return arm;
          });
        };
        // Braced initialization keeps field order, so the first reported
        // problem is the first malformed field.
        if (participant)
          out.value = ParticipantMatch{name((*r)[2]), pairs((*r)[3]), arms(),
                                       names((*r)[5])};
        else
          out.value =
              Match{name((*r)[2]), names((*r)[3]), arms(), names((*r)[5])};
      }
    } else if (tag == "if") {
      bool participant = kind == BodyKind::Participant;
      if (fields(7, participant ? "interactive-if-shape" : "local-if-shape")) {
        if (participant)
          out.value = ParticipantConditional{
              name((*r)[2]), pairs((*r)[3]), body((*r)[4], kind, depth + 1),
              body((*r)[5], kind, depth + 1), names((*r)[6])};
        else
          out.value = Conditional{
              name((*r)[2]), names((*r)[3]), body((*r)[4], kind, depth + 1),
              body((*r)[5], kind, depth + 1), names((*r)[6])};
      }
    } else if (tag == "for" || (tag == "for_while")) {
      if (fields(9, "local-for-shape"))
        out.value = For{name((*r)[2]),  name((*r)[3]),
                        name((*r)[4]),  pairs((*r)[5]),
                        names((*r)[6]), body((*r)[7], kind, depth + 1),
                        names((*r)[8]), tag == "for_while"};
    } else if (tag == "loop") {
      if (fields(7, "interactive-loop")) {
        Loop loop;
        if (const auto *count = array((*r)[2])) {
          if (count->size() == 4 && (*count)[0].getAsString() == "value") {
            loop.count.value = name((*count)[1]);
            loop.count.maximum = natural((*count)[2], loopMaximumLimit,
                                         "interactive-loop-count");
            loop.count.induction = name((*count)[3]);
          } else {
            fail(RC::Syntax, "interactive-loop-count");
          }
        }
        loop.carried = pairs((*r)[3]);
        loop.captures = pairs((*r)[4]);
        loop.body = body((*r)[5], kind, depth + 1);
        loop.outputs = names((*r)[6]);
        out.value = std::move(loop);
      }
    } else
      fail(RC::Syntax, "interactive-instruction");
    return out;
  }
  Function function(const V &v) {
    Function out;

    const auto *r = record(v, "function", 6);
    if (!r)
      return out;
    out.name = name((*r)[1]);
    out.arguments = parameters((*r)[2]);
    out.results = strings((*r)[3]);
    out.body = functionBody((*r)[4]);
    if (const auto *o = array((*r)[5], 2, "binding-logical-origin")) {
      // Assignment rows bind a parameter name to a static identity.
      auto definition = name((*o)[0]);
      out.origin = LogicalOrigin{
          std::move(definition),
          list((*o)[1], originAssignmentLimit,
               [&](const V &x) -> std::pair<std::string, std::string> {
                 const auto *p = array(x, 2);
                 return p ? std::make_pair(name((*p)[0]), string((*p)[1]))
                          : std::pair<std::string, std::string>{};
               })};
    }
    return out;
  }
  protocol::OperationBinding binding(const V &v) {
    protocol::OperationBinding out;

    if (const auto *r = array(v, 5, "binding-declaration")) {
      out.name = name((*r)[0]);
      out.application.contract = string((*r)[1]);
      out.application.arguments = strings((*r)[2], bindingArgumentLimit);
      out.application.implementation = string((*r)[3]);
      out.application.physicalArguments =
          strings((*r)[4], bindingArgumentLimit);
    }
    return out;
  }
  Participants participants(const V &v) {
    Participants out;

    const auto *r = array(v, 5);
    if (!r)
      return out;
    out.stage = Participants::Stage::Physical;
    out.bindings =
        list((*r)[1], bindingLimit, [&](const V &v) { return binding(v); });
    // Functions and participants share one definition bound, counted before
    // either list is decoded.
    const auto *functions = array((*r)[2]);
    const auto *participants = array((*r)[3]);
    if (functions && participants &&
        functions->size() + participants->size() > definitionLimit)
      fail(RC::Capacity, "interactive-definition-limit");
    if (!problem.empty())
      return out;
    out.functions =
        list((*r)[2], definitionLimit, [&](const V &x) { return function(x); });
    out.participants = list((*r)[3], definitionLimit, [&](const V &x) {
      Participant p;

      if (const auto *r = record(x, "participant", 8)) {
        p.name = name((*r)[1]);
        p.instance = name((*r)[2]);
        p.role = name((*r)[3]);
        p.arguments = this->parameters((*r)[4]);
        p.results = strings((*r)[5]);
        p.body = body((*r)[6], BodyKind::Participant);
        p.services = list((*r)[7], listEntryLimit, [&](const V &v) {
          ServicePort port;
          if (const auto *row = array(v, 3)) {
            port.name = name((*row)[0]);
            port.contract = string((*row)[1]);
            port.inputIndex =
                natural((*row)[2], UINT64_MAX, "service-port-index");
          }
          return port;
        });
      }
      return p;
    });
    out.entries = list((*r)[4], entryLimit, [&](const V &x) {
      ParticipantEntry e;

      if (const auto *r = record(x, "entry", 3)) {
        e.name = name((*r)[1]);
        e.participants = pairs((*r)[2]);
      }
      return e;
    });
    return out;
  }

public:
  Expected<Participants> run(const V &v) {
    const auto *r = v.getAsArray();
    if (!r || r->empty())
      return refuse(RC::Syntax, "interactive-shape");
    auto tag = string((*r)[0]);
    if (problem.empty() && tag != "zkc.program/0")
      return refuse(RC::Syntax, "interactive-format");
    auto result = participants(v);
    if (!problem.empty())
      return refuse(problemClass, problem);
    if (auto e = checkStructure(result))
      return std::move(e);
    return result;
  }
};
} // namespace
Expected<Participants> decode(const json::Value &v) {
  if (auto e = preflight(v))
    return std::move(e);
  return Decoder().run(v);
}
} // namespace zkc::program
