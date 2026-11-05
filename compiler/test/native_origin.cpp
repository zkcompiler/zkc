#include "zkc/Contracts/NativeOrigin.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Support/LogicalTree.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/raw_ostream.h"
#include <limits>
using namespace llvm;
using namespace zkc::protocol;
namespace {
bool require(bool condition, StringRef detail) {
  if (!condition)
    errs() << "native origin: " << detail << '\n';
  return condition;
}
template <typename T> bool rejects(Expected<T> result) {
  if (result)
    return require(false, "invalid origin accepted");
  bool correctCode = false;
  handleAllErrors(result.takeError(), [&](const zkc::Refusal &refusal) {
    correctCode = refusal.code == "interactive-native-origin";
  });
  return require(correctCode, "unexpected refusal identifier");
}
bool rejectsEveryEncoding(const NativeOriginTemplate &origin) {
  // Check each independently so no unchecked Expected is left on failure.
  bool valid = rejects(encodeNativeOriginTemplate(origin));
  valid &= rejects(layoutNativeOrigin(origin, NativeOriginFormat::Template));
  valid &= rejects(layoutNativeOrigin(origin, NativeOriginFormat::Dynamic));
  return valid;
}
// Reference trees are supplied independently of the typed path/event. Compare
// complete bytes against the general logical-tree encoder, not another origin
// encoder. Coordinates are decimal strings, including the full u64 boundary.
bool checkLayout(const NativeOriginTemplate &origin, const json::Array &path,
                 const json::Array &event, ArrayRef<uint64_t> coordinates) {
  for (auto format :
       {NativeOriginFormat::Template, NativeOriginFormat::Dynamic}) {
    auto layout = layoutNativeOrigin(origin, format);
    if (!layout) {
      errs() << toString(layout.takeError()) << '\n';
      return false;
    }
    if (!require(layout->coordinates == coordinates.size(),
                 "coordinate count must count repeats only"))
      return false;
    json::Array values;
    if (format == NativeOriginFormat::Dynamic)
      for (uint64_t coordinate : coordinates)
        values.push_back(std::to_string(coordinate));
    auto middle = zkc::encodeLogicalTree(json::Array(values));
    if (!middle) {
      consumeError(middle.takeError());
      return false;
    }
    StringRef tag = format == NativeOriginFormat::Template
                        ? "zkc.native-origin-template/0"
                        : "zkc.native-origin/0";
    auto expected = zkc::encodeLogicalTree(
        json::Array{tag, origin.entry, json::Array(path), json::Array(values),
                    json::Array(event)});
    if (!expected) {
      consumeError(expected.takeError());
      return false;
    }
    if (!require(layout->prefix + *middle + layout->suffix == *expected,
                 "spliced bytes differ from the complete canonical tree"))
      return false;
    auto suffix = zkc::encodeLogicalTree(json::Array(event));
    if (!suffix) {
      consumeError(suffix.takeError());
      return false;
    }
    if (!require(layout->suffix == *suffix,
                 "suffix must contain only the event"))
      return false;
    if (format == NativeOriginFormat::Template) {
      auto encoded = encodeNativeOriginTemplate(origin);
      if (!encoded) {
        consumeError(encoded.takeError());
        return false;
      }
      if (!require(*encoded == toHex(*expected, true),
                   "template hex changed from canonical bytes"))
        return false;
      auto decoded = decodeNativeOriginTemplate(*encoded);
      if (!decoded) {
        consumeError(decoded.takeError());
        return false;
      }
      auto roundTrip = encodeNativeOriginTemplate(*decoded);
      if (!roundTrip) {
        consumeError(roundTrip.takeError());
        return false;
      }
      if (!require(*roundTrip == *encoded, "template round trip changed bytes"))
        return false;
    } else if (!require(expected->size() <= 4096,
                        "dynamic byte limit exceeded"))
      return false;
  }
  return true;
}
bool layoutTests() {
  using Kind = NativeOriginStep::Kind;
  constexpr uint64_t largest = std::numeric_limits<uint64_t>::max();
  NativeOriginTemplate origin;
  origin.entry = "main";
  origin.event = NativeMessageOrigin{"Round", "reply", "Schema", "P", "V"};
  const json::Array message{"message", "Round", "reply", "Schema", "P", "V"};
  if (!checkLayout(origin, {}, message, {}))
    return false;
  origin.path = {{Kind::Apply, "main", "helper"}};
  if (!checkLayout(
          origin,
          json::Array{json::Value(json::Array{"apply", "main", "helper"})},
          message, {}))
    return false;
  // The branch-only path still needs no coordinate and preserves each label.
  for (StringRef arm : {"then", "else", "some", "!~"}) {
    origin.path = {{Kind::Branch, "Round", "choice", arm.str()}};
    if (!checkLayout(origin,
                     json::Array{json::Value(
                         json::Array{"branch", "Round", "choice", arm})},
                     message, {}))
      return false;
    // This one-repeat example also mirrors the existing Rust origin fixture.
    origin.path = {{Kind::Apply, "main", "helper"},
                   {Kind::Repeat, "Round", "rounds"},
                   {Kind::Branch, "Round", "choice", arm.str()}};
    if (!checkLayout(origin,
                     json::Array{json::Array{"apply", "main", "helper"},
                                 json::Array{"repeat", "Round", "rounds"},
                                 json::Array{"branch", "Round", "choice", arm}},
                     message, {7}))
      return false;
  }
  origin.path = {{Kind::Repeat, "main", "outer"},
                 {Kind::Branch, "main", "choice", "then"},
                 {Kind::Apply, "main", "helper"},
                 {Kind::Branch, "Round", "choice", "some"},
                 {Kind::Repeat, "Round", "inner"}};
  const json::Array nested{json::Array{"repeat", "main", "outer"},
                           json::Array{"branch", "main", "choice", "then"},
                           json::Array{"apply", "main", "helper"},
                           json::Array{"branch", "Round", "choice", "some"},
                           json::Array{"repeat", "Round", "inner"}};
  if (!checkLayout(origin, nested, message, {0, largest}) ||
      !checkLayout(origin, nested, message, {largest, 0}))
    return false;
  origin.event =
      NativeQueryOrigin{"Round", "draw", largest, "random", "draw", "V"};
  if (!checkLayout(origin, nested,
                   json::Array{"query", "Round", "draw",
                               "input_18446744073709551615", "random", "draw",
                               "V"},
                   {0, largest}))
    return false;
  origin.event = NativeStartOrigin{"Round", "child"};
  if (!checkLayout(origin, nested, json::Array{"start", "Round", "child"},
                   {0, largest}))
    return false;

  if (!rejects(layoutNativeOrigin(origin, static_cast<NativeOriginFormat>(-1))))
    return false;
  auto invalid = origin;
  invalid.path[0].kind = static_cast<Kind>(-1);
  if (!rejectsEveryEncoding(invalid))
    return false;
  for (auto kind : {Kind::Apply, Kind::Repeat}) {
    invalid = origin;
    invalid.path[0] = {kind, "main", "site", "then"};
    if (!rejectsEveryEncoding(invalid))
      return false;
  }
  for (size_t count : {64u, 65u}) {
    invalid = origin;
    invalid.path.assign(count, {Kind::Apply, "a", "b"});
    // Even 64 minimal steps exceed the independent 2048-byte template limit.
    if (!rejectsEveryEncoding(invalid))
      return false;
  }
  // Exact step widths and an empty template coordinate array remain required.
  // In particular, a branch label is a fourth field, never a coordinate.
  for (const auto &step :
       {json::Array{"branch", "Round", "choice"},
        json::Array{"branch", "Round", "choice", ""},
        json::Array{"branch", "Round", "choice", "then", "extra"},
        json::Array{"apply", "Round", "helper", "then"},
        json::Array{"repeat", "Round", "rounds", "then"},
        json::Array{"unknown", "Round", "choice"}}) {
    auto bytes = zkc::encodeLogicalTree(json::Array{
        "zkc.native-origin-template/0", "main", json::Array{json::Array(step)},
        json::Array{}, json::Array(message)});
    if (!bytes) {
      consumeError(bytes.takeError());
      return false;
    }
    if (!rejects(decodeNativeOriginTemplate(toHex(*bytes, true))))
      return false;
  }
  auto nonempty = zkc::encodeLogicalTree(
      json::Array{"zkc.native-origin-template/0", "main",
                  json::Array{json::Array{"branch", "Round", "choice", "then"}},
                  json::Array{"0"}, json::Array(message)});
  if (!nonempty) {
    consumeError(nonempty.takeError());
    return false;
  }
  if (!rejects(decodeNativeOriginTemplate(toHex(*nonempty, true))))
    return false;

  // Exercise every name slot in every event variant and in a branch step.
  for (unsigned eventKind = 0; eventKind != 3; ++eventKind) {
    NativeOriginTemplate names;
    names.entry = "main";
    names.path = {{Kind::Branch, "main", "choice", "then"}};
    std::vector<std::string *> fields{&names.entry, &names.path[0].protocol,
                                      &names.path[0].site,
                                      &names.path[0].alternative};
    if (eventKind == 0) {
      names.event =
          NativeQueryOrigin{"Round", "draw", 0, "random", "draw", "V"};
      auto &event = std::get<NativeQueryOrigin>(names.event);
      fields.insert(fields.end(), {&event.protocol, &event.site, &event.service,
                                   &event.method, &event.owner});
    } else if (eventKind == 1) {
      names.event = NativeMessageOrigin{"Round", "reply", "Schema", "P", "V"};
      auto &event = std::get<NativeMessageOrigin>(names.event);
      fields.insert(fields.end(), {&event.protocol, &event.site, &event.schema,
                                   &event.sender, &event.receiver});
    } else {
      names.event = NativeStartOrigin{"Round", "child"};
      auto &event = std::get<NativeStartOrigin>(names.event);
      fields.insert(fields.end(), {&event.protocol, &event.site});
    }
    for (auto *field : fields) {
      auto saved = *field;
      for (const auto &bad :
           {std::string(), std::string("has space"), std::string("\0", 1),
            std::string("\x1f", 1), std::string("\x7f", 1),
            std::string("\x80", 1), std::string(129, 'a')}) {
        *field = bad;
        if (!rejectsEveryEncoding(names))
          return false;
      }
      *field = std::string(128, '~');
      auto encoded = encodeNativeOriginTemplate(names);
      if (!encoded) {
        consumeError(encoded.takeError());
        return false;
      }
      auto decoded = decodeNativeOriginTemplate(*encoded);
      if (!decoded) {
        consumeError(decoded.takeError());
        return false;
      }
      *field = std::move(saved);
    }
  }

  // Pin the exact template byte boundary; Dynamic must not admit a 2049-byte
  // template merely because its format tag is nine bytes shorter.
  origin.entry = "e";
  origin.path.assign(43, {Kind::Repeat, "a", "b"});
  origin.event = NativeStartOrigin{"a", "b"};
  json::Array repeats;
  for (unsigned i = 0; i != 43; ++i)
    repeats.push_back(json::Array{"repeat", "a", "b"});
  auto small = zkc::encodeLogicalTree(json::Array{
      "zkc.native-origin-template/0", origin.entry, json::Array(repeats),
      json::Array{}, json::Array{"start", "a", "b"}});
  if (!small) {
    consumeError(small.takeError());
    return false;
  }
  if (!require(small->size() < 2048 && 2048 - small->size() < 128,
               "boundary fixture must fit by padding only the entry"))
    return false;
  origin.entry.append(2048 - small->size(), 'e');
  std::vector<uint64_t> coordinates(43, largest);
  if (!checkLayout(origin, repeats, json::Array{"start", "a", "b"},
                   coordinates))
    return false;
  auto exact = encodeNativeOriginTemplate(origin);
  if (!exact) {
    consumeError(exact.takeError());
    return false;
  }
  if (!require(exact->size() == 4096, "exact template byte boundary changed"))
    return false;
  origin.entry.push_back('e');
  return rejectsEveryEncoding(origin);
}
} // namespace
int main() {
  if (!layoutTests())
    return 1;
  auto refuses = [](Error e) {
    bool failed = bool(e);
    consumeError(std::move(e));
    return failed;
  };
  auto indexed = encodeNativeOriginTemplate(
      {"main",
       {{NativeOriginStep::Kind::Repeat, "main", "rounds"},
        {NativeOriginStep::Kind::Apply, "main", "step"}},
       NativeQueryOrigin{"Round", "draw", 2, "random.bls12-381.fr/0", "draw",
                         "V"}});
  if (!indexed) {
    errs() << toString(indexed.takeError());
    return 1;
  }
  if (refuses(
          checkParameters("transcript.native.indexed.challenge", {*indexed})) ||
      !refuses(checkParameters("transcript.native.indexed.observe.data",
                               {*indexed})))
    return 1;
  // A field challenge and a UniformIndex transition name different methods.
  auto index = encodeNativeOriginTemplate(
      {"main",
       {{NativeOriginStep::Kind::Repeat, "main", "rounds"}},
       NativeQueryOrigin{"Round", "sample", 2,
                         "random.koala-bear.ext8-binomial3/0", "index", "V"}});
  if (!index) {
    errs() << toString(index.takeError());
    return 1;
  }
  if (refuses(checkParameters("transcript.native.indexed.index", {*index})) ||
      !refuses(
          checkParameters("transcript.native.indexed.index", {*indexed})) ||
      !refuses(
          checkParameters("transcript.native.indexed.challenge", {*index})) ||
      refuses(checkNativeOrigin(*index, "query")) ||
      !refuses(checkNativeOrigin(*index, "query", "draw")))
    return 1;
  for (size_t end = 0; end < indexed->size(); ++end)
    if (!refuses(
            checkNativeOrigin(StringRef(*indexed).take_front(end), "query")))
      return 1;
  for (auto value :
       {*indexed + "00", StringRef(*indexed).upper(), std::string(4098, '0')})
    if (!refuses(checkNativeOrigin(value, "query")))
      return 1;
  auto message = encodeNativeOriginTemplate(
      {"main",
       {},
       NativeMessageOrigin{"Round", "response", "response", "P", "V"}});
  if (!message) {
    consumeError(message.takeError());
    return 1;
  }
  if (refuses(checkParameters("transcript.native.indexed.observe.data",
                              {*message})))
    return 1;
  for (auto entry : {"", "has space"}) {
    auto bad = encodeNativeOriginTemplate(
        {entry, {}, NativeMessageOrigin{"Round", "r", "r", "P", "V"}});
    if (bad)
      return 1;
    consumeError(bad.takeError());
  }
  for (StringRef port : {"service_2", "input_", "input_01", "input_+1",
                         "input_18446744073709551616"}) {
    // Invalid port spellings are byte-reader cases; typed service inputs
    // cannot represent them.
    auto bytes = zkc::encodeLogicalTree(json::Array{
        "zkc.native-origin-template/0", "main", json::Array{}, json::Array{},
        json::Array{"query", "Round", "draw", port.str(), "random", "draw",
                    "V"}});
    if (!bytes) {
      consumeError(bytes.takeError());
      return 1;
    }
    auto bad = decodeNativeOriginTemplate(toHex(*bytes, true));
    if (bad)
      return 1;
    consumeError(bad.takeError());
  }
  for (auto step : {"call", "unknown"}) {
    auto bytes = zkc::encodeLogicalTree(json::Array{
        "zkc.native-origin-template/0", "main",
        json::Array{json::Array{step, "main", "step"}}, json::Array{},
        json::Array{"message", "Round", "r", "r", "P", "V"}});
    if (!bytes) {
      consumeError(bytes.takeError());
      return 1;
    }
    auto bad = decodeNativeOriginTemplate(toHex(*bytes, true));
    if (bad)
      return 1;
    consumeError(bad.takeError());
  }
  NativeOriginTemplate selected;
  selected.entry = "main";
  selected.path.push_back(
      {NativeOriginStep::Kind::Branch, "main", "choose", "then"});
  selected.event = NativeMessageOrigin{"main", "message", "message", "P", "V"};
  auto thenOrigin = encodeNativeOriginTemplate(selected);
  if (!thenOrigin) {
    errs() << toString(thenOrigin.takeError());
    return 1;
  }
  auto decoded = decodeNativeOriginTemplate(*thenOrigin);
  if (!decoded) {
    consumeError(decoded.takeError());
    return 1;
  }
  if (decoded->path.size() != 1 ||
      decoded->path[0].kind != NativeOriginStep::Kind::Branch ||
      decoded->path[0].alternative != "then")
    return 1;
  selected.path[0].alternative = "else";
  auto elseOrigin = encodeNativeOriginTemplate(selected);
  if (!elseOrigin || *elseOrigin == *thenOrigin) {
    if (!elseOrigin)
      consumeError(elseOrigin.takeError());
    return 1;
  }
  selected.path[0].alternative.clear();
  auto missingArm = encodeNativeOriginTemplate(selected);
  if (missingArm)
    return 1;
  consumeError(missingArm.takeError());
  selected.path[0].kind = NativeOriginStep::Kind::Repeat;
  selected.path[0].alternative = "then";
  auto extraArm = encodeNativeOriginTemplate(selected);
  if (extraArm)
    return 1;
  consumeError(extraArm.takeError());
  for (size_t end = 0; end < thenOrigin->size(); ++end)
    if (!refuses(checkNativeOrigin(StringRef(*thenOrigin).take_front(end),
                                   "message")))
      return 1;
  // A plain origin header cannot be substituted for the indexed template.
  auto plain = *message;
  const std::string current =
      "7a6b632e6e61746976652d6f726967696e2d74656d706c6174652f30";
  auto start = plain.find(current);
  if (start == std::string::npos)
    return 1;
  plain.replace(start, current.size(),
                "7a6b632e6e61746976652d6f726967696e2f30");
  plain.replace(start - 16, 16, "1300000000000000");
  if (!refuses(checkNativeOrigin(plain, "message")))
    return 1;
}
