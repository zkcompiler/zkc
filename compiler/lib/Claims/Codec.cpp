#include "Internal.h"
#include "zkc/Target/Json.h"

using namespace llvm;
namespace zkc::claims {
namespace {
json::Array names(const source::Names &values) {
  json::Array out;
  for (const auto &value : values)
    out.push_back(value);
  return out;
}
struct Reader {
  size_t bytes = 0, records = 0;
  bool valid = true;
  const json::Array &array(const json::Value &value, size_t size = SIZE_MAX) {
    static const json::Array empty;
    const auto *a = value.getAsArray();
    if (!a || a->size() > maxRecords ||
        (size != SIZE_MAX && a->size() != size) ||
        records > maxItems - a->size()) {
      valid = false;
      return empty;
    }
    records += a->size();
    return *a;
  }
  std::string string(const json::Value &value) {
    auto s = value.getAsString();
    if (!s || s->empty() || s->size() > 4096 ||
        bytes > 1024 * 1024 - s->size() || !json::isUTF8(*s) ||
        s->contains('\0')) {
      valid = false;
      return {};
    }
    bytes += s->size();
    return s->str();
  }
  source::Names strings(const json::Value &value) {
    source::Names out;
    for (const auto &v : array(value))
      out.push_back(string(v));
    return out;
  }
};
} // namespace
Expected<Contract> decodeContract(const json::Value &value) {
  Reader r;
  const auto &a = r.array(value, 10);
  if (!r.valid)
    return error("claim-contract-format");
  if (r.string(a[0]) != "zkc.claim-contract/1")
    return error("claim-contract-format");
  Contract c;
  c.sourceDigest = r.string(a[1]);
  c.entry = r.string(a[2]);
  c.validator = r.string(a[3]);
  for (const auto &v : r.array(a[4])) {
    const auto &p = r.array(v, 3);
    if (!r.valid)
      return error("claim-contract-format");
    c.kinds.push_back({r.string(p[0]), r.strings(p[1]), r.string(p[2])});
  }
  for (const auto &v : r.array(a[5])) {
    const auto &p = r.array(v, 3);
    if (!r.valid)
      return error("claim-contract-format");
    c.claims.push_back({r.string(p[0]), r.string(p[1]), r.strings(p[2])});
  }
  c.required = r.strings(a[6]);
  for (const auto &v : r.array(a[7])) {
    const auto &p = r.array(v, 2);
    if (!r.valid)
      return error("claim-contract-format");
    c.terminals.push_back({r.string(p[0]), r.string(p[1])});
  }
  for (const auto &v : r.array(a[8])) {
    const auto &p = r.array(v, 3);
    if (!r.valid || r.string(p[1]) != "trust")
      return error("claim-contract-format");
    c.laws.push_back({r.string(p[0]), r.string(p[2])});
  }
  for (const auto &v : r.array(a[9])) {
    const auto &p = r.array(v, 9);
    if (!r.valid)
      return error("claim-contract-format");
    c.rules.push_back({r.string(p[0]), r.string(p[1]), r.string(p[2]),
                       r.string(p[3]), r.strings(p[4]), r.strings(p[5]),
                       r.strings(p[6]), r.strings(p[7]), r.string(p[8])});
  }
  if (!r.valid)
    return error("claim-contract-format");
  return c;
}
json::Value encode(const Contract &c) {
  json::Array kinds, claims, terminals, laws, rules;
  for (const auto &k : c.kinds)
    kinds.push_back(json::Array{k.name, names(k.types), k.meaning});
  for (const auto &p : c.claims)
    claims.push_back(json::Array{p.name, p.kind, names(p.values)});
  for (const auto &t : c.terminals)
    terminals.push_back(json::Array{t.claim, t.guard});
  for (const auto &l : c.laws)
    laws.push_back(json::Array{l.name, "trust", l.premise});
  for (const auto &r : c.rules)
    rules.push_back(json::Array{
        r.name, r.law, r.invocation, r.callee, names(r.inputs),
        names(r.outputs), names(r.guards), names(r.premises), r.conclusion});
  return json::Array{"zkc.claim-contract/1",
                     c.sourceDigest,
                     c.entry,
                     c.validator,
                     std::move(kinds),
                     std::move(claims),
                     names(c.required),
                     std::move(terminals),
                     std::move(laws),
                     std::move(rules)};
}
Expected<Certificate> decodeCertificate(const json::Value &value) {
  Reader r;
  const auto &a = r.array(value, 4);
  if (!r.valid || r.string(a[0]) != "zkc.claim-certificate/1")
    return error("claim-certificate-format");
  Certificate c{r.string(a[1]), r.string(a[2]), r.strings(a[3])};
  if (!r.valid)
    return error("claim-certificate-format");
  return c;
}
json::Value encode(const Certificate &c) {
  return json::Array{"zkc.claim-certificate/1", c.sourceDigest,
                     c.contractDigest, names(c.steps)};
}
} // namespace zkc::claims
