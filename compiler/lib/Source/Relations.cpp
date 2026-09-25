#include "zkc/Source/Relations.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include <functional>
#include <set>

using namespace llvm;
namespace zkc::relation {
namespace {
Error declarations(const source::Module &m) {
  if (m.relations.size() > DependencyLimits::count ||
      m.relationViews.size() > DependencyLimits::count)
    return zkc::error("relation-dependency-limit");
  std::set<std::string> symbols;
  size_t bytes = 0;
  for (const auto &r : m.relations) {
    if (!isValidSymbol(r.name))
      return zkc::error("relation-symbol");
    if (!symbols.insert(r.name).second)
      return zkc::error("relation-duplicate-alias");
    bool valid = std::visit([](const auto &p) { return bool(p); }, r.value);
    if (!valid)
      return zkc::error("relation-unresolved");
    auto value = std::visit([](const auto &p) { return p->encode(); }, r.value);
    auto size = zkc::printJson(value).size();
    if (size > DependencyLimits::bytes - bytes)
      return zkc::error("relation-dependency-limit");
    bytes += size;
  }
  for (const auto &v : m.relationViews) {
    if (!isValidSymbol(v.name))
      return zkc::error("relation-symbol");
    if (!symbols.insert(v.name).second)
      return zkc::error("relation-duplicate-alias");
  }
  auto reserve = [&](const auto &values) {
    for (const auto &v : values)
      if (symbols.count(v.name))
        return false;
    return true;
  };
  if (!reserve(m.functions) || !reserve(m.bindings) || !reserve(m.protocols) ||
      !reserve(m.definitions) || !reserve(m.configurations) ||
      !reserve(m.instances) || !reserve(m.entries))
    return zkc::error("relation-duplicate-alias");
  return Error::success();
}
json::Value function(const source::Function &f) {
  source::Module m;
  m.functions.push_back(f);
  auto &copy = m.functions.back();
  std::map<std::string, std::string> names;
  size_t next = 0;
  for (auto &p : copy.arguments) {
    auto name = "arg" + std::to_string(next++);
    names[p.name] = name;
    p.name = name;
  }
  auto rename = [&](source::Names &values, bool define) {
    for (auto &value : values) {
      if (define)
        names[value] = "v" + std::to_string(next++);
      auto found = names.find(value);
      if (found != names.end())
        value = found->second;
    }
  };
  if (copy.body)
    for (auto &i : *copy.body) {
      if (auto *op = i.get<source::Operation>()) {
        rename(op->inputs, false);
        rename(op->outputs, true);
      } else if (auto *ret = i.get<source::Return>())
        rename(ret->values, false);
    }
  return source::encode(m);
}
} // namespace

Expected<json::Value> readSnapshotJSON(StringRef text, size_t maximumBytes) {
  if (text.size() > maximumBytes)
    return zkc::error("relation-dependency-limit");
  struct Level {
    char open;
    std::set<std::string> keys;
  };
  std::vector<Level> stack;
  size_t nodes = 0;
  for (size_t i = 0; i < text.size(); ++i) {
    char c = text[i];
    if (c == '"') {
      size_t start = i++;
      while (i < text.size() && text[i] != '"') {
        if (text[i] == '\\')
          ++i;
        ++i;
      }
      if (i >= text.size() ||
          !zkc::validStringEncoding(text.slice(start, i + 1)))
        return zkc::error("relation-json");
      size_t next = i + 1;
      while (next < text.size() && isSpace(text[next]))
        ++next;
      if (next < text.size() && text[next] == ':') {
        auto key = json::parse(text.slice(start, i + 1));
        if (stack.empty() || stack.back().open != '{' || !key ||
            !stack.back().keys.insert(key->getAsString()->str()).second) {
          if (!key)
            consumeError(key.takeError());
          return zkc::error("relation-json");
        }
      }
      ++nodes;
    } else if (c == '[' || c == '{') {
      stack.push_back({c, {}});
      if (stack.size() > 256)
        return zkc::error("relation-depth-limit");
      ++nodes;
    } else if (c == ']' || c == '}') {
      if (stack.empty() || stack.back().open != (c == ']' ? '[' : '{'))
        return zkc::error("relation-json");
      stack.pop_back();
    }
    if (nodes > 16 * 1024 * 1024)
      return zkc::error("relation-node-limit");
  }
  if (!stack.empty())
    return zkc::error("relation-json");
  auto parsed = json::parse(text);
  if (!parsed) {
    consumeError(parsed.takeError());
    return zkc::error("relation-json");
  }
  return parsed;
}

std::string identity(const source::RelationDeclaration &r) {
  if (auto p = std::get_if<std::shared_ptr<const R1CS>>(&r.value))
    return (*p)->identity();
  return std::get<std::shared_ptr<const AIR>>(r.value)->identity();
}
Expected<source::Module> materializeRelations(const source::Module &source) {
  if (auto e = source::checkStructure(source))
    return std::move(e);
  auto verified = authoredSource(source);
  if (!verified)
    return verified.takeError();
  // Keep the actual checked arithmetic, including origin identities and
  // potentially failing guards. Only compile-time ownership is discharged.
  source::Module result = source;
  result.relations.clear();
  result.relationViews.clear();
  if (auto e = source::checkStructure(result))
    return std::move(e);
  return result;
}
Expected<source::Module> generateView(const source::Module &m,
                                      const source::RelationView &v) {
  auto found =
      find_if(m.relations, [&](const auto &r) { return r.name == v.relation; });
  if (found == m.relations.end())
    return zkc::error("relation-view-target");
  if (v.kind == "multilinear" || v.kind == "rank_one") {
    auto relation = std::get_if<std::shared_ptr<const R1CS>>(&found->value);
    if (!relation || !*relation || v.height)
      return zkc::error("relation-view-family");
    if (v.staging != "specialized" && v.staging != "public_matrices")
      return zkc::error("relation-view-staging");
    if (v.kind == "rank_one")
      return lowerRankOneR1CS(**relation, v.name,
                              v.staging == "specialized"
                                  ? Staging::Specialized
                                  : Staging::PublicMatrices);
    return lowerMultilinearR1CS(**relation, v.name,
                                v.staging == "specialized"
                                    ? Staging::Specialized
                                    : Staging::PublicMatrices);
  }
  if (v.kind == "arithmetic") {
    auto relation = std::get_if<std::shared_ptr<const AIR>>(&found->value);
    if (!relation || !*relation)
      return zkc::error("relation-view-family");
    if (v.staging != "specialized")
      return zkc::error("relation-view-staging");
    return lowerAIRArithmetic(**relation, v.name, v.height);
  }
  return zkc::error("relation-view-kind");
}
Error materializeViews(source::Module &m) {
  if (auto e = declarations(m))
    return e;
  source::Module generated;
  std::set<std::string> names;
  auto reserve = [&](const auto &values) {
    for (const auto &v : values)
      names.insert(v.name);
  };
  reserve(m.functions);
  reserve(m.bindings);
  reserve(m.definitions);
  reserve(m.configurations);
  reserve(m.protocols);
  reserve(m.instances);
  reserve(m.entries);
  reserve(m.relations);
  reserve(m.relationViews);
  for (const auto &v : m.relationViews) {
    auto part = generateView(m, v);
    if (!part)
      return part.takeError();
    for (auto &f : part->functions) {
      if (!names.insert(f.name).second)
        return zkc::error("relation-generated-collision");
      generated.functions.push_back(std::move(f));
    }
    for (auto &b : part->bindings) {
      if (!names.insert(b.name).second)
        return zkc::error("relation-generated-collision");
      generated.bindings.push_back(std::move(b));
    }
  }
  m.functions.insert(m.functions.end(), generated.functions.begin(),
                     generated.functions.end());
  m.bindings.insert(m.bindings.end(), generated.bindings.begin(),
                    generated.bindings.end());
  return Error::success();
}
Expected<source::Module> authoredSource(const source::Module &m) {
  if (auto e = declarations(m))
    return std::move(e);
  source::Module result = m;
  std::set<std::string> functions, bindings;
  for (const auto &v : m.relationViews) {
    auto expected = generateView(m, v);
    if (!expected)
      return expected.takeError();
    for (const auto &f : expected->functions) {
      if (!functions.insert(f.name).second)
        return zkc::error("relation-generated-collision");
      auto found =
          find_if(m.functions, [&](const auto &x) { return x.name == f.name; });
      if (found == m.functions.end() || function(f) != function(*found) ||
          count_if(m.functions,
                   [&](const auto &x) { return x.name == f.name; }) != 1)
        return zkc::error("relation-generated-function");
    }
    for (const auto &b : expected->bindings) {
      if (!bindings.insert(b.name).second)
        return zkc::error("relation-generated-collision");
      auto found =
          find_if(m.bindings, [&](const auto &x) { return x.name == b.name; });
      if (found == m.bindings.end() ||
          found->application.contract != b.application.contract ||
          found->application.arguments != b.application.arguments ||
          count_if(m.bindings,
                   [&](const auto &x) { return x.name == b.name; }) != 1)
        return zkc::error("relation-generated-binding");
      // Physical selections belong to source bindings and must not disappear
      // from the compact snapshot when generated code is reconstructed.
      if (!found->application.implementation.empty())
        return zkc::error("relation-generated-selection");
    }
  }
  llvm::erase_if(result.functions,
                 [&](const auto &f) { return functions.count(f.name); });
  llvm::erase_if(result.bindings,
                 [&](const auto &b) { return bindings.count(b.name); });
  result.relations.clear();
  result.relationViews.clear();
  return result;
}
json::Value encodeDeclarations(const source::Module &m) {
  json::Array relations, views;
  for (const auto &r : m.relations)
    relations.push_back(json::Array{
        r.name,
        std::visit([](const auto &p) { return p->encode(); }, r.value)});
  for (const auto &v : m.relationViews)
    views.push_back(json::Array{v.name, v.relation, v.kind, v.staging,
                                std::to_string(v.height)});
  return json::Array{std::move(relations), std::move(views)};
}
Error decodeDeclarations(const json::Value &value, source::Module &m) {
  auto *pair = value.getAsArray();
  if (!pair || pair->size() != 2)
    return zkc::error("relation-source-shape");
  auto *relations = (*pair)[0].getAsArray();
  auto *views = (*pair)[1].getAsArray();
  if (relations && relations->empty())
    return zkc::error("relation-source-shape");
  if (!relations || !views || relations->size() > DependencyLimits::count ||
      views->size() > DependencyLimits::count)
    return zkc::error("relation-dependency-limit");
  for (const auto &item : *relations) {
    auto *row = item.getAsArray();
    if (!row || row->size() != 2 || !(*row)[0].getAsString())
      return zkc::error("relation-source-shape");
    source::RelationDeclaration r;
    r.name = (*row)[0].getAsString()->str();
    auto *object = (*row)[1].getAsObject();
    if (object) {
      auto air = readAIR((*row)[1]);
      if (!air)
        return air.takeError();
      r.value = std::make_shared<const AIR>(std::move(*air));
    } else {
      auto r1cs = decodeR1CS((*row)[1]);
      if (!r1cs)
        return r1cs.takeError();
      r.value = std::make_shared<const R1CS>(std::move(*r1cs));
    }
    m.relations.push_back(std::move(r));
  }
  for (const auto &item : *views) {
    auto *row = item.getAsArray();
    if (!row || row->size() != 5 || !all_of(*row, [](const auto &x) {
          return x.getAsString().has_value();
        }))
      return zkc::error("relation-source-shape");
    source::RelationView v;
    v.name = (*row)[0].getAsString()->str();
    v.relation = (*row)[1].getAsString()->str();
    v.kind = (*row)[2].getAsString()->str();
    v.staging = (*row)[3].getAsString()->str();
    auto height = (*row)[4].getAsString();
    if (height->empty() || (height->size() > 1 && height->front() == '0') ||
        height->getAsInteger(10, v.height))
      return zkc::error("relation-view-height");
    m.relationViews.push_back(std::move(v));
  }
  return declarations(m);
}
Error checkEmbeddedRelations(const json::Value &protocol,
                             const source::Module &m) {
  std::set<std::string> subjects;
  for (const auto &r : m.relations)
    subjects.insert(zkc::printJson(
        std::visit([](const auto &p) { return p->encode(); }, r.value)));
  // A relation descriptor is an array tagged zkc.relation.* or an AIR object;
  // other nominal text (declaration identities, labels) is left alone.
  auto describesRelation = [](const json::Value &v) {
    if (const auto *object = v.getAsObject()) {
      auto schema = object->getString("schema");
      return schema && schema->starts_with("zkc.air");
    }
    if (const auto *array = v.getAsArray())
      if (!array->empty())
        if (auto tag = (*array)[0].getAsString())
          return tag->starts_with("zkc.relation.");
    return false;
  };
  bool foreign = false;
  std::function<void(const json::Value &)> nominal;
  std::function<void(StringRef)> type = [&](StringRef spelling) {
    // Malformed spellings are refused by admission; nothing to compare here.
    auto descriptor = protocol::decodeVariant(spelling);
    if (!descriptor)
      return;
    nominal(descriptor->nominal);
    for (const auto &alternative : descriptor->alternatives)
      for (const auto &payload : alternative.payload)
        if (StringRef(payload).starts_with("variant:"))
          type(payload);
  };
  nominal = [&](const json::Value &v) {
    if (foreign)
      return;
    if (auto text = v.getAsString()) {
      if (text->starts_with("variant:")) {
        type(*text);
        return;
      }
      if (text->empty() || (text->front() != '[' && text->front() != '{'))
        return;
      // The JSON reader recurses once per level, and a nominal may be long
      // enough to exhaust the stack. A relation encoding is shallow, so text
      // nested deeper than any encoding cannot match the table and is refused
      // like any relation the table does not hold.
      size_t depth = 0, deepest = 0;
      for (size_t i = 0; i < text->size(); ++i) {
        char c = (*text)[i];
        if (c == '"') {
          for (++i; i < text->size() && (*text)[i] != '"'; ++i)
            if ((*text)[i] == '\\')
              ++i;
        } else if (c == '[' || c == '{') {
          deepest = std::max(deepest, ++depth);
        } else if ((c == ']' || c == '}') && depth) {
          --depth;
        }
      }
      if (deepest > 512) {
        foreign = true;
        return;
      }
      auto parsed = json::parse(*text);
      if (!parsed) {
        consumeError(parsed.takeError());
        return;
      }
      if (describesRelation(*parsed) && !subjects.count(text->str()))
        foreign = true;
      return;
    }
    if (const auto *array = v.getAsArray())
      for (const auto &item : *array)
        nominal(item);
  };
  std::function<void(const json::Value &)> walk = [&](const json::Value &v) {
    if (foreign)
      return;
    if (auto text = v.getAsString()) {
      if (text->starts_with("variant:"))
        type(*text);
    } else if (const auto *array = v.getAsArray()) {
      for (const auto &item : *array)
        walk(item);
    } else if (const auto *object = v.getAsObject()) {
      for (const auto &item : *object)
        walk(item.second);
    }
  };
  walk(protocol);
  if (foreign)
    return zkc::error("relation-snapshot-subject");
  return Error::success();
}
Expected<std::map<std::string, std::pair<std::string, std::string>>>
associations(const source::Module &m) {
  std::map<std::string, std::pair<std::string, std::string>> result;
  for (const auto &v : m.relationViews) {
    auto generated = generateView(m, v);
    if (!generated)
      return generated.takeError();
    for (const auto &f : generated->functions)
      if (!result.emplace(f.name, std::make_pair(v.relation, v.name)).second)
        return zkc::error("relation-generated-collision");
  }
  return result;
}
} // namespace zkc::relation
