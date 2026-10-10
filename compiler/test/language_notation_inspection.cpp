#include "support/NativeCases.h"
#include "zkc/Language/Inspection.h"
#include "llvm/Support/JSON.h"
#include <set>

using namespace llvm;
using namespace zkc::language;
using zkc::test::refuses;
using zkc::test::require;
using zkc::test::take;
namespace {
CheckedProject check(std::vector<SourceBuffer> sources) {
  auto captured = take(capture(std::move(sources)));
  return take(analyze(captured).checkedProject());
}
CheckedProject inventory() {
  return check({{"definitions", R"(module definitions;
        pub math fn combine<F:Field>(lhs:F,rhs:F)->F{return lhs+rhs;}
        math fn hidden<F:Field>(lhs:F,rhs:F)->F{return lhs-rhs;}
        pub operator infixl(70) ⊙ = combine;
        operator infixl(70) ⊗ = hidden;
        pub notation ⟪ left , right ⟫ = combine(left,right);
      )",
                 "definitions.zkc"},
                {"bridge", R"(module bridge;
        pub use definitions::{combine,operator ⊙,notation ⟪};
      )",
                 "bridge.zkc"},
                {"client", R"(module client;
        use bridge as n;
        pub math fn shown<F:Field>(α:F,β:F)->F{return (α ⊙ β);}
        pub math fn paired<F:Field>(α:F,β:F)->F{return ⟪α,β⟫;}
        math fn secret<F:Field>(lhs:F,rhs:F)->F{return lhs ⊙ rhs;}
        pub math fn overridden<F:Field>(lhs:F,rhs:F)->F{
          operator ⊙ = n::combine;
          return lhs ⊙ rhs;
        }
        pub math fn nested<F:Field>(lhs:F,rhs:F)->F{
          return lhs ⊙ {operator ⊙ = n::combine; lhs ⊙ rhs};
        }
      )",
                 "client.zkc"},
                {"unused", R"(module unused;
        pub math fn unused_target<F:Field>(lhs:F,rhs:F)->F{return lhs;}
        pub operator infixr(63) ⊞ = unused_target;
      )",
                 "unused.zkc"}});
}
json::Value report(const CheckedProject &project,
                   NotationInspectionOptions options = {}) {
  return take(json::parse(take(inspectNotations(project, options))));
}
const json::Array &array(const json::Value &report, StringRef name) {
  auto *object = report.getAsObject();
  require(object && object->getArray(name), "missing inventory " + name);
  return *object->getArray(name);
}
const json::Object &find(const json::Array &values, StringRef key,
                         StringRef expected) {
  for (const auto &value : values) {
    auto *object = value.getAsObject();
    if (object && object->getString(key) == expected)
      return *object;
  }
  throw std::runtime_error("missing " + key.str() + "=" + expected.str());
}
std::set<int64_t> ids(const json::Array &values) {
  std::set<int64_t> result;
  for (const auto &value : values) {
    auto id = value.getAsObject()->getInteger("id");
    require(id.has_value() && result.insert(*id).second,
            "duplicate inventory ID");
  }
  return result;
}
void referencesClose(const json::Value &view) {
  auto descriptors = ids(array(view, "descriptors"));
  auto bindings = ids(array(view, "bindings"));
  auto scopes = ids(array(view, "scopes"));
  for (StringRef table : {"bindings", "occurrences"})
    for (const auto &value : array(view, table)) {
      const auto &record = *value.getAsObject();
      require(descriptors.count(*record.getInteger("descriptor")),
              "dangling descriptor reference");
      require(scopes.count(*record.getInteger("scope")),
              "dangling scope reference");
      if (auto binding = record.getInteger("selected_binding"))
        require(bindings.count(*binding), "dangling selected binding");
    }
  for (const auto &value : array(view, "scopes")) {
    const auto &scope = *value.getAsObject();
    if (auto parent = scope.getInteger("parent"))
      require(scopes.count(*parent), "dangling scope parent");
    for (StringRef key : {"bindings", "visible_bindings", "exported_bindings"})
      for (const auto &id : *scope.getArray(key))
        require(bindings.count(*id.getAsInteger()), "dangling scope binding");
    for (const auto &id : *scope.getArray("descriptors"))
      require(descriptors.count(*id.getAsInteger()),
              "dangling scope descriptor");
  }
}
} // namespace

int main() {
  zkc::test::Cases cases;
  cases.run(
      "public captured inventory excludes private and nested local text", [] {
        auto project = inventory();
        auto bytes = take(inspectNotations(project));
        auto view = take(json::parse(bytes));
        require(view.getAsObject()->getString("format") == "zkc.notations/0",
                "unversioned notation report");
        for (StringRef hidden : {"secret", "hidden", "⊗", "operator ⊙"}) {
          require(bytes.find(hidden.str()) == std::string::npos,
                  "private notation leaked: " + hidden);
        }
        for (StringRef table :
             {"descriptors", "bindings", "scopes", "occurrences"})
          for (const auto &value : array(view, table))
            require(value.getAsObject()->getString("origin") == "captured",
                    "installation record leaked by default");
        find(array(view, "bindings"), "target", "unused::unused_target");
        find(array(view, "occurrences"), "owner", "client::shown");
        for (const auto &value : array(view, "occurrences")) {
          auto owner = value.getAsObject()->getString("owner");
          require(owner != "client::nested" && owner != "client::overridden",
                  "local declaration leaked through an outer operand span");
        }
        referencesClose(view);
        require(take(inspectNotations(project)) == bytes,
                "unstable notation IDs/output");
      });
  cases.run(
      "private and installation filters are independent and IDs are stable",
      [] {
        auto project = inventory();
        auto publicView = report(project);
        auto privateView = report(project, {true, false});
        auto installedView = report(project, {false, true});
        auto all = report(project, {true, true});
        find(array(privateView, "bindings"), "visibility", "local");
        find(array(privateView, "bindings"), "target", "definitions::hidden");
        find(array(privateView, "occurrences"), "owner", "client::secret");
        find(array(privateView, "occurrences"), "owner", "client::nested");
        find(array(installedView, "bindings"), "origin", "installation");
        for (const auto *view :
             {&publicView, &privateView, &installedView, &all})
          referencesClose(*view);
        for (StringRef table :
             {"descriptors", "bindings", "scopes", "occurrences"}) {
          auto full = ids(array(all, table));
          for (auto id : ids(array(publicView, table)))
            require(full.count(id), "filter renumbered a project-local ID");
        }
        for (const auto &value : array(privateView, "bindings"))
          require(value.getAsObject()->getString("origin") == "captured",
                  "includePrivate implicitly included installation bindings");
        for (const auto &value : array(installedView, "bindings"))
          require(
              value.getAsObject()->getString("visibility") == "public",
              "includeInstallation implicitly included private/local bindings");
      });
  cases.run("prelude bindings remain visible in their own scope", [] {
    auto view = report(inventory(), {false, true});
    const auto &scope = find(array(view, "scopes"), "module", "zkc::prelude");
    const auto *visible = scope.getArray("visible_bindings");
    const auto *exported = scope.getArray("exported_bindings");
    require(scope.getString("kind") == "module" && visible && exported &&
                !exported->empty() && *visible == *exported,
            "prelude scope lost its own bindings");
    std::set<int64_t> unique;
    for (const auto &value : *visible)
      require(unique.insert(*value.getAsInteger()).second,
              "prelude binding was injected twice");
    referencesClose(view);
  });
  cases.run(
      "reexports retain original binding and authored UTF-8 byte operands", [] {
        auto project = inventory();
        auto view = report(project);
        const auto &occurrence =
            find(array(view, "occurrences"), "owner", "client::shown");
        auto selected = occurrence.getInteger("selected_binding");
        require(selected.has_value(), "checked emitted selection missing");
        const json::Object *binding = nullptr;
        for (const auto &value : array(view, "bindings"))
          if (value.getAsObject()->getInteger("id") == selected)
            binding = value.getAsObject();
        require(binding && binding->getString("module") == "definitions" &&
                    binding->getString("target") == "definitions::combine",
                "reexport changed the original binding site/target");
        auto *call = occurrence.getObject("named_call");
        require(call && call->getString("kind") == "target-qualified-call" &&
                    call->getString("target") == "definitions::combine" &&
                    call->getArray("static_arguments")->size() == 1 &&
                    call->getArray("operand_order")->size() == 2,
                "selected target/static arguments/authored order missing");
        require(call->getString("rendering")->contains("(α, β)"),
                "named rendering did not preserve authored operand order");
        const auto &operands = *occurrence.getArray("operands");
        require(operands[0].getAsObject()->getString("text") == "α" &&
                    operands[1].getAsObject()->getString("text") == "β",
                "operands were permuted or duplicated");
        for (const auto &value : operands) {
          auto *operand = value.getAsObject();
          auto *span = operand->getObject("span");
          auto begin = *span->getInteger("begin"),
               end = *span->getInteger("end");
          auto source =
              StringRef(project.sources()[*span->getInteger("module")].text);
          require(end - begin == 2 &&
                      source.slice(begin, end) == *operand->getString("text"),
                  "UTF-8 source spans were counted as characters");
          require(operand->getInteger("runtime_value").has_value(),
                  "emitted operand has no runtime value");
        }
        auto *scope = find(array(view, "scopes"), "module", "bridge")
                          .getArray("exported_bindings");
        require(scope && !scope->empty(), "reexport inventory is missing");
        bool reexported = false;
        for (const auto &id : *scope)
          reexported |= id.getAsInteger() == selected;
        require(reexported, "reexport allocated a replacement binding ID");
      });
  cases.run("guaranteed-stop operands reject before inspection", [] {
    auto captured = take(capture({{"m", R"(module m;
      pub math fn combine<F:Field>(lhs:F,rhs:F)->F{return lhs+rhs;}
      pub operator infixl(70) ⊙ = combine;
      pub fn stopped<F:Field>(lhs:F,rhs:F)->F{
        return {stop "reject";} ⊙ (lhs ⊙ rhs);
      })",
                                   "stopped.zkc"}}));
    refuses(analyze(captured).checkedProject(), "source.unreachable");
  });
  cases.run("stopping targets retain their actual checked call binding", [] {
    auto project = check({{"m", R"(module m;
      pub fn stopping<F:Field>(lhs:F,rhs:F)->F{stop "reject";}
      pub operator infixl(70) ⊙ = stopping;
      pub fn f<F:Field>(lhs:F,rhs:F)->F{return lhs ⊙ rhs;}
    )",
                           "stopped.zkc"}});
    const auto view = report(project);
    const auto &occurrence = find(array(view, "occurrences"), "owner", "m::f");
    require(occurrence.getString("state") == "emitted" &&
                occurrence.getInteger("selected_binding") &&
                occurrence.getObject("named_call")->getString("target") ==
                    "m::stopping",
            "runtime stop behavior erased checked selection evidence");
  });
  cases.run(
      "nested emitted regions retain binding evidence and region IDs", [] {
        auto project = check({{"m", R"(module m;
      pub math fn combine<F:Field>(lhs:F,rhs:F)->F{return lhs+rhs;}
      pub operator infixl(70) ⊙ = combine;
      pub fn branched<F:Field>(flag:bool,lhs:F,rhs:F)->F{
        return if flag {lhs ⊙ rhs} else {rhs ⊙ lhs};
      }
    )",
                               "regions.zkc"}});
        auto view = report(project);
        std::set<int64_t> regions;
        for (const auto &value : array(view, "occurrences")) {
          auto &occurrence = *value.getAsObject();
          if (occurrence.getString("owner") != "m::branched")
            continue;
          require(occurrence.getString("state") == "emitted" &&
                      occurrence.getInteger("selected_binding").has_value(),
                  "nested operation evidence was lost");
          regions.insert(*occurrence.getInteger("region"));
        }
        require(regions.size() == 2 && !regions.count(0),
                "runtime values from separate regions are not distinguishable");
      });
  cases.run(
      "reuse rechecks retained work declaration descriptor and hole maxima",
      [] {
        auto project = inventory();
        for (unsigned i = 0; i < 5; ++i) {
          Limits limits;
          switch (i) {
          case 0:
            limits.work = project.checkedWork() - 1;
            break;
          case 1:
            limits.declarations = project.checkedDeclarations() - 1;
            break;
          case 2:
            limits.notationDescriptors =
                project.checkedNotationDescriptors() - 1;
            break;
          case 3:
            limits.notationHoles = project.checkedNotationHoles() - 1;
            break;
          case 4:
            limits.operations = project.checkedOperations() - 1;
            break;
          }
          refuses(inspectNotations(project, {}, limits), "source.limit");
        }
      });
  cases.run(
      "streaming output honors exact byte ceiling with no partial result", [] {
        auto project = inventory();
        auto bytes = take(inspectNotations(project, {true, true}));
        Limits limits;
        limits.notationInspectionBytes = bytes.size();
        require(take(inspectNotations(project, {true, true}, limits)) == bytes,
                "exact output ceiling rejected");
        --limits.notationInspectionBytes;
        refuses(inspectNotations(project, {true, true}, limits),
                "source.limit");
        limits.notationInspectionBytes = 32;
        refuses(inspectNotations(project, {true, true}, limits),
                "source.limit");
      });
  cases.run(
      "lexical overrides share parents and Boolean syntax has no bindings", [] {
        auto project = inventory();
        auto view = report(project, {true, true});
        const auto &local =
            find(array(view, "bindings"), "visibility", "local");
        bool linked = false;
        for (const auto &value : array(view, "scopes")) {
          const auto &scope = *value.getAsObject();
          if (scope.getInteger("id") != local.getInteger("scope"))
            continue;
          require(scope.getInteger("parent").has_value() &&
                      scope.getString("binding_policy") ==
                          "replace-matching-descriptor" &&
                      scope.getArray("visible_bindings")->empty(),
                  "local scope copied its inherited environment or lost its "
                  "parent");
          linked = true;
        }
        require(linked, "local binding has no owning lexical scope");
        std::set<int64_t> booleans;
        for (const auto &value : array(view, "descriptors")) {
          const auto &descriptor = *value.getAsObject();
          auto symbol = descriptor.getString("symbol");
          if (symbol == "!" || symbol == "&&" || symbol == "||") {
            require(descriptor.getBoolean("fixed") == true,
                    "Boolean control descriptor is replaceable");
            booleans.insert(*descriptor.getInteger("id"));
          }
        }
        require(!booleans.empty(), "fixed Boolean grammar missing");
        for (const auto &value : array(view, "bindings"))
          require(
              !booleans.count(*value.getAsObject()->getInteger("descriptor")),
              "Boolean control acquired a callable binding");
      });
  cases.run(
      "public short bindings carry private syntax and authored statics", [] {
        auto project = check({{"defs", R"(module defs;
          pub domain Fr=field("bls12-381.fr");
          pub math fn combine<F:Field>(lhs:F,rhs:F)->F{return lhs+rhs;}
          operator infixl(68) ⊞ = combine<Fr>;
          pub operator ⊞ = combine<Fr>;
        )",
                               "defs.zkc"},
                              {"m", R"(module m;
          use defs::{Fr,operator ⊞};
          pub math fn shown(lhs:Fr,rhs:Fr)->Fr{return lhs ⊞ rhs;}
        )",
                               "m.zkc"}});
        auto view = report(project);
        const auto &occurrence =
            find(array(view, "occurrences"), "owner", "m::shown");
        require(occurrence.getInteger("selected_binding").has_value(),
                "public binding lost its privately declared syntax");
        const auto &binding =
            find(array(view, "bindings"), "target", "defs::combine");
        auto *authored = binding.getArray("authored_static_arguments");
        require(authored && authored->size() == 1 &&
                    authored->front().getAsObject()->getString("text") == "Fr",
                "authored static argument bytes were lost");
        require(binding.getArray("static_arguments")
                    ->front()
                    .getAsString()
                    .has_value(),
                "resolved explicit static argument missing");
        referencesClose(view);
      });
  return cases.result();
}
