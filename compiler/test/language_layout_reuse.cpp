#include "../lib/Language/Semantics.h"
#include "support/NativeCases.h"
#include "zkc/Language/Builtins.h"
#include "llvm/Support/MemoryBuffer.h"
#include <cstdlib>
#include <new>
#include <numeric>
#include <type_traits>

using namespace llvm;
using namespace zkc::language;
using namespace zkc::language::detail;
using namespace zkc::test;
namespace {
// Confined to this executable: cancellation during normal allocation must not
// turn into allocation failure. The scope also disarms on exception unwinding.
struct CancellationAllocations;
thread_local CancellationAllocations *allocationObserver = nullptr;
struct CancellationAllocations {
  const Work &work;
  const zkc::source::Cancellation &cancellation;
  const unsigned target;
  unsigned count = 0;
  bool fired = false;
  uint64_t prefix = 0;
  CancellationAllocations(const Work &work,
                          const zkc::source::Cancellation &cancellation,
                          unsigned target)
      : work(work), cancellation(cancellation), target(target) {
    assert(!allocationObserver);
    allocationObserver = this;
  }
  CancellationAllocations(const CancellationAllocations &) = delete;
  ~CancellationAllocations() { stop(); }
  void stop() { allocationObserver = nullptr; }
  void observe() {
    if (++count == target) {
      prefix = work.used;
      fired = true;
      cancellation.cancel();
    }
  }
};
} // namespace
void *operator new(std::size_t size) {
  if (allocationObserver)
    allocationObserver->observe();
  if (void *value = std::malloc(size ? size : 1))
    return value;
  throw std::bad_alloc();
}
void operator delete(void *value) noexcept { std::free(value); }
void operator delete(void *value, std::size_t) noexcept { std::free(value); }
void *operator new[](std::size_t size) { return ::operator new(size); }
void operator delete[](void *value) noexcept { ::operator delete(value); }
void operator delete[](void *value, std::size_t) noexcept {
  ::operator delete(value);
}
namespace {
void success(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
Declaration record(unsigned ordinal, StringRef name = "m::Record") {
  Declaration result;
  result.kind = Declaration::Kind::Record;
  result.id = result.module = {ordinal};
  result.qualifiedName = name.str();
  result.fields = {{"value", Type(Type::Kind::Index), true, {}}};
  return result;
}
Type nominal(StringRef name = "m::Record") {
  return Type(Type::Kind::Record, name.str());
}
Type sequence(Type element) {
  return take(builtinType("sequence", {std::move(element)}));
}
Port port(Type type) { return {"value", std::move(type), {0}, {}}; }
void ledger(const Work &work) {
  require(work.used == work.ledger.total &&
              std::accumulate(work.ledger.phases.begin(),
                              work.ledger.phases.end(),
                              uint64_t(0)) == work.used,
          "nested work was omitted or charged twice");
}
struct NativeObservation {
  unsigned allocations;
  bool cancelled;
  uint64_t prefix, used;
  std::string value, refusal;
};
NativeObservation observeCancellation(unsigned adapter, bool missing,
                                      unsigned target = 0) {
  Limits limits;
  limits.work = 8192;
  uint64_t remaining = 4096;
  auto declaration = record(0);
  declaration.fields.clear();
  for (unsigned i = 0; i < 4; ++i)
    declaration.fields.push_back(
        {"field" + std::to_string(i), Type(Type::Kind::Index), true, {}});
  std::vector<Declaration> declarations{std::move(declaration)};
  Work work{limits};
  work.allowance = &remaining;
  zkc::source::Cancellation cancellation;
  work.cancellation = cancellation;
  success(work.charge(7));
  Semantics types(declarations, {}, work);
  auto type = nominal(missing ? "m::Missing" : "m::Record");
  auto input = port(type);
  std::string value, refusal;
  CancellationAllocations allocations(work, cancellation, target);
  {
    Work::Scope phase(work, SourceWorkPhase::Permissions);
    if (adapter == 0) {
      auto result = types.nativeLayout(type);
      allocations.stop();
      if (result)
        value = result->spelling();
      else
        refusal = toString(result.takeError());
    } else if (adapter == 1) {
      auto result = types.nativeMessagePayload(type);
      allocations.stop();
      if (result)
        value = *result ? "payload" : "non-payload";
      else
        refusal = toString(result.takeError());
    } else {
      auto result = types.nativePortLayout(input);
      allocations.stop();
      if (result) {
        require(result->size() == 4 && result->leaves.size() == 4 &&
                    result->components.size() == 4,
                "ordinary port observation changed");
        for (unsigned i = 0; i < 4; ++i)
          require(result->leaves[i].leaf.data() &&
                      result->leaves[i].leaf.data()->spelling() == "index" &&
                      result->nativeOffsets[i] == i,
                  "ordinary port leaf or offset changed");
        value = result->body->identity.key;
      } else
        refusal = toString(result.takeError());
    }
  }
  require(work.phase == SourceWorkPhase::Unscoped &&
              work.ledger.used(SourceWorkPhase::Unscoped) == 7 &&
              work.ledger.used(SourceWorkPhase::Permissions) == work.used - 7 &&
              remaining == 4096 - work.used,
          "observation changed its phase, prefix or enclosing allowance");
  ledger(work);
  return {allocations.count,  allocations.fired && cancellation.cancelled(),
          allocations.prefix, work.used,
          std::move(value),   std::move(refusal)};
}
std::vector<Declaration> padded(unsigned padding) {
  std::vector<Declaration> declarations{record(0)};
  for (unsigned i = 0; i < padding; ++i) {
    auto unused = record(i + 1, "m::Unused" + std::to_string(i));
    declarations.push_back(std::move(unused));
  }
  return declarations;
}
} // namespace
int main() {
  static_assert(!std::is_copy_constructible_v<Semantics>);
  static_assert(!std::is_move_constructible_v<Semantics>);
  static_assert(!std::is_constructible_v<Semantics, const Semantics &, Work &>);
  Cases cases;
  cases.run(
      "direct and helper source calls have no declaration index amplification",
      [] {
        auto library = MemoryBuffer::getFile(ZKC_SEQUENCE_SOURCE);
        require(bool(library), "sequence library fixture is unavailable");
        for (bool helper : {false, true}) {
          std::vector<uint64_t> marginals;
          for (unsigned padding : {0, 256, 512}) {
            std::vector<uint64_t> costs;
            for (unsigned calls : {0, 1, 4}) {
              std::string source =
                  "module scaling; use zkc::sequence::{Sequence}; "
                  "use zkc::sequence as sequence;\n";
              for (unsigned i = 0; i < padding; ++i)
                source += "fn unused" + std::to_string(i) +
                          "(value:index)->index{return value;}\n";
              if (helper)
                source +=
                    "fn count<T:Type+Copy+Drop>(values:Sequence<T>)->index{"
                    "return sequence::length(values);}\n";
              source += "entry fn Run(values:Sequence<index>)->index{\n";
              for (unsigned i = 0; i < calls; ++i)
                source += "let count" + std::to_string(i) + "=" +
                          (helper ? "count" : "sequence::length") +
                          "(values);\n";
              source += "return ";
              if (calls == 0)
                source += "0";
              for (unsigned i = 0; i < calls; ++i)
                source += (i ? "+count" : "count") + std::to_string(i);
              source += ";}\n";
              auto captured =
                  take(capture({{"scaling", source, "calls.zkc"},
                                {"zkc::sequence", (*library)->getBuffer().str(),
                                 "sequence.zkc"}}));
              auto checked = take(analyze(captured).checkedProject());
              auto closed = take(closeEntry(checked, "scaling::Run"));
              costs.push_back(closed.workObservation().charged.used(
                  SourceWorkPhase::Specialization));
            }
            const auto one = costs[1] - costs[0];
            const auto four = costs[2] - costs[0];
            require(
                one > 0 && four > one,
                "repeated source sites stopped paying current validation work");
            // Keep the empty control, then compare two padded projects
            // separately: retained source-witness and key work need not equal
            // the empty case. Another 256 declarations must not multiply
            // per-call index work.
            if (padding == 256)
              marginals = {one, four};
            else if (padding == 512)
              require(
                  marginals == std::vector<uint64_t>({one, four}),
                  "unused declarations multiplied direct or helper call work");
          }
        }
      });
  cases.run(
      "unused declarations do not multiply nested query construction", [] {
        Limits limits;
        const auto type = sequence(sequence(nominal()));
        uint64_t cost = 0;
        std::string bytes;
        for (unsigned padding : {0, 256}) {
          auto declarations = padded(padding);
          Work work{limits};
          Semantics types(declarations, {}, work);
          for (unsigned call = 0; call < 4; ++call) {
            const auto before = work.used;
            auto result = take(types.nativeLayout(type)).spelling();
            if (padding == 0 && call == 0) {
              cost = work.used;
              bytes = result;
            }
            require(
                cost > 0 && work.used - before == cost && result == bytes,
                "nested query rebuilt the project index or reused a result");
          }
          ledger(work);
        }
      });
  cases.run("nested layouts read completed and mutated nominal fields", [] {
    Limits limits;
    std::vector<Declaration> declarations{record(0)};
    Work work{limits};
    Semantics types(declarations, {}, work);
    auto input = port(nominal());
    auto before = take(types.nativePortLayout(input));
    declarations[0].fields.push_back({"flag", Type{}, true, {}});
    auto after = take(types.nativePortLayout(input));
    require(before.body->fields.size() == 1 && after.body->fields.size() == 2 &&
                after.body->fields[1].layout->type.kind == Type::Kind::Boolean,
            "a layout survived source signature mutation");
    declarations[0].resource = Resource::Linear;
    refuses(types.nativeLayout(sequence(nominal())), "source.sequence");
    declarations[0].resource.reset();
    take(types.nativeLayout(sequence(nominal())));
    require(!types.diagnostic, "nested failure poisoned the owner's query");
  });
  cases.run("nominal kind, parameter bounds and placement remain per use", [] {
    Limits limits;
    std::vector<Declaration> declarations{record(0)};
    Parameter parameter;
    parameter.sort = Parameter::Sort::Type;
    parameter.atom = "m::Record::T";
    parameter.permissions = {true, true};
    declarations[0].parameters.push_back(parameter);
    declarations[0].fields[0].type = parameterType(parameter);
    Work work{limits};
    Semantics types(declarations, {}, work);
    auto type = nominal();
    type.arguments = {Type{}};
    auto input = port(type);
    input.placement = DataPlacement{{0}};
    take(types.nativePortLayout(input));
    input.placement = OraclePlacement{0, {1}};
    refuses(types.nativePortLayout(input), "source.placement");
    input.placement = DataPlacement{{0}};
    declarations[0].kind = Declaration::Kind::Variant;
    refuses(types.nativePortLayout(input), "source.layout");
    declarations[0].kind = Declaration::Kind::Record;
    type.arguments.clear();
    refuses(types.nativeLayout(type), "source.layout");
    take(types.nativePortLayout(input));
  });
  cases.run("vector growth and explicit parameter indexing remain visible", [] {
    Limits limits;
    auto declarations = padded(0);
    Work work{limits};
    Semantics types(declarations, {}, work);
    take(types.nativeLayout(sequence(nominal())));
    const auto capacity = declarations.capacity();
    while (declarations.size() <= capacity)
      declarations.push_back(record(
          declarations.size(), "m::New" + std::to_string(declarations.size())));
    const auto id = declarations.back().id;
    types.indexDeclaration(declarations.back());
    Parameter parameter;
    parameter.sort = Parameter::Sort::Type;
    parameter.atom = "m::New::T";
    parameter.permissions = {true, true};
    types.indexParameter(parameter, id, 0);
    declarations[id.index].parameters.push_back(parameter);
    declarations[id.index].fields[0].type = parameterType(parameter);
    auto type = nominal(declarations[id.index].qualifiedName);
    type.arguments = {Type(Type::Kind::Index)};
    require(types.parameter(parameter.atom) ==
                &declarations[id.index].parameters.front(),
            "parameter index retained an invalidated vector element");
    take(types.nativeLayout(sequence(type)));
    declarations[id.index].fields[0].type = Type(Type::Kind::Formal, "invalid");
    refuses(types.nativeLayout(sequence(type)), "source.formal");
    declarations[id.index].fields[0].type = parameterType(parameter);
    take(types.nativeLayout(sequence(type)));
  });
  cases.run(
      "native results outlive the index, declarations and caller work", [] {
        std::optional<zkc::protocol::BoundType> packed;
        std::optional<ProtocolPortLayout> observed;
        std::string spelling;
        {
          Limits limits;
          Work work{limits};
          std::vector<Declaration> declarations{record(0)};
          Semantics types(declarations, {}, work);
          packed = take(types.nativeLayout(nominal()));
          spelling = packed->spelling();
          observed = take(types.nativePortLayout(port(nominal())));
        }
        require(
            !spelling.empty() && packed->spelling() == spelling &&
                observed->body->fields.size() == 1 &&
                observed->leaves.size() == 1 &&
                observed->leaves[0].leaf.data()->spelling() == "index",
            "native result retained a borrow from its synchronous observer");
      });
  cases.run("origin and anonymous declarations do not become new names", [] {
    Limits limits;
    std::vector<Declaration> declarations{record(0)};
    Work work{limits};
    Semantics types(declarations, {}, work);
    auto instance = record(1, "m::Instance");
    instance.origin = DeclarationId{0};
    declarations.push_back(instance);
    types.indexDeclaration(declarations.back());
    auto anonymous = record(2, "m::Anonymous");
    anonymous.anonymous = true;
    declarations.push_back(anonymous);
    types.indexDeclaration(declarations.back());
    refuses(types.nativeLayout(nominal("m::Instance")), "source.layout");
    refuses(types.nativeLayout(nominal("m::Anonymous")), "source.layout");
    take(types.nativeLayout(nominal()));
  });
  cases.run(
      "nested semantics has independent diagnostics and no inference hooks",
      [] {
        Limits limits;
        std::vector<Declaration> declarations{record(0)};
        Work work{limits};
        unsigned hooks = 0;
        Semantics types(declarations, {}, work, [&](DeclarationId) {
          ++hooks;
          return false;
        });
        types.inferCapability = [&](const Declaration *,
                                    const CapabilityBound &) {
          ++hooks;
          return true;
        };
        types.inferNatural = [&](const Declaration &, const NaturalBound &) {
          ++hooks;
          return true;
        };
        types.collectUsage = [&](const Declaration &, const Type &, Usage, Span,
                                 StringRef, StringRef) {
          ++hooks;
          return false;
        };
        types.recordAdmission = [&](const Declaration &, AdmissionObligation) {
          ++hooks;
          return false;
        };
        types.completeDispatchBody = [&](DeclarationId, unsigned) {
          ++hooks;
          return false;
        };
        types.diagnostic =
            Diagnostic{"source.test", "owner diagnostic", {}, {}};
        refuses(types.nativeLayout(nominal("m::Missing")), "source.layout");
        take(types.nativeLayout(sequence(nominal())));
        require(hooks == 0 && types.diagnostic->code == "source.test",
                "nested observation borrowed owner hooks or diagnostic state");
      });
  cases.run(
      "authority changes never reuse provisional or finalized results", [] {
        Limits limits;
        auto captured = take(capture({{"m", "module m;", "authority.zkc"}}));
        CheckedStorage storage(captured, installedCatalogIdentity());
        storage.sources = std::make_shared<std::vector<SourceBuffer>>(
            std::vector<SourceBuffer>{{"m", "module m;", "authority.zkc"}});
        storage.declarations = {record(0)};
        auto index = std::make_shared<DeclarationIndex>();
        require(index->add(storage.declarations[0], SourceOrigin::Captured),
                "authority fixture was not indexed");
        index->finish(storage.declarations, *storage.sources);
        storage.declarationIndex = std::move(index);
        storage.authorities.computed = true;
        storage.authorities.sources = {0};
        storage.authorities.units = {{"m", {0}, {}, std::string(64, 'a')}};
        Work work{limits};
        Semantics types(storage.declarations, {}, work);
        auto input = port(nominal());
        auto provisional =
            take(types.nativePortLayout(input)).body->identity.key;
        types.authorities.final = &storage;
        auto first = take(types.nativePortLayout(input)).body->identity.key;
        storage.authorities.units[0].revision = std::string(64, 'b');
        auto second = take(types.nativePortLayout(input)).body->identity.key;
        require(provisional != first && first != second,
                "layout reused a result under another nominal authority");
        storage.authorities.computed = false;
        refuses(types.nativePortLayout(input), "source.authority");
        types.authorities = {};
        require(
            take(types.nativePortLayout(input)).body->identity.key ==
                provisional,
            "failed final authority observation poisoned provisional queries");
      });
  cases.run("aliases keep their canonical nominal declaration identity", [] {
    auto captured = take(capture({{"m", R"(module m;
      struct R { pub value:index }
      type Alias = R;
      protocol Run roles(P,V)(value:Alias@P)->(out:R@P){return(out=value);}
    )",
                                   "alias.zkc"}}));
    auto checked = take(analyze(captured).checkedProject());
    std::vector<Declaration> declarations(checked.declarations().begin(),
                                          checked.declarations().end());
    auto run = llvm::find_if(declarations, [](const Declaration &decl) {
      return decl.qualifiedName == "m::Run";
    });
    require(run != declarations.end() &&
                run->inputs[0].type == run->outputs[0].type,
            "alias did not resolve to its canonical type");
    Limits limits;
    Work work{limits};
    Semantics types(declarations, {}, work);
    auto before = take(types.nativePortLayout(run->inputs[0]));
    auto after = take(types.nativePortLayout(run->outputs[0]));
    require(before.body->identity.key == after.body->identity.key,
            "borrowing created a second alias namespace");
  });
  cases.run(
      "all native adapters keep exact and partial work in caller ledger", [] {
        for (unsigned adapter = 0; adapter < 3; ++adapter) {
          uint64_t cost = 0;
          for (unsigned trial = 0; trial < 3; ++trial) {
            Limits limits;
            limits.work = trial == 0 ? Limits{}.work : cost - (trial == 2);
            uint64_t remaining = limits.work;
            const auto initial = remaining;
            auto declarations = padded(256);
            Work work{limits};
            work.allowance = &remaining;
            Work::Scope phase(work, SourceWorkPhase::Permissions);
            Semantics types(declarations, {}, work);
            const auto type = sequence(nominal());
            auto query = [&]() -> Error {
              if (adapter == 0) {
                auto result = types.nativeLayout(type);
                return result ? Error::success() : result.takeError();
              }
              if (adapter == 1) {
                auto result = types.nativePortLayout(port(type));
                return result ? Error::success() : result.takeError();
              }
              auto result = types.nativeMessagePayload(type);
              return result ? Error::success() : result.takeError();
            };
            auto result = query();
            if (trial < 2) {
              success(std::move(result));
              if (trial == 0)
                cost = work.used;
              else
                require(remaining == 0, "exact work allowance changed");
            } else {
              require(bool(result), "nested query reset the work ceiling");
              require(
                  namesIdentifier(toString(std::move(result)), "source.limit"),
                  "exhaustion changed its refusal");
              require(work.used > 1, "partial failed query refunded its work");
            }
            require(
                work.used == initial - remaining &&
                    work.ledger.used(SourceWorkPhase::Permissions) == work.used,
                "nested work escaped the active phase or enclosing allowance");
            ledger(work);
          }
        }
      });
  cases.run(
      "cancellation preserves earlier work and blocks every native adapter",
      [] {
        Limits limits;
        auto declarations = padded(0);
        Work work{limits};
        zkc::source::Cancellation cancellation;
        work.cancellation = cancellation;
        Semantics types(declarations, {}, work);
        take(types.nativeLayout(sequence(nominal())));
        auto used = work.used;
        cancellation.cancel();
        refuses(types.nativeLayout(sequence(nominal())), "source.cancelled");
        refuses(types.nativePortLayout(port(nominal())), "source.cancelled");
        refuses(types.nativeMessagePayload(nominal()), "source.cancelled");
        require(work.used == used,
                "cancellation charged unperformed layout work");
        ledger(work);
      });
  // Warm lazy catalog state before selecting allocation ordinals.
  for (unsigned adapter = 0; adapter < 3; ++adapter)
    cases.run("warm native adapter " + std::to_string(adapter), [=] {
      require(observeCancellation(adapter, false).refusal.empty(),
              "ordinary observation failed");
    });
  for (unsigned adapter = 0; adapter < 3; ++adapter)
    for (bool missing : {false, true})
      cases.run(
          "allocation cancellation in native adapter " +
              std::to_string(adapter) + (missing ? " refusal" : " success"),
          [=] {
            const auto body = observeCancellation(1, false);
            const auto control = observeCancellation(adapter, missing);
            require(control.allocations > 0 && control.allocations <= 128,
                    "observation exceeded bounded allocation probe");
            if (missing)
              require(namesIdentifier(control.refusal, "source.layout"),
                      "ordinary missing-record refusal changed");
            else
              require(control.refusal.empty() && !control.value.empty(),
                      "ordinary observation failed");
            for (unsigned target = 1; target <= control.allocations; ++target) {
              auto result = observeCancellation(adapter, missing, target);
              require(result.cancelled && result.value.empty() &&
                          namesIdentifier(result.refusal, "source.cancelled"),
                      "adapter lost cancellation at allocation " +
                          std::to_string(target));
              // This ordinary record's port helper starts after get(),
              // runs synchronously without cancellation polls, and
              // commits its full admitted numeric work on return.
              auto expected =
                  adapter == 2 && !missing && result.prefix == body.used
                      ? control.used
                      : result.prefix;
              require(result.used == expected,
                      "cancellation changed the exact admitted prefix");
            }
            const auto retry = observeCancellation(adapter, missing);
            require(retry.value == control.value &&
                        retry.refusal == control.refusal &&
                        retry.used == control.used &&
                        retry.allocations == control.allocations,
                    "allocation probe state escaped into a later query");
          });
  cases.run(
      "numeric helpers retain exact prefixes for independent allowances", [] {
        for (uint64_t ceiling : {2u, 4u, 16u})
          for (uint64_t allowance : {1u, 3u, 12u}) {
            Limits limits;
            limits.work = ceiling;
            uint64_t remaining = allowance, performed = 0;
            Work work{limits};
            work.allowance = &remaining;
            Work::Scope phase(work, SourceWorkPhase::Permissions);
            success(work.charge(1));
            {
              Work::Budget budget(work);
              const auto before = budget.remaining;
              auto error = validatePlacement(
                  DataPlacement{{0}}, 1, budget.remaining, limits.typeDepth);
              performed = before - budget.remaining;
              require(bool(error) == (before < 3),
                      "numeric helper changed its exact refusal boundary");
              consumeError(std::move(error));
              success(budget.finish());
              const auto once = work.used;
              success(budget.finish());
              require(work.used == once,
                      "repeated finish duplicated the prefix");
            }
            require(
                work.used == 1 + performed &&
                    remaining == allowance - work.used &&
                    work.ledger.used(SourceWorkPhase::Permissions) == work.used,
                "numeric helper lost a prefix, phase or enclosing allowance");
            ledger(work);
          }
      });
  cases.run(
      "cancellation cannot refund an admitted placement helper prefix", [] {
        Limits limits;
        uint64_t remaining = 100;
        Work work{limits};
        work.allowance = &remaining;
        zkc::source::Cancellation cancellation;
        work.cancellation = cancellation;
        Work::Scope phase(work, SourceWorkPhase::Permissions);
        // Exercise the same bounded helper and reconciliation boundary as a
        // nested port observation, with cancellation between its admission and
        // return.
        auto available = work.remaining();
        Work::Budget budget(work);
        success(validatePlacement(DataPlacement{{0}}, 1, budget.remaining,
                                  limits.typeDepth));
        require(budget.remaining < available,
                "placement helper performed no work");
        cancellation.cancel();
        auto result = budget.finish();
        require(bool(result) && namesIdentifier(toString(std::move(result)),
                                                "source.cancelled"),
                "completed helper lost cancellation");
        require(remaining == budget.remaining &&
                    work.used == available - remaining &&
                    work.ledger.used(SourceWorkPhase::Permissions) == work.used,
                "cancellation refunded completed helper work");
        ledger(work);
      });
  cases.run("exception unwinding retains a bounded helper's performed debit",
            [] {
              Limits limits;
              uint64_t remaining = 100;
              Work work{limits};
              work.allowance = &remaining;
              uint64_t performed = 0;
              try {
                Work::Budget budget(work);
                success(validatePlacement(DataPlacement{{0}}, 1,
                                          budget.remaining, limits.typeDepth));
                performed = 100 - budget.remaining;
                // Model allocation failure after the helper has admitted its
                // prefix.
                throw std::bad_alloc();
              } catch (const std::bad_alloc &) {
                require(performed > 0 && work.used == performed &&
                            remaining == 100 - performed,
                        "exception discarded completed helper work");
              }
              ledger(work);
            });
  cases.run("standalone layouts retain their independently charged index", [] {
    auto captured = take(capture(
        {{"m", "module m; struct R{pub x:index}", "layout-reuse.zkc"}}));
    auto checked = take(analyze(captured).checkedProject());
    Limits limits;
    Work indexWork{limits};
    std::vector<Declaration> declarations(checked.declarations().begin(),
                                          checked.declarations().end());
    success(chargeSemanticIndex(declarations, indexWork));
    Work work{limits};
    Semantics types(declarations, {}, work);
    auto type = sequence(nominal("m::R"));
    take(types.nativeLayout(type));
    const auto standaloneCost = work.used - 1 + indexWork.used;
    limits.work = standaloneCost;
    Layouts exact(checked, limits);
    auto first = take(exact.packed(type));
    require(!first.carrier.spelling().empty(), "standalone result was lost");
    --limits.work;
    Layouts shortWork(checked, limits);
    refuses(shortWork.packed(type), "source.limit");
  });
  return cases.result();
}
