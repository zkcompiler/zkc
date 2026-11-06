#include "../lib/Language/Semantics.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Language/SourceTerms.h"
#include <cstdlib>
#include <new>
#include <numeric>

using namespace llvm;
using namespace zkc::language;
using namespace zkc::language::detail;
using namespace zkc::test;
namespace {
// Cancel through the normal API during allocation at the export's admitted
// prefix. This observer is confined to this executable and never fails an
// allocation. It is disarmed before diagnostics are inspected or on unwinding.
struct CancelAtWork;
thread_local CancelAtWork *allocationObserver = nullptr;
struct CancelAtWork {
  const Work &work;
  const zkc::source::Cancellation &cancellation;
  uint64_t prefix;
  bool fired = false;
  CancelAtWork(const Work &work, const zkc::source::Cancellation &cancellation,
               uint64_t prefix)
      : work(work), cancellation(cancellation), prefix(prefix) {
    assert(!allocationObserver);
    allocationObserver = this;
  }
  ~CancelAtWork() { stop(); }
  void stop() { allocationObserver = nullptr; }
  void observe() {
    if (work.used == prefix) {
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
constexpr StringLiteral source = R"zkc(module sample;
domain A = field("bls12-381.fr");
relation Layer<F:Field, N:nat, Unused:nat>(statement point:F, witness value:F)
  = opaque("vendor.layer/0", "layer", "0");
protocol Run roles(P,V)(a:A@(P,V))->(accepted:bool@V)
spec {
  target proof = Layer<A,2,7>(in.a@V, in.a@P) accept out.accepted;
} {
  let accepted@V = true;
  return (accepted=accepted);
}
)zkc";
struct Observation {
  uint64_t used;
  bool cancelled;
  std::optional<Diagnostic> error;
  std::vector<Declaration> declarations;
};
Observation specializeSource(const CheckedProject &project, uint64_t allowance,
                             std::optional<uint64_t> cancelAt = {},
                             const Declaration *retained = nullptr) {
  auto authentic = take(closeNativeRun(project, "sample::Run"));
  std::vector<Declaration> declarations(project.declarations().begin(),
                                        project.declarations().end());
  if (retained) {
    auto copy = *retained;
    copy.id = {unsigned(declarations.size())};
    copy.qualifiedName = "sample::Retained";
    declarations.push_back(std::move(copy));
  }
  auto owner = authentic.entry();
  owner.id = {unsigned(declarations.size())};
  for (const auto &decl : project.declarations())
    if (decl.qualifiedName == "sample::Run")
      owner.target = decl.id;
  declarations.push_back(owner);
  // The public closure also enforces checkedWork. Isolate the real native
  // specialization allowance, as in the consumer-requirements boundary test.
  Limits limits;
  limits.work = allowance;
  Work work{limits};
  zkc::source::Cancellation cancellation;
  work.cancellation = cancellation;
  CancelAtWork observer(work, cancellation, cancelAt.value_or(UINT64_MAX));
  Error error = Error::success();
  {
    Work::Scope phase(work, SourceWorkPhase::Specialization);
    error = specialize(declarations, project.assets(), work, owner.id);
  }
  observer.stop();
  require(work.phase == SourceWorkPhase::Unscoped &&
              work.ledger.total == work.used &&
              work.ledger.used(SourceWorkPhase::Specialization) == work.used &&
              std::accumulate(work.ledger.phases.begin(),
                              work.ledger.phases.end(),
                              uint64_t(0)) == work.used,
          "export changed exclusive specialization accounting");
  return {work.used, observer.fired, diagnose(std::move(error)),
          std::move(declarations)};
}
const Declaration &opaque(const Observation &observation) {
  const Declaration *result = nullptr;
  for (const auto &decl : observation.declarations)
    if (decl.origin && decl.relation &&
        decl.relation->kind == RelationDefinition::Kind::Opaque) {
      require(!result, "expected one ordinary opaque instance");
      result = &decl;
    }
  require(result, "ordinary source omitted its opaque instance");
  return *result;
}
void diagnostic(const Observation &observed, StringRef code, StringRef message,
                Span span) {
  require(observed.error.has_value(), "expected opaque export refusal");
  const auto &error = *observed.error;
  outs() << "opaque export: " << error.code << ": " << error.message
         << "; admitted prefix=" << observed.used << '\n';
  require(error.code == code, "wrong export code: " + error.code);
  require(error.message == message,
          "wrong export explanation: " + error.message);
  require(error.primary && error.primary->source.index == span.source.index &&
              error.primary->begin == span.begin &&
              error.primary->end == span.end,
          "export lost its original declaration span");
}
} // namespace
int main() {
  Cases cases;
  auto project =
      take(analyze(take(capture({{"sample", source.str(), "opaque-export.zkc"}},
                                {})))
               .checkedProject());
  auto baseline = specializeSource(project, Limits{}.work);
  require(!baseline.error, "ordinary closed opaque source refused");
  const auto &instance = opaque(baseline);
  require(instance.staticArguments.size() == 3,
          "opaque argument arity changed");
  uint64_t cost = 0;
  for (const auto &argument : instance.staticArguments)
    cost += take(typeComplexity(argument, 4096, 64, Limits{}.work, nullptr,
                                true, TypeWork::StaticExport));
  require(cost > 0 && baseline.used > cost, "opaque export prefix is absent");
  const auto prefix = baseline.used - cost;
  const auto &first = instance.staticArguments.front();
  const auto firstCost = take(typeComplexity(
      first, 4096, 64, Limits{}.work, nullptr, true, TypeWork::StaticExport));
  outs() << "ordinary opaque specialization: total=" << baseline.used
         << "; export prefix=" << prefix << "; export cost=" << cost << '\n';
  cases.run("closed opaque source succeeds with its exact allowance", [&] {
    auto exact = specializeSource(project, baseline.used);
    require(!exact.error && exact.used == baseline.used && !exact.cancelled,
            "exact closed opaque specialization refused or changed work");
    require(opaque(exact).staticArguments == instance.staticArguments,
            "closed static arguments changed");
    require(take(encodeStaticTerm(first)) ==
                take(json::parse(R"(["field","bls12-381.fr"])")),
            "closed field encoding changed");
  });
  cases.run("opaque export preserves actual preflight allowance refusal", [&] {
    unsigned charges = 0;
    auto helper = encodeStaticTerm(first, {}, firstCost - 1, [&](uint64_t) {
      ++charges;
      return Error::success();
    });
    require(!helper, "one-unit-short helper preflight succeeded");
    auto expected = diagnose(helper.takeError());
    require(expected && expected->code == "source.limit" && charges == 0,
            "helper did not refuse before its charge callback");
    auto limited = specializeSource(project, prefix + firstCost - 1);
    diagnostic(limited, "source.limit",
               expected->message + " in specialization", instance.span);
    require(limited.used == prefix && !limited.cancelled,
            "preflight refusal charged unperformed export work");
  });
  cases.run("opaque export preserves cancellation at its charge callback", [&] {
    auto cancelled = specializeSource(project, baseline.used, prefix);
    require(cancelled.cancelled, "cancellation was not triggered at export");
    diagnostic(cancelled, "source.cancelled", "source analysis cancelled",
               instance.span);
    require(cancelled.used == prefix,
            "cancelled export charged unperformed work");
  });
  cases.run("actual nonclosed retained argument keeps relation refusal", [&] {
    // Private API refusal control, not an accepted-source permission claim.
    auto retained = instance;
    retained.staticArguments.front() = Type(Type::Kind::Parameter, "scope::F");
    refuses(encodeStaticTerm(retained.staticArguments.front()),
            "source.static-term");
    auto refused = specializeSource(project, Limits{}.work, {}, &retained);
    diagnostic(refused, "source.relation",
               "opaque static argument is not closed", instance.span);
    require(!refused.cancelled, "nonclosed refusal fabricated cancellation");
  });
  return cases.result();
}
