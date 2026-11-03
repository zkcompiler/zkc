#include "../lib/Language/Semantics.h"
#include "support/NativeCases.h"
#include <numeric>

using namespace llvm;
using namespace zkc::language;
using namespace zkc::language::detail;
using namespace zkc::test;
namespace {
constexpr StringLiteral source = R"(
module sample;
pub protocol Echo roles(P,V)(value:bool@P)->(received:bool@V){
  let received=send P->V(value);return received;
}
)";
CapturedProject captured(StringRef text = source, StringRef format = "zkc") {
  return take(capture({{"sample", text.str(), "sample.zkc"}}, {},
                      CaptureOptions{format.str(), {}}));
}
void exact(const WorkLedger &ledger, uint64_t total) {
  require(ledger.total == total &&
              std::accumulate(ledger.phases.begin(), ledger.phases.end(),
                              uint64_t(0)) == total,
          "exclusive work counters lost or duplicated a charge");
}
void complete(const SourceWorkObservation &observation, uint64_t total) {
  exact(observation.charged, total);
  require(observation.charged.used(SourceWorkPhase::Unscoped) == 0,
          "complete source phase contains unattributed work");
  for (const auto &budget : observation.separateBudgets) {
    exact(budget.ledger, budget.ledger.total);
    require(budget.ledger.used(budget.phase) == budget.ledger.total &&
                budget.ledger.total > 0,
            "independent work did not land in its own phase");
  }
}
void success(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
void limit(Error error, StringRef phase) {
  require(bool(error), "expected a checked work refusal");
  bool diagnosed = false;
  handleAllErrors(std::move(error), [&](const DiagnosticError &error) {
    const auto &diagnostic = error.diagnostic();
    require(diagnostic.code == "source.limit" &&
                StringRef(diagnostic.message).contains(("in " + phase).str()),
            "work refusal lost active subphase: " + diagnostic.message);
    diagnosed = true;
  });
  require(diagnosed, "work refusal lost its diagnostic identifier");
}
uint64_t operations(const Body &body) {
  uint64_t result = body.operations.size();
  for (const auto &operation : body.operations)
    if (auto *control = std::get_if<Control>(&operation.action))
      for (const auto &region : control->regions)
        result += operations(*region);
  return result;
}
void scopedChecks(const ClosedEntry &entry) {
  std::vector<SourceWorkBudget> observed;
  success(checkScopedElaboration(entry.project(), {}, &observed));
  success(checkScopedSpecialization(entry, {}, &observed));
  const auto &retained = entry.workObservation().separateBudgets;
  require(retained.size() == 3 && observed.size() == retained.size(),
          "closure hid or merged an independently bounded scoped check");
  for (size_t i = 0; i < retained.size(); ++i)
    require(retained[i].phase == observed[i].phase &&
                retained[i].ledger.phases == observed[i].ledger.phases &&
                retained[i].ledger.total == observed[i].ledger.total,
            "retained scoped-check cost differs from performing the check");
}
} // namespace
int main() {
  Cases cases;
  cases.run("nested scopes attribute each accepted charge exactly once", [] {
    Limits limits;
    limits.work = 20;
    uint64_t remaining = 12;
    Work work{limits};
    work.allowance = &remaining;
    success(work.charge(1));
    {
      Work::Scope outer(work, SourceWorkPhase::Bodies);
      success(work.charge(2));
      {
        Work::Scope inner(work, SourceWorkPhase::CommonInputs);
        success(work.charge(4));
        limit(work.charge(6), "common_inputs");
        require(work.used == 7 && remaining == 5,
                "rejected charge consumed work or enclosing allowance");
      }
      success(work.charge(3));
    }
    success(work.charge(2));
    limit(work.charge(), "unscoped");
    exact(work.ledger, 12);
    require(work.used == 12 && remaining == 0 &&
                work.ledger.used(SourceWorkPhase::Unscoped) == 3 &&
                work.ledger.used(SourceWorkPhase::Bodies) == 5 &&
                work.ledger.used(SourceWorkPhase::CommonInputs) == 4,
            "nested scope restoration double-counted or moved work");
  });
  cases.run("cancelled charges neither debit nor enter the ledger", [] {
    Limits limits;
    Work work{limits};
    zkc::source::Cancellation cancellation;
    work.cancellation = cancellation;
    Work::Scope phase(work, SourceWorkPhase::Signatures);
    success(work.charge(3));
    cancellation.cancel();
    require(toString(work.charge(5)).find("source.cancelled") !=
                std::string::npos,
            "work instrumentation changed cancellation priority");
    exact(work.ledger, 3);
    require(work.used == 3 &&
                work.ledger.used(SourceWorkPhase::Signatures) == 3,
            "cancellation charged unperformed work");
  });
  cases.run("nested semantic layout work inherits phase and allowance", [] {
    Limits limits;
    const std::vector<Declaration> declarations;
    Port port;
    port.type = Type{};
    port.roles = {0};
    uint64_t cost = 0;
    for (unsigned trial = 0; trial < 3; ++trial) {
      uint64_t remaining = trial == 0 ? limits.work : cost - (trial == 2);
      const auto initial = remaining;
      Work work{limits};
      work.allowance = &remaining;
      Work::Scope phase(work, SourceWorkPhase::Permissions);
      Semantics types(declarations, {}, work);
      auto layout = types.nativePortLayout(port);
      if (trial < 2) {
        require(take(std::move(layout)).leaves.size() == 1,
                "work observation changed port layout");
        if (trial == 0) {
          cost = work.used;
          require(cost > 1, "nested port layout stopped charging");
        } else
          require(remaining == 0, "exact nested allowance was not consumed");
      } else {
        // The nested observer owns its diagnostic type. Its accepted work is
        // still attributed to the caller's phase exactly once.
        refuses(std::move(layout), "source.limit");
      }
      exact(work.ledger, work.used);
      require(work.ledger.used(SourceWorkPhase::Permissions) == work.used &&
                  initial - remaining == work.used,
              "nested layout work was charged twice or lost on refusal");
    }
  });
  cases.run("brace and layout checking retain complete exclusive ledgers", [] {
    const auto brace = captured();
    const auto layout = captured(R"(module sample
pub protocol Echo roles(P, V)(value: bool @P) -> bool @V:
    received <- send value to V
    return received
)",
                                 "zkc-layout");
    for (const auto &capture : {brace, layout}) {
      auto analysis = analyze(capture);
      auto project = take(analysis.checkedProject());
      complete(project.workObservation(), project.checkedWork());
      require(project.workObservation().charged.phases ==
                  analysis.workObservation().charged.phases,
              "analysis and checked snapshot disagree on performed work");
      for (auto phase :
           {SourceWorkPhase::Parsing, SourceWorkPhase::InstalledDeclarations,
            SourceWorkPhase::WrittenRetention, SourceWorkPhase::Signatures,
            SourceWorkPhase::Bodies, SourceWorkPhase::ScopedSources,
            SourceWorkPhase::SourceAuthorities})
        require(project.workObservation().charged.used(phase) > 0,
                "real source work disappeared from " +
                    sourceWorkPhaseName(phase));
    }
  });
  cases.run("real body work ceiling identifies its subphase", [] {
    auto capture = captured();
    auto project = take(analyze(capture).checkedProject());
    const auto &ledger = project.workObservation().charged;
    uint64_t beforeBodies = ledger.total;
    for (auto phase :
         {SourceWorkPhase::Bodies, SourceWorkPhase::CommonInputs,
          SourceWorkPhase::EntriesAndClaims, SourceWorkPhase::RetainedViews,
          SourceWorkPhase::ScopedSources, SourceWorkPhase::SourceAuthorities})
      beforeBodies -= ledger.used(phase);
    require(ledger.used(SourceWorkPhase::Bodies) > 0,
            "fixture has no body work to bound");
    Limits limits;
    limits.work = beforeBodies;
    auto failed = analyze(capture, limits);
    refuses(failed.checkedProject(), "source.limit");
    bool bodyRefusal = false;
    for (const auto &diagnostic : failed.diagnostics())
      bodyRefusal |= diagnostic.code == "source.limit" &&
                     StringRef(diagnostic.message).contains("in bodies");
    require(bodyRefusal, "real checking limit lost the active body phase");
    exact(failed.workObservation().charged,
          failed.workObservation().charged.total);
    require(failed.workObservation().charged.total <= limits.work,
            "failed analysis published work beyond the allowance");
  });
  cases.run("subject and Host closure preserve child and separate budgets", [] {
    auto project = take(analyze(captured()).checkedProject());
    auto subject = take(closeSubject(project, "sample::Echo"));
    complete(subject.workObservation(), subject.closedWork());
    scopedChecks(subject);
    require(subject.invocations().empty() &&
                subject.workObservation().charged.used(
                    SourceWorkPhase::HostChildren) == 0,
            "subject closure invented a Host child charge");
    auto host = take(closeEntry(project, "sample::Echo"));
    complete(host.workObservation(), host.closedWork());
    scopedChecks(host);
    require(host.invocations().size() == 1,
            "generated Host Entry lost its child deployment");
    uint64_t expectedHost = 0;
    for (const auto &declaration : host.declarations())
      if (declaration.body)
        expectedHost += operations(*declaration.body);
    for (const auto &invocation : host.invocations()) {
      const auto &child = *invocation.deployment;
      complete(child.workObservation(), child.closedWork());
      scopedChecks(child);
      expectedHost += child.closedWork();
    }
    require(
        host.workObservation().charged.used(SourceWorkPhase::HostChildren) ==
            expectedHost,
        "Host observation lost traversal work or double-counted child phases");
  });
  cases.run("repeated Host calls charge each distinct child only once", [] {
    auto text = source.str() + R"(
      entry fn Twice(inputs:Echo::Inputs){
        let first=Echo::run(inputs);return Echo::run(inputs);
      }
    )";
    auto project = take(analyze(captured(text)).checkedProject());
    auto host = take(closeEntry(project, "sample::Twice"));
    complete(host.workObservation(), host.closedWork());
    require(host.invocations().size() == 1,
            "repeated identical calls unexpectedly closed two children");
    uint64_t traversal = 0;
    for (const auto &declaration : host.declarations())
      if (declaration.body)
        traversal += operations(*declaration.body);
    const auto &child = *host.invocations().front().deployment;
    require(
        host.workObservation().charged.used(SourceWorkPhase::HostChildren) ==
            traversal + child.closedWork(),
        "repeated calls hid traversal charges or duplicated child work");
  });
  cases.run("proof invocation retains every independently performed check", [] {
    auto project = take(analyze(captured(R"(module sample;
      protocol Work roles(P,V)(x:bool@(P,V),y:bool@P)
          ->(value:bool@P,ok:bool@V){let ok@V=x;return(value=y,ok=ok);}
      pub proof Family=Work{
        prover P;verifier V;public{x};accept ok;construction authored;
      }
    )"))
                            .checkedProject());
    auto subject = take(closeSubject(project, "sample::Family"));
    complete(subject.workObservation(), subject.closedWork());
    scopedChecks(subject);
    DeclarationId proof{};
    bool found = false;
    for (const auto &declaration : project.declarations())
      if (declaration.qualifiedName == "sample::Family") {
        proof = declaration.id;
        found = true;
      }
    require(found, "proof fixture lost its declaration");
    auto invocation = take(
        closeInvocation(project, {HostInvocation::Kind::Prove, proof, {}, {}}));
    complete(invocation.workObservation(), invocation.closedWork());
    const auto &budgets = invocation.workObservation().separateBudgets;
    require(budgets.size() == 4 &&
                budgets[0].phase == SourceWorkPhase::ScopedElaboration &&
                budgets[1].phase == SourceWorkPhase::ScopedElaboration &&
                budgets[2].phase == SourceWorkPhase::ScopedElaboration &&
                budgets[3].phase == SourceWorkPhase::ScopedSpecialization,
            "proof invocation hid an extra elaboration check on delegation");
  });
  cases.run("generic subject selector retains its independent work", [] {
    auto project = take(analyze(captured(R"(module sample;
      domain F=field("bls12-381.fr");
      pub protocol Echo<C:Field> roles(P)(value:C@P)->(result:C@P){return value;}
    )"))
                            .checkedProject());
    auto entry = take(closeSubject(project, "sample::Echo<F>"));
    complete(entry.workObservation(), entry.closedWork());
    const auto &budgets = entry.workObservation().separateBudgets;
    require(budgets.size() == 4 &&
                budgets.front().phase == SourceWorkPhase::EntrySelection &&
                budgets.front().ledger.total > 0,
            "generic selector work vanished or entered the closure allowance");
  });
  return cases.result();
}
