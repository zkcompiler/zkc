import Examples.InteractiveRound

set_option autoImplicit false

-- Not `Tests.PhaseAdmission`, which every other file here uses: this one opens the
-- library's own `PhaseAdmission`, and a namespace of that name would shadow it at
-- the `open` rather than being opened alongside it.
namespace PhaseAdmissionTests

open Zkc.Source Zkc.Compiler PhaseAdmission InteractiveRound

example : (run true 1).outcome = .returned 17 := by decide
example : (run true 1).state = (.ready, 9) := by rfl
example : (run true 1).events = [
    .inl (.ready, .commit 1), .inr (.commit 1),
    .inl (.committed, .challenge), .inr .challenge,
    .inl (.challenged, .respond 11), .inr (.respond 11),
    .inl (.ready, .commit 11), .inr (.commit 11),
    .inl (.committed, .challenge), .inr .challenge,
    .inl (.challenged, .respond 14), .inr (.respond 14),
    .inl (.ready, .commit 14), .inr (.commit 14),
    .inl (.committed, .challenge), .inr .challenge,
    .inl (.challenged, .respond 17), .inr (.respond 17)] := by rfl

example : (run true 0).outcome = .stopped .abort := by decide
example : (run true 0).state = (.ready, 1) := by rfl
example : (run true 0).events = [.inl (.ready, .commit 0), .inr (.commit 0)] := by rfl
example : (run false 1).outcome = .stopped .reject := by decide
example : (run false 1).state = (.ready, 0) := by rfl
example : (run false 1).events = [] := by decide

theorem source_conforms (env : Environment meaning.Value context) :
    PIR.Conforms interaction (source.denote meaning env) .ready :=
  (admitted.sound meaning interaction summaryLaws env .ready ⟨.ready, by simp, rfl⟩).1

/-- Actual checked-plan calls obey the interaction for any provider, including
ones that stop. This theorem does not specialize to the example handler. -/
theorem checked_calls {candidate : RawProgram Ty Op} (checked : CheckedPlan source candidate)
    {S E : Type} (provider : PIR.Handler interface S E)
    (env : Environment meaning.Value context) (state : S) :
    ∀ before op, Sum.inl (before, op) ∈
      (checked.plan.run meaning (PIR.ExecutionPath.handler interaction provider)
        env (.ready, state)).events → interaction.enabled before op :=
  checked.calls_permitted admitted meaning interaction summaryLaws provider env .ready state
    ⟨.ready, by simp, rfl⟩

theorem checked_return {candidate : RawProgram Ty Op} (checked : CheckedPlan source candidate)
    {S E : Type} (provider : PIR.Handler interface S E)
    (env : Environment meaning.Value context) (value : Nat) (initialState : S)
    (returned : (checked.plan.run meaning (PIR.ExecutionPath.handler interaction provider)
      env (.ready, initialState)).outcome = .returned value) :
    (checked.plan.run meaning (PIR.ExecutionPath.handler interaction provider)
      env (.ready, initialState)).state.1 = .ready := by
  have permitted := checked.return_permitted admitted meaning interaction summaryLaws provider env
    .ready initialState ⟨.ready, by simp, rfl⟩ value returned
  apply Eq.symm
  simpa [Covered, summaryLaws, interaction] using permitted

/-- Value typing and exact compiler preservation alone allow this illegal call. -/
def wrongOrder : Program language context .natural :=
  .letOp .challenge .nil (.ret .here)

example : (checkDirect wrongOrder (lower wrongOrder).erase).isSome = true := by decide
example : check policy wrongOrder (.next .terminal) [.ready] = none := by decide
example (env : Environment meaning.Value context) :
    ¬ PIR.Conforms interaction (wrongOrder.denote meaning env) .ready := by
  intro formed
  exact formed.1

def unfinished : Program language context .natural :=
  .letOp .commit (.cons (.there .here) .nil) (.ret .here)

example : check policy unfinished (.next .terminal) [.ready] = some [.committed] := by decide
example : (admit policy unfinished (.next .terminal) [.ready] [.ready]).isNone = true := by decide

/-- An explicit stop is observable but has no successful-return obligation. -/
def stopped : Program language context .natural :=
  .letOp .commit (.cons (.there .here) .nil) (.stop .refused)

example : (admit policy stopped (.next .terminal) [.ready] [.ready]).isSome = true := by decide
example : check policy source .terminal [.ready] = none := by decide
example : check policy source
    (.branch (.loop [] (.next (.next (.next .terminal))) .terminal) .terminal) [.ready] = none := by decide
example : check policy source
    (.branch (.loop [.ready, .committed] (.next (.next (.next .terminal))) .terminal) .terminal)
    [.ready] = none := by decide

/-- Counts do not participate in invariant checking, even at arbitrary precision. -/
def repeated (count : Nat) : Program language context .natural :=
  .iterate count (.there .here)
    (.letOp .commit (.cons .here .nil)
      (.letOp .challenge .nil (.letOp .respond (.cons .here .nil) (.ret .here))))
    (.ret .here)

example (count : Nat) : check policy (repeated count)
    (.loop [.ready] (.next (.next (.next .terminal))) .terminal) [.ready] = some [.ready] := by rfl

/-- Deliberate incompleteness: the zero-count denotation skips an invalid body,
whereas the invariant rule still checks it. Refusal is not semantic illegality. -/
def zeroBadBody : Program language context .natural :=
  .iterate 0 (.there .here) (.letOp .challenge .nil (.ret .here)) (.ret .here)

example (env : Environment meaning.Value context) :
    PIR.Conforms interaction (zeroBadBody.denote meaning env) .ready := by trivial
example : check policy zeroBadBody (.loop [.ready] (.next .terminal) .terminal) [.ready] = none := by decide

/-- A provider-dependent phase cannot be replaced by the phase of one sampled
reply. The returning boundary must cover the reply that resets the phase too. -/
def replySensitive : PIR.Interaction interface := { interaction with
  advance := fun phase op reply => match op with
    | .challenge => if reply == 0 then .ready else .challenged
    | _ => interaction.advance phase op reply }

theorem no_sampled_summary (laws : Realizes policy meaning replySensitive)
    (exactPhases : laws.relates = Eq) : False := by
  have law := laws.operation .challenge .committed [.challenged] rfl .nil .committed
    (by rw [exactPhases])
  have zeroReply := law.2 0
  simp [meaning, PIR.Boundary.Returns, replySensitive, interaction, exactPhases] at zeroReply

/-- The shared suffix receives the actual body's return-phase cover. -/
def compactRound : Region language context .natural :=
  .bind (.letOp .commit (.cons (.there .here) .nil) (.ret .here))
    (.letOp .challenge .nil (.letOp .respond (.cons .here .nil) (.ret .here)))

def compactCertificate : Certificate Phase :=
  .bind (.next .terminal) (.next (.next .terminal))

example : checkRegion policy compactRound compactCertificate [.ready] = some [.ready] := by decide

theorem compact_conforms (env : Environment meaning.Value context) :
    PIR.Conforms interaction (compactRound.denote meaning env) .ready :=
  (checkRegion_sound policy meaning interaction summaryLaws compactRound compactCertificate
    [.ready] [.ready] (by decide) env .ready ⟨.ready, by simp, rfl⟩).1

def compactRequest : RegionArtifact.Request Ty Op :=
  ⟨request.context, [], compactRound.erase⟩

def compactCandidate : RegionArtifact.Candidate Ty Op :=
  ⟨⟨1, RegionArtifact.semanticsVersion, [], "direct-logical-plan", "direct-lowering",
    completeExecution, compactRequest.context, []⟩, compactRound.erase⟩

def compactChecked : RegionArtifact.Checked (language := language) compactRequest compactCandidate :=
  (RegionArtifact.check (language := language) compactRequest compactCandidate).toOption.get (by decide)

theorem compact_artifact_calls {S E : Type} (provider : PIR.Handler interface S E)
    (env : Environment meaning.Value context) (state : S) :
    ∀ before op, Sum.inl (before, op) ∈
      ((compactChecked.region.denote meaning env).run
        (PIR.ExecutionPath.handler interaction provider) (.ready, state)).events →
      interaction.enabled before op :=
  compactChecked.calls_permitted policy compactCertificate [.ready] [.ready]
    (by decide) meaning interaction summaryLaws env .ready ⟨.ready, by simp, rfl⟩
    provider state compactChecked.region compactChecked.candidateDecoded

theorem compact_artifact_return {S E : Type} (provider : PIR.Handler interface S E)
    (env : Environment meaning.Value context) (value : Nat)
    (providerState : S)
    (returned : ((compactChecked.region.denote meaning env).run
      (PIR.ExecutionPath.handler interaction provider) (.ready, providerState)).outcome =
        .returned value) :
    Covered summaryLaws [.ready]
      ((compactChecked.region.denote meaning env).run
        (PIR.ExecutionPath.handler interaction provider) (.ready, providerState)).state.1 :=
  compactChecked.return_permitted policy compactCertificate [.ready] [.ready] [.ready]
    (by decide) (fun _ h => h) meaning interaction summaryLaws env .ready
    ⟨.ready, by simp, rfl⟩ provider providerState compactChecked.region
    compactChecked.candidateDecoded value returned

/-- Shape evidence cannot be reused after the shared body changes its phase. -/
def compactWrongOrder : Region language context .natural :=
  .bind (.ret (.there .here))
    (.letOp .challenge .nil (.ret .here))

example : checkRegion policy compactWrongOrder (.bind .terminal (.next .terminal)) [.ready] =
    none := by decide
example : checkRegion policy compactRound (.next .terminal) [.ready] = none := by decide

/-- A returning branch cannot stand in for the other branch's phase. -/
def mixedExit : Region language context .natural :=
  .bind (.branch .here
    (.letOp .commit (.cons (.there .here) .nil) (.ret .here))
    (.ret (.there .here)))
    (.letOp .challenge .nil (.ret .here))

example : checkRegion policy mixedExit
    (.bind (.branch (.next .terminal) .terminal) (.next .terminal)) [.ready] = none := by decide

/-- A stopped prefix never grants permission to call its suffix. There are no
returning phases to check; the complete execution still retains the stop. -/
example : checkRegion policy
    (Region.bind (Region.stop (language := language) (Γ := context) (ty := Ty.natural) .abort)
      (.letOp .challenge .nil (.ret .here)))
    (.bind .terminal (.next .terminal)) [.ready] = some [] := by decide

example : decodeCertificate phaseCodec 8 (encodeCertificate phaseCodec compactCertificate) =
    .ok compactCertificate := by rfl
example : decodeCertificate phaseCodec 1 (encodeCertificate phaseCodec compactCertificate) =
    .error .depthLimit := by rfl
example : decodeCertificate phaseCodec 8 (.arr #[.str "bind", .arr #[.str "terminal"]]) =
    .error .shape := by rfl

example : checkRegion policy (.bind source.toRegion (.ret .here))
    (.bind certificate .terminal) [.ready] = some [.ready] := by decide
example : decodeCertificate phaseCodec 16
    (encodeCertificate phaseCodec (.bind certificate .terminal)) =
      .ok (.bind certificate .terminal) := by rfl

/-- A family of compact shared continuations. Admission visits the continuation
once per level; it neither expands both paths nor guesses a particular branch. -/
def shared {Γ : List Ty} {ty : Ty} (condition : Var Γ .boolean) (value : Var Γ ty) :
    Nat → Region language Γ ty
  | 0 => .ret value
  | n + 1 => .bind (.branch condition (.ret value) (.ret value))
      (shared (.there condition) .here n)

def sharedCertificate : Nat → Certificate Phase
  | 0 => .terminal
  | n + 1 => .bind (.branch .terminal .terminal) (sharedCertificate n)

theorem shared_checked {Γ : List Ty} {ty : Ty} (condition : Var Γ .boolean)
    (value : Var Γ ty) (count : Nat) :
    checkRegion policy (shared condition value count) (sharedCertificate count) [.ready] =
      some [.ready] := by
  induction count generalizing Γ with
  | zero => rfl
  | succ n ih =>
    change checkRegion policy (shared (.there condition) .here n) (sharedCertificate n)
      [.ready] = some [.ready]
    exact ih (.there condition) (Var.here (Γ := Γ))

end PhaseAdmissionTests
