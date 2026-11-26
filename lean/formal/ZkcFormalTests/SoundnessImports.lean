import ZkcFormal.Written.Soundness

/-!
What the statement of written soundness stands on.

`ZkcFormal.Written.Soundness` says what is bounded: the probability that the verifier returns
on a rejected statement, against every conforming service. A proof method is one way to prove
such a bound; a statement that could only be read together with a method would be shaped by
it. This file imports the statement alone and compares the modules of the formal library and
of the compiler's subject library in its environment with the list below. A module that is not
listed is refused, whatever it holds: the judgment with fees and what stands on it, the earlier
charge modules that do not stand on it, an author's tactics. A change of what the statement
stands on is made here, in view.

One listed module is of the method of fees: `Zkc.Subject.Charges`, the type of a table of caps,
which a written goal's fields hold. It leaves this list when the fields no longer hold a table.
-/

open Lean Elab Command

/-- The modules of `ZkcFormal` and of `Zkc.Subject` that the statement of written soundness
imports, directly or through others. -/
def soundnessStandsOn : List Name := [
  `Zkc.Subject.Charges,
  `Zkc.Subject.Package,
  `Zkc.Subject.WrittenGoal,
  `ZkcFormal.OracleProcess,
  `ZkcFormal.ProbabilisticProcess,
  `ZkcFormal.ProcessJudgment,
  `ZkcFormal.ReturnExperiment,
  `ZkcFormal.Samplers,
  `ZkcFormal.Written.Execution,
  `ZkcFormal.Written.Extraction,
  `ZkcFormal.Written.FunctionMeaning,
  `ZkcFormal.Written.Goal.Inputs,
  `ZkcFormal.Written.LawSamplers,
  `ZkcFormal.Written.PortSamplers,
  `ZkcFormal.Written.Soundness,
  `ZkcFormal.Written.Source,
  `ZkcFormal.Written.StandardDefaults,
  `ZkcFormal.Written.StandardModel]

run_cmd do
  let watched (module : Name) : Bool :=
    module.getRoot == `ZkcFormal || (`Zkc.Subject).isPrefixOf module
  let found := ((← getEnv).header.moduleNames.filter watched).toList
  let added := found.filter (!soundnessStandsOn.contains ·)
  let gone := soundnessStandsOn.filter (!found.contains ·)
  unless added.isEmpty && gone.isEmpty do
    throwError "the statement of written soundness stands on other modules than listed: \
      not listed {added}; listed and not imported {gone}"
