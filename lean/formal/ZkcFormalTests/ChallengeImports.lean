import ZkcFormal.Written.Publish

/-!
What a challenge stands on.

A challenge is its data module and the command `publish_goals` (`ZkcFormal.Written.Publish`).
This file imports the command alone and compares the modules of the formal library and of the
compiler's subject library in its environment with the list below. A module that is not listed is
refused, whatever it holds: the judgment with fees and what stands on it, the views, an author's
tactics. The control of a challenge's imports (`#challenge_module`) allows whatever the command
imports, so it cannot see a module that the command itself gains; this list is where such a
change is made, in view.

Beyond what the statement of soundness stands on (`SoundnessImports`), the command reads the
subject's rows (`Zkc.Subject.WrittenGoal`, with the table of caps and the bound that a row
holds: the command decides the bound of a goal without a ceiling against its table, by the
budget's arithmetic in `ZkcFormal.Written.Budget`, which is no part of the fee judgment) and
states at the standard interpretation (its model, draws and coverage).
-/

open Lean Elab Command

/-- The modules of `ZkcFormal` and of `Zkc.Subject` that the command of a challenge imports,
directly or through others. -/
def challengeStandsOn : List Name := [
  `Zkc.Subject.Bound,
  `Zkc.Subject.Charges,
  `Zkc.Subject.Coverage,
  `Zkc.Subject.Coverage.Pending,
  `Zkc.Subject.Package,
  `Zkc.Subject.ShortApplication,
  `Zkc.Subject.WrittenGoal,
  `ZkcFormal.OracleProcess,
  `ZkcFormal.ProbabilisticProcess,
  `ZkcFormal.ProcessJudgment,
  `ZkcFormal.ReturnExperiment,
  `ZkcFormal.Samplers,
  `ZkcFormal.Written.ArithmeticDraws,
  `ZkcFormal.Written.ArithmeticModel,
  `ZkcFormal.Written.Bound,
  `ZkcFormal.Written.Budget,
  `ZkcFormal.Written.Execution,
  `ZkcFormal.Written.Extraction,
  `ZkcFormal.Written.FunctionMeaning,
  `ZkcFormal.Written.Goal.Inputs,
  `ZkcFormal.Written.LawSamplers,
  `ZkcFormal.Written.PortSamplers,
  `ZkcFormal.Written.Publish,
  `ZkcFormal.Written.ScalarField,
  `ZkcFormal.Written.Soundness,
  `ZkcFormal.Written.Source,
  `ZkcFormal.Written.StandardDefaults,
  `ZkcFormal.Written.StandardInterpretation,
  `ZkcFormal.Written.StandardModel,
  `ZkcFormal.Written.UniformVector]

run_cmd do
  let watched (module : Name) : Bool :=
    module.getRoot == `ZkcFormal || (`Zkc.Subject).isPrefixOf module
  let found := ((← getEnv).header.moduleNames.filter watched).toList
  let added := found.filter (!challengeStandsOn.contains ·)
  let gone := challengeStandsOn.filter (!found.contains ·)
  unless added.isEmpty && gone.isEmpty do
    throwError "a challenge stands on other modules than listed: \
      not listed {added}; listed and not imported {gone}"
