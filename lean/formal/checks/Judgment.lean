import ZkcFormalTests.WrittenSubject

/-!
The judgment of a recipe's proof modules.

The checks of the written subjects that a recipe runs write each pair that they accept (the
module of the statements, the challenge and the proof module) into the folder that the recipe
names (`ZKC_SUBJECTS`). This is the recipe's last step: one run of `lake comparator` over all
of them. The cost of a run is the libraries that the subjects share, so one run for all costs
little more than a run for one. With `ZKC_PARANOID` set, the comparator also runs every other
kernel that the toolchain bundles.
-/

open ZkcFormalTests ZkcFormalTests.WrittenSubject

#eval show IO Unit from do
  let some shared ← IO.getEnv "ZKC_SUBJECTS"
    | throw (IO.userError "the judgment of a recipe needs the folder of its checks' pairs (ZKC_SUBJECTS)")
  let (pairs, theorems) ← accepted shared
  if pairs.isEmpty then
    throw (IO.userError s!"the checks of the recipe noted no pair in {shared}")
  let paranoid := (← IO.getEnv "ZKC_PARANOID").isSome
  let (ok, said) ← SubjectProject.judge shared "Accepted" pairs theorems allowed paranoid
  unless ok do
    throw (IO.userError s!"the judgment refuses the proof modules that the checks accepted\n{said}")
  IO.println (s!"`lake comparator` accepts the {pairs.length} proof modules that the checks " ++
    s!"accepted: each of their {theorems.length} published theorems has the statement of its " ++
    "challenge, the kernel accepts the solutions" ++
    (if paranoid then ", as does every other kernel that the toolchain bundles," else "") ++
    s!" and the theorems rest on {allowed} at most.")
