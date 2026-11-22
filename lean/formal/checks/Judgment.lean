import ZkcFormalTests.WrittenSubject

/-!
The judgment of a recipe's proof modules.

The checks of the written subjects that a recipe runs write each pair that they accept (the
module of the statements, the challenge and the proof module) into the folder that the recipe
names (`ZKC_SUBJECTS`). This is the recipe's last step: the folder is a project of its own,
settled as every project of a check is (the statements and the challenges built and exported
before any text is read, every text read confined), and judged by one run of
`lake comparator` over all the pairs. The cost of a run is the libraries that the subjects
share, so one run for all costs little more than a run for one. With `ZKC_PARANOID` set, the
comparator also runs every other kernel that the toolchain bundles.
-/

open ZkcFormalTests ZkcFormalTests.WrittenSubject

#eval show IO Unit from do
  let some shared ← IO.getEnv "ZKC_SUBJECTS"
    | throw (IO.userError "the judgment of a recipe needs the folder of its checks' pairs (ZKC_SUBJECTS)")
  let (pairs, theorems) ← accepted shared
  if pairs.isEmpty then
    throw (IO.userError s!"the checks of the recipe noted no pair in {shared}")
  let paranoid := (← IO.getEnv "ZKC_PARANOID").isSome
  SubjectProject.expect shared acceptedLabel pairs theorems allowed
  match ← SubjectProject.judge shared acceptedLabel paranoid with
  | (.accepted, _) => pure ()
  | (.refused, said) =>
    throw (IO.userError s!"the judgment refuses the proof modules that the checks accepted\n{said}")
  | (.failed, said) =>
    throw (IO.userError s!"the proof modules that the checks accepted were not judged\n{said}")
  IO.println (s!"`lake comparator` accepts the {pairs.length} proof modules that the checks " ++
    s!"accepted: each of their {theorems.length} judged theorems has the statement of its " ++
    "challenge, the kernel accepts the solutions" ++
    (if paranoid then ", as does every other kernel that the toolchain bundles," else "") ++
    s!" and the theorems rest on {allowed} at most.")
