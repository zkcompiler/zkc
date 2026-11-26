import ZkcFormal.Written.Soundness

/-!
The statement of written soundness imports nothing of the method of fees.

`ZkcFormal.Written.Soundness` says what is bounded: the probability that the verifier returns
on a rejected statement, against every conforming service. A judgment with fees is one way to
prove such a bound, and its modules all stand on `ZkcFormal.ChargedJudgment`. This file imports
the statement alone and refuses an environment that holds that module: a statement that could
only be read together with a proof method would be shaped by it.

One module of the compiler's subject library that the method of fees reads is still imported:
`Zkc.Subject.Charges`, the type of a table of caps, which a written goal's fields hold.
-/

open Lean Elab Command in
run_cmd do
  let judgment := `ZkcFormal.ChargedJudgment
  if (← getEnv).header.moduleNames.contains judgment then
    throwError "the statement of written soundness imports {judgment}, the judgment with fees"
