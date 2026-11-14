module

public import Zkc.Core.EndpointsLegal
public import Zkc.Core.Interpret

public section

/-! Completeness of a grouped interactive program and of a derived scheme: the two
conditions.

- `GroupedComplete`: a process returns, **for every sampler**, values that are accepted. It
  is stated for every sampler because the coins of a derived scheme are computed, not
  sampled: a statement about the derived scheme needs the interactive run on whatever coins
  the transcript yields. `Zkc.Core.EveryRun` shows that it is the condition that every run
  returns an accepted value.
- `DerivedComplete`: for every sampler the prover's program, run alone, returns a proof, and
  the verifier's program, run alone on that proof, returns an accepted result. The proof is
  the only thing that passes from the one run to the other.
- `threadedProgram`: a program that makes a state, interprets a source from that state by a
  handler, and finishes with the source's value and the final state; what follows it is part
  of its finish (`threadedProgram_bind`). The state is the result of a process, not a
  value: a suite's start function may stop, and the verifier's reader is made from the
  proof.

Nothing is proved here that relates the two conditions. `Zkc.Core.DerivedScheme` proves
`DerivedComplete` of the role programs that the construction steps derive, from
`GroupedComplete` of the interactive entry, the laws of the layout and the condition that
the prover's messages are writable.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

section Conditions

variable {model : Model}

/-- The run starts with no site asked. -/
abbrev Asked.start : Asked := fun _ => 0

/-- Completeness of a grouped interactive process: for every sampler the run returns
values that are accepted. -/
@[expose] def GroupedComplete {grouped : Type} (whole : PIR.Process (Effects model) grouped)
    (accepted : grouped → Prop) : Prop :=
  ∀ sampler : Sampler model, ∃ values, ReturnsAlone sampler whole Asked.start values ∧ accepted values

/-- Completeness of a derived scheme: for every sampler the prover's program returns a
proof, and the verifier's program on that proof returns an accepted decision. -/
@[expose] def DerivedComplete {Proof proverValues decision : Type}
    (prover : PIR.Process (Effects model) (Proof × proverValues))
    (verifier : Proof → PIR.Process (Effects model) decision) (accepted : decision → Prop) : Prop :=
  ∀ sampler : Sampler model, ∃ proof values,
    ReturnsAlone sampler prover Asked.start (proof, values) ∧
      ∃ result, ReturnsAlone sampler (verifier proof) Asked.start result ∧ accepted result

/-- A program that threads: it makes a state, interprets a source from that state by a
handler, and finishes with the source's value and the final state. -/
@[expose] def threadedProgram {values state result : Type}
    (handler : PIR.StatefulInterpretation (Effects model) (Effects model) state)
    (start : PIR.Process (Effects model) state)
    (source : PIR.Process (Effects model) values)
    (finish : values × state → PIR.Process (Effects model) result) :
    PIR.Process (Effects model) result :=
  start.bind fun first => (source.interpretWith handler first).bind finish

/-- What follows a program that threads is part of its finish. -/
theorem threadedProgram_bind {values state result later : Type}
    (handler : PIR.StatefulInterpretation (Effects model) (Effects model) state)
    (start : PIR.Process (Effects model) state)
    (source : PIR.Process (Effects model) values)
    (finish : values × state → PIR.Process (Effects model) result)
    (next : result → PIR.Process (Effects model) later) :
    (threadedProgram handler start source finish).bind next =
      threadedProgram handler start source fun final => (finish final).bind next := by
  unfold threadedProgram
  rw [PIR.Process.bind_assoc]
  congr 1
  funext first
  rw [PIR.Process.bind_assoc]

end Conditions

end Zkc.Core
