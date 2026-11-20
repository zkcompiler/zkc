module

public import Zkc.Formal.Written.Ceiling
public import Zkc.Formal.ChargedProbability
public import Zkc.Core.World.Stack

@[expose] public section

/-!
What a written charge allows the effects of a run.

A charge has a ceiling, its numerator over its denominator, and the addresses of its draws in
the definition that owns it. In a run of that definition it allows each effect at one of those
addresses its ceiling, and every other effect nothing; in a run of another definition it allows
nothing (`allowance`). All its draws together are allowed its budget, which as a probability is
its total (`toProbability_budget`). A judgment whose fees are within the allowance pays each fee
at a draw of the charge, and not elsewhere.

The allowance is of the event at an address, whichever part of the event a role has: the role
that owns a draw and a role that hears it are allowed the same there. Which of them can pay is
said by the samplers of the judgment, and a role that hears has none.

An address is the blocks around an instruction and its key, and it occurs in a run at the path
of the run, then the iterations of those blocks, outermost first, as `Term.addresses` and the
meaning of a block write them (`occurrenceOf`). That is the occurrence of every instruction
around which no loop with a count read at run time, no application and no attempt stands: such
an instruction has one address and an occurrence for every iteration, application or attempt,
and what a charge allows there is not stated here.
-/

namespace Zkc.Formal.Written
open Core ProbabilisticProcess
open Frontend.Written (DrawCharge)
open scoped NNRat ENNReal

/-- What a charge allows one of its draws. -/
def ceiling (charge : DrawCharge) : ℚ≥0 := (charge.numerator : ℚ≥0) / charge.denominator

/-- What a charge allows all its draws together. -/
def budget (charge : DrawCharge) : ℚ≥0 := charge.draws.length * ceiling charge

/-- The budget of a charge, as a probability, is its total. -/
theorem toProbability_budget (charge : DrawCharge) (positive : 0 < charge.denominator) :
    toProbability (budget charge) = total charge := by
  have nonzero : ((charge.denominator : NNReal)) ≠ 0 := by exact_mod_cast positive.ne'
  simp [toProbability, budget, ceiling, total, ENNReal.coe_div nonzero]

/-- Where the instruction at an address occurs in a run that starts at `path`. -/
def occurrenceOf (path : List Frame) (address : List (Key × Nat) × Key) : Occurrence :=
  ⟨path ++ address.1.map fun block => .iteration block.1 block.2, address.2⟩

/-- What a charge allows an effect of a run of the definition `key` that starts at `path`: its
ceiling at each of its draws when the definition is the one that owns the charge, and nothing
elsewhere. -/
def allowance {V : Vocabulary} (M : Model V) (charge : DrawCharge) (key : Key)
    (path : List Frame) (op : ROp M) : ℚ≥0 :=
  if charge.owner = key ∧ ROp.occurrence M op ∈ charge.draws.map (occurrenceOf path) then
    ceiling charge
  else 0

end Zkc.Formal.Written
