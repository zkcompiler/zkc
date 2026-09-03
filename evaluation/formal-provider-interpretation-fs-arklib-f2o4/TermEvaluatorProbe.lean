import M0.Terminal

open M0

namespace ZkcFiatShamirTermEvaluatorProbe

def asFin3 (value : Nat) : Fin 3 :=
  ⟨value % 3, Nat.mod_lt value (by decide)⟩

def bit (value : Bool) : Nat := if value then 1 else 0

def nonterminalOccurrence : ScheduledOccurrence := {
  openingsBefore := []
  guard := .always
  isTerminal := false
}

def terminalSchedule : List ScheduledOccurrence := [
  nonterminalOccurrence,
  nonterminalOccurrence,
  nonterminalOccurrence,
  nonterminalOccurrence,
  { openingsBefore := [], guard := .evaluate 0, isTerminal := true },
  { openingsBefore := [], guard := .always, isTerminal := true }
]

def terminalValuation (verdict : Bool) : GuardAtom → Bool
  | 0 => verdict
  | _ => false

def attemptedBit (verdict : Bool) (occurrence : Nat) : Bool :=
  let region := Region terminalSchedule occurrence
  !region.impossible &&
    region.requiredTrue.all (terminalValuation verdict) &&
    region.requiredFalse.all (fun atom => !(terminalValuation verdict atom))

def selectedTerminal (verdict : Bool) : Nat :=
  if attemptedBit verdict 4 then 4
  else if attemptedBit verdict 5 then 5
  else terminalSchedule.length

def emitRows : IO Unit := do
  for statement in List.range 3 do
    for commitment in List.range 3 do
      for challenge in List.range 3 do
        for response in List.range 3 do
          let answer := schnorrDenotation (asFin3 statement) (asFin3 commitment)
            (asFin3 challenge) (asFin3 response)
          IO.println s!"TERM\t{statement}\t{commitment}\t{challenge}\t{response}\t{bit answer}"
  for value in [false, true] do
    IO.println s!"TERMINAL\t{bit value}\t{bit (attemptedBit value 4)}\t{bit (attemptedBit value 5)}\t{selectedTerminal value}"

#eval emitRows

end ZkcFiatShamirTermEvaluatorProbe
