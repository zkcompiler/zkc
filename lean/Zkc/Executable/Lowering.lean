module

public import Zkc.Executable.Execution

@[expose] public section

/-! The lowering rule from a constructed validator to its executable program.

`Validator.read` reads the executable validator's machine work back as
constructed-participant instructions. Frame entries and returns are
transparent: a local call's formals denote its actual operands and its results
denote the operands of its return, exactly as the constructed-participant
export expands helpers. Each installed operation is read through the
vocabulary's meaning; operand sorts, including those of a local call's
declared formals, are checked, transcript operations must consume the live
transcript, and every value the participant returns with a transcript sort must
be the live transcript. Function and binding symbols must be distinct and every
declared type must have an admitted representation. The reading also records
the cumulative instruction charge at which each instruction executes, the
charge of a complete run and the receive types in order.

`checkLowering` is the per-compile rule: the executable must read back as
exactly the constructed validator's instructions, returned references, input
and output sorts, symbol, entry and validator role. Its refusals name the first
difference.

`metered` is the ideal meaning of constructed instructions under an instruction
budget, in the continuation style of `Zkc.Construction.idealK`: an instruction
runs only if its charge is within the budget, and a complete run needs the
total charge. With a sufficient budget it is the ideal meaning itself
(`Zkc.Executable.Soundness`).
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction Zkc.Source

/-- Why the rule refuses. -/
inductive Refusal where
  | unsupported (name : String)
  | binding (symbol : String)
  | operand (name : String)
  | operation (site : String)
  | representation
  | frames
  | entry
  | duplicate (kind : String)
  | different (part : String)
  | instruction (index : Nat)
  deriving DecidableEq, Repr

/-- The reading state: name scopes of the active frames, innermost first, each
mapping names to absolute references; the sorts of all references; the live
transcript reference; and the instructions charged so far. -/
structure Reading where
  scopes : List (List (String × Nat))
  sorts : List ValueSort
  current : Nat
  tick : Nat
  deriving DecidableEq, Repr

/-- The reading of machine work: instructions with the cumulative charge at
which each executes, the returned references, the charge of a complete run
and the receive types in order. -/
structure Lowered where
  code : List (Instruction × Nat)
  returned : List Nat
  total : Nat
  receives : List PhysicalType
  deriving DecidableEq, Repr

def Vocabulary.admits (vocabulary : Vocabulary) (type : PhysicalType) : Bool :=
  vocabulary.representations.contains (type.sort, type.representation)

/-- The constructed instruction an installed operation denotes, its result
sorts and whether it produces the next live transcript. -/
def readOperation (sorts : List ValueSort) (current : Nat) (site : String) :
    Resolved → List Nat → Except Refusal (Operation × List ValueSort × Bool)
  | .indicesEmpty, [] => .ok (.indicesEmpty, [.indices], false)
  | .observe suite leaf template, [state, value, coordinates] =>
      if state = current ∧ sorts[state]? = some (.transcript suite) ∧
          sorts[value]? = some (.data leaf) ∧ sorts[coordinates]? = some .indices then
        .ok (.observe suite template, [.transcript suite], true)
      else .error (.operation site)
  | .challenge suite field template, [state, coordinates] =>
      if state = current ∧ sorts[state]? = some (.transcript suite) ∧
          sorts[coordinates]? = some .indices then
        .ok (.challenge suite field template, [.data (.field field), .transcript suite], true)
      else .error (.operation site)
  | .calculate calculation, operands =>
      if operands.map (sorts[·]?) = calculation.op.arguments.map (some ∘ .data) then
        .ok (.calculate calculation, calculation.op.results.map .data, false)
      else .error (.operation site)
  | _, _ => .error (.operation site)

def lookupName (scope : List (String × Nat)) (name : String) : Except Refusal Nat :=
  match List.lookup name scope with
  | some reference => .ok reference
  | none => .error (.operand name)

/-- Read machine work from a reading state. -/
def readItems (vocabulary : Vocabulary) (validator : Validator) :
    List Item → Reading → Except Refusal Lowered
  | [], _ => .error (.unsupported "missing-return")
  | .receive site schema peer output type :: rest, R =>
      match type.sort, R.scopes with
      | .data ty, scope :: below =>
          if vocabulary.admits type then
            match readItems vocabulary validator rest
                ⟨((output, R.sorts.length) :: scope) :: below, R.sorts ++ [.data ty], R.current,
                  R.tick + 1⟩ with
            | .ok tail =>
                .ok ⟨(⟨.receive site schema peer ty, [], [.data ty], []⟩, R.tick + 1) :: tail.code,
                  tail.returned, tail.total, type :: tail.receives⟩
            | .error refusal => .error refusal
          else .error .representation
      | _, _ => .error (.operation site)
  | .enter site function arguments formals :: rest, R =>
      match R.scopes with
      | scope :: _ =>
          match arguments.mapM (lookupName scope) with
          | .ok references =>
              if formals.length = references.length ∧
                  (validator.function? function).map (·.inputs.map (some ·.2.sort)) =
                    some (references.map (R.sorts[·]?)) then
                readItems vocabulary validator rest
                  ⟨formals.zip references :: R.scopes, R.sorts, R.current, R.tick + 1⟩
              else .error (.operation site)
          | .error refusal => .error refusal
      | [] => .error .frames
  | .operation _ _ site binding parameters inputs outputs :: rest, R =>
      match R.scopes, validator.binding? binding >>= (vocabulary.resolve · parameters) with
      | scope :: below, some resolved =>
          match inputs.mapM (lookupName scope) with
          | .ok operands =>
              match readOperation R.sorts R.current site resolved operands with
              | .ok (operation, results, advances) =>
                  if outputs.length = results.length then
                    match readItems vocabulary validator rest
                        ⟨(outputs.zip (List.range' R.sorts.length results.length) ++ scope) :: below,
                          R.sorts ++ results,
                          if advances then R.sorts.length + results.length - 1 else R.current,
                          R.tick + 1⟩ with
                    | .ok tail =>
                        .ok ⟨(⟨operation, operands, results, []⟩, R.tick + 1) :: tail.code,
                          tail.returned, tail.total, tail.receives⟩
                    | .error refusal => .error refusal
                  else .error (.operation site)
              | .error refusal => .error refusal
          | .error refusal => .error refusal
      | _ :: _, none => .error (.binding binding)
      | [], _ => .error .frames
  | .leave call _ values outputs results :: rest, R =>
      match R.scopes with
      | scope :: caller :: below =>
          match values.mapM (lookupName scope) with
          | .ok references =>
              if outputs.length = references.length ∧
                  references.map (R.sorts[·]?) = results.map (some ·.sort) then
                readItems vocabulary validator rest
                  ⟨(outputs.zip references ++ caller) :: below, R.sorts, R.current, R.tick + 1⟩
              else .error (.operation call)
          | .error refusal => .error refusal
      | _ => .error .frames
  | .finish values :: _, R =>
      match R.scopes with
      | [scope] =>
          match values.mapM (lookupName scope) with
          | .ok references =>
              if references.all fun reference =>
                  match (R.sorts[reference]? : Option ValueSort) with
                  | some (.transcript _) => reference == R.current
                  | _ => true then
                .ok ⟨[], references, R.tick + 1, []⟩
              else .error (.different "returned transcript")
          | .error refusal => .error refusal
      | _ => .error .frames
  | .unsupported name :: _, _ => .error (.unsupported name)

/-- Whether every declared formal and result of a local function has an
admitted representation. -/
def Function.admitted (vocabulary : Vocabulary) (function : Function) : Bool :=
  function.inputs.all (vocabulary.admits ·.2) && function.results.all vocabulary.admits

/-- Read the validator: distinct function and binding symbols, admitted
representations for every declared type, data inputs followed by the host's
transcript, then its unfolded work. -/
def Validator.read (vocabulary : Vocabulary) (validator : Validator) : Except Refusal Lowered :=
  let sorts := validator.inputs.map (·.2.sort)
  if ¬ (validator.functions.map (·.symbol)).Nodup then .error (.duplicate "function")
  else if ¬ (validator.bindings.map (·.symbol)).Nodup then .error (.duplicate "binding")
  else if ¬ validator.functions.all (·.admitted vocabulary) then .error .representation
  else if validator.inputs.all (vocabulary.admits ·.2) ∧ validator.results.all vocabulary.admits ∧
      (sorts.getLast? matches some (ValueSort.transcript _)) ∧ (sorts.dropLast.all fun sort => sort matches ValueSort.data _) then
    readItems vocabulary validator (validator.unfold validator.body)
      ⟨[(validator.inputs.map (·.1)).zip (List.range sorts.length)], sorts, sorts.length - 1, 0⟩
  else .error .entry

/-- The first position at which two instruction lists differ. -/
def firstDifference : List Instruction → List Instruction → Nat
  | first :: rest, other :: others => if first = other then firstDifference rest others + 1 else 0
  | _, _ => 0

/-- The per-compile lowering rule: the executable validator reads back as
exactly the constructed validator. -/
def checkLowering (vocabulary : Vocabulary) (participant : Participant) (validator : Validator) :
    Except Refusal Lowered := do
  let lowered ← validator.read vocabulary
  unless validator.symbol = participant.symbol do throw (Refusal.different "symbol")
  unless validator.entry = participant.policy.entry do throw (Refusal.different "entry")
  unless validator.role = participant.policy.validator do throw (Refusal.different "role")
  unless validator.inputs.map (·.2.sort) = participant.inputs do throw (Refusal.different "inputs")
  unless validator.results.map (·.sort) = participant.outputs do throw (Refusal.different "outputs")
  unless lowered.code.map (·.1) = participant.instructions do
    throw (Refusal.instruction (firstDifference (lowered.code.map (·.1)) participant.instructions))
  unless lowered.returned = participant.returned do throw (Refusal.different "returned")
  pure lowered

/-- The ideal meaning of constructed instructions under an instruction budget:
each instruction runs, as `Zkc.Construction.idealStep` runs it, only if its
charge is within the budget; the final return needs the total charge. -/
def metered {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    {m : Type → Type} [Monad m] (context : Context) (challenge : History F G → m F)
    (table : Structured.Evaluation.Meanings F G Structured.closedInterface) (returned : List Nat)
    (total budget : Nat) :
    List (Instruction × Nat) → List (Value F G) → Proof F G →
      m (PIR.Outcome (List (Value F G)) × Proof F G)
  | [], env, proof => pure (if total ≤ budget then finish returned env else .stopped .exhausted, proof)
  | (instruction, charge) :: rest, env, proof =>
      if charge ≤ budget then
        idealStep context challenge table instruction env proof fun env' unread =>
          metered context challenge table returned total budget rest env' unread
      else pure (.stopped .exhausted, proof)

/-- The typed proof a message byte string denotes for a sequence of receive
types: each length-framed message decoded at its type, up to the first message
that is missing or does not decode. Bytes left after the last receive become
one unread entry, so that a run which returns has read the whole proof exactly
when its ideal reading has. -/
def decodeProof {F G : Type} (decode : PhysicalType → List UInt8 → Option (Payload F G)) :
    List PhysicalType → List UInt8 → Proof F G
  | [], bytes => if bytes.isEmpty then [] else [.boolean false]
  | type :: types, bytes =>
      match readFrame bytes with
      | some (payload, rest) =>
          match decode type payload with
          | some value => value :: decodeProof decode types rest
          | none => []
      | none => []

end Zkc.Executable
