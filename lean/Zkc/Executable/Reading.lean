module

public import Zkc.Executable.Execution
public import Zkc.Executable.Code
public import Zkc.Executable.DomainNormalizationCheck

@[expose] public section

/-! Structural reading and artifact admission. These checks contain no
constructed execution interpreter; Code charges and receive plans are stage
syntax and normalization compares explicit scopes. -/
set_option autoImplicit false
namespace Zkc.Executable
open Zkc.Construction Zkc.Source

/-- The reading state: the sorts of all references and the live transcript
reference. -/
structure Reading where
  sorts : List ValueSort
  current : Nat
  deriving DecidableEq, Repr

def Vocabulary.admits (vocabulary : Vocabulary) (type : PhysicalType) : Bool :=
  vocabulary.representations.contains (type.sort, type.representation)

/-- The constructed instruction an installed operation denotes, its result
sorts and whether it produces the next live transcript. -/
def readOperation (sorts : List ValueSort) (current : Nat) (site : String) :
    Resolved → List Nat → Except Refusal (Operation × List ValueSort × Bool)
  | .indicesEmpty, [] => .ok (.indicesEmpty, [.indices], false)
  | .indicesAppend, [coordinates, index] =>
      if sorts[coordinates]? = some .indices ∧ sorts[index]? = some (.data .index) then
        .ok (.indicesAppend, [.indices], false)
      else .error (.operation site)
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

/-- The name of a local instruction, for refusals. -/
def Step.name : Step → String
  | .operation site _ _ _ _ => site
  | .constant site _ _ => site
  | .cond site _ _ _ _ _ => site
  | .iterate site _ _ _ _ _ _ _ => site
  | .stop site _ => site
  | .yield _ => "yield"
  | .ret _ => "return-not-final"
  | .unsupported name => name

/-- Read a transparent local body in its call's scope: its constructed
instructions with their charges (the return's included), the references it
returns and the reading state after it. -/
def readBody (vocabulary : Vocabulary) (validator : Validator) :
    List Step → List (String × Nat) → Reading → Except Refusal (List Code × List Nat × Reading)
  | [], _, _ => .error (.unsupported "missing-return")
  | [.ret values], scope, R =>
      match values.mapM (lookupName scope) with
      | .ok references => .ok ([.charge 1], references, R)
      | .error refusal => .error refusal
  | .operation site binding parameters inputs outputs :: rest, scope, R =>
      match validator.binding? binding >>= (vocabulary.resolve · parameters) with
      | some resolved =>
          match inputs.mapM (lookupName scope) with
          | .ok operands =>
              match readOperation R.sorts R.current site resolved operands with
              | .ok (operation, results, advances) =>
                  if outputs.length = results.length then
                    match readBody vocabulary validator rest
                        (outputs.zip (List.range' R.sorts.length results.length) ++ scope)
                        ⟨R.sorts ++ results,
                          if advances then R.sorts.length + results.length - 1 else R.current⟩ with
                    | .ok (codes, returned, R') =>
                        .ok (.step ⟨operation, operands, results, []⟩ 1 :: codes, returned, R')
                    | .error refusal => .error refusal
                  else .error (.operation site)
              | .error refusal => .error refusal
          | .error refusal => .error refusal
      | none => .error (.binding binding)
  | .constant _ output value :: rest, scope, R =>
      match readBody vocabulary validator rest ((output, R.sorts.length) :: scope)
          ⟨R.sorts ++ [.data .boolean], R.current⟩ with
      | .ok (codes, returned, R') =>
          .ok (.step ⟨.calculate (.booleanConstant value), [], [.data .boolean], []⟩ 1 :: codes, returned, R')
      | .error refusal => .error refusal
  | .cond site condition [] [.yield []] [.stop stopSite "reject"] [] :: rest, scope, R =>
      match lookupName scope condition with
      | .ok reference =>
          if R.sorts[reference]? = some (.data .boolean) then
            match readBody vocabulary validator rest scope R with
            | .ok (codes, returned, R') =>
                .ok (.step ⟨.guard stopSite, [reference], [], []⟩ 2 :: codes, returned, R')
            | .error refusal => .error refusal
          else .error (.operation site)
      | .error refusal => .error refusal
  | step :: _, _, _ => .error (.unsupported step.name)

mutual
/-- Whether a local body applies only operations without a transcript. -/
def transcriptFree (vocabulary : Vocabulary) (validator : Validator) : List Step → Bool
  | [] => true
  | step :: rest => transcriptFreeStep vocabulary validator step && transcriptFree vocabulary validator rest

def transcriptFreeStep (vocabulary : Vocabulary) (validator : Validator) : Step → Bool
  | .operation _ binding parameters _ _ =>
      match validator.binding? binding >>= (vocabulary.resolve · parameters) with
      | some (.observe _ _ _) | some (.challenge _ _ _) => false
      | _ => true
  | .cond _ _ _ yes no _ => transcriptFree vocabulary validator yes && transcriptFree vocabulary validator no
  | .iterate _ _ _ _ _ _ body _ => transcriptFree vocabulary validator body
  | _ => true
end

/-- How a participant body ends: a loop body yields references, the
participant's body returns them. -/
inductive Ending where
  | yielded (references : List Nat)
  | returned (references : List Nat)
  deriving DecidableEq, Repr

/-- The position of the first transcript sort. -/
def transcriptPosition (sorts : List ValueSort) : Option Nat :=
  sorts.findIdx? fun sort => sort matches .transcript _

/-- Whether references of a transcript sort are exactly the live one. -/
def custody (sorts : List ValueSort) (current : Nat) (references : List Nat) : Bool :=
  references.all fun reference =>
    match (sorts[reference]? : Option ValueSort) with
    | some (.transcript _) => reference == current
    | _ => true

/-- Read participant instructions in the scope of the innermost participant
frame: the constructed instructions with their charges, the receive plan, how
the body ends and the reading state at its end. `helpers` are the helpers the
constructed validator calls by name; `inputs` is the number of data inputs. -/
def readActions (vocabulary : Vocabulary) (validator : Validator) (helpers : List String)
    (inputs : Nat) :
    List Action → List (String × Nat) → Reading →
      Except Refusal (List Code × List Plan × Ending × Reading)
  | [], _, _ => .error (.unsupported "missing-return")
  | [.yield values], scope, R =>
      match values.mapM (lookupName scope) with
      | .ok references => .ok ([], [], .yielded references, R)
      | .error refusal => .error refusal
  | [.ret values], scope, R =>
      match values.mapM (lookupName scope) with
      | .ok references =>
          if custody R.sorts R.current references then .ok ([], [], .returned references, R)
          else .error (.different "returned transcript")
      | .error refusal => .error refusal
  | .receive site schema peer output type :: rest, scope, R =>
      match type.sort with
      | .data ty =>
          if vocabulary.admits type then
            match readActions vocabulary validator helpers inputs rest ((output, R.sorts.length) :: scope)
                ⟨R.sorts ++ [.data ty], R.current⟩ with
            | .ok (codes, plan, ending, R') =>
                .ok (.step ⟨.receive site schema peer ty, [], [.data ty], []⟩ 1 :: codes,
                  .receive type :: plan, ending, R')
            | .error refusal => .error refusal
          else .error .representation
      | _ => .error (.operation site)
  | .call site function arguments outputs :: rest, scope, R =>
      match validator.function? function, arguments.mapM (lookupName scope) with
      | some callee, .ok operands =>
          if callee.inputs.length = operands.length ∧
              callee.inputs.map (some ·.2.sort) = operands.map (R.sorts[·]?) then
            if helpers.contains function then
              let results := callee.results.map (·.sort)
              if transcriptFree vocabulary validator callee.body ∧ outputs.length = results.length ∧
                  results.all (· matches .data _) then
                match readActions vocabulary validator helpers inputs rest
                    (outputs.zip (List.range' R.sorts.length results.length) ++ scope)
                    ⟨R.sorts ++ results, R.current⟩ with
                | .ok (codes, plan, ending, R') =>
                    .ok (.helper ⟨.call function, operands, results, []⟩ :: codes, plan, ending, R')
                | .error refusal => .error refusal
              else .error (.helper function)
            else
              match readBody vocabulary validator callee.body ((callee.inputs.map (·.1)).zip operands) R with
              | .ok (body, returned, R₁) =>
                  if outputs.length = returned.length ∧
                      returned.map (R₁.sorts[·]?) = callee.results.map (some ·.sort) then
                    match readActions vocabulary validator helpers inputs rest (outputs.zip returned ++ scope) R₁ with
                    | .ok (codes, plan, ending, R') => .ok (.charge 1 :: body ++ codes, plan, ending, R')
                    | .error refusal => .error refusal
                  else .error (.operation site)
              | .error refusal => .error refusal
          else .error (.operation site)
      | none, _ => .error (.unsupported function)
      | _, .error refusal => .error refusal
  | .loop site count maximum induction carried captures body outputs :: rest, scope, R =>
      match lookupName scope count, (carried.map (·.2)).mapM (lookupName scope),
          captures.mapM (lookupName scope) with
      | .ok counter, .ok initial, .ok captured =>
          let sorts := initial.filterMap (R.sorts[·]?)
          let base := R.sorts.length
          if counter < inputs ∧ R.sorts[counter]? = some (.data .index) ∧
              sorts.length = initial.length ∧ carried.length = initial.length ∧
              outputs.length = initial.length ∧ custody R.sorts R.current initial ∧
              (sorts.filter (· matches .transcript _)).length ≤ 1 ∧
              captured.all (fun reference => R.sorts[reference]? matches some (.data _)) then
            match readActions vocabulary validator helpers inputs body
                ((induction, base) :: (carried.map (·.1)).zip (List.range' (base + 1) initial.length) ++
                  captures.zip captured)
                ⟨R.sorts ++ .data .index :: sorts,
                  match transcriptPosition sorts with
                  | some position => base + 1 + position
                  | none => R.current⟩ with
            | .ok (inner, innerPlan, .yielded yielded, R₁) =>
                if yielded.map (R₁.sorts[·]?) = sorts.map some ∧ custody R₁.sorts R₁.current yielded ∧
                    (transcriptPosition sorts = none → R₁.current = R.current) then
                  match readActions vocabulary validator helpers inputs rest
                      (outputs.zip (List.range' base sorts.length) ++ scope)
                      ⟨R.sorts ++ sorts,
                        match transcriptPosition sorts with
                        | some position => base + position
                        | none => R.current⟩ with
                  | .ok (codes, plan, ending, R') =>
                      .ok (.loop site maximum yielded (counter :: initial) sorts inner :: codes,
                        .loop counter maximum innerPlan :: plan, ending, R')
                  | .error refusal => .error refusal
                else .error (.loop site)
            | .ok (_, _, .returned _, _) => .error (.loop site)
            | .error refusal => .error refusal
          else .error (.loop site)
      | .error refusal, _, _ => .error refusal
      | _, .error refusal, _ => .error refusal
      | _, _, .error refusal => .error refusal
  | .yield _ :: _ :: _, _, _ => .error (.unsupported "yield-not-final")
  | .ret _ :: _ :: _, _, _ => .error (.unsupported "return-not-final")
  | .unsupported name :: _, _, _ => .error (.unsupported name)

mutual
/-- `readActions` by structural recursion, which the kernel evaluates
(`readActionList_eq`). -/
def readActionList (vocabulary : Vocabulary) (validator : Validator) (helpers : List String)
    (inputs : Nat) :
    List Action → List (String × Nat) → Reading →
      Except Refusal (List Code × List Plan × Ending × Reading)
  | [], _, _ => .error (.unsupported "missing-return")
  | [.yield values], scope, R =>
      match values.mapM (lookupName scope) with
      | .ok references => .ok ([], [], .yielded references, R)
      | .error refusal => .error refusal
  | [.ret values], scope, R =>
      match values.mapM (lookupName scope) with
      | .ok references =>
          if custody R.sorts R.current references then .ok ([], [], .returned references, R)
          else .error (.different "returned transcript")
      | .error refusal => .error refusal
  | action :: rest, scope, R =>
      match readAction vocabulary validator helpers inputs action scope R with
      | .ok (codes, plan, scope', R₁) =>
          match readActionList vocabulary validator helpers inputs rest scope' R₁ with
          | .ok (codes', plan', ending, R') => .ok (codes ++ codes', plan ++ plan', ending, R')
          | .error refusal => .error refusal
      | .error refusal => .error refusal

/-- Read one participant action that does not end its body: its constructed
instructions with their charges, its receives, and the scope and reading state
after it. -/
def readAction (vocabulary : Vocabulary) (validator : Validator) (helpers : List String)
    (inputs : Nat) :
    Action → List (String × Nat) → Reading →
      Except Refusal (List Code × List Plan × List (String × Nat) × Reading)
  | .receive site schema peer output type, scope, R =>
      match type.sort with
      | .data ty =>
          if vocabulary.admits type then
            .ok ([.step ⟨.receive site schema peer ty, [], [.data ty], []⟩ 1], [.receive type],
              (output, R.sorts.length) :: scope, ⟨R.sorts ++ [.data ty], R.current⟩)
          else .error .representation
      | _ => .error (.operation site)
  | .call site function arguments outputs, scope, R =>
      match validator.function? function, arguments.mapM (lookupName scope) with
      | some callee, .ok operands =>
          if callee.inputs.length = operands.length ∧
              callee.inputs.map (some ·.2.sort) = operands.map (R.sorts[·]?) then
            if helpers.contains function then
              let results := callee.results.map (·.sort)
              if transcriptFree vocabulary validator callee.body ∧ outputs.length = results.length ∧
                  results.all (· matches .data _) then
                .ok ([.helper ⟨.call function, operands, results, []⟩], [],
                  outputs.zip (List.range' R.sorts.length results.length) ++ scope,
                  ⟨R.sorts ++ results, R.current⟩)
              else .error (.helper function)
            else
              match readBody vocabulary validator callee.body ((callee.inputs.map (·.1)).zip operands) R with
              | .ok (body, returned, R₁) =>
                  if outputs.length = returned.length ∧
                      returned.map (R₁.sorts[·]?) = callee.results.map (some ·.sort) then
                    .ok (.charge 1 :: body, [], outputs.zip returned ++ scope, R₁)
                  else .error (.operation site)
              | .error refusal => .error refusal
          else .error (.operation site)
      | none, _ => .error (.unsupported function)
      | _, .error refusal => .error refusal
  | .loop site count maximum induction carried captures body outputs, scope, R =>
      match lookupName scope count, (carried.map (·.2)).mapM (lookupName scope),
          captures.mapM (lookupName scope) with
      | .ok counter, .ok initial, .ok captured =>
          let sorts := initial.filterMap (R.sorts[·]?)
          let base := R.sorts.length
          if counter < inputs ∧ R.sorts[counter]? = some (.data .index) ∧
              sorts.length = initial.length ∧ carried.length = initial.length ∧
              outputs.length = initial.length ∧ custody R.sorts R.current initial ∧
              (sorts.filter (· matches .transcript _)).length ≤ 1 ∧
              captured.all (fun reference => R.sorts[reference]? matches some (.data _)) then
            match readActionList vocabulary validator helpers inputs body
                ((induction, base) :: (carried.map (·.1)).zip (List.range' (base + 1) initial.length) ++
                  captures.zip captured)
                ⟨R.sorts ++ .data .index :: sorts,
                  match transcriptPosition sorts with
                  | some position => base + 1 + position
                  | none => R.current⟩ with
            | .ok (inner, innerPlan, .yielded yielded, R₁) =>
                if yielded.map (R₁.sorts[·]?) = sorts.map some ∧ custody R₁.sorts R₁.current yielded ∧
                    (transcriptPosition sorts = none → R₁.current = R.current) then
                  .ok ([.loop site maximum yielded (counter :: initial) sorts inner],
                    [.loop counter maximum innerPlan],
                    outputs.zip (List.range' base sorts.length) ++ scope,
                    ⟨R.sorts ++ sorts,
                      match transcriptPosition sorts with
                      | some position => base + position
                      | none => R.current⟩)
                else .error (.loop site)
            | .ok (_, _, .returned _, _) => .error (.loop site)
            | .error refusal => .error refusal
          else .error (.loop site)
      | .error refusal, _, _ => .error refusal
      | _, .error refusal, _ => .error refusal
      | _, _, .error refusal => .error refusal
  | .yield _, _, _ => .error (.unsupported "yield-not-final")
  | .ret _, _, _ => .error (.unsupported "return-not-final")
  | .unsupported name, _, _ => .error (.unsupported name)
end

theorem readActionList_eq (vocabulary : Vocabulary) (validator : Validator) (helpers : List String)
    (inputs : Nat) :
    ∀ (actions : List Action) (scope : List (String × Nat)) (R : Reading),
      readActionList vocabulary validator helpers inputs actions scope R =
        readActions vocabulary validator helpers inputs actions scope R
  | [], _, _ => by simp [readActionList, readActions]
  | [.yield _], _, _ => by simp [readActionList, readActions]
  | [.ret _], _, _ => by simp [readActionList, readActions]
  | .yield _ :: _ :: _, _, _ => by simp [readActionList, readAction, readActions]
  | .ret _ :: _ :: _, _, _ => by simp [readActionList, readAction, readActions]
  | .unsupported _ :: _, _, _ => by simp [readActionList, readAction, readActions]
  | .receive site schema peer output type :: rest, scope, R => by
      simp only [readActionList, readAction, readActions]
      cases sort : type.sort with
      | data ty =>
          by_cases admits : vocabulary.admits type
          · simp only [admits, ite_true, readActionList_eq vocabulary validator helpers inputs rest]
            cases readActions vocabulary validator helpers inputs rest ((output, R.sorts.length) :: scope)
                ⟨R.sorts ++ [.data ty], R.current⟩ with
            | ok result => rfl
            | error refusal => rfl
          · simp only [admits, Bool.false_eq_true, ite_false]
      | transcript suite => rfl
      | indices => rfl
  | .call site function arguments outputs :: rest, scope, R => by
      simp only [readActionList, readAction, readActions]
      cases found : validator.function? function with
      | none => cases arguments.mapM (lookupName scope) <;> rfl
      | some callee =>
          cases looked : arguments.mapM (lookupName scope) with
          | error refusal => rfl
          | ok operands =>
              simp only
              split_ifs
              · dsimp only
                rw [readActionList_eq vocabulary validator helpers inputs rest]
                symm
                split <;> rfl
              · rfl
              · cases readBody vocabulary validator callee.body ((callee.inputs.map (·.1)).zip operands) R with
                | error refusal => rfl
                | ok read =>
                    obtain ⟨body, returned, R₁⟩ := read
                    simp only
                    split_ifs
                    · dsimp only
                      rw [readActionList_eq vocabulary validator helpers inputs rest]
                      symm
                      split <;> rfl
                    · rfl
              · rfl
  | .loop site count maximum induction carried captures body outputs :: rest, scope, R => by
      simp only [readActionList, readAction, readActions]
      cases counter : lookupName scope count with
      | error refusal => rfl
      | ok counter =>
          cases initial : (carried.map (·.2)).mapM (lookupName scope) with
          | error refusal => cases captures.mapM (lookupName scope) <;> rfl
          | ok initial =>
              cases captured : captures.mapM (lookupName scope) with
              | error refusal => rfl
              | ok captured =>
                  simp only
                  split_ifs
                  · rw [readActionList_eq vocabulary validator helpers inputs body]
                    symm
                    split
                    · split_ifs
                      · dsimp only
                        rw [readActionList_eq vocabulary validator helpers inputs rest]
                        split <;> rfl
                      · rfl
                    · rfl
                    · rfl
                  · rfl

/-- Whether every declared formal and result of a local function has an
admitted representation. -/
def Function.admitted (vocabulary : Vocabulary) (function : Function) : Bool :=
  function.inputs.all (vocabulary.admits ·.2) && function.results.all vocabulary.admits

/-- Read the validator: distinct function and binding symbols, admitted
representations for every declared type, data inputs followed by the host's
transcript, then its body, which must end in its return. -/
def Validator.read (vocabulary : Vocabulary) (helpers : List String) (validator : Validator) :
    Except Refusal Lowered :=
  let sorts := validator.inputs.map (·.2.sort)
  if ¬ (validator.functions.map (·.symbol)).Nodup then .error (.duplicate "function")
  else if ¬ (validator.bindings.map (·.symbol)).Nodup then .error (.duplicate "binding")
  else if ¬ validator.functions.all (·.admitted vocabulary) then .error .representation
  else if validator.inputs.all (vocabulary.admits ·.2) ∧ validator.results.all vocabulary.admits ∧
      (sorts.getLast? matches some (ValueSort.transcript _)) ∧
      (sorts.dropLast.all fun sort => sort matches ValueSort.data _) then
    match readActionList vocabulary validator helpers (sorts.length - 1) validator.body
        ((validator.inputs.map (·.1)).zip (List.range sorts.length)) ⟨sorts, sorts.length - 1⟩ with
    | .ok (code, plan, .returned returned, _) => .ok ⟨code, returned, plan⟩
    | .ok (_, _, .yielded _, _) => .error (.unsupported "yield")
    | .error refusal => .error refusal
  else .error .entry

/-- The helpers constructed instructions call by name. -/
def Instruction.helpers : List Instruction → List String
  | [] => []
  | ⟨.call helper, _, _, _⟩ :: rest => helper :: Instruction.helpers rest
  | ⟨.loop _ _ _, _, _, body⟩ :: rest => Instruction.helpers body ++ Instruction.helpers rest
  | _ :: rest => Instruction.helpers rest

mutual
/-- `Instruction.helpers` by structural recursion, which the kernel evaluates. -/
def Instruction.helperList : List Instruction → List String
  | [] => []
  | instruction :: rest => Instruction.helpersOf instruction ++ Instruction.helperList rest

/-- The helpers one constructed instruction calls by name. -/
def Instruction.helpersOf : Instruction → List String
  | ⟨.call helper, _, _, _⟩ => [helper]
  | ⟨.loop _ _ _, _, _, body⟩ => Instruction.helperList body
  | _ => []
end

theorem Instruction.helperList_eq :
    ∀ instructions : List Instruction, Instruction.helperList instructions = Instruction.helpers instructions
  | [] => by simp [Instruction.helperList, Instruction.helpers]
  | ⟨operation, operands, results, body⟩ :: rest => by
      cases operation <;>
        simp [Instruction.helperList, Instruction.helpersOf, Instruction.helpers, Instruction.helperList_eq rest,
          Instruction.helperList_eq body]

/-- A computed result that is present is that result. -/
theorem ok_of_isSome {ε α : Type} :
    ∀ (result : Except ε α) (present : result.toOption.isSome = true),
      result = .ok (result.toOption.get present)
  | .ok _, _ => rfl
  | .error _, present => by simp [Except.toOption] at present

/-- Admit the exact native identity, input/output ABI and canonical normalization
of its reading. Even an identical schedule passes the result-schema check. -/
def checkLowering (vocabulary : Vocabulary) (participant : Participant) (validator : Validator) :
    Except Refusal Lowered := do
  let lowered ← validator.read vocabulary (Instruction.helperList participant.instructions)
  unless validator.symbol = participant.symbol do throw (Refusal.different "symbol")
  unless validator.entry = participant.policy.entry do throw (Refusal.different "entry")
  unless validator.role = participant.policy.validator do throw (Refusal.different "role")
  unless validator.inputs.map (·.2.sort) = participant.inputs do throw (Refusal.different "inputs")
  unless validator.results.map (·.sort) = participant.outputs do throw (Refusal.different "outputs")
  let _ ← CanonicalNormalization.check participant.inputs participant.outputs
    participant.instructions participant.returned (Code.instructionList lowered.code) lowered.returned
  pure lowered


/-- Successful admission exposes finite reader, identity, ABI and normalization
facts. It assumes no execution equality or protocol-validity proposition. -/
theorem checkLowering_checks {vocabulary : Vocabulary} {participant : Participant}
    {validator : Validator} {lowered : Lowered}
    (accepted : checkLowering vocabulary participant validator = .ok lowered) :
    validator.read vocabulary (Instruction.helperList participant.instructions) = .ok lowered ∧
      validator.symbol = participant.symbol ∧ validator.entry = participant.policy.entry ∧
      validator.role = participant.policy.validator ∧
      validator.inputs.map (·.2.sort) = participant.inputs ∧
      validator.results.map (·.sort) = participant.outputs ∧
      (CanonicalNormalization.check participant.inputs participant.outputs
        participant.instructions participant.returned
        (Code.instructionList lowered.code) lowered.returned).toOption.isSome = true := by
  unfold checkLowering at accepted
  cases reading : validator.read vocabulary (Instruction.helperList participant.instructions) with
  | error refusal => simp [reading, bind, Except.bind] at accepted
  | ok candidate =>
    simp only [reading, bind, Except.bind] at accepted
    by_cases symbol : validator.symbol = participant.symbol <;>
    by_cases entry : validator.entry = participant.policy.entry <;>
    by_cases role : validator.role = participant.policy.validator <;>
    by_cases inputs : validator.inputs.map (·.2.sort) = participant.inputs <;>
    by_cases outputs : validator.results.map (·.sort) = participant.outputs <;>
    cases normalized : CanonicalNormalization.check participant.inputs participant.outputs
      participant.instructions participant.returned (Code.instructionList candidate.code) candidate.returned <;>
    simp_all [pure, Except.pure, Except.toOption]


end Zkc.Executable
