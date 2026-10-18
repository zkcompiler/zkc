module

public import Zkc.Executable.Execution

@[expose] public section

/-! The lowering rule from a constructed validator to its executable program.

`Validator.read` reads the executable validator's participant body back as
constructed-participant instructions. A local call is read in one of two ways.

* A call of a helper that the constructed validator calls by name is read as
  that helper call. Its body must apply no transcript operation, and its
  meaning is related to the checked helper separately
  (`Zkc.Executable.Prepared`).
* Any other local call is transparent: its formals denote its actual operands
  and its results denote the operands of its return, exactly as the
  constructed-participant export expands helpers. Its body must be straight
  line: installed operations, Boolean literals and generated guards (a
  conditional on a Boolean that yields nothing or stops with reason `reject`),
  ending in its only return.

A participant loop is read as a constructed loop: the loop's frame names its
index, carried values and captures, its body is read once in that frame, and its
yield gives the carried values of the next iteration. A loop that carries the
live transcript must yield it; one that does not cannot reach it. The loop count must be one
of the validator's data inputs, so that the receive types of a run are fixed by
the data inputs (`Plan`). Each installed operation is read through the
vocabulary's meaning; operand sorts, including those of a local call's declared
formals, are checked, transcript operations must consume the live transcript,
and the live transcript passes through a loop only as a carried value. Function
and binding symbols must be distinct and every declared type must have an
admitted representation.

The reading also records where the executable charges instructions (`Code`):
each constructed instruction with the instructions it charges itself, and
separately the charges of transparent calls and their returns, which execute no
constructed instruction. A helper call charges its call and then whatever its
body charges on the actual arguments.

`checkLowering` is the per-compile rule: the executable must read back as
exactly the constructed validator's instructions, returned references, input
and output sorts, symbol, entry and validator role. Its refusals name the first
difference.

`metered` is the ideal meaning of constructed instructions under an instruction
budget, in the continuation style of `Zkc.Construction.idealK`: an instruction
runs, as `Zkc.Construction.idealStep` runs it, only if the instructions charged
so far and its own fit within the budget.
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
  | helper (symbol : String)
  | loop (site : String)
  deriving DecidableEq, Repr

/-- The reading state: the sorts of all references and the live transcript
reference. -/
structure Reading where
  sorts : List ValueSort
  current : Nat
  deriving DecidableEq, Repr

/-- A constructed instruction and where the executable charges instructions.
`charge` is executable work with no constructed instruction (a transparent
call's entry or return); `step` is a constructed instruction with the
instructions it charges itself; `helper` is a helper call, charging its call and
its body's work; `loop` is a constructed loop, charging one instruction to start
and one to end each iteration. -/
inductive Code where
  | charge (count : Nat)
  | step (instruction : Instruction) (charged : Nat)
  | helper (instruction : Instruction)
  | loop (site : String) (maximum : Nat) (yielded operands : List Nat) (results : List ValueSort)
      (body : List Code)
  deriving Repr

/-- The constructed instructions of a reading. -/
def Code.instructions : List Code → List Instruction
  | [] => []
  | .charge _ :: rest => Code.instructions rest
  | .step instruction _ :: rest => instruction :: Code.instructions rest
  | .helper instruction :: rest => instruction :: Code.instructions rest
  | .loop site maximum yielded operands results body :: rest =>
      ⟨.loop site maximum yielded, operands, results, Code.instructions body⟩ :: Code.instructions rest

mutual
/-- `Code.instructions` by structural recursion, which the kernel evaluates. -/
def Code.instructionList : List Code → List Instruction
  | [] => []
  | code :: rest => Code.instructionsOf code ++ Code.instructionList rest

/-- The constructed instructions of one code item. -/
def Code.instructionsOf : Code → List Instruction
  | .charge _ => []
  | .step instruction _ => [instruction]
  | .helper instruction => [instruction]
  | .loop site maximum yielded operands results body =>
      [⟨.loop site maximum yielded, operands, results, Code.instructionList body⟩]
end

theorem Code.instructionList_eq : ∀ code : List Code, Code.instructionList code = Code.instructions code
  | [] => by simp [Code.instructionList, Code.instructions]
  | .charge _ :: rest => by
      simp [Code.instructionList, Code.instructionsOf, Code.instructions, Code.instructionList_eq rest]
  | .step _ _ :: rest => by
      simp [Code.instructionList, Code.instructionsOf, Code.instructions, Code.instructionList_eq rest]
  | .helper _ :: rest => by
      simp [Code.instructionList, Code.instructionsOf, Code.instructions, Code.instructionList_eq rest]
  | .loop _ _ _ _ _ body :: rest => by
      simp [Code.instructionList, Code.instructionsOf, Code.instructions, Code.instructionList_eq body,
        Code.instructionList_eq rest]

/-- The receives of a reading: a receive at a physical type, or a loop whose
count is the data input at position `count`, run at most `maximum` times. -/
inductive Plan where
  | receive (type : PhysicalType)
  | loop (count maximum : Nat) (body : List Plan)
  deriving Repr

mutual
def Plan.decide : (left right : Plan) → Decidable (left = right)
  | .receive type, .receive type' =>
      if same : type = type' then isTrue (by rw [same])
      else isFalse (by intro equal; cases equal; exact same rfl)
  | .loop count maximum body, .loop count' maximum' body' =>
      if same : count = count' ∧ maximum = maximum' then
        match Plan.decideList body body' with
        | isTrue bodies => isTrue (by obtain ⟨rfl, rfl⟩ := same; rw [bodies])
        | isFalse bodies => isFalse (by intro equal; cases equal; exact bodies rfl)
      else isFalse (by intro equal; cases equal; exact same ⟨rfl, rfl⟩)
  | .receive _, .loop _ _ _ => isFalse (by intro equal; cases equal)
  | .loop _ _ _, .receive _ => isFalse (by intro equal; cases equal)

def Plan.decideList : (left right : List Plan) → Decidable (left = right)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by simp)
  | _ :: _, [] => isFalse (by simp)
  | head :: tail, head' :: tail' =>
      match Plan.decide head head', Plan.decideList tail tail' with
      | isTrue heads, isTrue tails => isTrue (by rw [heads, tails])
      | isFalse heads, _ => isFalse (by intro equal; cases equal; exact heads rfl)
      | _, isFalse tails => isFalse (by intro equal; cases equal; exact tails rfl)
end

instance : DecidableEq Plan := Plan.decide

/-- The receive types of a run on the given data inputs, in order. -/
def Plan.types {F G : Type} (data : List (Value F G)) : List Plan → List PhysicalType
  | [] => []
  | .receive type :: rest => type :: Plan.types data rest
  | .loop count maximum body :: rest =>
      (match data[count]? with
        | some (.index bound) =>
            if bound ≤ maximum then (List.replicate bound (Plan.types data body)).flatten else []
        | _ => []) ++ Plan.types data rest

/-- The receive types of a plan without loops, which do not depend on the
data inputs. -/
def Plan.static : List Plan → Option (List PhysicalType)
  | [] => some []
  | .receive type :: rest => (Plan.static rest).map (type :: ·)
  | .loop _ _ _ :: _ => none

theorem Plan.types_static {F G : Type} (data : List (Value F G)) :
    ∀ {plan : List Plan} {types : List PhysicalType}, Plan.static plan = some types →
      Plan.types data plan = types
  | [], types, static => by
      simp only [Plan.static, Option.some.injEq] at static
      subst static
      simp only [Plan.types]
  | .receive type :: rest, types, static => by
      simp only [Plan.static] at static
      cases restStatic : Plan.static rest with
      | none => simp [restStatic] at static
      | some restTypes =>
          simp only [restStatic, Option.map_some, Option.some.injEq] at static
          subst static
          simp only [Plan.types, Plan.types_static data restStatic]
  | .loop _ _ _ :: _, _, static => by simp [Plan.static] at static

/-- The reading of a validator: its constructed instructions with their
charges, the returned references and the receive plan. -/
structure Lowered where
  code : List Code
  returned : List Nat
  plan : List Plan
  deriving Repr


/-- The instructions a reading without loops and helper calls charges before
its return. -/
def Code.static : List Code → Option Nat
  | [] => some 0
  | .charge count :: rest => (Code.static rest).map (count + ·)
  | .step _ charged :: rest => (Code.static rest).map (charged + ·)
  | _ :: _ => none

/-- The instructions a complete run of a reading without loops and helper
calls charges, its return included. -/
def Lowered.total? (lowered : Lowered) : Option Nat := (Code.static lowered.code).map (· + 1)

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

/-- The first position at which two instruction lists differ. -/
def firstDifference : List Instruction → List Instruction → Nat
  | first :: rest, other :: others => if first = other then firstDifference rest others + 1 else 0
  | _, _ => 0

/-- A computed result that is present is that result. -/
theorem ok_of_isSome {ε α : Type} :
    ∀ (result : Except ε α) (present : result.toOption.isSome = true),
      result = .ok (result.toOption.get present)
  | .ok _, _ => rfl
  | .error _, present => by simp [Except.toOption] at present

/-- The per-compile lowering rule: the executable validator reads back as
exactly the constructed validator. -/
def checkLowering (vocabulary : Vocabulary) (participant : Participant) (validator : Validator) :
    Except Refusal Lowered := do
  let lowered ← validator.read vocabulary (Instruction.helperList participant.instructions)
  unless validator.symbol = participant.symbol do throw (Refusal.different "symbol")
  unless validator.entry = participant.policy.entry do throw (Refusal.different "entry")
  unless validator.role = participant.policy.validator do throw (Refusal.different "role")
  unless validator.inputs.map (·.2.sort) = participant.inputs do throw (Refusal.different "inputs")
  unless validator.results.map (·.sort) = participant.outputs do throw (Refusal.different "outputs")
  unless Code.instructionList lowered.code = participant.instructions do
    throw (Refusal.instruction (firstDifference (Code.instructionList lowered.code) participant.instructions))
  unless lowered.returned = participant.returned do throw (Refusal.different "returned")
  pure lowered

section Metered
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m]
variable (context : Context) (challenge : History F G → m F)
  (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
  (cost : String → List (Value F G) → Nat) (budget : Nat)

/-- Iterate a metered loop body over the given induction values: each iteration
then charges one instruction to yield its carried values. -/
def meteredIterate {R : Type}
    (body : List (Value F G) → Proof F G → Nat →
      (List (Value F G) → Proof F G → Nat → m (PIR.Outcome R × Proof F G)) →
        m (PIR.Outcome R × Proof F G))
    (env : List (Value F G)) (yielded : List Nat) :
    List Nat → List (Value F G) → Proof F G → Nat →
      (List (Value F G) → Proof F G → Nat → m (PIR.Outcome R × Proof F G)) →
        m (PIR.Outcome R × Proof F G)
  | [], carried, proof, used, next => next carried proof used
  | index :: rest, carried, proof, used, next =>
      body (env ++ .index index :: carried) proof used fun final unread used' =>
        if used' + 1 ≤ budget then
          match read final yielded with
          | some carried' => meteredIterate body env yielded rest carried' unread (used' + 1) next
          | none => pure (.stopped .refused, unread)
        else pure (.stopped .exhausted, unread)

mutual
/-- The ideal meaning of a reading under an instruction budget, in continuation
style: `used` counts the instructions charged so far. -/
def meteredK {R : Type} : List Code → List (Value F G) → Proof F G → Nat →
    (List (Value F G) → Proof F G → Nat → m (PIR.Outcome R × Proof F G)) →
      m (PIR.Outcome R × Proof F G)
  | [], env, proof, used, next => next env proof used
  | code :: rest, env, proof, used, next =>
      meteredStep code env proof used fun env' unread used' => meteredK rest env' unread used' next

def meteredStep {R : Type} : Code → List (Value F G) → Proof F G → Nat →
    (List (Value F G) → Proof F G → Nat → m (PIR.Outcome R × Proof F G)) →
      m (PIR.Outcome R × Proof F G)
  | .charge count, env, proof, used, next =>
      if used + count ≤ budget then next env proof (used + count)
      else pure (.stopped .exhausted, proof)
  | .step instruction charged, env, proof, used, next =>
      if used + charged ≤ budget then
        idealStep context challenge table instruction env proof fun env' unread =>
          next env' unread (used + charged)
      else pure (.stopped .exhausted, proof)
  | .helper instruction, env, proof, used, next =>
      if used + 1 ≤ budget then
        match instruction.operation, read env instruction.operands with
        | .call helper, some arguments =>
            if used + 1 + cost helper arguments ≤ budget then
              idealStep context challenge table instruction env proof fun env' unread =>
                next env' unread (used + 1 + cost helper arguments)
            else pure (.stopped .exhausted, proof)
        | _, _ => pure (.stopped .refused, proof)
      else pure (.stopped .exhausted, proof)
  | .loop _ maximum yielded operands _ body, env, proof, used, next =>
      match operands with
      | count :: initial =>
          match indexAt env count, read env initial with
          | some bound, some carried =>
              if bound ≤ maximum then
                if used + 1 ≤ budget then
                  meteredIterate budget (fun start unread used' continuation =>
                      meteredK body start unread used' continuation) env yielded
                    (List.range bound) carried proof (used + 1) fun final unread used' =>
                      next (env ++ final) unread used'
                else pure (.stopped .exhausted, proof)
              else pure (.stopped .refused, proof)
          | _, _ => pure (.stopped .refused, proof)
      | [] => pure (.stopped .refused, proof)
end

/-- The metered meaning of a reading: its instructions, then the final return,
which charges one instruction. -/
def metered (lowered : Lowered) (env : List (Value F G)) (proof : Proof F G) :
    m (PIR.Outcome (List (Value F G)) × Proof F G) :=
  meteredK context challenge table cost budget lowered.code env proof 0 fun final unread used =>
    pure (if used + 1 ≤ budget then finish lowered.returned final else .stopped .exhausted, unread)

end Metered

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
