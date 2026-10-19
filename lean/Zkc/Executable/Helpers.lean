module

public import Zkc.Executable.Lowering
public import Zkc.Construction.Structured

@[expose] public section

/-! The helper rule: a per-compile check that the executable body of a helper
the constructed validator calls by name implements the checked helper of the
admitted original.

`checkHelper` reads the local function of the helper's name against the typed
body of the checked definition of the same name, one structured operation at a
time, through a closed table of recipes. Each recipe names the executable steps
that implement one structured form:

* a site mark has no step;
* an operation without nested regions is one installed operation whose meaning
  is the structured operation's (`implements`): the same primitive, an index
  constant below the index limit, a carrier calculation, or the unchecked index
  equality when both operands are known to be below the index limit;
* a Boolean constant is a constant step;
* an invocation of a checked helper is that helper's body, inlined under the
  names of its actual operands, its returned names standing for its results;
* a guard is a conditional that yields nothing on true and stops with reason
  `reject` on false;
* a branch is a conditional on the same condition and captures, each region
  read as the corresponding callback, ending in a yield of the callback's
  returned names or in a stop;
* a stop is an explicit stop for the same reason, and the body's return is the
  function's return of the returned names.

Every name an executable step binds must be fresh, so that a name keeps the
value it denotes. Index names produced by checked index primitives and by index
constants below the limit are tracked as bounded. Operations outside the table
(loops, folds, maps, binds and the remaining calculations) are refused with
their names: such a helper keeps a proof of its own.

`Zkc.Executable.HelperSoundness` proves that an accepted helper is prepared
(`checkHelpers_sound`).
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction Zkc.Source Zkc.Source.Structured

/-- Why the helper rule refuses a helper body. -/
inductive HelperRefusal where
  /-- No local function or no checked definition carries this name. -/
  | missing (name : String)
  /-- The local function's formals or results are not those of the checked
  helper, or its formals repeat a name. -/
  | signature (name : String)
  /-- The structured operation has no recipe in the closed table. -/
  | recipe (operation : String)
  /-- The executable step does not implement the structured operation. -/
  | step (site : String)
  /-- An operand of the structured operation has no name. -/
  | operand
  /-- An executable step binds a name that is already bound, or binds a name
  twice. -/
  | rebound (site : String)
  /-- An index operand is not known to be below the index limit. -/
  | unbounded (site : String)
  /-- A body or region ends otherwise than its structured counterpart. -/
  | ending
  /-- The walk exceeded its depth. -/
  | depth
  deriving DecidableEq, Repr

/-- The kind of a structured operation, for refusals. -/
def operationKind : Structured.Op → String
  | .exec _ => "primitive"
  | .indexConstant _ => "index-constant"
  | .indexEqual => "index-equal"
  | .fieldConstant .. => "field-constant"
  | .fieldAdd _ | .fieldSubtract _ | .fieldMultiply _ | .fieldEqual _ => "field"
  | .groupIdentity _ | .groupAdd _ | .groupScale .. | .groupEqual _ => "group"
  | .booleanConstant _ => "boolean-constant"
  | .booleanAnd | .booleanOr | .booleanXor | .booleanEqual | .booleanNotEqual => "boolean"
  | .select _ => "select"
  | .boundedAt _ => "bounded-at"
  | .invoke _ => "invoke"
  | .fold _ => "fold"
  | .map _ => "map"
  | .branch .. => "branch"
  | .loop .. => "loop"
  | .loopCondition .. => "loop-condition"
  | .guard => "guard"
  | .mark _ => "mark"

/-- Whether an installed operation implements a structured operation without
nested regions: on arguments that encode the structured arguments, it returns
the encoded structured results or stops for the same reason. A carrier
calculation must take data arguments only. -/
def implements : Structured.Op → Resolved → Bool
  | .exec (.indexConstant value), .calculate (.indexConstant value') =>
      value == value' && decide (value < indexLimit)
  | .exec .indexEqual, .calculate .indexEqual => true
  | .exec (.fieldEqual domain), .calculate (.fieldEqual domain') => domain == domain'
  | .exec primitive, .compute (.primitive primitive') => primitive == primitive'
  | operation, .calculate calculation =>
      match Calculation.ofOp? operation with
      | some calculation' => calculation' == calculation && calculation.op.arguments.all dataType
      | none => false
  | _, _ => false

/-- Whether the recipe of `implements` needs operands known to be below the
index limit: the checked index equality read as the unchecked one. -/
def needsBounded : Structured.Op → Resolved → Bool
  | .exec .indexEqual, .calculate .indexEqual => true
  | _, _ => false

/-- Whether every index a structured operation returns is below the index limit:
checked primitives check or bound their results, and an index constant is
bounded when it is. Other results are not tracked. -/
def resultsBounded : Structured.Op → Bool
  | .exec _ => true
  | .indexConstant value => decide (value < indexLimit)
  | _ => false

/-- Whether a structured operation without nested regions has a recipe: a
carrier calculation or a primitive. -/
def hasRecipe (op : Structured.Op) : Bool := (Calculation.ofOp? op).isSome || (op matches .exec _)

/-- The names a walk has bound so far, and those of its index names whose value
is known to be below the index limit. -/
structure Scope where
  used : List String
  bounded : List String
  deriving Repr

/-- Bind fresh, distinct names; they are bounded if `bounded` holds. -/
def Scope.bind (scope : Scope) (outputs : List String) (bounded : Bool) : Option Scope :=
  if outputs.Nodup ∧ ∀ output ∈ outputs, output ∉ scope.used then
    some ⟨outputs ++ scope.used, if bounded then outputs ++ scope.bounded else scope.bounded⟩
  else none

/-- What a walked region leaves: the executable steps after it, with the names
of its returned values and the walk's scope, or a stop that ends it. -/
inductive Walked where
  | returned (rest : List Step) (names : List String) (scope : Scope)
  | stopped
  deriving Repr

/-- The names of structured operands. -/
def operandNames (names : List String) {Γ args : List Ty} (operands : Operands Γ args) :
    Option (List String) :=
  (Operands.indices operands).mapM (names[·]?)

/-- Whether a walked region ends as a conditional's region must: in a yield of
its returned names, or in a stop. -/
def regionEnds : Walked → Bool
  | .returned [.yield values] names _ => values == names
  | .returned _ _ _ => false
  | .stopped => true

/-- The condition of a generated guard: a conditional on a Boolean that yields
nothing when it holds and stops with reason `reject` otherwise. -/
def guardCondition? : Step → Option String
  | .cond _ condition [] [.yield []] [.stop _ "reject"] [] => some condition
  | _ => none

/-- Walk one structured operation without nested regions: one installed
operation that implements it, or a constant step for a Boolean constant. Returns
the bound names, the scope after them and the remaining steps. -/
def walkOperation (vocabulary : Vocabulary) (validator : Validator) (op : Structured.Op)
    (inputs : List String) (scope : Scope) (steps : List Step) :
    Except HelperRefusal (List String × Scope × List Step) :=
  if hasRecipe op then
    match steps with
    | .operation site binding parameters inputs' outputs :: rest =>
        match validator.binding? binding >>= (vocabulary.resolve · parameters) with
        | some resolved =>
            if implements op resolved ∧ inputs' = inputs ∧ outputs.length = op.results.length then
              if needsBounded op resolved → ∀ input ∈ inputs, input ∈ scope.bounded then
                match scope.bind outputs (resultsBounded op) with
                | some scope' => .ok (outputs, scope', rest)
                | none => .error (.rebound site)
              else .error (.unbounded site)
            else .error (.step site)
        | none => .error (.step site)
    | .constant site output value :: rest =>
        match op with
        | .booleanConstant value' =>
            if value = value' then
              match scope.bind [output] false with
              | some scope' => .ok ([output], scope', rest)
              | none => .error (.rebound site)
            else .error (.step site)
        | _ => .error (.step site)
    | step :: _ => .error (.step step.name)
    | [] => .error .ending
  else .error (.recipe (operationKind op))

/-- The position of the checked definition of a helper among those available
to a body. -/
def findDefinition (available : List CheckedDefinition) (helper : Helper) : Option Nat :=
  available.findIdx? (·.helper == helper)

/-- The values after the first. -/
def valuesTail {Value : Ty → Type} {ty : Ty} {tys : List Ty} : Values Value (ty :: tys) → Values Value tys
  | .cons _ rest => rest

/-- The two callbacks of a branch. -/
def branchRegions {captures outputs : List Ty} :
    Regions dialect [(captures, outputs), (captures, outputs)] →
      Region dialect captures outputs × Region dialect captures outputs
  | .cons yes (.cons no .nil) => (yes, no)

/-- Walk a structured region against executable steps. `available` are the
checked definitions the region may invoke, in declaration order; `names` name
the region's context, its first entry the most recent. -/
def walkRegion (vocabulary : Vocabulary) (validator : Validator) :
    Nat → List CheckedDefinition → {Γ out : List Ty} → List String → Scope → Region dialect Γ out →
      List Step → Except HelperRefusal Walked
  | 0, _, _, _, _, _, _, _ => .error .depth
  | fuel + 1, available, _, _, names, scope, region, steps =>
      match region with
      | .ret values =>
          match operandNames names values with
          | some returned => .ok (.returned steps returned scope)
          | none => .error .operand
      | .stop reason =>
          match steps with
          | .stop site text :: _ => if stopReason? text = some reason then .ok .stopped else .error (.step site)
          | _ => .error .ending
      | .bind _ _ => .error (.recipe "bind")
      | .letOp op arguments bodies next =>
          match operandNames names arguments with
          | none => .error .operand
          | some inputs =>
              match op, bodies with
              | .mark _, _ => walkRegion vocabulary validator fuel available names scope next steps
              | .invoke helper, _ =>
                  match findDefinition available helper with
                  | some index =>
                      match available[index]? with
                      | some definition =>
                          match walkRegion vocabulary validator fuel (available.take index) inputs scope
                              definition.body steps with
                          | .ok (.returned rest returned scope') =>
                              if returned.length = helper.outputs.length then
                                walkRegion vocabulary validator fuel available (returned ++ names)
                                  ⟨scope'.used ++ scope.used, scope'.bounded⟩ next rest
                              else .error .ending
                          | .ok .stopped => .ok .stopped
                          | .error refusal => .error refusal
                      | none => .error (.missing helper.name)
                  | none => .error (.missing helper.name)
              | .guard, _ =>
                  match steps with
                  | step :: rest =>
                      match guardCondition? step with
                      | some condition =>
                          if inputs = [condition] then walkRegion vocabulary validator fuel available names scope next rest
                          else .error (.step step.name)
                      | none => .error (.step step.name)
                  | [] => .error .ending
              | .branch _ outputs, bodies =>
                  match steps with
                  | .cond site condition captures yesSteps noSteps bound :: rest =>
                      if inputs = condition :: captures ∧ bound.length = outputs.length then
                        match walkRegion vocabulary validator fuel available captures scope (branchRegions bodies).1 yesSteps,
                            walkRegion vocabulary validator fuel available captures scope (branchRegions bodies).2 noSteps with
                        | .ok yesWalked, .ok noWalked =>
                            if regionEnds yesWalked ∧ regionEnds noWalked then
                              match scope.bind bound false with
                              | some scope' => walkRegion vocabulary validator fuel available (bound ++ names) scope' next rest
                              | none => .error (.rebound site)
                            else .error .ending
                        | .error refusal, _ => .error refusal
                        | _, .error refusal => .error refusal
                      else .error (.step site)
                  | step :: _ => .error (.step step.name)
                  | [] => .error .ending
              | op, _ =>
                  (walkOperation vocabulary validator op inputs scope steps).bind fun walked =>
                    walkRegion vocabulary validator fuel available (walked.1 ++ names) walked.2.1 next walked.2.2

/-- The walk's depth: nested regions and inlined helpers. -/
def helperFuel : Nat := 1048576

/-- The helper rule for one helper: the local function of the name implements
the checked definition of the same name among `definitions`. -/
def checkHelper (vocabulary : Vocabulary) (validator : Validator) (definitions : List CheckedDefinition)
    (name : String) : Except HelperRefusal Unit :=
  match validator.function? name, definitions.findIdx? (·.name == name) with
  | some function, some index =>
      match definitions[index]? with
      | some definition =>
          let formals := function.inputs.map (·.1)
          if function.inputs.map (·.2.sort) = definition.inputs.map .data ∧
              function.results.map (·.sort) = definition.outputs.map .data ∧ formals.Nodup ∧
              definition.inputs.all dataType then
            match walkRegion vocabulary validator helperFuel (definitions.take index) formals ⟨formals, []⟩
                definition.body function.body with
            | .ok (.returned [.ret values] returned _) =>
                if values = returned then .ok () else .error .ending
            | .ok (.returned _ _ _) => .error .ending
            | .ok .stopped => .ok ()
            | .error refusal => .error refusal
          else .error (.signature name)
      | none => .error (.missing name)
  | _, _ => .error (.missing name)

/-- The helper rule for the helpers named: each is implemented by its local
function, against the admitted program's checked definitions. -/
def checkHelpers (vocabulary : Vocabulary) (validator : Validator) (program : Structured.Program) :
    List String → Except HelperRefusal Unit
  | [] => .ok ()
  | name :: rest =>
      match checkHelper vocabulary validator program.payload.definitions name with
      | .ok () => checkHelpers vocabulary validator program rest
      | .error refusal => .error refusal

end Zkc.Executable
