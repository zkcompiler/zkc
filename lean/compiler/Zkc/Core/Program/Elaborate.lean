module

public import Zkc.Core.Program.Typed
public import Zkc.Core.Program.Problem

@[expose] public section

/-!
Elaboration: the typed term of a region by names, through the rules of its dialect.

The names in scope are a list aligned with the context, the innermost first; a name stands for
its latest binding. A region of an instruction sees the names around it, with its inputs bound
in front. A region is elaborated in a context to its result types and its term: its
instructions in order, then its exit. The rules of a dialect give its operations from what is
written and the types of the operands, read who performs, and decide the conditions that a form
of control asks of who performs it and of the types of its subject and of what it gives.

Every function here is defined by structural recursion and every decision is a `Decidable`
instance that reduces, so that elaboration runs in the kernel.
-/

namespace Zkc.Core

/-- The rules of a dialect, by which its regions by names are elaborated and its terms are
printed. `Raw` is what is written for an operation, `Who` what is written for who performs. -/
structure Rules (D : Dialect) (Raw Who : Type) where
  sameTy : DecidableEq D.Ty
  /-- The operation that is written, on operands of the types given, with its result types. -/
  op : Raw → (operands : List D.Ty) →
    Except (Problem D.Ty Raw) ((res : List D.Ty) × D.Op operands res)
  who : Who → Except (Problem D.Ty Raw) D.Who
  condition : ∀ w t, Decidable (D.Condition w t)
  /-- The payloads of the alternatives of a variant that `w` may choose on. -/
  alternatives : ∀ w t, Option ((payloads : List D.Ty) ×' D.Alternatives w t payloads)
  count : ∀ w t, Decidable (D.Count w t)
  gives : ∀ w a, Decidable (D.Gives w a)
  attempt : ∀ w, Decidable (D.Attempt w)
  /-- What is written for an operation, and for who performs. -/
  printOp : ∀ {ins res : List D.Ty}, D.Op ins res → Raw
  printWho : D.Who → Who

/-- The equality of lists of types of a dialect. -/
def Rules.sameTys {D : Dialect} {Raw Who : Type} (rules : Rules D Raw Who) :
    DecidableEq (List D.Ty) :=
  @instDecidableEqList D.Ty rules.sameTy

/-- Whether a property holds of every item of a list. -/
def decideAll {α : Type} (P : α → Prop) (dec : ∀ a, Decidable (P a)) :
    (items : List α) → Decidable (∀ a, a ∈ items → P a)
  | [] => isTrue fun _ h => nomatch h
  | a :: rest =>
      match dec a, decideAll P dec rest with
      | isTrue first, isTrue others =>
          isTrue fun b hb => by
            cases hb with
            | head => exact first
            | tail _ hb => exact others b hb
      | isFalse first, _ => isFalse fun all => first (all a (.head _))
      | _, isFalse others => isFalse fun all => others fun b hb => all b (.tail _ hb)

/-! ## Names in scope -/

/-- The latest binding of a name, as a variable of the context with its type. -/
def lookup {T : Type} : (Γ : List T) → List Name → Name → Option ((t : T) × Var Γ t)
  | [], _, _ => none
  | _ :: _, [], _ => none
  | t :: Γ, n :: names, name =>
      if n = name then some ⟨t, .head⟩
      else (lookup Γ names name).map fun found => ⟨found.1, .tail found.2⟩

/-- The latest bindings of names; the first name that is not in scope otherwise. -/
def lookupAll {T : Type} (Γ : List T) (names : List Name) :
    List Name → Except Name ((items : List T) × HList (Var Γ) items)
  | [] => .ok ⟨[], .nil⟩
  | name :: rest =>
      match lookup Γ names name with
      | none => .error name
      | some ⟨t, x⟩ =>
          match lookupAll Γ names rest with
          | .error missing => .error missing
          | .ok ⟨items, xs⟩ => .ok ⟨t :: items, .cons x xs⟩

/-- A name that is not in scope. -/
def scopeProblem {T Raw : Type} (blocks : List (Key × Nat)) (key : Option Key) (name : Name) :
    Problem T Raw :=
  { rule := .scope, blocks := blocks, instruction := key, detail := .name name }

/-- The values that an instruction names. -/
def scope {T Raw : Type} (Γ : List T) (names : List Name) (blocks : List (Key × Nat))
    (key : Option Key) (operands : List Name) :
    Except (Problem T Raw) ((items : List T) × HList (Var Γ) items) :=
  match lookupAll Γ names operands with
  | .ok found => .ok found
  | .error name => .error (scopeProblem blocks key name)

/-- The value that an instruction names. -/
def scopeOne {T Raw : Type} (Γ : List T) (names : List Name) (blocks : List (Key × Nat))
    (key : Key) (name : Name) : Except (Problem T Raw) ((t : T) × Var Γ t) :=
  match lookup Γ names name with
  | some found => .ok found
  | none => .error (scopeProblem blocks (some key) name)

/-! ## Regions -/

/-- A list that starts with `pre`, as `pre` and what follows it. -/
def splitPrefix {T : Type} [DecidableEq T] :
    (pre items : List T) → Option ((rest : List T) ×' items = pre ++ rest)
  | [], items => some ⟨items, rfl⟩
  | a :: pre, b :: items =>
      if same : b = a then
        (splitPrefix pre items).map fun found => ⟨found.1, by rw [same]; exact congrArg (List.cons a) found.2⟩
      else none
  | _ :: _, [] => none

section
variable {D : Dialect} {Raw Who : Type}

/-- How often a loop that `w` perform runs. -/
def elabTimes (rules : Rules D Raw Who) (w : D.Who) (Γ : List D.Ty) (names : List Name)
    (blocks : List (Key × Nat)) (key : Key) : Repeat → Except (Problem D.Ty Raw) (Times D w Γ)
  | .fixed n => .ok (.fixed n)
  | .count name =>
      match scopeOne Γ names blocks key name with
      | .error problem => .error problem
      | .ok ⟨t, count⟩ =>
          match rules.count w t with
          | isTrue ok => .ok (.value count ok)
          | isFalse _ => .error (problemAt blocks key .count (.type t))

mutual
  /-- The term of a list of instructions and an exit, in a context with the names in scope,
  with the types of what it gives. -/
  def elabBody (rules : Rules D Raw Who) (Γ : List D.Ty) (names : List Name)
      (blocks : List (Key × Nat)) :
      List (Instruction Raw Who) → List Name →
        Except (Problem D.Ty Raw) ((outs : List D.Ty) × Term D Γ outs)
    | [], exit =>
        match scope Γ names blocks none exit with
        | .error problem => .error problem
        | .ok ⟨outs, xs⟩ => .ok ⟨outs, .ret xs⟩
    | .op key results raw operands :: rest, exit =>
        match scope Γ names blocks (some key) operands with
        | .error problem => .error problem
        | .ok ⟨ins, args⟩ =>
            match rules.op raw ins with
            | .error problem => .error (problem.at blocks key)
            | .ok ⟨res, o⟩ =>
                if results.length = res.length then
                  match elabBody rules (res ++ Γ) (results ++ names) blocks rest exit with
                  | .error problem => .error problem
                  | .ok ⟨outs, t⟩ => .ok ⟨outs, .op key o args t⟩
                else .error (problemAt blocks key .results (.number res.length results.length))
    | .guard key who condition why :: rest, exit =>
        match rules.who who with
        | .error problem => .error (problem.at blocks key)
        | .ok w =>
            match scopeOne Γ names blocks key condition with
            | .error problem => .error problem
            | .ok ⟨t, c⟩ =>
                match rules.condition w t with
                | isFalse _ => .error (problemAt blocks key .condition (.type t))
                | isTrue ok =>
                    match elabBody rules Γ names blocks rest exit with
                    | .error problem => .error problem
                    | .ok ⟨outs, t⟩ => .ok ⟨outs, .guard key w c ok why t⟩
    | .choose key who condition results onTrue onFalse :: rest, exit =>
        match rules.who who with
        | .error problem => .error (problem.at blocks key)
        | .ok w =>
            match scopeOne Γ names blocks key condition with
            | .error problem => .error problem
            | .ok ⟨t, c⟩ =>
                match rules.condition w t with
                | isFalse _ => .error (problemAt blocks key .condition (.type t))
                | isTrue ok =>
                    match elabRegion rules Γ names blocks key [] onTrue with
                    | .error problem => .error problem
                    | .ok ⟨mid, yes⟩ =>
                        match elabRegion rules Γ names blocks key [] onFalse with
                        | .error problem => .error problem
                        | .ok ⟨mid', no⟩ =>
                            match rules.sameTys mid' mid with
                            | isFalse _ => .error (problemAt blocks key .regions (.types mid mid'))
                            | isTrue same =>
                                match decideAll (D.Gives w) (rules.gives w) mid with
                                | isFalse _ => .error (problemAt blocks key .gives (.given mid))
                                | isTrue gives =>
                                    if results.length = mid.length then
                                      match elabBody rules (mid ++ Γ) (results ++ names) blocks
                                          rest exit with
                                      | .error problem => .error problem
                                      | .ok ⟨outs, t⟩ =>
                                          .ok ⟨outs, .choose key w c ok gives yes
                                            (cast (congrArg (Term D Γ) same) no) t⟩
                                    else .error (problemAt blocks key .results
                                      (.number mid.length results.length))
    | .cases key who subject results arms :: rest, exit =>
        match rules.who who with
        | .error problem => .error (problem.at blocks key)
        | .ok w =>
            match scopeOne Γ names blocks key subject with
            | .error problem => .error problem
            | .ok ⟨t, x⟩ =>
                match rules.alternatives w t with
                | none => .error (problemAt blocks key .variant (.type t))
                | some ⟨payloads, ok⟩ =>
                    if arms.length = payloads.length then
                      match elabCases rules Γ names blocks key payloads arms with
                      | .error problem => .error problem
                      | .ok ⟨mid, elaborated⟩ =>
                          match decideAll (D.Gives w) (rules.gives w) mid with
                          | isFalse _ => .error (problemAt blocks key .gives (.given mid))
                          | isTrue gives =>
                              if results.length = mid.length then
                                match elabBody rules (mid ++ Γ) (results ++ names) blocks rest
                                    exit with
                                | .error problem => .error problem
                                | .ok ⟨outs, t⟩ => .ok ⟨outs, .cases key w x ok gives elaborated t⟩
                              else .error (problemAt blocks key .results
                                (.number mid.length results.length))
                    else .error (problemAt blocks key .arms (.number payloads.length arms.length))
    | .loop key who times carried results body :: rest, exit =>
        match rules.who who with
        | .error problem => .error (problem.at blocks key)
        | .ok w =>
            match scope Γ names blocks (some key) carried with
            | .error problem => .error problem
            | .ok ⟨carried, init⟩ =>
                match elabTimes rules w Γ names blocks key times with
                | .error problem => .error problem
                | .ok times =>
                    match elabRegion rules Γ names blocks key (D.index w :: carried) body with
                    | .error problem => .error problem
                    | .ok ⟨outs, b⟩ =>
                        match @splitPrefix _ rules.sameTy carried outs with
                        | none => .error (problemAt blocks key .carried (.types carried outs))
                        | some ⟨each, split⟩ =>
                            match decideAll (D.Gives w) (rules.gives w) (carried ++ each) with
                            | isFalse _ => .error (problemAt blocks key .gives
                                (.given (carried ++ each)))
                            | isTrue gives =>
                                if results.length =
                                    (carried ++ each.map (D.collected times.size)).length then
                                  match elabBody rules
                                      ((carried ++ each.map (D.collected times.size)) ++ Γ)
                                      (results ++ names) blocks rest exit with
                                  | .error problem => .error problem
                                  | .ok ⟨outs, t⟩ =>
                                      .ok ⟨outs, .loop key w times gives init
                                        (cast (congrArg (Term D (D.index w :: (carried ++ Γ))) split) b)
                                        t⟩
                                else .error (problemAt blocks key .results
                                  (.number (carried ++ each.map (D.collected times.size)).length
                                    results.length))
    | .block key number results body :: rest, exit =>
        match elabRegion rules Γ names (blocks ++ [(key, number)]) key [] body with
        | .error problem => .error problem
        | .ok ⟨mid, b⟩ =>
            if results.length = mid.length then
              match elabBody rules (mid ++ Γ) (results ++ names) blocks rest exit with
              | .error problem => .error problem
              | .ok ⟨outs, t⟩ => .ok ⟨outs, .block key number b t⟩
            else .error (problemAt blocks key .results (.number mid.length results.length))
    | .attempt key who results body :: rest, exit =>
        match rules.who who with
        | .error problem => .error (problem.at blocks key)
        | .ok w =>
            match rules.attempt w with
            | isFalse _ => .error (problemAt blocks key .attempt .nothing)
            | isTrue owns =>
                match elabRegion rules Γ names blocks key [D.index w] body with
                | .error problem => .error problem
                | .ok ⟨mid, b⟩ =>
                    if results.length = mid.length then
                      match elabBody rules (mid ++ Γ) (results ++ names) blocks rest exit with
                      | .error problem => .error problem
                      | .ok ⟨outs, t⟩ => .ok ⟨outs, .attempt key w owns b t⟩
                    else .error (problemAt blocks key .results (.number mid.length results.length))
  /-- The term of a region of the instruction with the key, whose inputs have the types
  `ins`. -/
  def elabRegion (rules : Rules D Raw Who) (Γ : List D.Ty) (names : List Name)
      (blocks : List (Key × Nat)) (key : Key) (ins : List D.Ty) :
      Region Raw Who → Except (Problem D.Ty Raw) ((outs : List D.Ty) × Term D (ins ++ Γ) outs)
    | .mk inputs body exit =>
        if inputs.length = ins.length then
          elabBody rules (ins ++ Γ) (inputs ++ names) blocks body exit
        else .error (problemAt blocks key .inputs (.number ins.length inputs.length))
  /-- The arms of a case analysis, one per alternative, each with the payload as its input:
  the first arm says what they give, and a case analysis without arms gives nothing. -/
  def elabCases (rules : Rules D Raw Who) (Γ : List D.Ty) (names : List Name)
      (blocks : List (Key × Nat)) (key : Key) :
      (payloads : List D.Ty) → List (Region Raw Who) →
        Except (Problem D.Ty Raw) ((mid : List D.Ty) × Arms D Γ mid payloads)
    | [], [] => .ok ⟨[], .nil⟩
    | payload :: payloads, arm :: arms =>
        match elabRegion rules Γ names blocks key [payload] arm with
        | .error problem => .error problem
        | .ok ⟨mid, first⟩ =>
            match elabArms rules Γ names blocks key mid payloads arms with
            | .error problem => .error problem
            | .ok others => .ok ⟨mid, .cons first others⟩
    | payloads, arms => .error (problemAt blocks key .arms (.number payloads.length arms.length))
  /-- The other arms of a case analysis, each giving the types `mid`. -/
  def elabArms (rules : Rules D Raw Who) (Γ : List D.Ty) (names : List Name)
      (blocks : List (Key × Nat)) (key : Key) (mid : List D.Ty) :
      (payloads : List D.Ty) → List (Region Raw Who) →
        Except (Problem D.Ty Raw) (Arms D Γ mid payloads)
    | [], [] => .ok .nil
    | payload :: payloads, arm :: arms =>
        match elabRegion rules Γ names blocks key [payload] arm with
        | .error problem => .error problem
        | .ok ⟨mid', a⟩ =>
            match rules.sameTys mid' mid with
            | isFalse _ => .error (problemAt blocks key .armTypes (.types mid mid'))
            | isTrue same =>
                match elabArms rules Γ names blocks key mid payloads arms with
                | .error problem => .error problem
                | .ok others => .ok (.cons (cast (congrArg (Term D (payload :: Γ)) same) a) others)
    | payloads, arms => .error (problemAt blocks key .arms (.number payloads.length arms.length))
end

/-- Whether the instructions of a body have their own addresses. -/
instance Term.decideDistinct {Γ outs : List D.Ty} (t : Term D Γ outs) : Decidable t.Distinct :=
  inferInstanceAs (Decidable (_ = true))

/-- Whether every value of a linear type is used once in a body. -/
def Term.decideUsedOnce (linear : D.Ty → Bool) {Γ outs : List D.Ty} (t : Term D Γ outs) :
    Decidable (t.UsedOnce linear) :=
  match found : t.uses linear with
  | some counts =>
      if once : boundOnce linear Γ counts = true then isTrue ⟨counts, found, once⟩
      else isFalse fun ⟨other, uses, otherOnce⟩ => by
        rw [found] at uses
        cases uses
        exact once otherOnce
  | none => isFalse fun ⟨_, uses, _⟩ => by
      rw [found] at uses
      cases uses

end

end Zkc.Core
