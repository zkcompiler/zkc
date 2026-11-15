module

public import Zkc.Core.Program.Typed
public import Zkc.Core.Program.Refusal

@[expose] public section

/-!
Elaboration: the typed term of a region by names, through the rules of its dialect.

Elaboration takes the key of the definition that it elaborates and makes each refusal at its
place: the blocks around the instruction and its key; for the exit of a region, the instruction
whose region it is; for the exit of the body, the definition. The rules of a dialect know no
place: they answer a finding.

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
    Except (Finding D.Ty Raw) ((res : List D.Ty) × D.Op operands res)
  who : Who → Except (Finding D.Ty Raw) D.Who
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

/-- The latest binding of a name, as a variable of the context with its type. Each step
compares two naturals and builds one step of the variable. -/
def lookup {T : Type} : (Γ : List T) → List Name → Name → Option ((t : T) × Var Γ t)
  | [], _, _ => none
  | _ :: _, [], _ => none
  | t :: Γ, n :: names, name =>
      cond (Nat.beq n name) (some ⟨t, .head⟩)
        ((lookup Γ names name).map fun found => ⟨found.1, .tail found.2⟩)

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

/-! ## Regions -/

/-- A list that starts with `pre`, as `pre` and what follows it. -/
def splitPrefix {T : Type} [DecidableEq T] :
    (pre items : List T) → Option ((rest : List T) ×' items = pre ++ rest)
  | [], items => some ⟨items, rfl⟩
  | a :: pre, b :: items =>
      if same : b = a then
        (splitPrefix pre items).map fun found =>
          ⟨found.1, by rw [same]; exact congrArg (List.cons a) found.2⟩
      else none
  | _ :: _, [] => none

section
variable {D : Dialect} {Raw Who : Type}

/-- How often a loop that `w` perform runs. -/
def elabTimes (rules : Rules D Raw Who) (definition : Key) (w : D.Who) (Γ : List D.Ty)
    (names : List Name) (blocks : List (Key × Nat)) (key : Key) :
    Repeat → Except (Refusal D.Ty Raw) (Times D w Γ)
  | .fixed n => .ok (.fixed n)
  | .count name =>
      match lookup Γ names name with
      | none => .error (refuseAt definition blocks key .scope (.name name))
      | some ⟨t, count⟩ =>
          match rules.count w t with
          | isTrue ok => .ok (.value count ok)
          | isFalse _ => .error (refuseAt definition blocks key .count (.type t))

mutual
  /-- The term of a list of instructions and an exit, in a context with the names in scope,
  with the types of what it gives. -/
  def elabBody (rules : Rules D Raw Who) (definition : Key) (Γ : List D.Ty) (names : List Name)
      (blocks : List (Key × Nat)) (owner : Option Key) :
      List (Instruction Raw Who) → List Name →
        Except (Refusal D.Ty Raw) ((outs : List D.Ty) × Term D Γ outs)
    | [], exit =>
        match lookupAll Γ names exit with
        | .error name =>
            .error (match owner with
              | some key => refuseAt definition blocks key .scope (.name name)
              | none => refuseWhole definition .scope (.name name))
        | .ok ⟨outs, xs⟩ => .ok ⟨outs, .ret xs⟩
    | .op key results raw operands :: rest, exit =>
        match lookupAll Γ names operands with
        | .error name => .error (refuseAt definition blocks key .scope (.name name))
        | .ok ⟨ins, args⟩ =>
            match rules.op raw ins with
            | .error finding => .error (finding.refuseAt definition blocks key)
            | .ok ⟨res, o⟩ =>
                if results.length = res.length then
                  match elabBody rules definition (res ++ Γ) (results ++ names) blocks none rest
                      exit with
                  | .error refusal => .error refusal
                  | .ok ⟨outs, t⟩ => .ok ⟨outs, .op key o args t⟩
                else .error (refuseAt definition blocks key .results
                  (.number res.length results.length))
    | .guard key who condition why :: rest, exit =>
        match rules.who who with
        | .error finding => .error (finding.refuseAt definition blocks key)
        | .ok w =>
            match lookup Γ names condition with
            | none => .error (refuseAt definition blocks key .scope (.name condition))
            | some ⟨t, c⟩ =>
                match rules.condition w t with
                | isFalse _ => .error (refuseAt definition blocks key .condition (.type t))
                | isTrue ok =>
                    match elabBody rules definition Γ names blocks none rest exit with
                    | .error refusal => .error refusal
                    | .ok ⟨outs, t⟩ => .ok ⟨outs, .guard key w c ok why t⟩
    | .choose key who condition results onTrue onFalse :: rest, exit =>
        match rules.who who with
        | .error finding => .error (finding.refuseAt definition blocks key)
        | .ok w =>
            match lookup Γ names condition with
            | none => .error (refuseAt definition blocks key .scope (.name condition))
            | some ⟨t, c⟩ =>
                match rules.condition w t with
                | isFalse _ => .error (refuseAt definition blocks key .condition (.type t))
                | isTrue ok =>
                    match elabRegion rules definition Γ names blocks key [] onTrue with
                    | .error refusal => .error refusal
                    | .ok ⟨mid, yes⟩ =>
                        match elabRegion rules definition Γ names blocks key [] onFalse with
                        | .error refusal => .error refusal
                        | .ok ⟨mid', no⟩ =>
                            match rules.sameTys mid' mid with
                            | isFalse _ => .error (refuseAt definition blocks key .regions
                              (.types mid mid'))
                            | isTrue same =>
                                match decideAll (D.Gives w) (rules.gives w) mid with
                                | isFalse _ => .error (refuseAt definition blocks key .gives
                                  (.given mid))
                                | isTrue gives =>
                                    if results.length = mid.length then
                                      match elabBody rules definition (mid ++ Γ)
                                          (results ++ names) blocks none rest exit with
                                      | .error refusal => .error refusal
                                      | .ok ⟨outs, t⟩ =>
                                          .ok ⟨outs, .choose key w c ok gives yes
                                            (cast (congrArg (Term D Γ) same) no) t⟩
                                    else .error (refuseAt definition blocks key .results
                                      (.number mid.length results.length))
    | .cases key who subject results arms :: rest, exit =>
        match rules.who who with
        | .error finding => .error (finding.refuseAt definition blocks key)
        | .ok w =>
            match lookup Γ names subject with
            | none => .error (refuseAt definition blocks key .scope (.name subject))
            | some ⟨t, x⟩ =>
                match rules.alternatives w t with
                | none => .error (refuseAt definition blocks key .variant (.type t))
                | some ⟨payloads, ok⟩ =>
                    if arms.length = payloads.length then
                      match elabCases rules definition Γ names blocks key payloads arms with
                      | .error refusal => .error refusal
                      | .ok ⟨mid, elaborated⟩ =>
                          match decideAll (D.Gives w) (rules.gives w) mid with
                          | isFalse _ => .error (refuseAt definition blocks key .gives (.given mid))
                          | isTrue gives =>
                              if results.length = mid.length then
                                match elabBody rules definition (mid ++ Γ) (results ++ names)
                                    blocks none rest exit with
                                | .error refusal => .error refusal
                                | .ok ⟨outs, t⟩ => .ok ⟨outs, .cases key w x ok gives elaborated t⟩
                              else .error (refuseAt definition blocks key .results
                                (.number mid.length results.length))
                    else .error (refuseAt definition blocks key .arms
                      (.number payloads.length arms.length))
    | .loop key who times carried results body :: rest, exit =>
        match rules.who who with
        | .error finding => .error (finding.refuseAt definition blocks key)
        | .ok w =>
            match lookupAll Γ names carried with
            | .error name => .error (refuseAt definition blocks key .scope (.name name))
            | .ok ⟨carried, init⟩ =>
                match elabTimes rules definition w Γ names blocks key times with
                | .error refusal => .error refusal
                | .ok times =>
                    match elabRegion rules definition Γ names blocks key (D.index w :: carried)
                        body with
                    | .error refusal => .error refusal
                    | .ok ⟨outs, b⟩ =>
                        match @splitPrefix _ rules.sameTy carried outs with
                        | none => .error (refuseAt definition blocks key .carried
                          (.types carried outs))
                        | some ⟨each, split⟩ =>
                            match decideAll (D.Gives w) (rules.gives w) (carried ++ each) with
                            | isFalse _ => .error (refuseAt definition blocks key .gives
                                (.given (carried ++ each)))
                            | isTrue gives =>
                                if results.length =
                                    (carried ++ each.map (D.collected times.size)).length then
                                  match elabBody rules definition
                                      ((carried ++ each.map (D.collected times.size)) ++ Γ)
                                      (results ++ names) blocks none rest exit with
                                  | .error refusal => .error refusal
                                  | .ok ⟨outs, t⟩ =>
                                      .ok ⟨outs, .loop key w times gives init
                                        (cast (congrArg (Term D (D.index w :: (carried ++ Γ)))
                                          split) b)
                                        t⟩
                                else .error (refuseAt definition blocks key .results
                                  (.number (carried ++ each.map (D.collected times.size)).length
                                    results.length))
    | .block key number results body :: rest, exit =>
        match elabRegion rules definition Γ names (blocks ++ [(key, number)]) key [] body with
        | .error refusal => .error refusal
        | .ok ⟨mid, b⟩ =>
            if results.length = mid.length then
              match elabBody rules definition (mid ++ Γ) (results ++ names) blocks none rest
                  exit with
              | .error refusal => .error refusal
              | .ok ⟨outs, t⟩ => .ok ⟨outs, .block key number b t⟩
            else .error (refuseAt definition blocks key .results
              (.number mid.length results.length))
    | .attempt key who results body :: rest, exit =>
        match rules.who who with
        | .error finding => .error (finding.refuseAt definition blocks key)
        | .ok w =>
            match rules.attempt w with
            | isFalse _ => .error (refuseAt definition blocks key .attempt .nothing)
            | isTrue owns =>
                match elabRegion rules definition Γ names blocks key [D.index w] body with
                | .error refusal => .error refusal
                | .ok ⟨mid, b⟩ =>
                    if results.length = mid.length then
                      match elabBody rules definition (mid ++ Γ) (results ++ names) blocks none rest
                  exit with
                      | .error refusal => .error refusal
                      | .ok ⟨outs, t⟩ => .ok ⟨outs, .attempt key w owns b t⟩
                    else .error (refuseAt definition blocks key .results
                      (.number mid.length results.length))
  /-- The term of a region of the instruction with the key, whose inputs have the types
  `ins`. -/
  def elabRegion (rules : Rules D Raw Who) (definition : Key) (Γ : List D.Ty)
      (names : List Name) (blocks : List (Key × Nat)) (key : Key) (ins : List D.Ty) :
      Region Raw Who → Except (Refusal D.Ty Raw) ((outs : List D.Ty) × Term D (ins ++ Γ) outs)
    | .mk inputs body exit =>
        if inputs.length = ins.length then
          elabBody rules definition (ins ++ Γ) (inputs ++ names) blocks (some key) body exit
        else .error (refuseAt definition blocks key .inputs (.number ins.length inputs.length))
  /-- The arms of a case analysis, one per alternative, each with the payload as its input:
  the first arm says what they give, and a case analysis without arms gives nothing. -/
  def elabCases (rules : Rules D Raw Who) (definition : Key) (Γ : List D.Ty)
      (names : List Name) (blocks : List (Key × Nat)) (key : Key) :
      (payloads : List D.Ty) → List (Region Raw Who) →
        Except (Refusal D.Ty Raw) ((mid : List D.Ty) × Arms D Γ mid payloads)
    | [], [] => .ok ⟨[], .nil⟩
    | payload :: payloads, arm :: arms =>
        match elabRegion rules definition Γ names blocks key [payload] arm with
        | .error refusal => .error refusal
        | .ok ⟨mid, first⟩ =>
            match elabArms rules definition Γ names blocks key mid payloads arms with
            | .error refusal => .error refusal
            | .ok others => .ok ⟨mid, .cons first others⟩
    | payloads, arms => .error (refuseAt definition blocks key .arms
      (.number payloads.length arms.length))
  /-- The other arms of a case analysis, each giving the types `mid`. -/
  def elabArms (rules : Rules D Raw Who) (definition : Key) (Γ : List D.Ty)
      (names : List Name) (blocks : List (Key × Nat)) (key : Key) (mid : List D.Ty) :
      (payloads : List D.Ty) → List (Region Raw Who) →
        Except (Refusal D.Ty Raw) (Arms D Γ mid payloads)
    | [], [] => .ok .nil
    | payload :: payloads, arm :: arms =>
        match elabRegion rules definition Γ names blocks key [payload] arm with
        | .error refusal => .error refusal
        | .ok ⟨mid', a⟩ =>
            match rules.sameTys mid' mid with
            | isFalse _ => .error (refuseAt definition blocks key .armTypes (.types mid mid'))
            | isTrue same =>
                match elabArms rules definition Γ names blocks key mid payloads arms with
                | .error refusal => .error refusal
                | .ok others => .ok (.cons (cast (congrArg (Term D (payload :: Γ)) same) a) others)
    | payloads, arms => .error (refuseAt definition blocks key .arms
      (.number payloads.length arms.length))
end

/-! ## What elaboration gives -/

variable (rules : Rules D Raw Who)

mutual
  /-- Elaboration gives a term whose case analyses without an arm give nothing. -/
  theorem elabBody_armed : ∀ {definition : Key} {Γ : List D.Ty} {names : List Name}
      {blocks : List (Key × Nat)} {owner : Option Key} (instructions : List (Instruction Raw Who))
      (exit : List Name) {outs : List D.Ty}
      {t : Term D Γ outs},
      elabBody rules definition Γ names blocks owner instructions exit = .ok ⟨outs, t⟩ →
      t.armed = true
    | _, _, _, _, _, [], _, _, _, elaborated => by
        simp only [elabBody] at elaborated
        split at elaborated
        · cases elaborated
        · cases elaborated
          rfl
    | _, _, _, _, _, .op .. :: rest, exit, _, _, elaborated => by
        simp only [elabBody] at elaborated
        repeat' split at elaborated
        all_goals first
          | (cases elaborated; done)
          | (cases elaborated
             simp only [Term.armed]
             exact elabBody_armed rest exit ‹_›)
    | _, _, _, _, _, .guard .. :: rest, exit, _, _, elaborated => by
        simp only [elabBody] at elaborated
        repeat' split at elaborated
        all_goals first
          | (cases elaborated; done)
          | (cases elaborated
             simp only [Term.armed]
             exact elabBody_armed rest exit ‹_›)
    | _, _, _, _, _, .choose _ _ _ _ onTrue onFalse :: rest, exit, _, _, elaborated => by
        simp only [elabBody] at elaborated
        repeat' split at elaborated
        all_goals first
          | (cases elaborated; done)
          | (cases elaborated
             subst_vars
             simp only [Term.armed, cast_eq, Bool.and_eq_true]
             exact ⟨⟨elabRegion_armed onTrue ‹elabRegion rules _ _ _ _ _ _ onTrue = _›,
               elabRegion_armed onFalse ‹elabRegion rules _ _ _ _ _ _ onFalse = _›⟩,
               elabBody_armed rest exit ‹_›⟩)
    | _, _, _, _, _, .cases _ _ _ _ arms :: rest, exit, _, _, elaborated => by
        simp only [elabBody] at elaborated
        repeat' split at elaborated
        all_goals first
          | (cases elaborated; done)
          | (cases elaborated
             simp only [Term.armed, Bool.and_eq_true]
             exact ⟨elabCases_armed arms ‹elabCases rules _ _ _ _ _ _ arms = _›,
               elabBody_armed rest exit ‹_›⟩)
    | _, _, _, _, _, .loop _ _ _ _ _ body :: rest, exit, _, _, elaborated => by
        simp only [elabBody] at elaborated
        repeat' split at elaborated
        all_goals first
          | (cases elaborated; done)
          | (cases elaborated
             subst_vars
             simp only [Term.armed, cast_eq, Bool.and_eq_true]
             exact ⟨elabRegion_armed body ‹elabRegion rules _ _ _ _ _ _ body = _›,
               elabBody_armed rest exit ‹_›⟩)
    | _, _, _, _, _, .block _ _ _ body :: rest, exit, _, _, elaborated => by
        simp only [elabBody] at elaborated
        repeat' split at elaborated
        all_goals first
          | (cases elaborated; done)
          | (cases elaborated
             simp only [Term.armed, Bool.and_eq_true]
             exact ⟨elabRegion_armed body ‹elabRegion rules _ _ _ _ _ _ body = _›,
               elabBody_armed rest exit ‹_›⟩)
    | _, _, _, _, _, .attempt _ _ _ body :: rest, exit, _, _, elaborated => by
        simp only [elabBody] at elaborated
        repeat' split at elaborated
        all_goals first
          | (cases elaborated; done)
          | (cases elaborated
             simp only [Term.armed, Bool.and_eq_true]
             exact ⟨elabRegion_armed body ‹elabRegion rules _ _ _ _ _ _ body = _›,
               elabBody_armed rest exit ‹_›⟩)
  theorem elabRegion_armed : ∀ {definition : Key} {Γ : List D.Ty} {names : List Name}
      {blocks : List (Key × Nat)} {key : Key} {ins : List D.Ty} (region : Region Raw Who)
      {outs : List D.Ty}
      {t : Term D (ins ++ Γ) outs},
      elabRegion rules definition Γ names blocks key ins region = .ok ⟨outs, t⟩ → t.armed = true
    | _, _, _, _, _, _, .mk _ body exit, _, _, elaborated => by
        simp only [elabRegion] at elaborated
        split at elaborated
        · exact elabBody_armed body exit elaborated
        · cases elaborated
  theorem elabCases_armed : ∀ {definition : Key} {Γ : List D.Ty} {names : List Name}
      {blocks : List (Key × Nat)} {key : Key} {payloads : List D.Ty}
      (regions : List (Region Raw Who)) {mid : List D.Ty}
      {arms : Arms D Γ mid payloads},
      elabCases rules definition Γ names blocks key payloads regions = .ok ⟨mid, arms⟩ →
      (arms.hasArm || mid.isEmpty) = true ∧ Arms.armed arms = true
    | _, _, _, _, _, [], [], _, _, elaborated => by
        cases elaborated
        exact ⟨rfl, rfl⟩
    | _, _, _, _, _, [], _ :: _, _, _, elaborated => by cases elaborated
    | _, _, _, _, _, _ :: _, [], _, _, elaborated => by cases elaborated
    | _, _, _, _, _, _ :: _, arm :: others, _, _, elaborated => by
        simp only [elabCases] at elaborated
        repeat' split at elaborated
        all_goals first
          | (cases elaborated; done)
          | (cases elaborated
             simp only [Arms.hasArm, Arms.armed, Bool.true_or, Bool.and_eq_true]
             exact ⟨trivial, elabRegion_armed arm ‹elabRegion rules _ _ _ _ _ _ arm = _›,
               elabArms_armed others ‹_›⟩)
  theorem elabArms_armed : ∀ {definition : Key} {Γ : List D.Ty} {names : List Name}
      {blocks : List (Key × Nat)} {key : Key} {mid payloads : List D.Ty}
      (regions : List (Region Raw Who))
      {arms : Arms D Γ mid payloads},
      elabArms rules definition Γ names blocks key mid payloads regions = .ok arms →
      Arms.armed arms = true
    | _, _, _, _, _, _, [], [], _, elaborated => by
        cases elaborated
        rfl
    | _, _, _, _, _, _, [], _ :: _, _, elaborated => by cases elaborated
    | _, _, _, _, _, _, _ :: _, [], _, elaborated => by cases elaborated
    | _, _, _, _, _, _, _ :: _, arm :: others, _, elaborated => by
        simp only [elabArms] at elaborated
        repeat' split at elaborated
        all_goals first
          | (cases elaborated; done)
          | (cases elaborated
             subst_vars
             simp only [Arms.armed, cast_eq, Bool.and_eq_true]
             exact ⟨elabRegion_armed arm ‹elabRegion rules _ _ _ _ _ _ arm = _›,
               elabArms_armed others ‹_›⟩)
end

end

end Zkc.Core
