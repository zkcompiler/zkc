module

public import Zkc.Core.Program.Term
public import Zkc.Core.Program.Refusal

@[expose] public section

/-!
Elaboration: the typed term of a region by names, through the rules of its dialect.

Elaboration takes the key of the definition that it elaborates and makes each refusal at its
place: the blocks around the instruction and its key; for the exit of a region, the instruction
whose region it is; for the exit of the body, the definition. The rules of a dialect know no
place: they answer a finding.

A name is looked up in the context; the variable that it becomes is the name with the proof of
what the context has there. A binding takes the names that are written for it, and a region of
an instruction sees the names around it, with its inputs bound. A region is elaborated in a
context to its result types and its term: its instructions in order, then its exit. The rules
of a dialect give its operations from what is written and the types of the operands, read who
performs, and decide the conditions that a form of control asks of who performs it and of the
types of its subject and of what it gives.

Every function here is defined by structural recursion and every decision is a `Decidable`
instance that reduces, so that elaboration runs in the kernel. Elaboration gives only terms whose
case analyses without an arm give nothing (`elabBody_armed`).
-/

namespace Zkc.Core

/-- How a dialect decides that two of its types are equal: what elaboration (`Rules`) and following
(`SkelRules`, `Value/Skeleton.lean`) compare types with. -/
structure TypeEquality (D : Dialect) where
  sameTy : DecidableEq D.Ty

/-- Whether two lists of types are equal, by the dialect's decision for types. -/
def TypeEquality.sameTys {D : Dialect} (types : TypeEquality D) : DecidableEq (List D.Ty) :=
  @instDecidableEqList D.Ty types.sameTy

/-- The rules of a dialect, by which its regions by names are elaborated and its terms are
printed. `Raw` is what is written for an operation, `Who` what is written for who performs. -/
structure Rules (D : Dialect) (Raw Who : Type) extends TypeEquality D where
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
variable {T : Type}

theorem splitPrefix_append [DecidableEq T] (rest : List T) : ∀ (pre : List T),
    splitPrefix pre (pre ++ rest) = some ⟨rest, rfl⟩
  | [] => rfl
  | a :: pre => by
      simp only [List.cons_append, splitPrefix, splitPrefix_append rest pre, ↓reduceDIte,
        Option.map_some]

end

/-! ## Names in scope -/

section
variable {T : Type}

/-- A name in scope, as a variable of the context with its type. -/
def lookup (Γ : Ctx T) (name : Name) : Option ((t : T) × Var Γ t) :=
  match found : Γ.find? name with
  | none => none
  | some t => some ⟨t, ⟨name, found⟩⟩

/-- Names in scope, as variables; the first name that is not in scope otherwise. -/
def lookupAll (Γ : Ctx T) : List Name → Except Name ((items : List T) × HList (Var Γ) items)
  | [] => .ok ⟨[], .nil⟩
  | name :: rest =>
      match lookup Γ name with
      | none => .error name
      | some ⟨t, x⟩ =>
          match lookupAll Γ rest with
          | .error missing => .error missing
          | .ok ⟨items, xs⟩ => .ok ⟨t :: items, .cons x xs⟩

end

/-! ## Elaboration -/

section
variable {D : Dialect} {Raw Who : Type}

/-- How often a loop that `w` perform runs. -/
def elabTimes (rules : Rules D Raw Who) (definition : Key) (w : D.Who) (Γ : Ctx D.Ty)
    (blocks : List (Key × Nat)) (key : Key) :
    Repeat → Except (Refusal D.Ty Raw) (Times D w Γ)
  | .fixed n => .ok (.fixed n)
  | .count name =>
      match lookup Γ name with
      | none => .error (refuseAt definition blocks key .scope (.name name))
      | some ⟨t, count⟩ =>
          match rules.count w t with
          | isTrue ok => .ok (.value count ok)
          | isFalse _ => .error (refuseAt definition blocks key .count (.type t))

mutual
  /-- The term of a list of instructions and an exit, in a context, with the types of what it
  gives. -/
  def elabBody (rules : Rules D Raw Who) (definition : Key) (Γ : Ctx D.Ty)
      (blocks : List (Key × Nat)) (owner : Option Key) :
      List (Instruction Raw Who) → List Name →
        Except (Refusal D.Ty Raw) ((outs : List D.Ty) × Term D Γ outs)
    | [], exit =>
        match lookupAll Γ exit with
        | .error name =>
            .error (match owner with
              | some key => refuseAt definition blocks key .scope (.name name)
              | none => refuseWhole definition .scope (.name name))
        | .ok ⟨outs, xs⟩ => .ok ⟨outs, .ret xs⟩
    | .op key results raw operands :: rest, exit =>
        match lookupAll Γ operands with
        | .error name => .error (refuseAt definition blocks key .scope (.name name))
        | .ok ⟨ins, args⟩ =>
            match rules.op raw ins with
            | .error finding => .error (finding.refuseAt definition blocks key)
            | .ok ⟨res, o⟩ =>
                match Names.ofList res results with
                | none => .error (refuseAt definition blocks key .results
                    (.number res.length results.length))
                | some bound =>
                    match elabBody rules definition (Γ.extend bound) blocks none rest exit with
                    | .error refusal => .error refusal
                    | .ok ⟨outs, t⟩ => .ok ⟨outs, .op key o args bound t⟩
    | .guard key who condition why :: rest, exit =>
        match rules.who who with
        | .error finding => .error (finding.refuseAt definition blocks key)
        | .ok w =>
            match lookup Γ condition with
            | none => .error (refuseAt definition blocks key .scope (.name condition))
            | some ⟨t, c⟩ =>
                match rules.condition w t with
                | isFalse _ => .error (refuseAt definition blocks key .condition (.type t))
                | isTrue ok =>
                    match elabBody rules definition Γ blocks none rest exit with
                    | .error refusal => .error refusal
                    | .ok ⟨outs, t⟩ => .ok ⟨outs, .guard key w c ok why t⟩
    | .choose key who condition results onTrue onFalse :: rest, exit =>
        match rules.who who with
        | .error finding => .error (finding.refuseAt definition blocks key)
        | .ok w =>
            match lookup Γ condition with
            | none => .error (refuseAt definition blocks key .scope (.name condition))
            | some ⟨t, c⟩ =>
                match rules.condition w t with
                | isFalse _ => .error (refuseAt definition blocks key .condition (.type t))
                | isTrue ok =>
                    match elabClosed rules definition Γ blocks key onTrue with
                    | .error refusal => .error refusal
                    | .ok ⟨mid, yes⟩ =>
                        match elabClosed rules definition Γ blocks key onFalse with
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
                                    match Names.ofList mid results with
                                    | none => .error (refuseAt definition blocks key .results
                                        (.number mid.length results.length))
                                    | some bound =>
                                        match elabBody rules definition (Γ.extend bound) blocks
                                            none rest exit with
                                        | .error refusal => .error refusal
                                        | .ok ⟨outs, t⟩ =>
                                            .ok ⟨outs, .choose key w c ok gives yes
                                              (cast (congrArg (Term D Γ) same) no) bound t⟩
    | .cases key who subject results arms :: rest, exit =>
        match rules.who who with
        | .error finding => .error (finding.refuseAt definition blocks key)
        | .ok w =>
            match lookup Γ subject with
            | none => .error (refuseAt definition blocks key .scope (.name subject))
            | some ⟨t, x⟩ =>
                match rules.alternatives w t with
                | none => .error (refuseAt definition blocks key .variant (.type t))
                | some ⟨payloads, ok⟩ =>
                    if arms.length = payloads.length then
                      match elabCases rules definition Γ blocks key payloads arms with
                      | .error refusal => .error refusal
                      | .ok ⟨mid, elaborated⟩ =>
                          match decideAll (D.Gives w) (rules.gives w) mid with
                          | isFalse _ => .error (refuseAt definition blocks key .gives (.given mid))
                          | isTrue gives =>
                              match Names.ofList mid results with
                              | none => .error (refuseAt definition blocks key .results
                                  (.number mid.length results.length))
                              | some bound =>
                                  match elabBody rules definition (Γ.extend bound) blocks none
                                      rest exit with
                                  | .error refusal => .error refusal
                                  | .ok ⟨outs, t⟩ =>
                                      .ok ⟨outs, .cases key w x ok gives elaborated bound t⟩
                    else .error (refuseAt definition blocks key .arms
                      (.number payloads.length arms.length))
    | .loop key who times carried results body :: rest, exit =>
        match rules.who who with
        | .error finding => .error (finding.refuseAt definition blocks key)
        | .ok w =>
            match lookupAll Γ carried with
            | .error name => .error (refuseAt definition blocks key .scope (.name name))
            | .ok ⟨carried, init⟩ =>
                match elabTimes rules definition w Γ blocks key times with
                | .error refusal => .error refusal
                | .ok times =>
                    match elabRegion rules definition Γ blocks key (D.index w :: carried)
                        body with
                    | .error refusal => .error refusal
                    | .ok ⟨outs, inputs, b⟩ =>
                        match @splitPrefix _ rules.sameTy carried outs with
                        | none => .error (refuseAt definition blocks key .carried
                          (.types carried outs))
                        | some ⟨each, split⟩ =>
                            match decideAll (D.Gives w) (rules.gives w) (carried ++ each) with
                            | isFalse _ => .error (refuseAt definition blocks key .gives
                                (.given (carried ++ each)))
                            | isTrue gives =>
                                match Names.ofList
                                    (carried ++ each.map (D.collected times.size)) results with
                                | none => .error (refuseAt definition blocks key .results
                                    (.number (carried ++ each.map (D.collected times.size)).length
                                      results.length))
                                | some bound =>
                                    match elabBody rules definition (Γ.extend bound) blocks none
                                        rest exit with
                                    | .error refusal => .error refusal
                                    | .ok ⟨outs, t⟩ =>
                                        .ok ⟨outs, .loop key w times gives init inputs
                                          (cast (congrArg (Term D (Γ.extend inputs)) split) b)
                                          bound t⟩
    | .block key number results body :: rest, exit =>
        match elabClosed rules definition Γ (blocks ++ [(key, number)]) key body with
        | .error refusal => .error refusal
        | .ok ⟨mid, b⟩ =>
            match Names.ofList mid results with
            | none => .error (refuseAt definition blocks key .results
                (.number mid.length results.length))
            | some bound =>
                match elabBody rules definition (Γ.extend bound) blocks none rest exit with
                | .error refusal => .error refusal
                | .ok ⟨outs, t⟩ => .ok ⟨outs, .block key number b bound t⟩
    | .attempt key who results body :: rest, exit =>
        match rules.who who with
        | .error finding => .error (finding.refuseAt definition blocks key)
        | .ok w =>
            match rules.attempt w with
            | isFalse _ => .error (refuseAt definition blocks key .attempt .nothing)
            | isTrue owns =>
                match elabRegion rules definition Γ blocks key [D.index w] body with
                | .error refusal => .error refusal
                | .ok ⟨mid, inputs, b⟩ =>
                    match Names.ofList mid results with
                    | none => .error (refuseAt definition blocks key .results
                        (.number mid.length results.length))
                    | some bound =>
                        match elabBody rules definition (Γ.extend bound) blocks none rest
                            exit with
                        | .error refusal => .error refusal
                        | .ok ⟨outs, t⟩ => .ok ⟨outs, .attempt key w owns inputs b bound t⟩
  /-- The term of a region of the instruction with the key, whose inputs have the types `ins`,
  with the names of its inputs. -/
  def elabRegion (rules : Rules D Raw Who) (definition : Key) (Γ : Ctx D.Ty)
      (blocks : List (Key × Nat)) (key : Key) (ins : List D.Ty) :
      Region Raw Who →
        Except (Refusal D.Ty Raw)
          ((outs : List D.Ty) × (inputs : Names ins) × Term D (Γ.extend inputs) outs)
    | .mk inputs body exit =>
        match Names.ofList ins inputs with
        | none => .error (refuseAt definition blocks key .inputs
            (.number ins.length inputs.length))
        | some bound =>
            match elabBody rules definition (Γ.extend bound) blocks (some key) body exit with
            | .error refusal => .error refusal
            | .ok ⟨outs, t⟩ => .ok ⟨outs, bound, t⟩
  /-- The term of a region of the instruction with the key that has no input: a region of a
  choice or the body of a block, in the context around it. -/
  def elabClosed (rules : Rules D Raw Who) (definition : Key) (Γ : Ctx D.Ty)
      (blocks : List (Key × Nat)) (key : Key) :
      Region Raw Who → Except (Refusal D.Ty Raw) ((outs : List D.Ty) × Term D Γ outs)
    | .mk [] body exit => elabBody rules definition Γ blocks (some key) body exit
    | .mk (input :: inputs) _ _ =>
        .error (refuseAt definition blocks key .inputs (.number 0 (input :: inputs).length))
  /-- The arms of a case analysis, one per alternative, each with the payload as its input:
  the first arm says what they give, and a case analysis without arms gives nothing. -/
  def elabCases (rules : Rules D Raw Who) (definition : Key) (Γ : Ctx D.Ty)
      (blocks : List (Key × Nat)) (key : Key) :
      (payloads : List D.Ty) → List (Region Raw Who) →
        Except (Refusal D.Ty Raw) ((mid : List D.Ty) × Arms D Γ mid payloads)
    | [], [] => .ok ⟨[], .nil⟩
    | payload :: payloads, arm :: arms =>
        match elabRegion rules definition Γ blocks key [payload] arm with
        | .error refusal => .error refusal
        | .ok ⟨mid, inputs, first⟩ =>
            match elabArms rules definition Γ blocks key mid payloads arms with
            | .error refusal => .error refusal
            | .ok others => .ok ⟨mid, .cons inputs first others⟩
    | payloads, arms => .error (refuseAt definition blocks key .arms
      (.number payloads.length arms.length))
  /-- The other arms of a case analysis, each giving the types `mid`. -/
  def elabArms (rules : Rules D Raw Who) (definition : Key) (Γ : Ctx D.Ty)
      (blocks : List (Key × Nat)) (key : Key) (mid : List D.Ty) :
      (payloads : List D.Ty) → List (Region Raw Who) →
        Except (Refusal D.Ty Raw) (Arms D Γ mid payloads)
    | [], [] => .ok .nil
    | payload :: payloads, arm :: arms =>
        match elabRegion rules definition Γ blocks key [payload] arm with
        | .error refusal => .error refusal
        | .ok ⟨mid', inputs, a⟩ =>
            match rules.sameTys mid' mid with
            | isFalse _ => .error (refuseAt definition blocks key .armTypes (.types mid mid'))
            | isTrue same =>
                match elabArms rules definition Γ blocks key mid payloads arms with
                | .error refusal => .error refusal
                | .ok others =>
                    .ok (.cons inputs (cast (congrArg (Term D (Γ.extend inputs)) same) a) others)
    | payloads, arms => .error (refuseAt definition blocks key .arms
      (.number payloads.length arms.length))
end

/-! ## What elaboration gives -/

variable (rules : Rules D Raw Who)

mutual
  /-- Elaboration gives a term whose case analyses without an arm give nothing. -/
  theorem elabBody_armed : ∀ {definition : Key} {Γ : Ctx D.Ty} {blocks : List (Key × Nat)}
      {owner : Option Key} (instructions : List (Instruction Raw Who)) (exit : List Name)
      {outs : List D.Ty} {t : Term D Γ outs},
      elabBody rules definition Γ blocks owner instructions exit = .ok ⟨outs, t⟩ →
      t.armed = true
    | _, _, _, _, [], _, _, _, elaborated => by
        simp only [elabBody] at elaborated
        split at elaborated
        · cases elaborated
        · cases elaborated
          rfl
    | _, _, _, _, .op .. :: rest, exit, _, _, elaborated => by
        simp only [elabBody] at elaborated
        repeat' split at elaborated
        all_goals first
          | (cases elaborated; done)
          | (cases elaborated
             simp only [Term.armed]
             exact elabBody_armed rest exit ‹_›)
    | _, _, _, _, .guard .. :: rest, exit, _, _, elaborated => by
        simp only [elabBody] at elaborated
        repeat' split at elaborated
        all_goals first
          | (cases elaborated; done)
          | (cases elaborated
             simp only [Term.armed]
             exact elabBody_armed rest exit ‹_›)
    | _, _, _, _, .choose _ _ _ _ onTrue onFalse :: rest, exit, _, _, elaborated => by
        simp only [elabBody] at elaborated
        repeat' split at elaborated
        all_goals first
          | (cases elaborated; done)
          | (cases elaborated
             subst_vars
             simp only [Term.armed, cast_eq, Bool.and_eq_true]
             exact ⟨⟨elabClosed_armed onTrue ‹elabClosed rules _ _ _ _ onTrue = _›,
               elabClosed_armed onFalse ‹elabClosed rules _ _ _ _ onFalse = _›⟩,
               elabBody_armed rest exit ‹_›⟩)
    | _, _, _, _, .cases _ _ _ _ arms :: rest, exit, _, _, elaborated => by
        simp only [elabBody] at elaborated
        repeat' split at elaborated
        all_goals first
          | (cases elaborated; done)
          | (cases elaborated
             simp only [Term.armed, Bool.and_eq_true]
             exact ⟨elabCases_armed arms ‹elabCases rules _ _ _ _ _ arms = _›,
               elabBody_armed rest exit ‹_›⟩)
    | _, _, _, _, .loop _ _ _ _ _ body :: rest, exit, _, _, elaborated => by
        simp only [elabBody] at elaborated
        repeat' split at elaborated
        all_goals first
          | (cases elaborated; done)
          | (cases elaborated
             subst_vars
             simp only [Term.armed, cast_eq, Bool.and_eq_true]
             exact ⟨elabRegion_armed body ‹elabRegion rules _ _ _ _ _ body = _›,
               elabBody_armed rest exit ‹_›⟩)
    | _, _, _, _, .block _ _ _ body :: rest, exit, _, _, elaborated => by
        simp only [elabBody] at elaborated
        repeat' split at elaborated
        all_goals first
          | (cases elaborated; done)
          | (cases elaborated
             simp only [Term.armed, Bool.and_eq_true]
             exact ⟨elabClosed_armed body ‹elabClosed rules _ _ _ _ body = _›,
               elabBody_armed rest exit ‹_›⟩)
    | _, _, _, _, .attempt _ _ _ body :: rest, exit, _, _, elaborated => by
        simp only [elabBody] at elaborated
        repeat' split at elaborated
        all_goals first
          | (cases elaborated; done)
          | (cases elaborated
             simp only [Term.armed, Bool.and_eq_true]
             exact ⟨elabRegion_armed body ‹elabRegion rules _ _ _ _ _ body = _›,
               elabBody_armed rest exit ‹_›⟩)
  /-- Elaboration gives a region whose case analyses without an arm give nothing. -/
  theorem elabRegion_armed : ∀ {definition : Key} {Γ : Ctx D.Ty} {blocks : List (Key × Nat)}
      {key : Key} {ins : List D.Ty} (region : Region Raw Who) {outs : List D.Ty}
      {inputs : Names ins} {t : Term D (Γ.extend inputs) outs},
      elabRegion rules definition Γ blocks key ins region = .ok ⟨outs, inputs, t⟩ →
      t.armed = true
    | _, _, _, _, _, .mk _ body exit, _, _, _, elaborated => by
        simp only [elabRegion] at elaborated
        split at elaborated
        · cases elaborated
        · split at elaborated
          · cases elaborated
          · cases elaborated
            exact elabBody_armed body exit ‹_›
  /-- Elaboration gives a region without inputs whose case analyses without an arm give
  nothing. -/
  theorem elabClosed_armed : ∀ {definition : Key} {Γ : Ctx D.Ty} {blocks : List (Key × Nat)}
      {key : Key} (region : Region Raw Who) {outs : List D.Ty} {t : Term D Γ outs},
      elabClosed rules definition Γ blocks key region = .ok ⟨outs, t⟩ → t.armed = true
    | _, _, _, _, .mk [] body exit, _, _, elaborated => by
        simp only [elabClosed] at elaborated
        exact elabBody_armed body exit elaborated
    | _, _, _, _, .mk (_ :: _) _ _, _, _, elaborated => by
        simp only [elabClosed] at elaborated
        cases elaborated
  /-- Elaboration gives arms of a case analysis that say what they give and whose case
  analyses without an arm give nothing. -/
  theorem elabCases_armed : ∀ {definition : Key} {Γ : Ctx D.Ty} {blocks : List (Key × Nat)}
      {key : Key} {payloads : List D.Ty} (regions : List (Region Raw Who)) {mid : List D.Ty}
      {arms : Arms D Γ mid payloads},
      elabCases rules definition Γ blocks key payloads regions = .ok ⟨mid, arms⟩ →
      (arms.hasArm || mid.isEmpty) = true ∧ Arms.armed arms = true
    | _, _, _, _, [], [], _, _, elaborated => by
        cases elaborated
        exact ⟨rfl, rfl⟩
    | _, _, _, _, [], _ :: _, _, _, elaborated => by cases elaborated
    | _, _, _, _, _ :: _, [], _, _, elaborated => by cases elaborated
    | _, _, _, _, _ :: _, arm :: others, _, _, elaborated => by
        simp only [elabCases] at elaborated
        repeat' split at elaborated
        all_goals first
          | (cases elaborated; done)
          | (cases elaborated
             simp only [Arms.hasArm, Arms.armed, Bool.true_or, Bool.and_eq_true]
             exact ⟨trivial, elabRegion_armed arm ‹elabRegion rules _ _ _ _ _ arm = _›,
               elabArms_armed others ‹_›⟩)
  /-- Elaboration gives arms after the first whose case analyses without an arm give
  nothing. -/
  theorem elabArms_armed : ∀ {definition : Key} {Γ : Ctx D.Ty} {blocks : List (Key × Nat)}
      {key : Key} {mid payloads : List D.Ty} (regions : List (Region Raw Who))
      {arms : Arms D Γ mid payloads},
      elabArms rules definition Γ blocks key mid payloads regions = .ok arms →
      Arms.armed arms = true
    | _, _, _, _, _, [], [], _, elaborated => by
        cases elaborated
        rfl
    | _, _, _, _, _, [], _ :: _, _, elaborated => by cases elaborated
    | _, _, _, _, _, _ :: _, [], _, elaborated => by cases elaborated
    | _, _, _, _, _, _ :: _, arm :: others, _, elaborated => by
        simp only [elabArms] at elaborated
        repeat' split at elaborated
        all_goals first
          | (cases elaborated; done)
          | (cases elaborated
             subst_vars
             simp only [Arms.armed, cast_eq, Bool.and_eq_true]
             exact ⟨elabRegion_armed arm ‹elabRegion rules _ _ _ _ _ arm = _›,
               elabArms_armed others ‹_›⟩)
end

end

end Zkc.Core
