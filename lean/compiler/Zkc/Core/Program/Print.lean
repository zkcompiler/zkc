module

public import Zkc.Core.Program.Elaborate

@[expose] public section

/-!
The printed form of a typed term: the program by names that elaborates to it.

The name of a value is its level: its position from the outermost binding. So the names in
scope in a context are its levels, the innermost first, and the results of an instruction are
named by the levels that they take. The printed form of a term is its instructions in order,
then its exit; the printed form of a region of an instruction has the names of its inputs.

For rules whose laws hold, the printed form of a term elaborates to it when its case analyses
without an arm give nothing (`Term.armed`), and elaboration gives only such terms.
-/

namespace Zkc.Core

/-! ## Names as levels -/

section
variable {T : Type}

/-- The level of a variable: its position from the outermost binding. -/
def Var.level {Γ : List T} {a : T} : Var Γ a → Nat
  | .head (rest := rest) => rest.length
  | .tail x => x.level

/-- The names of the variables of a context: their levels, the innermost first. -/
def levels : List T → List Name
  | [] => []
  | _ :: rest => rest.length :: levels rest

/-- The names of values bound in front of a context: the levels that they take. -/
def front : List T → List T → List Name
  | [], _ => []
  | _ :: items, Γ => (items ++ Γ).length :: front items Γ

/-- The names of variables. -/
def HList.levels {Γ : List T} : {items : List T} → HList (Var Γ) items → List Name
  | [], .nil => []
  | _ :: _, .cons x rest => x.level :: HList.levels rest

end

/-! ## The printer -/

section
variable {D : Dialect} {Raw Who : Type}

/-- How often a loop runs, by names. -/
def printTimes {w : D.Who} {Γ : List D.Ty} : Times D w Γ → Repeat
  | .fixed n => .fixed n
  | .value count _ => .count count.level

mutual
  /-- The instructions and the exit of a term, by names. -/
  def printBody (printOp : ∀ {ins res : List D.Ty}, D.Op ins res → Raw) (printWho : D.Who → Who) :
      {Γ outs : List D.Ty} → Term D Γ outs → List (Instruction Raw Who) × List Name
    | _, _, .ret xs => ([], xs.levels)
    | Γ, _, .op (res := res) key o args rest =>
        let printed := printBody printOp printWho rest
        (.op key (front res Γ) (printOp o) args.levels :: printed.1, printed.2)
    | _, _, .guard key w c _ why rest =>
        let printed := printBody printOp printWho rest
        (.guard key (printWho w) c.level why :: printed.1, printed.2)
    | Γ, _, .choose (mid := mid) key w c _ _ onTrue onFalse rest =>
        let yes := printBody printOp printWho onTrue
        let no := printBody printOp printWho onFalse
        let printed := printBody printOp printWho rest
        (.choose key (printWho w) c.level (front mid Γ) (.mk [] yes.1 yes.2) (.mk [] no.1 no.2) ::
          printed.1, printed.2)
    | Γ, _, .cases (mid := mid) key w x _ _ arms rest =>
        let printed := printBody printOp printWho rest
        (.cases key (printWho w) x.level (front mid Γ) (printArms printOp printWho arms) ::
          printed.1, printed.2)
    | Γ, _, .loop (carried := carried) (each := each) key w times _ init body rest =>
        let inside := printBody printOp printWho body
        let printed := printBody printOp printWho rest
        (.loop key (printWho w) (printTimes times) init.levels
            (front (carried ++ each.map (D.collected times.size)) Γ)
            (.mk (front (D.index w :: carried) Γ) inside.1 inside.2) ::
          printed.1, printed.2)
    | Γ, _, .block (mid := mid) key number body rest =>
        let inside := printBody printOp printWho body
        let printed := printBody printOp printWho rest
        (.block key number (front mid Γ) (.mk [] inside.1 inside.2) :: printed.1, printed.2)
    | Γ, _, .attempt (mid := mid) key w _ body rest =>
        let inside := printBody printOp printWho body
        let printed := printBody printOp printWho rest
        (.attempt key (printWho w) (front mid Γ) (.mk (front [D.index w] Γ) inside.1 inside.2) ::
          printed.1, printed.2)
  /-- The regions of the arms of a case analysis, each with the name of its payload. -/
  def printArms (printOp : ∀ {ins res : List D.Ty}, D.Op ins res → Raw) (printWho : D.Who → Who) :
      {Γ mid payloads : List D.Ty} → Arms D Γ mid payloads → List (Region Raw Who)
    | _, _, _, .nil => []
    | Γ, _, _, .cons (payload := payload) arm rest =>
        let inside := printBody printOp printWho arm
        .mk (front [payload] Γ) inside.1 inside.2 :: printArms printOp printWho rest
end

/-- The printed arms of a case analysis are one per alternative. -/
theorem length_printArms {D : Dialect} {Raw Who : Type}
    (printOp : ∀ {ins res : List D.Ty}, D.Op ins res → Raw) (printWho : D.Who → Who) :
    ∀ {Γ mid payloads : List D.Ty} (arms : Arms D Γ mid payloads),
      (printArms printOp printWho arms).length = payloads.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ rest => congrArg (· + 1) (length_printArms printOp printWho rest)

/-- A term by names, as a region whose inputs are its context. -/
def printRegion (printOp : ∀ {ins res : List D.Ty}, D.Op ins res → Raw) (printWho : D.Who → Who)
    {Γ outs : List D.Ty} (t : Term D Γ outs) : Region Raw Who :=
  let printed := printBody printOp printWho t
  .mk (levels Γ) printed.1 printed.2

end

/-! ## The round trip -/

section
variable {T : Type}

theorem Var.level_lt : ∀ {Γ : List T} {a : T} (x : Var Γ a), x.level < Γ.length
  | _ :: _, _, .head => Nat.lt_succ_self _
  | _ :: _, _, .tail x => Nat.lt_succ_of_lt (Var.level_lt x)

theorem lookup_level : ∀ {Γ : List T} {a : T} (x : Var Γ a),
    lookup Γ (levels Γ) x.level = some ⟨a, x⟩
  | _ :: _, _, .head => by simp [lookup, levels, Var.level]
  | _ :: rest, _, .tail x => by
      have differ : Nat.beq rest.length x.level = false := by
        cases same : Nat.beq rest.length x.level
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true same) (Nat.ne_of_gt (Var.level_lt x))
      simp only [lookup, levels, Var.level, differ, Bool.cond_false, lookup_level x,
        Option.map_some]

theorem lookupAll_levels {Γ : List T} : ∀ {items : List T} (xs : HList (Var Γ) items),
    lookupAll Γ (levels Γ) xs.levels = .ok ⟨items, xs⟩
  | [], .nil => rfl
  | _ :: _, .cons x rest => by
      simp only [HList.levels, lookupAll, lookup_level x, lookupAll_levels rest]

theorem levels_append (Γ : List T) : ∀ (items : List T),
    levels (items ++ Γ) = front items Γ ++ levels Γ
  | [] => rfl
  | _ :: items => by
      show (items ++ Γ).length :: levels (items ++ Γ) = _
      rw [levels_append Γ items]
      rfl

theorem length_front (Γ : List T) : ∀ (items : List T), (front items Γ).length = items.length
  | [] => rfl
  | _ :: items => congrArg (· + 1) (length_front Γ items)

theorem length_levels : ∀ (Γ : List T), (levels Γ).length = Γ.length
  | [] => rfl
  | _ :: Γ => congrArg (· + 1) (length_levels Γ)

end

/-- A decision of a proposition that holds. -/
theorem Decidable.eq_isTrue {p : Prop} (decision : Decidable p) (holds : p) :
    decision = isTrue holds := by
  cases decision with
  | isFalse fails => exact absurd holds fails
  | isTrue _ => rfl

section
variable {D : Dialect} {Raw Who : Type}

/-- The laws of the rules of a dialect: what the printer writes, the rules read back. -/
structure Rules.Lawful (rules : Rules D Raw Who) : Prop where
  op : ∀ {ins res : List D.Ty} (o : D.Op ins res), rules.op (rules.printOp o) ins = .ok ⟨res, o⟩
  who : ∀ w, rules.who (rules.printWho w) = .ok w
  alternatives : ∀ w t payloads, D.Alternatives w t payloads →
    ∃ ok, rules.alternatives w t = some ⟨payloads, ok⟩

variable (rules : Rules D Raw Who)

theorem elabTimes_print (definition : Key) (w : D.Who) {Γ : List D.Ty} (blocks : List (Key × Nat))
    (key : Key) : ∀ (times : Times D w Γ),
      elabTimes rules definition w Γ (levels Γ) blocks key (printTimes times) = .ok times
  | .fixed _ => rfl
  | .value count ok => by
      simp only [printTimes, elabTimes, lookup_level, Decidable.eq_isTrue (rules.count w _) ok]

/-- A printed region of an instruction elaborates as its term in the context with its inputs. -/
theorem elabRegion_print {Γ outs : List D.Ty} (definition : Key) (blocks : List (Key × Nat))
    (key : Key) (ins : List D.Ty) (t : Term D (ins ++ Γ) outs)
    (body : elabBody rules definition (ins ++ Γ) (levels (ins ++ Γ)) blocks (some key)
      (printBody rules.printOp rules.printWho t).1 (printBody rules.printOp rules.printWho t).2 =
        .ok ⟨outs, t⟩) :
    elabRegion rules definition Γ (levels Γ) blocks key ins
      (.mk (front ins Γ) (printBody rules.printOp rules.printWho t).1
        (printBody rules.printOp rules.printWho t).2) = .ok ⟨outs, t⟩ := by
  simp only [elabRegion, length_front, ↓reduceIte, ← levels_append, body]

mutual
  /-- The round trip: for lawful rules, the printed form of a term whose case analyses without
  an arm give nothing, elaborated in its context with its levels as the names in scope, is the
  term. -/
  theorem elabBody_print (lawful : rules.Lawful) (definition : Key) :
      ∀ {Γ outs : List D.Ty} (t : Term D Γ outs), t.armed = true →
      ∀ (blocks : List (Key × Nat)) (owner : Option Key),
        elabBody rules definition Γ (levels Γ) blocks owner
          (printBody rules.printOp rules.printWho t).1
          (printBody rules.printOp rules.printWho t).2 = .ok ⟨outs, t⟩
    | _, _, .ret xs, _, blocks, owner => by
        simp only [printBody, elabBody, lookupAll_levels]
    | _, _, .op key o args rest, armed, blocks, owner => by
        have ih := elabBody_print lawful definition rest armed blocks none
        simp only [printBody, elabBody, lookupAll_levels, lawful.op, length_front, ↓reduceIte,
          ← levels_append, ih]
    | _, _, .guard key w c ok why rest, armed, blocks, owner => by
        have ih := elabBody_print lawful definition rest armed blocks none
        simp only [printBody, elabBody, lawful.who, lookup_level,
          Decidable.eq_isTrue (rules.condition w _) ok, ih]
    | _, _, .choose (mid := mid) key w c ok gives onTrue onFalse rest, armed, blocks, owner => by
        simp only [Term.armed, Bool.and_eq_true] at armed
        have yes := elabRegion_print rules definition blocks key [] onTrue
          (elabBody_print lawful definition onTrue armed.1.1 blocks (some key))
        have no := elabRegion_print rules definition blocks key [] onFalse
          (elabBody_print lawful definition onFalse armed.1.2 blocks (some key))
        have ih := elabBody_print lawful definition rest armed.2 blocks none
        simp only [front] at yes no
        simp only [printBody, elabBody, lawful.who, lookup_level,
          Decidable.eq_isTrue (rules.condition w _) ok, yes, no,
          Decidable.eq_isTrue (rules.sameTys mid mid) rfl,
          Decidable.eq_isTrue (decideAll (D.Gives w) (rules.gives w) mid) gives, length_front,
          ↓reduceIte, ← levels_append, ih, cast_eq]
    | _, _, .cases (mid := mid) (payloads := payloads) key w x ok gives arms rest, armed,
        blocks, owner => by
        simp only [Term.armed, Bool.and_eq_true] at armed
        obtain ⟨found, alternatives⟩ := lawful.alternatives w _ payloads ok
        have elaborated := elabCases_print lawful definition arms armed.1.1 armed.1.2 blocks key
        have ih := elabBody_print lawful definition rest armed.2 blocks none
        simp only [printBody, elabBody, lawful.who, lookup_level, alternatives,
          length_printArms, ↓reduceIte, elaborated,
          Decidable.eq_isTrue (decideAll (D.Gives w) (rules.gives w) mid) gives, length_front,
          ↓reduceIte, ← levels_append, ih]
    | _, _, .loop (carried := carried) (each := each) key w times gives init body rest, armed,
        blocks, owner => by
        simp only [Term.armed, Bool.and_eq_true] at armed
        have inside := elabRegion_print rules definition blocks key (D.index w :: carried) body
          (elabBody_print lawful definition body armed.1 blocks (some key))
        have ih := elabBody_print lawful definition rest armed.2 blocks none
        simp only [printBody, elabBody, lawful.who, lookupAll_levels,
          elabTimes_print rules definition, inside,
          @splitPrefix_append _ rules.sameTy, cast_eq,
          Decidable.eq_isTrue (decideAll (D.Gives w) (rules.gives w) (carried ++ each)) gives,
          length_front, ↓reduceIte, ← levels_append, ih]
    | _, _, .block (mid := mid) key number body rest, armed, blocks, owner => by
        simp only [Term.armed, Bool.and_eq_true] at armed
        have inside := elabRegion_print rules definition (blocks ++ [(key, number)]) key [] body
          (elabBody_print lawful definition body armed.1 (blocks ++ [(key, number)]) (some key))
        have ih := elabBody_print lawful definition rest armed.2 blocks none
        simp only [front] at inside
        simp only [printBody, elabBody, inside, length_front, ↓reduceIte, ← levels_append, ih]
    | _, _, .attempt (mid := mid) key w owns body rest, armed, blocks, owner => by
        simp only [Term.armed, Bool.and_eq_true] at armed
        have inside := elabRegion_print rules definition blocks key [D.index w] body
          (elabBody_print lawful definition body armed.1 blocks (some key))
        have ih := elabBody_print lawful definition rest armed.2 blocks none
        simp only [printBody, elabBody, lawful.who, Decidable.eq_isTrue (rules.attempt w) owns,
          inside, length_front, ↓reduceIte, ← levels_append, ih]
  /-- The printed arms of a case analysis elaborate as its arms, with what the first gives. -/
  theorem elabCases_print (lawful : rules.Lawful) (definition : Key) :
      ∀ {Γ mid payloads : List D.Ty} (arms : Arms D Γ mid payloads),
      (arms.hasArm || mid.isEmpty) = true → Arms.armed arms = true →
      ∀ (blocks : List (Key × Nat)) (key : Key),
        elabCases rules definition Γ (levels Γ) blocks key payloads
          (printArms rules.printOp rules.printWho arms) = .ok ⟨mid, arms⟩
    | _, [], _, .nil, _, _, blocks, key => rfl
    | _, _ :: _, _, .nil, given, _, blocks, key => by simp [Arms.hasArm] at given
    | _, _, _, .cons (payload := payload) arm rest, _, armed, blocks, key => by
        simp only [Arms.armed, Bool.and_eq_true] at armed
        have first := elabRegion_print rules definition blocks key [payload] arm
          (elabBody_print lawful definition arm armed.1 blocks (some key))
        have others := elabArms_print lawful definition rest armed.2 blocks key
        simp only [printArms, elabCases, first, others]
  /-- The printed arms of a case analysis after the first elaborate as its arms. -/
  theorem elabArms_print (lawful : rules.Lawful) (definition : Key) :
      ∀ {Γ mid payloads : List D.Ty} (arms : Arms D Γ mid payloads),
      Arms.armed arms = true → ∀ (blocks : List (Key × Nat)) (key : Key),
        elabArms rules definition Γ (levels Γ) blocks key mid payloads
          (printArms rules.printOp rules.printWho arms) = .ok arms
    | _, _, _, .nil, _, blocks, key => rfl
    | _, mid, _, .cons (payload := payload) arm rest, armed, blocks, key => by
        simp only [Arms.armed, Bool.and_eq_true] at armed
        have first := elabRegion_print rules definition blocks key [payload] arm
          (elabBody_print lawful definition arm armed.1 blocks (some key))
        have others := elabArms_print lawful definition rest armed.2 blocks key
        simp only [printArms, elabArms, first, others,
          Decidable.eq_isTrue (rules.sameTys mid mid) rfl, cast_eq]
end

end

end Zkc.Core
