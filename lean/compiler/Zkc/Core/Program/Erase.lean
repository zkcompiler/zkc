module

public import Zkc.Core.Program.Elaborate

@[expose] public section

/-!
Erasure: the program by names of a typed term, and the round trip.

Erasing a term drops its contexts and its proofs: what is left is its instructions in order,
then its exit, with the names that the term keeps; the erased form of a region of an
instruction has the names of its inputs.

Erasure and elaboration are inverse to each other. For rules whose laws hold (`Rules.Lawful`:
what is written for an operation reads back as it), the erased form of a term whose case
analyses without an arm give nothing elaborates to the term (`elabBody_erase`). For rules whose
written forms are canonical (`Rules.Canonical`: an operation that a written form reads as is
written as that form), a term that elaboration gives erases to what was elaborated
(`eraseBody_elab`). A region of an instruction erases with the names of its inputs
(`elabRegion_erase`, `eraseRegion_elab`), and a region without inputs with none
(`elabClosed_erase`, `eraseClosed_elab`).
-/

namespace Zkc.Core

section
variable {D : Dialect} {Raw Who : Type}

/-! ## Erasure -/

/-- How often a loop runs, by names. -/
def eraseTimes {w : D.Who} {Γ : Ctx D.Ty} : Times D w Γ → Repeat
  | .fixed n => .fixed n
  | .value count _ => .count count.name

mutual
  /-- The instructions and the exit of a term, by names. -/
  def eraseBody (printOp : ∀ {ins res : List D.Ty}, D.Op ins res → Raw) (printWho : D.Who → Who) :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → List (Instruction Raw Who) × List Name
    | _, _, .ret exit => ([], HList.names exit)
    | _, _, .op key o operands results rest =>
        let erased := eraseBody printOp printWho rest
        (.op key results.toList (printOp o) (HList.names operands) :: erased.1, erased.2)
    | _, _, .guard key w c _ why rest =>
        let erased := eraseBody printOp printWho rest
        (.guard key (printWho w) c.name why :: erased.1, erased.2)
    | _, _, .choose key w c _ _ onTrue onFalse results rest =>
        let yes := eraseBody printOp printWho onTrue
        let no := eraseBody printOp printWho onFalse
        let erased := eraseBody printOp printWho rest
        (.choose key (printWho w) c.name results.toList (.mk [] yes.1 yes.2) (.mk [] no.1 no.2) ::
          erased.1, erased.2)
    | _, _, .cases key w x _ _ arms results rest =>
        let erased := eraseBody printOp printWho rest
        (.cases key (printWho w) x.name results.toList (eraseArms printOp printWho arms) ::
          erased.1, erased.2)
    | _, _, .loop key w times _ initial inputs body results rest =>
        let inside := eraseBody printOp printWho body
        let erased := eraseBody printOp printWho rest
        (.loop key (printWho w) (eraseTimes times) (HList.names initial) results.toList
            (.mk inputs.toList inside.1 inside.2) :: erased.1, erased.2)
    | _, _, .block key number body results rest =>
        let inside := eraseBody printOp printWho body
        let erased := eraseBody printOp printWho rest
        (.block key number results.toList (.mk [] inside.1 inside.2) :: erased.1, erased.2)
    | _, _, .attempt key w _ inputs body results rest =>
        let inside := eraseBody printOp printWho body
        let erased := eraseBody printOp printWho rest
        (.attempt key (printWho w) results.toList (.mk inputs.toList inside.1 inside.2) ::
          erased.1, erased.2)
  /-- The regions of the arms of a case analysis, each with the name of its payload. -/
  def eraseArms (printOp : ∀ {ins res : List D.Ty}, D.Op ins res → Raw) (printWho : D.Who → Who) :
      {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads → List (Region Raw Who)
    | _, _, _, .nil => []
    | _, _, _, .cons inputs arm rest =>
        let inside := eraseBody printOp printWho arm
        .mk inputs.toList inside.1 inside.2 :: eraseArms printOp printWho rest
end

end

/-- A decision of a proposition that holds. -/
theorem Decidable.eq_isTrue {p : Prop} (decision : Decidable p) (holds : p) :
    decision = isTrue holds := by
  cases decision with
  | isFalse fails => exact absurd holds fails
  | isTrue _ => rfl

section
variable {D : Dialect} {Raw Who : Type}

/-- The laws of the rules of a dialect: what erasure writes, the rules read back. -/
structure Rules.Lawful (rules : Rules D Raw Who) : Prop where
  op : ∀ {ins res : List D.Ty} (o : D.Op ins res), rules.op (rules.printOp o) ins = .ok ⟨res, o⟩
  who : ∀ w, rules.who (rules.printWho w) = .ok w
  alternatives : ∀ w t payloads, D.Alternatives w t payloads →
    ∃ ok, rules.alternatives w t = some ⟨payloads, ok⟩

/-- The other half of the laws: an operation that a written form reads as is written as that
form, and so is who performs. With it a region by names has one spelling. -/
structure Rules.Canonical (rules : Rules D Raw Who) : Prop where
  op : ∀ {ins res : List D.Ty} (raw : Raw) (o : D.Op ins res),
    rules.op raw ins = .ok ⟨res, o⟩ → rules.printOp o = raw
  who : ∀ (written : Who) (w : D.Who), rules.who written = .ok w → rules.printWho w = written

end

/-! ## Names and variables -/

section
variable {T : Type}

/-- The name of a variable is found as the variable. -/
theorem lookup_var {Γ : Ctx T} {τ : T} (x : Var Γ τ) : lookup Γ x.name = some ⟨τ, x⟩ := by
  obtain ⟨name, typed⟩ := x
  unfold lookup
  split
  · rename_i missing
    exact nomatch typed.symm.trans missing
  · rename_i t found
    have same : t = τ := Option.some.inj (found.symm.trans typed)
    subst same
    rfl

/-- The names of variables are found as the variables. -/
theorem lookupAll_names {Γ : Ctx T} : ∀ {items : List T} (xs : HList (Var Γ) items),
    lookupAll Γ (HList.names xs) = .ok ⟨items, xs⟩
  | [], .nil => rfl
  | _ :: _, .cons x rest => by
      simp only [HList.names, lookupAll, lookup_var x, lookupAll_names rest]

/-- A name that is found is the name of the variable found. -/
theorem name_of_lookup {Γ : Ctx T} {name : Name} {τ : T} {x : Var Γ τ}
    (found : lookup Γ name = some ⟨τ, x⟩) : x.name = name := by
  unfold lookup at found
  split at found
  · exact nomatch found
  · cases found
    rfl

/-- Names that are found are the names of the variables found. -/
theorem names_of_lookupAll {Γ : Ctx T} : ∀ {names : List Name} {items : List T}
    {xs : HList (Var Γ) items}, lookupAll Γ names = .ok ⟨items, xs⟩ → HList.names xs = names
  | [], _, _, found => by
      simp only [lookupAll] at found
      cases found
      rfl
  | name :: rest, _, _, found => by
      simp only [lookupAll] at found
      split at found
      · exact nomatch found
      · rename_i t x located
        split at found
        · exact nomatch found
        · rename_i items xs others
          cases found
          simp only [HList.names, name_of_lookup located, names_of_lookupAll others]

end

section
variable {D : Dialect} {Raw Who : Type} (rules : Rules D Raw Who)

/-! ## Erased, then elaborated -/

/-- The erased arms of a case analysis are one per alternative. -/
theorem length_eraseArms (printOp : ∀ {ins res : List D.Ty}, D.Op ins res → Raw)
    (printWho : D.Who → Who) :
    ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads),
      (eraseArms printOp printWho arms).length = payloads.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ _ rest => congrArg (· + 1) (length_eraseArms printOp printWho rest)

/-- How often a loop runs, erased, elaborates to itself. -/
theorem elabTimes_erase (definition : Key) (w : D.Who) {Γ : Ctx D.Ty}
    (blocks : List (Key × Nat)) (key : Key) : ∀ (times : Times D w Γ),
      elabTimes rules definition w Γ blocks key (eraseTimes times) = .ok times
  | .fixed _ => rfl
  | .value count ok => by
      simp only [eraseTimes, elabTimes, lookup_var, Decidable.eq_isTrue (rules.count w _) ok]

/-- An erased region of an instruction, written with the names of its inputs, elaborates as
its term in the context extended by them, when its body does. -/
theorem elabRegion_erase {Γ : Ctx D.Ty} {outs : List D.Ty} (definition : Key)
    (blocks : List (Key × Nat)) (key : Key) (ins : List D.Ty) (inputs : Names ins)
    (t : Term D (Γ.extend inputs) outs)
    (body : elabBody rules definition (Γ.extend inputs) blocks (some key)
      (eraseBody rules.printOp rules.printWho t).1 (eraseBody rules.printOp rules.printWho t).2 =
        .ok ⟨outs, t⟩) :
    elabRegion rules definition Γ blocks key ins
      (.mk inputs.toList (eraseBody rules.printOp rules.printWho t).1
        (eraseBody rules.printOp rules.printWho t).2) = .ok ⟨outs, inputs, t⟩ := by
  simp only [elabRegion, Names.ofList_toList, body]

/-- An erased region without inputs elaborates as its term in the context around it, when its
body does. -/
theorem elabClosed_erase {Γ : Ctx D.Ty} {outs : List D.Ty} (definition : Key)
    (blocks : List (Key × Nat)) (key : Key) (t : Term D Γ outs)
    (body : elabBody rules definition Γ blocks (some key)
      (eraseBody rules.printOp rules.printWho t).1 (eraseBody rules.printOp rules.printWho t).2 =
        .ok ⟨outs, t⟩) :
    elabClosed rules definition Γ blocks key
      (.mk [] (eraseBody rules.printOp rules.printWho t).1
        (eraseBody rules.printOp rules.printWho t).2) = .ok ⟨outs, t⟩ := by
  simp only [elabClosed, body]

mutual
  /-- For lawful rules, the erased form of a term whose case analyses without an arm give
  nothing elaborates, in its context, to the term. -/
  theorem elabBody_erase (lawful : rules.Lawful) (definition : Key) :
      ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs), t.armed = true →
      ∀ (blocks : List (Key × Nat)) (owner : Option Key),
        elabBody rules definition Γ blocks owner
          (eraseBody rules.printOp rules.printWho t).1
          (eraseBody rules.printOp rules.printWho t).2 = .ok ⟨outs, t⟩
    | _, _, .ret xs, _, blocks, owner => by
        simp only [eraseBody, elabBody, lookupAll_names]
    | _, _, .op key o args results rest, armed, blocks, owner => by
        have ih := elabBody_erase lawful definition rest armed blocks none
        simp only [eraseBody, elabBody, lookupAll_names, lawful.op, Names.ofList_toList, ih]
    | _, _, .guard key w c ok why rest, armed, blocks, owner => by
        have ih := elabBody_erase lawful definition rest armed blocks none
        simp only [eraseBody, elabBody, lawful.who, lookup_var,
          Decidable.eq_isTrue (rules.condition w _) ok, ih]
    | _, _, .choose (mid := mid) key w c ok gives onTrue onFalse results rest, armed, blocks,
        owner => by
        simp only [Term.armed, Bool.and_eq_true] at armed
        have yes := elabClosed_erase rules definition blocks key onTrue
          (elabBody_erase lawful definition onTrue armed.1.1 blocks (some key))
        have no := elabClosed_erase rules definition blocks key onFalse
          (elabBody_erase lawful definition onFalse armed.1.2 blocks (some key))
        have ih := elabBody_erase lawful definition rest armed.2 blocks none
        simp only [eraseBody, elabBody, lawful.who, lookup_var,
          Decidable.eq_isTrue (rules.condition w _) ok, yes, no,
          Decidable.eq_isTrue (rules.sameTys mid mid) rfl,
          Decidable.eq_isTrue (decideAll (D.Gives w) (rules.gives w) mid) gives,
          Names.ofList_toList, ih, cast_eq]
    | _, _, .cases (mid := mid) (payloads := payloads) key w x ok gives arms results rest, armed,
        blocks, owner => by
        simp only [Term.armed, Bool.and_eq_true] at armed
        obtain ⟨found, alternatives⟩ := lawful.alternatives w _ payloads ok
        have elaborated := elabCases_erase lawful definition arms armed.1.1 armed.1.2 blocks key
        have ih := elabBody_erase lawful definition rest armed.2 blocks none
        simp only [eraseBody, elabBody, lawful.who, lookup_var, alternatives,
          length_eraseArms, ↓reduceIte, elaborated,
          Decidable.eq_isTrue (decideAll (D.Gives w) (rules.gives w) mid) gives,
          Names.ofList_toList, ih]
    | _, _, .loop (carried := carried) (each := each) key w times gives init inputs body results
        rest, armed, blocks, owner => by
        simp only [Term.armed, Bool.and_eq_true] at armed
        have inside := elabRegion_erase rules definition blocks key (D.index w :: carried) inputs
          body (elabBody_erase lawful definition body armed.1 blocks (some key))
        have ih := elabBody_erase lawful definition rest armed.2 blocks none
        simp only [eraseBody, elabBody, lawful.who, lookupAll_names,
          elabTimes_erase rules definition, inside,
          @splitPrefix_append _ rules.sameTy, cast_eq,
          Decidable.eq_isTrue (decideAll (D.Gives w) (rules.gives w) (carried ++ each)) gives,
          Names.ofList_toList, ih]
    | _, _, .block (mid := mid) key number body results rest, armed, blocks, owner => by
        simp only [Term.armed, Bool.and_eq_true] at armed
        have inside := elabClosed_erase rules definition (blocks ++ [(key, number)]) key body
          (elabBody_erase lawful definition body armed.1 (blocks ++ [(key, number)]) (some key))
        have ih := elabBody_erase lawful definition rest armed.2 blocks none
        simp only [eraseBody, elabBody, inside, Names.ofList_toList, ih]
    | _, _, .attempt (mid := mid) key w owns inputs body results rest, armed, blocks, owner => by
        simp only [Term.armed, Bool.and_eq_true] at armed
        have inside := elabRegion_erase rules definition blocks key [D.index w] inputs body
          (elabBody_erase lawful definition body armed.1 blocks (some key))
        have ih := elabBody_erase lawful definition rest armed.2 blocks none
        simp only [eraseBody, elabBody, lawful.who,
          Decidable.eq_isTrue (rules.attempt w) owns, inside, Names.ofList_toList, ih]
  /-- The erased arms of a case analysis elaborate as its arms, with what the first gives. -/
  theorem elabCases_erase (lawful : rules.Lawful) (definition : Key) :
      ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads),
      (arms.hasArm || mid.isEmpty) = true → Arms.armed arms = true →
      ∀ (blocks : List (Key × Nat)) (key : Key),
        elabCases rules definition Γ blocks key payloads
          (eraseArms rules.printOp rules.printWho arms) = .ok ⟨mid, arms⟩
    | _, [], _, .nil, _, _, blocks, key => rfl
    | _, _ :: _, _, .nil, given, _, blocks, key => by simp [Arms.hasArm] at given
    | Γ, _, _, .cons (payload := payload) inputs arm rest, _, armed, blocks, key => by
        simp only [Arms.armed, Bool.and_eq_true] at armed
        have first := elabRegion_erase rules (Γ := Γ) definition blocks key [payload] inputs arm
          (elabBody_erase lawful definition arm armed.1 blocks (some key))
        have others := elabArms_erase lawful definition rest armed.2 blocks key
        simp only [eraseArms, elabCases, first, others]
  /-- The erased arms of a case analysis after the first elaborate as its arms. -/
  theorem elabArms_erase (lawful : rules.Lawful) (definition : Key) :
      ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads),
      Arms.armed arms = true → ∀ (blocks : List (Key × Nat)) (key : Key),
        elabArms rules definition Γ blocks key mid payloads
          (eraseArms rules.printOp rules.printWho arms) = .ok arms
    | _, _, _, .nil, _, blocks, key => rfl
    | Γ, mid, _, .cons (payload := payload) inputs arm rest, armed, blocks, key => by
        simp only [Arms.armed, Bool.and_eq_true] at armed
        have first := elabRegion_erase rules (Γ := Γ) definition blocks key [payload] inputs arm
          (elabBody_erase lawful definition arm armed.1 blocks (some key))
        have others := elabArms_erase lawful definition rest armed.2 blocks key
        simp only [eraseArms, elabArms, first, others,
          Decidable.eq_isTrue (rules.sameTys mid mid) rfl, cast_eq]
end

/-! ## Elaborated, then erased -/

/-- How often a loop runs, as elaborated, erases to the `Repeat` that was read. -/
theorem eraseTimes_elab (definition : Key) (w : D.Who) {Γ : Ctx D.Ty}
    (blocks : List (Key × Nat)) (key : Key) : ∀ (written : Repeat) (times : Times D w Γ),
      elabTimes rules definition w Γ blocks key written = .ok times → eraseTimes times = written
  | .fixed _, _, found => by
      simp only [elabTimes] at found
      cases found
      rfl
  | .count _, _, found => by
      simp only [elabTimes] at found
      split at found
      · contradiction
      · rename_i t count located
        split at found
        · cases found
          simp only [eraseTimes, name_of_lookup located]
        · contradiction

mutual
  /-- For rules with canonical written forms, a term that elaboration gives erases to the
  instructions and the exit that were elaborated. -/
  theorem eraseBody_elab (canonical : rules.Canonical) (definition : Key) :
      ∀ (body : List (Instruction Raw Who)) (exit : List Name) {Γ : Ctx D.Ty}
        (blocks : List (Key × Nat)) (owner : Option Key) {outs : List D.Ty} (t : Term D Γ outs),
        elabBody rules definition Γ blocks owner body exit = .ok ⟨outs, t⟩ →
        eraseBody rules.printOp rules.printWho t = (body, exit)
    | [], exit, Γ, blocks, owner, outs, t, h => by
        simp only [elabBody] at h
        split at h
        · contradiction
        · rename_i outs' xs found
          cases h
          simp only [eraseBody, names_of_lookupAll found]
    | .op key results raw operands :: rest, exit, Γ, blocks, owner, outs, t, h => by
        simp only [elabBody] at h
        split at h
        · contradiction
        · rename_i ins args found
          split at h
          · contradiction
          · rename_i res o read
            split at h
            · contradiction
            · rename_i bound named
              split at h
              · contradiction
              · rename_i outs' t' elaborated
                cases h
                simp only [eraseBody,
                  eraseBody_elab canonical definition rest exit blocks none t' elaborated,
                  canonical.op raw o read, Names.toList_of_ofList res results bound named,
                  names_of_lookupAll found]
    | .guard key who condition why :: rest, exit, Γ, blocks, owner, outs, t, h => by
        simp only [elabBody] at h
        split at h
        · contradiction
        · rename_i w read
          split at h
          · contradiction
          · rename_i ty c found
            split at h
            · contradiction
            · rename_i ok decided
              split at h
              · contradiction
              · rename_i outs' t' elaborated
                cases h
                simp only [eraseBody, eraseBody_elab canonical definition rest exit blocks none t'
                    elaborated, canonical.who who w read, name_of_lookup found]
    | .choose key who condition results onTrue onFalse :: rest, exit, Γ, blocks, owner, outs, t,
        h => by
        simp only [elabBody] at h
        split at h
        · contradiction
        · rename_i w read
          split at h
          · contradiction
          · rename_i ty c found
            split at h
            · contradiction
            · rename_i ok decided
              split at h
              · contradiction
              · rename_i mid yes yesFound
                split at h
                · contradiction
                · rename_i mid' no noFound
                  split at h
                  · contradiction
                  · rename_i same sameFound
                    split at h
                    · contradiction
                    · rename_i gives givesFound
                      split at h
                      · contradiction
                      · rename_i bound named
                        split at h
                        · contradiction
                        · rename_i outs' t' elaborated
                          have yesRegion := eraseClosed_elab canonical definition onTrue blocks key
                            yes yesFound
                          have noRegion := eraseClosed_elab canonical definition onFalse blocks key
                            no noFound
                          have equal : mid' = mid := same
                          subst equal
                          cases h
                          subst yesRegion
                          subst noRegion
                          simp only [eraseBody, cast_eq,
                            eraseBody_elab canonical definition rest exit blocks none t' elaborated,
                            canonical.who who w read, name_of_lookup found,
                            Names.toList_of_ofList _ results bound named]
    | .cases key who subject results arms :: rest, exit, Γ, blocks, owner, outs, t, h => by
        simp only [elabBody] at h
        split at h
        · contradiction
        · rename_i w read
          split at h
          · contradiction
          · rename_i ty x found
            split at h
            · contradiction
            · rename_i payloads ok alternatives
              split at h
              · split at h
                · contradiction
                · rename_i mid elaborated elaboratedFound
                  split at h
                  · contradiction
                  · rename_i gives givesFound
                    split at h
                    · contradiction
                    · rename_i bound named
                      split at h
                      · contradiction
                      · rename_i outs' t' restFound
                        cases h
                        simp only [eraseBody,
                          eraseBody_elab canonical definition rest exit blocks none t' restFound,
                          canonical.who who w read, name_of_lookup found,
                          Names.toList_of_ofList _ results bound named,
                          eraseArms_elabCases canonical definition arms blocks key payloads
                            elaborated elaboratedFound]
              · contradiction
    | .loop key who written carried results body :: rest, exit, Γ, blocks, owner, outs, t, h => by
        simp only [elabBody] at h
        split at h
        · contradiction
        · rename_i w read
          split at h
          · contradiction
          · rename_i carriedTys init initFound
            split at h
            · contradiction
            · rename_i times timesFound
              split at h
              · contradiction
              · rename_i bodyOuts inputs b bodyFound
                split at h
                · contradiction
                · rename_i each split splitFound
                  split at h
                  · contradiction
                  · rename_i gives givesFound
                    split at h
                    · contradiction
                    · rename_i bound named
                      split at h
                      · contradiction
                      · rename_i outs' t' restFound
                        have region := eraseRegion_elab canonical definition body blocks key _
                          inputs b bodyFound
                        subst split
                        cases h
                        subst region
                        simp only [eraseBody, cast_eq,
                          eraseBody_elab canonical definition rest exit blocks none t' restFound,
                          canonical.who who w read, names_of_lookupAll initFound,
                          eraseTimes_elab rules definition w blocks key written times timesFound,
                          Names.toList_of_ofList _ results bound named]
    | .block key number results body :: rest, exit, Γ, blocks, owner, outs, t, h => by
        simp only [elabBody] at h
        split at h
        · contradiction
        · rename_i mid b bodyFound
          split at h
          · contradiction
          · rename_i bound named
            split at h
            · contradiction
            · rename_i outs' t' restFound
              have region := eraseClosed_elab canonical definition body (blocks ++ [(key, number)])
                key b bodyFound
              cases h
              subst region
              simp only [eraseBody,
                eraseBody_elab canonical definition rest exit blocks none t' restFound,
                Names.toList_of_ofList _ results bound named]
    | .attempt key who results body :: rest, exit, Γ, blocks, owner, outs, t, h => by
        simp only [elabBody] at h
        split at h
        · contradiction
        · rename_i w read
          split at h
          · contradiction
          · rename_i owns ownsFound
            split at h
            · contradiction
            · rename_i mid inputs b bodyFound
              split at h
              · contradiction
              · rename_i bound named
                split at h
                · contradiction
                · rename_i outs' t' restFound
                  have region := eraseRegion_elab canonical definition body blocks key _ inputs b
                    bodyFound
                  cases h
                  subst region
                  simp only [eraseBody,
                    eraseBody_elab canonical definition rest exit blocks none t' restFound,
                    canonical.who who w read, Names.toList_of_ofList _ results bound named]
  /-- A region that elaborates is its input names with the erased form of its term. -/
  theorem eraseRegion_elab (canonical : rules.Canonical) (definition : Key) :
      ∀ (region : Region Raw Who) {Γ : Ctx D.Ty} (blocks : List (Key × Nat)) (key : Key)
        (ins : List D.Ty) {outs : List D.Ty} (inputs : Names ins)
        (t : Term D (Γ.extend inputs) outs),
        elabRegion rules definition Γ blocks key ins region = .ok ⟨outs, inputs, t⟩ →
        region = .mk inputs.toList (eraseBody rules.printOp rules.printWho t).1
          (eraseBody rules.printOp rules.printWho t).2
    | .mk names body exit, Γ, blocks, key, ins, outs, inputs, t, h => by
        simp only [elabRegion] at h
        split at h
        · contradiction
        · rename_i bound named
          split at h
          · contradiction
          · rename_i outs' t' found
            have erased := eraseBody_elab canonical definition body exit blocks (some key) t' found
            have written := Names.toList_of_ofList ins names bound named
            cases h
            simp only [erased, written]
  /-- A region without inputs that elaborates is the erased form of its term, with no input. -/
  theorem eraseClosed_elab (canonical : rules.Canonical) (definition : Key) :
      ∀ (region : Region Raw Who) {Γ : Ctx D.Ty} (blocks : List (Key × Nat)) (key : Key)
        {outs : List D.Ty} (t : Term D Γ outs),
        elabClosed rules definition Γ blocks key region = .ok ⟨outs, t⟩ →
        region = .mk [] (eraseBody rules.printOp rules.printWho t).1
          (eraseBody rules.printOp rules.printWho t).2
    | .mk [] body exit, Γ, blocks, key, outs, t, h => by
        simp only [elabClosed] at h
        have erased := eraseBody_elab canonical definition body exit blocks (some key) t h
        simp only [erased]
    | .mk (_ :: _) _ _, Γ, blocks, key, outs, t, h => by
        simp only [elabClosed] at h
        contradiction
  /-- The arms that a case analysis elaborates to erase to its regions. -/
  theorem eraseArms_elabCases (canonical : rules.Canonical) (definition : Key) :
      ∀ (regions : List (Region Raw Who)) {Γ : Ctx D.Ty} (blocks : List (Key × Nat)) (key : Key)
        (payloads : List D.Ty) {mid : List D.Ty} (arms : Arms D Γ mid payloads),
        elabCases rules definition Γ blocks key payloads regions = .ok ⟨mid, arms⟩ →
        eraseArms rules.printOp rules.printWho arms = regions
    | [], Γ, blocks, key, [], mid, arms, h => by
        simp only [elabCases] at h
        cases h
        rfl
    | [], Γ, blocks, key, _ :: _, mid, arms, h => by
        simp [elabCases] at h
    | _ :: _, Γ, blocks, key, [], mid, arms, h => by
        simp [elabCases] at h
    | region :: regions, Γ, blocks, key, payload :: payloads, mid, arms, h => by
        simp only [elabCases] at h
        split at h
        · contradiction
        · rename_i mid' inputs first firstFound
          split at h
          · contradiction
          · rename_i others othersFound
            have erased := eraseRegion_elab canonical definition region blocks key [payload] inputs
              first firstFound
            have rest := eraseArms_elabArms canonical definition regions blocks key mid' payloads
              others othersFound
            cases h
            subst erased
            simp only [eraseArms, rest]
  /-- The arms after the first that a case analysis elaborates to erase to their regions. -/
  theorem eraseArms_elabArms (canonical : rules.Canonical) (definition : Key) :
      ∀ (regions : List (Region Raw Who)) {Γ : Ctx D.Ty} (blocks : List (Key × Nat)) (key : Key)
        (mid payloads : List D.Ty) (arms : Arms D Γ mid payloads),
        elabArms rules definition Γ blocks key mid payloads regions = .ok arms →
        eraseArms rules.printOp rules.printWho arms = regions
    | [], Γ, blocks, key, mid, [], arms, h => by
        simp only [elabArms] at h
        cases h
        rfl
    | [], Γ, blocks, key, mid, _ :: _, arms, h => by
        simp [elabArms] at h
    | _ :: _, Γ, blocks, key, mid, [], arms, h => by
        simp [elabArms] at h
    | region :: regions, Γ, blocks, key, mid, payload :: payloads, arms, h => by
        simp only [elabArms] at h
        split at h
        · contradiction
        · rename_i mid' inputs a found
          split at h
          · contradiction
          · rename_i same sameFound
            split at h
            · contradiction
            · rename_i others othersFound
              have erased := eraseRegion_elab canonical definition region blocks key [payload]
                inputs a found
              have rest := eraseArms_elabArms canonical definition regions blocks key mid payloads
                others othersFound
              have equal : mid' = mid := same
              subst equal
              cases h
              subst erased
              simp only [eraseArms, cast_eq, rest]
end

end

end Zkc.Core
