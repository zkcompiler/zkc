module

public import Zkc.Core.ThreadTogether

public section

/-! The refinement of a threading step for a side that holds both transcript roles, for a
region.

`threadRegion_refines`: for a side that holds the prover and the verifier of a definition,
a rule whose emitted operations run as its meaning (`RuleSound`) and whose meaning keeps the
two threaded values coupled without an effect (`RuleCouples`), and callees whose images
refine (`CalleesRefine`): the image of a region under `threadRegion`, in an environment that
holds a coupled state, refines the region, and its results are the region's results after a
coupled state. The proof is the structural induction of `threadRegion_meaning`, one case per
operation form:

- an exchange from the prover to the verifier is internal on both sides: the old process
  hands the prover's value to the verifier, and so does the rule's meaning, which performs no
  effect from a coupled state;
- a draw between the two is one `draw` effect of the old process, every reply to which is
  allowed, and the coin that both roles derive in the new one;
- local work, every other exchange and draw and every sample is the same process on both
  sides;
- a `repeat` or `choose` whose regions contain a rewritten operation carries the two values,
  and its regions refine the old regions from every coupled state (the induction
  hypothesis); otherwise its regions are copies, which have the old meaning;
- an `apply` of an image that threads refines the callee (`CalleesRefine`); an `apply` of the
  image with the callee's own header is the callee.

The theorem is generic in the rule. It does not ask that the functions perform no effect: a
local operation is the same process in the region and in its image.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Core

open Zkc.Source

section Region

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {old new : List ProtocolHeader} {deployed : Bool} {t : Threads}
  {rule : Rule t operations functions} {sem : RuleMeaning model t operations}
  {functionTable : FunctionTable model functions} {oldTable : ProtocolTable model old}
  {newTable : ProtocolTable model new} {table : CalleeTable t.header old new} {place : Place}
  {side : Side} {label : Nat → Site}
  {coupled : model.Value t.prover → model.Value t.verifier → Prop}
  {isProver : side place.roles.prover = true} {isVerifier : side place.roles.verifier = true}

/-- The statement for one region: every image of the region under `threadRegion`, in an
environment that holds a coupled state, refines the region and returns its results after a
coupled state. -/
@[expose] def RegionRefines (t : Threads) (rule : Rule t operations functions)
    (functionTable : FunctionTable model functions) (oldTable : ProtocolTable model old)
    (newTable : ProtocolTable model new) (table : CalleeTable t.header old new) (place : Place)
    (side : Side) (label : Nat → Site)
    (coupled : model.Value t.prover → model.Value t.verifier → Prop)
    (isProver : side place.roles.prover = true) (isVerifier : side place.roles.verifier = true)
    {Γ out : List Located}
    (region : Region (ProtocolDialect operations functions old deployed) Γ out) : Prop :=
  ∀ {Δ : List Located} (rename : Renaming Γ Δ) (first : Var Δ (t.first place.roles))
    (second : Var Δ (t.second place.roles))
    (image : Region (ProtocolDialect operations functions new deployed) Δ
      (t.states place.roles ++ out)),
    threadRegion t rule table place region rename first second = .ok image →
    ∀ (env : Environment (SideValue model side) Γ) (env' : Environment (SideValue model side) Δ),
      rename.Agrees env env' →
      CoupledState coupled isProver isVerifier (env' first, env' second) →
      Refines (CoupledImage coupled isProver isVerifier (threadedValues (roles := place.roles)))
        (region.denote (labelledMeaning model label functionTable oldTable side) env)
        (image.denote (labelledMeaning model label functionTable newTable side) env')

local notation "Refines[" region "]" =>
  RegionRefines t rule functionTable oldTable newTable table place side label coupled isProver
    isVerifier region

/-- A step that the step leaves as it is: one process on both sides. `passed` is the old
operation's process and `copy` the new one's. -/
theorem same_step {Γ Δ out results : List Located}
    {rest : Region (ProtocolDialect operations functions old deployed) (bindAll Γ results) out}
    (ihRest : Refines[rest])
    {rename : Renaming Γ Δ} {first : Var Δ (t.first place.roles)}
    {second : Var Δ (t.second place.roles)}
    {rest' : Region (ProtocolDialect operations functions new deployed) (bindAll Δ results)
      (t.states place.roles ++ out)}
    (threadsRest : threadRegion t rule table place rest (rename.keepAll results)
      (first.weaken results) (second.weaken results) = .ok rest')
    {env : Environment (SideValue model side) Γ} {env' : Environment (SideValue model side) Δ}
    (agrees : rename.Agrees env env')
    (holds : CoupledState coupled isProver isVerifier (env' first, env' second))
    (passed copy : PIR.Process (Effects model) (Values (SideValue model side) results))
    (same : copy = passed) :
    Refines (CoupledImage coupled isProver isVerifier (threadedValues (roles := place.roles)))
      (passed.bind fun values =>
        rest.denote (labelledMeaning model label functionTable oldTable side)
          (Environment.bindAll env values))
      (copy.bind fun values =>
        rest'.denote (labelledMeaning model label functionTable newTable side)
          (Environment.bindAll env' values)) := by
  subst same
  refine Refines.bind_same _ fun values => ?_
  exact ihRest _ _ _ rest' threadsRest (Environment.bindAll env values)
    (Environment.bindAll env' values) (agrees.keepAll values)
    (holds.of_eq (Environment.bindAll_weaken env' values first)
      (Environment.bindAll_weaken env' values second))

theorem ret_refines {Γ out : List Located} (values : Operands Γ out) :
    Refines[(Region.ret values : Region (ProtocolDialect operations functions old deployed) Γ out)] := by
  intro Δ rename first second image threads env env' agrees holds
  simp only [threadRegion, Except.ok.injEq] at threads
  subst threads
  exact Refines.done ⟨(env' first, env' second), holds,
    cons_congr rfl (cons_congr rfl (agrees.operands values))⟩

theorem stop_refines {Γ out : List Located} (reason : PIR.Stop) :
    Refines[(Region.stop reason : Region (ProtocolDialect operations functions old deployed) Γ out)] := by
  intro Δ rename first second image threads env env' agrees holds
  exact Refines.halt _ _

theorem bind_refines {Γ mid out : List Located}
    {body : Region (ProtocolDialect operations functions old deployed) Γ mid}
    {rest : Region (ProtocolDialect operations functions old deployed) (bindAll Γ mid) out}
    (ihBody : Refines[body]) (ihRest : Refines[rest]) : Refines[Region.bind body rest] := by
  intro Δ rename first second image threads env env' agrees holds
  unfold threadRegion at threads
  dsimp only at threads
  split at threads
  · rename_i body' rest' threadsBody threadsRest
    simp only [Except.ok.injEq] at threads
    subst threads
    refine Refines.step (threadedValues (roles := place.roles))
      (threadedValues (roles := place.roles))
      (ihBody rename first second body' threadsBody env env' agrees holds) ?_
    intro values state coupledState
    have next := afterTwo_agrees agrees (t.first place.roles) (t.second place.roles)
      state.1 state.2 values
    exact ihRest _ _ _ rest' threadsRest _ _ next.1 (coupledState.of_eq next.2.1 next.2.2)
  · cases threads
  · cases threads

theorem at_refines {Γ out : List Located} {role : Nat}
    {op : LocalOp operations functions deployed}
    {bodies : Regions (LocalDialect operations functions deployed) op.regions}
    {arguments : Operands Γ (Located.atRole role op.arguments)}
    {rest : Region (ProtocolDialect operations functions old deployed)
      (bindAll Γ (Located.atRole role op.results)) out}
    (ihRest : Refines[rest]) :
    Refines[Region.letOp (dialect := ProtocolDialect operations functions old deployed)
      (.at role op bodies) arguments .nil rest] := by
  intro Δ rename first second image threads env env' agrees holds
  unfold threadRegion at threads
  split at threads
  · rename_i rest' threadsRest
    simp only [Except.ok.injEq] at threads
    subst threads
    refine same_step ihRest threadsRest agrees holds
      (labelledOperation model label functionTable oldTable side (.at role op bodies)
        (Operands.eval env arguments) .nil) _ ?_
    show labelledOperation model label functionTable newTable side (.at role op bodies)
        (Operands.eval env' (rename.operands arguments)) .nil = _
    rw [agrees.operands]
    rfl
  · cases threads

theorem sample_refines {Γ out : List Located} {owner site : Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩} {populated : output.populated = true}
    {arguments : Operands Γ (Located.atRole owner inputs)}
    {rest : Region (ProtocolDialect operations functions old deployed)
      (bindAll Γ [⟨output, owner⟩]) out}
    (ihRest : Refines[rest]) :
    Refines[Region.letOp (dialect := ProtocolDialect operations functions old deployed)
      (.sample owner site law populated) arguments .nil rest] := by
  intro Δ rename first second image threads env env' agrees holds
  unfold threadRegion at threads
  split at threads
  · rename_i rest' threadsRest
    simp only [Except.ok.injEq] at threads
    subst threads
    refine same_step ihRest threadsRest agrees holds
      (labelledOperation model label functionTable oldTable side (.sample owner site law populated)
        (Operands.eval env arguments) .nil) _ ?_
    show labelledOperation model label functionTable newTable side (.sample owner site law populated)
        (Operands.eval env' (rename.operands arguments)) .nil = _
    rw [agrees.operands]
    rfl
  · cases threads

theorem exchange_refines (sound : RuleSound rule sem functionTable)
    (couples : RuleCouples rule sem coupled) {Γ out : List Located}
    {sender receiver site : Nat} {type : Ty} {arguments : Operands Γ [⟨type, sender⟩]}
    {rest : Region (ProtocolDialect operations functions old deployed)
      (bindAll Γ [⟨type, receiver⟩]) out}
    (ihRest : Refines[rest]) :
    Refines[Region.letOp (dialect := ProtocolDialect operations functions old deployed)
      (.exchange sender receiver site type) arguments .nil rest] := by
  intro Δ rename first second image threads env env' agrees holds
  by_cases between : sender = place.roles.prover ∧ receiver = place.roles.verifier
  · obtain ⟨rfl, rfl⟩ := between
    unfold threadRegion at threads
    split at threads
    · rename_i emitted rewritten
      have emits := rewrittenExchange_ok rewritten
      split at threads
      · rename_i rest' threadsRest
        simp only [Except.ok.injEq] at threads
        subst threads
        obtain ⟨later, runs, kept⟩ := sound.exchange newTable label side place site type _
          first second emitted emits env'
        obtain ⟨next, acts, coupledNext⟩ := couples.exchange_at emits isProver isVerifier
          (label site) (env' (rename.rename (arguments.get .here))) (env' first, env' second) holds
        have value : (Operands.eval env arguments).get .here =
            env' (rename.rename (arguments.get .here)) :=
          (Operands.get_eval env arguments .here).trans (agrees (arguments.get .here)).symm
        -- The verifier's value on both sides: the prover's.
        obtain ⟨received, stateFirst, stateSecond, keeps⟩ := kept
          (Held.of (side place.roles.verifier)
            (Held.value (side place.roles.prover) isProver
              (env' (rename.rename (arguments.get .here)))), next)
        have oldRuns : (Region.letOp (dialect := ProtocolDialect operations functions old deployed)
              (.exchange place.roles.prover place.roles.verifier site type) arguments .nil
              rest).denote (labelledMeaning model label functionTable oldTable side) env =
            rest.denote (labelledMeaning model label functionTable oldTable side)
              (Environment.push env
                (Held.of (side place.roles.verifier)
                  (Held.value (side place.roles.prover) isProver
                    (env' (rename.rename (arguments.get .here)))))) := by
          show ((exchangeStep model (label site) type (side place.roles.prover)
              (side place.roles.verifier) ((Operands.eval env arguments).get .here)).bind _).bind _ = _
          rw [exchangeStep_internal model type _ _ isProver isVerifier, value]
          rfl
        refine Refines.of_eq oldRuns ((runs rest').trans (by rw [acts])) ?_
        exact ihRest _ _ _ rest' threadsRest _ (later _)
          (Renaming.Agrees.to (agrees.extend emitted.grows (later _) keeps) _ _ received)
          (coupledNext.of_eq stateFirst stateSecond)
      · cases threads
    · cases threads
    · rename_i missing
      exact absurd missing rewrittenExchange_some
  · unfold threadRegion at threads
    split at threads
    · rename_i emitted rewritten
      exact absurd (rewrittenExchange_between rewritten) between
    · rename_i refusal rewritten
      exact absurd (rewrittenExchange_between rewritten) between
    · split at threads
      · rename_i rest' threadsRest
        simp only [Except.ok.injEq] at threads
        subst threads
        refine same_step ihRest threadsRest agrees holds
          (labelledOperation model label functionTable oldTable side
            (.exchange sender receiver site type) (Operands.eval env arguments) .nil) _ ?_
        show labelledOperation model label functionTable newTable side
            (.exchange sender receiver site type)
            (Operands.eval env' (rename.operands arguments)) .nil = _
        rw [agrees.operands]
        rfl
      · cases threads

theorem draw_refines (sound : RuleSound rule sem functionTable)
    (couples : RuleCouples rule sem coupled) {Γ out : List Located}
    {owner site : Nat} {receivers : List Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩} {populated : output.populated = true}
    {arguments : Operands Γ (Located.atRole owner inputs)}
    {rest : Region (ProtocolDialect operations functions old deployed)
      (bindAll Γ (⟨output, owner⟩ :: Located.ofRoles output receivers)) out}
    (ihRest : Refines[rest]) :
    Refines[Region.letOp (dialect := ProtocolDialect operations functions old deployed)
      (.draw owner receivers site law populated) arguments .nil rest] := by
  intro Δ rename first second image threads env env' agrees holds
  -- A draw that the step leaves as it is.
  have plain : ∀ rest', threadRegion t rule table place rest
        (rename.keepAll (⟨output, owner⟩ :: Located.ofRoles output receivers))
        (first.weaken _) (second.weaken _) = .ok rest' →
      Refines (CoupledImage coupled isProver isVerifier (threadedValues (roles := place.roles)))
        ((Region.letOp (dialect := ProtocolDialect operations functions old deployed)
          (.draw owner receivers site law populated) arguments .nil rest).denote
          (labelledMeaning model label functionTable oldTable side) env)
        ((Region.letOp (dialect := ProtocolDialect operations functions new deployed)
          (.draw owner receivers site law populated) (rename.operands arguments) .nil rest').denote
          (labelledMeaning model label functionTable newTable side) env') := by
    intro rest' threadsRest
    refine same_step ihRest threadsRest agrees holds
      (labelledOperation model label functionTable oldTable side (.draw owner receivers site law populated)
        (Operands.eval env arguments) .nil) _ ?_
    show labelledOperation model label functionTable newTable side (.draw owner receivers site law populated)
        (Operands.eval env' (rename.operands arguments)) .nil = _
    rw [agrees.operands]
    rfl
  cases receivers with
  | nil =>
      unfold threadRegion at threads
      split at threads
      · rename_i rest' threadsRest
        have same := Except.ok.inj threads
        subst same
        exact plain rest' threadsRest
      · cases threads
  | cons receiver others =>
      cases others with
      | cons another more =>
          unfold threadRegion at threads
          split at threads
          · rename_i rest' threadsRest
            have same := Except.ok.inj threads
            subst same
            exact plain rest' threadsRest
          · cases threads
      | nil =>
          by_cases byVerifier : owner = place.roles.verifier ∧ receiver = place.roles.prover
          · obtain ⟨rfl, rfl⟩ := byVerifier
            unfold threadRegion at threads
            split at threads
            · rename_i emitted rewritten
              obtain ⟨raw, emits, rfl⟩ := rewrittenDraw_verifier_ok rewritten
              split at threads
              · rename_i rest' threadsRest
                have same := Except.ok.inj threads
                subst same
                obtain ⟨later, runs, kept⟩ := sound.draw newTable label side place site law first
                  second raw emits env'
                obtain ⟨coin, next, acts, coupledNext⟩ := couples.draw_at emits isProver
                  isVerifier (label site) (env' first, env' second) holds
                have continues : ∀ (result : (SideValue model side ⟨output, place.roles.prover⟩ ×
                      SideValue model side ⟨output, place.roles.verifier⟩) ×
                    ThreadState model t (side place.roles.prover) (side place.roles.verifier)),
                    CoupledState coupled isProver isVerifier result.2 →
                    Refines
                      (CoupledImage coupled isProver isVerifier
                        (threadedValues (roles := place.roles)))
                      (rest.denote (labelledMeaning model label functionTable oldTable side)
                        (Environment.push (Environment.push env result.1.2) result.1.1))
                      (rest'.denote (labelledMeaning model label functionTable newTable side)
                        (later result)) := by
                  intro result coupledResult
                  obtain ⟨proverCoin, verifierCoin, stateFirst, stateSecond, keeps⟩ := kept result
                  exact ihRest _ _ _ rest' threadsRest
                    (Environment.push (Environment.push env result.1.2) result.1.1) (later result)
                    (Renaming.Agrees.to
                      (Renaming.Agrees.to (agrees.extend raw.grows (later result) keeps) _ result.1.2
                        verifierCoin) _ result.1.1 proverCoin)
                    (coupledResult.of_eq
                      ((congrArg (later result) ((tail_get _ _).trans (tail_get _ _))).trans
                        stateFirst)
                      ((congrArg (later result) ((tail_get _ _).trans (tail_get _ _))).trans
                        stateSecond))
                have oldRuns : (Region.letOp
                      (dialect := ProtocolDialect operations functions old deployed)
                      (.draw place.roles.verifier [place.roles.prover] site law populated) arguments
                      .nil rest).denote (labelledMeaning model label functionTable oldTable side) env =
                    .call (.draw (label site) (.of law populated)
                        (presentValues (side place.roles.verifier) isVerifier
                          (unmapValues _ _ (Operands.eval env arguments))))
                      fun reply => rest.denote (labelledMeaning model label functionTable oldTable side)
                        (Environment.bindAll env
                          (broadcast model side place.roles.verifier [place.roles.prover] output
                            reply)) := by
                  show (drawStep model (label site) (.of law populated) _ (side place.roles.verifier)
                    _ _).bind _ = _
                  rw [drawStep_owner model _ _ _ isVerifier]
                  rfl
                refine Refines.of_eq oldRuns
                  ((show (raw.wrap rest').denote
                      (labelledMeaning model label functionTable newTable side) env' = _ from
                    runs rest').trans (by rw [acts])) (Refines.draw coin ?_)
                exact continues
                  ((Held.of (side place.roles.prover) coin, Held.of (side place.roles.verifier) coin),
                    next) coupledNext
              · cases threads
            · cases threads
            · rename_i missing
              exact absurd missing rewrittenDraw_verifier_some
          · by_cases byProver : owner = place.roles.prover ∧ receiver = place.roles.verifier
            · obtain ⟨rfl, rfl⟩ := byProver
              unfold threadRegion at threads
              split at threads
              · rename_i emitted rewritten
                obtain ⟨raw, emits, rfl⟩ := rewrittenDraw_prover_ok byVerifier rewritten
                split at threads
                · rename_i rest' threadsRest
                  have same := Except.ok.inj threads
                  subst same
                  obtain ⟨later, runs, kept⟩ := sound.draw newTable label side place site law
                    first second raw emits env'
                  obtain ⟨coin, next, acts, coupledNext⟩ := couples.draw_at emits isProver
                    isVerifier (label site) (env' first, env' second) holds
                  have continues : ∀ (result : (SideValue model side ⟨output, place.roles.prover⟩ ×
                        SideValue model side ⟨output, place.roles.verifier⟩) ×
                      ThreadState model t (side place.roles.prover) (side place.roles.verifier)),
                      CoupledState coupled isProver isVerifier result.2 →
                      Refines
                        (CoupledImage coupled isProver isVerifier
                          (threadedValues (roles := place.roles)))
                        (rest.denote (labelledMeaning model label functionTable oldTable side)
                          (Environment.push (Environment.push env result.1.1) result.1.2))
                        (rest'.denote (labelledMeaning model label functionTable newTable side)
                          (later result)) := by
                    intro result coupledResult
                    obtain ⟨proverCoin, verifierCoin, stateFirst, stateSecond, keeps⟩ := kept result
                    exact ihRest _ _ _ rest' threadsRest
                      (Environment.push (Environment.push env result.1.1) result.1.2) (later result)
                      (Renaming.Agrees.to
                        (Renaming.Agrees.to (agrees.extend raw.grows (later result) keeps) _
                          result.1.1 proverCoin) _ result.1.2 verifierCoin)
                      (coupledResult.of_eq
                        ((congrArg (later result) ((tail_get _ _).trans (tail_get _ _))).trans
                          stateFirst)
                        ((congrArg (later result) ((tail_get _ _).trans (tail_get _ _))).trans
                          stateSecond))
                  have oldRuns : (Region.letOp
                        (dialect := ProtocolDialect operations functions old deployed)
                        (.draw place.roles.prover [place.roles.verifier] site law populated)
                        arguments .nil rest).denote
                        (labelledMeaning model label functionTable oldTable side) env =
                      .call (.draw (label site) (.of law populated)
                          (presentValues (side place.roles.prover) isProver
                            (unmapValues _ _ (Operands.eval env arguments))))
                        fun reply =>
                          rest.denote (labelledMeaning model label functionTable oldTable side)
                            (Environment.bindAll env
                              (broadcast model side place.roles.prover [place.roles.verifier] output
                                reply)) := by
                    show (drawStep model (label site) (.of law populated) _ (side place.roles.prover)
                      _ _).bind _ = _
                    rw [drawStep_owner model _ _ _ isProver]
                    rfl
                  refine Refines.of_eq oldRuns
                    ((show (raw.wrap rest').denote
                        (labelledMeaning model label functionTable newTable side) env' = _ from
                      runs rest').trans (by rw [acts])) (Refines.draw coin ?_)
                  exact continues
                    ((Held.of (side place.roles.prover) coin,
                      Held.of (side place.roles.verifier) coin), next) coupledNext
                · cases threads
              · cases threads
              · rename_i missing
                exact absurd missing rewrittenDraw_prover_some
            · unfold threadRegion at threads
              split at threads
              · rename_i emitted rewritten
                rcases rewrittenDraw_between rewritten with between | between
                · exact absurd between byVerifier
                · exact absurd between byProver
              · rename_i refusal rewritten
                rcases rewrittenDraw_between rewritten with between | between
                · exact absurd between byVerifier
                · exact absurd between byProver
              · split at threads
                · rename_i rest' threadsRest
                  have same := Except.ok.inj threads
                  subst same
                  exact plain rest' threadsRest
                · cases threads

theorem repeat_region_refines (callees : CalleesRefine coupled table oldTable newTable)
    {Γ out : List Located} {participants : List Nat} {count : RepeatCount}
    {carried collected captures : List Located}
    {covered : Located.heldBy participants collected = true}
    {arguments : Operands Γ (count.operands participants ++ (carried ++ captures))}
    {body : Region (ProtocolDialect operations functions old deployed)
      (bindAll [] (Located.ofRoles .nat participants ++ (carried ++ captures)))
      (collected ++ carried)}
    {rest : Region (ProtocolDialect operations functions old deployed)
      (bindAll Γ (collectedSequencesAt count.size collected ++ carried)) out}
    (ihBody : Refines[body]) (ihRest : Refines[rest]) :
    Refines[Region.letOp (dialect := ProtocolDialect operations functions old deployed)
      (.repeat participants count carried collected captures covered) arguments
      (.cons body .nil) rest] := by
  intro Δ rename first second image threads env env' agrees holds
  unfold threadRegion at threads
  dsimp only at threads
  split at threads
  · rename_i touched
    split at threads
    rename_i inner same
    obtain ⟨rfl⟩ : body = inner := by injection same
    split at threads
    · rename_i body' rest' threadsBody threadsRest
      have same := Except.ok.inj threads
      subst same
      -- The image of the loop's region: the threaded region, which refines the old region,
      -- with the two values returned after the collected ones.
      have region : ∀ (state : ThreadState model t (side place.roles.prover)
            (side place.roles.verifier))
          (numbers : Values (SideValue model side) (Located.ofRoles .nat participants))
          (values : Values (SideValue model side) (carried ++ captures)),
          CoupledState coupled isProver isVerifier state →
          Refines (CoupledImage coupled isProver isVerifier (threadedAfter collected))
            (body.denote (labelledMeaning model label functionTable oldTable side)
              (Environment.ofValues (numbers.append values)))
            ((Region.returnAfter (dialect := ProtocolDialect operations functions new deployed)
              (t.states place.roles) collected body').denote
              (labelledMeaning model label functionTable newTable side)
              (Environment.ofValues (numbers.append (.cons state.1 (.cons state.2 values))))) := by
        intro state numbers values coupledState
        have start := afterLeading_agrees (Value := SideValue model side)
          (t.first place.roles) (t.second place.roles) state.1 state.2 values
          (Located.ofRoles .nat participants)
          (rename := Mapping.start (Δ := ([] : List Located)) 0 rfl)
          (old := Environment.empty) (new := Environment.empty)
          (fun reference => reference.elimNil) numbers
        have ih := ihBody _ _ _ body' threadsBody _ _ start.1
          (coupledState.of_eq start.2.1 start.2.2)
        rw [Region.returnAfter_denote]
        refine Refines.andThen ih ?_
        rintro result made ⟨next, coupledNext, rfl⟩
        exact ⟨_, rfl, next, coupledNext, rfl⟩
      refine Refines.step (threadedValues (roles := place.roles))
        (threadedAfter (collectedSequencesAt count.size collected)) ?_ ?_
      · show Refines _
          (labelledOperation model label functionTable oldTable side
            (.repeat participants count carried collected captures covered) (Operands.eval env arguments)
            ((Regions.cons body Regions.nil).denote
              (labelledMeaning model label functionTable oldTable side)))
          (labelledOperation model label functionTable newTable side
            (.repeat participants count (t.states place.roles ++ carried) collected captures covered)
            (Operands.eval env' _)
            ((Regions.cons (Region.returnAfter (t.states place.roles) collected body')
              Regions.nil).denote (labelledMeaning model label functionTable newTable side)))
        rw [eval_threaded, ← agrees.operands arguments]
        generalize Operands.eval env' (rename.operands arguments) = evaluated
        obtain ⟨counts, others, rfl⟩ : ∃ counts others, evaluated = Values.append counts others :=
          ⟨_, _, (Values.append_split (count.operands participants) evaluated).symm⟩
        simp only [Values.split_append]
        exact repeat_refines _ _ region counts others (env' first, env' second) holds
      · intro results state coupledState
        obtain ⟨sequences, values, rfl⟩ : ∃ sequences values,
            results = Values.append sequences values :=
          ⟨_, _, (Values.append_split (collectedSequencesAt count.size collected) results).symm⟩
        have next := afterLeading_agrees (Value := SideValue model side)
          (t.first place.roles) (t.second place.roles) state.1 state.2 values
          (collectedSequencesAt count.size collected) agrees sequences
        show Refines _ _ (rest'.denote (labelledMeaning model label functionTable newTable side)
          (Environment.bindAll env' (threadedAfter (collectedSequencesAt count.size collected)
            (Values.append sequences values, state))))
        rw [show threadedAfter (collectedSequencesAt count.size collected)
            (Values.append sequences values, state) =
              sequences.append (.cons state.1 (.cons state.2 values)) by
          simp only [threadedAfter, Values.split_append]]
        exact ihRest _ _ _ rest' threadsRest _ _ next.1 (coupledState.of_eq next.2.1 next.2.2)
    · cases threads
    · cases threads
  · rename_i untouched
    split at threads
    · rename_i bodies' rest' plainBodies threadsRest
      have same := Except.ok.inj threads
      subst same
      refine same_step ihRest threadsRest agrees holds
        (labelledOperation model label functionTable oldTable side
          (.repeat participants count carried collected captures covered) (Operands.eval env arguments)
          ((Regions.cons body Regions.nil).denote
            (labelledMeaning model label functionTable oldTable side))) _ ?_
      show labelledOperation model label functionTable newTable side
          (.repeat participants count carried collected captures covered)
          (Operands.eval env' (rename.operands arguments))
          (bodies'.denote (labelledMeaning model label functionTable newTable side)) = _
      rw [agrees.operands,
        plainRegions_meaning callees.plain (Regions.cons body Regions.nil) bodies' plainBodies]
      rfl
    · cases threads
    · cases threads
  · cases threads

theorem choose_region_refines (callees : CalleesRefine coupled table oldTable newTable)
    {Γ out : List Located} {participants : List Nat} {tag : ChoiceTag}
    {captures outputs : List Located} {covered : Located.heldBy participants outputs = true}
    {arguments : Operands Γ (Located.ofRoles tag.type participants ++ captures)}
    {bodies : Regions (ProtocolDialect operations functions old deployed)
      (tag.regions participants captures outputs)}
    {rest : Region (ProtocolDialect operations functions old deployed) (bindAll Γ outputs) out}
    (ihBodies : ∀ images,
      threadRegions t rule table place bodies
        (t.choice place.roles participants captures outputs tag) = .ok images →
      RegionsRefine coupled isProver isVerifier
        (t.choice place.roles participants captures outputs tag)
        (bodies.denote (labelledMeaning model label functionTable oldTable side))
        (images.denote (labelledMeaning model label functionTable newTable side)))
    (ihRest : Refines[rest]) :
    Refines[Region.letOp (dialect := ProtocolDialect operations functions old deployed)
      (.choose participants tag captures outputs covered) arguments bodies rest] := by
  intro Δ rename first second image threads env env' agrees holds
  unfold threadRegion at threads
  split at threads
  · rename_i touched
    split at threads
    · rename_i held
      dsimp only at threads
      split at threads
      · rename_i bodies' rest' threadsBodies threadsRest
        have same := Except.ok.inj threads
        subst same
        have regions := ihBodies bodies' threadsBodies
        refine Refines.step (threadedValues (roles := place.roles))
          (threadedValues (roles := place.roles)) ?_ ?_
        · show Refines _
            (labelledOperation model label functionTable oldTable side
              (.choose participants tag captures outputs covered) (Operands.eval env arguments)
              (bodies.denote (labelledMeaning model label functionTable oldTable side)))
            (labelledOperation model label functionTable newTable side
              (.choose participants tag (t.states place.roles ++ captures)
                (t.states place.roles ++ outputs) held)
              (Operands.eval env' _)
              (bodies'.denote (labelledMeaning model label functionTable newTable side)))
          rw [eval_threaded, ← agrees.operands arguments]
          generalize Operands.eval env' (rename.operands arguments) = evaluated
          obtain ⟨tags, others, rfl⟩ : ∃ tags others, evaluated = Values.append tags others :=
            ⟨_, _, (Values.append_split (Located.ofRoles tag.type participants) evaluated).symm⟩
          simp only [Values.split_append]
          exact choose_refines _ _ regions tags others (env' first, env' second) holds
        · intro result state coupledState
          have next := afterTwo_agrees agrees (t.first place.roles) (t.second place.roles)
            state.1 state.2 result
          exact ihRest _ _ _ rest' threadsRest _ _ next.1
            (coupledState.of_eq next.2.1 next.2.2)
      · cases threads
      · cases threads
    · cases threads
  · rename_i untouched
    split at threads
    · rename_i bodies' rest' plainBodies threadsRest
      have same := Except.ok.inj threads
      subst same
      refine same_step ihRest threadsRest agrees holds
        (labelledOperation model label functionTable oldTable side
          (.choose participants tag captures outputs covered) (Operands.eval env arguments)
          (bodies.denote (labelledMeaning model label functionTable oldTable side))) _ ?_
      show labelledOperation model label functionTable newTable side
          (.choose participants tag captures outputs covered)
          (Operands.eval env' (rename.operands arguments))
          (bodies'.denote (labelledMeaning model label functionTable newTable side)) = _
      rw [agrees.operands, plainRegions_meaning callees.plain bodies bodies' plainBodies]
      rfl
    · cases threads
    · cases threads
  · cases threads

/-- The operands or results of an application of an image that threads: the two threaded
values, held by the caller's roles that run the callee's transcript roles, then the
callee's. -/
@[expose, reducible] def appliedValues (roleMap : RoleMap) (inner : TranscriptRoles)
    {ports : List Located}
    (first : SideValue model side (Located.rename roleMap (t.first inner)))
    (second : SideValue model side (Located.rename roleMap (t.second inner)))
    (values : Values (SideValue model side) (ports.map (Located.rename roleMap))) :
    Values (SideValue model side) ((t.states inner ++ ports).map (Located.rename roleMap)) :=
  .cons first (.cons second values)

/-- The application of an image that threads refines the application of the callee: the
callee's statement at the preimage side, with the caller's two values held by the callee's
transcript roles. -/
theorem apply_operation_refines (callees : CalleesRefine coupled table oldTable newTable)
    {header : ProtocolHeader} {callee : Var old header} {roleMap : RoleMap} {site : Nat}
    {permitted : (deployed && header.specificationOnly) = false}
    (threaded : ThreadedCallee t new place.roles roleMap header)
    (found : table.find callee (some threaded.inner) = some threaded.image)
    (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier))
    (holds : CoupledState coupled isProver isVerifier state)
    (arguments : Values (SideValue model side) (header.inputs.map (Located.rename roleMap)))
    (evaluated : Values (SideValue model side)
      ((t.header (some threaded.inner) header).inputs.map (Located.rename roleMap)))
    (same : evaluated = appliedValues roleMap threaded.inner
      (Held.along (X := model.Value t.prover) (congrArg side threaded.prover) state.1)
      (Held.along (X := model.Value t.verifier) (congrArg side threaded.verifier) state.2)
      arguments) :
    Refines
      (CoupledImage coupled isProver isVerifier
        (fun result : Values (SideValue model side) (header.outputs.map (Located.rename roleMap)) ×
            ThreadState model t (side place.roles.prover) (side place.roles.verifier) =>
          appliedValues roleMap threaded.inner
            (Held.along (X := model.Value t.prover) (congrArg side threaded.prover) result.2.1)
            (Held.along (X := model.Value t.verifier) (congrArg side threaded.verifier) result.2.2)
            result.1))
      (labelledOperation model label functionTable oldTable side (operations := operations)
        (deployed := deployed) (.apply callee roleMap site permitted) arguments .nil)
      (labelledOperation model label functionTable newTable side (operations := operations)
        (deployed := deployed) (.apply threaded.image roleMap site permitted) evaluated .nil) := by
  subst same
  have calleeRefines := callees.threaded callee threaded.inner threaded.image found
    (label site).below (Side.preimage roleMap side)
    ((congrArg side threaded.prover).trans isProver)
    ((congrArg side threaded.verifier).trans isVerifier)
    (Held.along (X := model.Value t.prover) (congrArg side threaded.prover) state.1,
      Held.along (X := model.Value t.verifier) (congrArg side threaded.verifier) state.2)
    (unmapValues (F := SideValue model side) (Located.rename roleMap) header.inputs arguments)
    (holds.along (congrArg side threaded.prover) (congrArg side threaded.verifier))
  show Refines _ (PIR.Process.bind _ _) (PIR.Process.bind _ _)
  refine Refines.bind calleeRefines ?_
  rintro values made ⟨next, coupledNext, rfl⟩
  refine Refines.done
    ⟨(Held.back (X := model.Value t.prover) (congrArg side threaded.prover) next.1,
        Held.back (X := model.Value t.verifier) (congrArg side threaded.verifier) next.2),
      coupledNext.back (congrArg side threaded.prover) (congrArg side threaded.verifier), ?_⟩
  simp only [Held.along_back]
  rfl

theorem apply_refines (callees : CalleesRefine coupled table oldTable newTable)
    {Γ out : List Located} {header : ProtocolHeader} {callee : Var old header} {roleMap : RoleMap}
    {site : Nat} {permitted : (deployed && header.specificationOnly) = false}
    {arguments : Operands Γ (header.inputs.map (Located.rename roleMap))}
    {rest : Region (ProtocolDialect operations functions old deployed)
      (bindAll Γ (header.outputs.map (Located.rename roleMap))) out}
    (ihRest : Refines[rest]) :
    Refines[Region.letOp (dialect := ProtocolDialect operations functions old deployed)
      (.apply callee roleMap site permitted) arguments .nil rest] := by
  intro Δ rename first second image threads env env' agrees holds
  unfold threadRegion at threads
  split at threads
  · rename_i threaded found
    dsimp only at threads
    split at threads
    · rename_i rest' threadsRest
      have same := Except.ok.inj threads
      subst same
      refine Refines.step (threadedValues (roles := place.roles))
        (fun result : Values (SideValue model side)
              (header.outputs.map (Located.rename roleMap)) ×
            ThreadState model t (side place.roles.prover) (side place.roles.verifier) =>
          appliedValues roleMap threaded.inner
            (Held.along (X := model.Value t.prover) (congrArg side threaded.prover) result.2.1)
            (Held.along (X := model.Value t.verifier) (congrArg side threaded.verifier) result.2.2)
            result.1) ?_ ?_
      · exact apply_operation_refines (functionTable := functionTable) callees threaded
          (threadedCallee_find found) (env' first, env' second) holds
          (Operands.eval env arguments) _
          (cons_congr (retype_along threaded.prover env' first)
            (cons_congr (retype_along threaded.verifier env' second) (agrees.operands arguments)))
      · intro result state coupledState
        have next := afterTwo_agrees agrees
          (Located.rename roleMap (t.first threaded.inner))
          (Located.rename roleMap (t.second threaded.inner))
          (Held.along (X := model.Value t.prover) (congrArg side threaded.prover) state.1)
          (Held.along (X := model.Value t.verifier) (congrArg side threaded.verifier) state.2)
          result
        refine ihRest _ _ _ rest' threadsRest _ _ next.1 (coupledState.of_eq ?_ ?_)
        · exact (retype_back threaded.prover _ _).trans
            ((congrArg (Held.back (congrArg side threaded.prover)) next.2.1).trans
              (Held.back_along _ _))
        · exact (retype_back threaded.verifier _ _).trans
            ((congrArg (Held.back (congrArg side threaded.verifier)) next.2.2).trans
              (Held.back_along _ _))
    · cases threads
  · rename_i missing
    split at threads
    · rename_i plainImage rest' foundPlain threadsRest
      have same := Except.ok.inj threads
      subst same
      refine same_step ihRest threadsRest agrees holds
        (labelledOperation model label functionTable oldTable side
          (.apply callee roleMap site permitted) (Operands.eval env arguments) .nil) _ ?_
      show ((newTable.get plainImage) (label site).below (Side.preimage roleMap side)
          (unmapValues (F := SideValue model side) (Located.rename roleMap) header.inputs
            (Operands.eval env' (rename.operands arguments)))).bind _ = _
      rw [agrees.operands, callees.plain callee plainImage foundPlain]
      rfl
    · cases threads
    · cases threads

mutual
  /-- The refinement for a region. -/
  theorem threadRegion_refines (sound : RuleSound rule sem functionTable)
      (couples : RuleCouples rule sem coupled)
      (callees : CalleesRefine coupled table oldTable newTable) {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out),
        Refines[region]
    | .ret values => ret_refines values
    | .stop reason => stop_refines reason
    | .bind body rest =>
        bind_refines (threadRegion_refines sound couples callees body)
          (threadRegion_refines sound couples callees rest)
    | .letOp (.at role op bodies) arguments .nil rest =>
        at_refines (threadRegion_refines sound couples callees rest)
    | .letOp (.sample owner site law populated) arguments .nil rest =>
        sample_refines (threadRegion_refines sound couples callees rest)
    | .letOp (.exchange sender receiver site type) arguments .nil rest =>
        exchange_refines sound couples (threadRegion_refines sound couples callees rest)
    | .letOp (.draw owner receivers site law populated) arguments .nil rest =>
        draw_refines sound couples (threadRegion_refines sound couples callees rest)
    | .letOp (.repeat participants count carried collected captures covered) arguments
        (.cons body .nil) rest =>
        repeat_region_refines callees (threadRegion_refines sound couples callees body)
          (threadRegion_refines sound couples callees rest)
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest =>
        choose_region_refines callees
          (fun images => threadRegions_refines sound couples callees bodies _ images)
          (threadRegion_refines sound couples callees rest)
    | .letOp (.apply (header := header) callee roleMap site permitted) arguments .nil rest =>
        apply_refines callees (threadRegion_refines sound couples callees rest)

  /-- The refinement for the regions of a threaded operation. -/
  theorem threadRegions_refines (sound : RuleSound rule sem functionTable)
      (couples : RuleCouples rule sem coupled)
      (callees : CalleesRefine coupled table oldTable newTable)
      {signatures targets : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures)
        (threaded : ThreadedRegions t place.roles signatures targets)
        (images : Regions (ProtocolDialect operations functions new deployed) targets),
        threadRegions t rule table place regions threaded = .ok images →
        RegionsRefine coupled isProver isVerifier threaded
          (regions.denote (labelledMeaning model label functionTable oldTable side))
          (images.denote (labelledMeaning model label functionTable newTable side))
    | regions, threaded, images, threads =>
        match threaded, regions, images, threads with
        | .nil, .nil, _, _ => trivial
        | .cons leading added threaded, .cons body tail, images, threads => by
            simp only [threadRegions] at threads
            split at threads
            · rename_i body' tail' threadsBody threadsTail
              have same := Except.ok.inj threads
              subst same
              refine ⟨fun state before values coupledState => ?_,
                threadRegions_refines sound couples callees tail threaded tail' threadsTail⟩
              have start := afterLeading_agrees (Value := SideValue model side)
                (t.first place.roles) (t.second place.roles) state.1 state.2 values leading
                (rename := Mapping.start (Δ := ([] : List Located)) 0 rfl)
                (old := Environment.empty) (new := Environment.empty)
                (fun reference => reference.elimNil) before
              exact threadRegion_refines sound couples callees body _ _ _ body' threadsBody _ _
                start.1 (coupledState.of_eq start.2.1 start.2.2)
            · cases threads
            · cases threads
end

end Region

end Zkc.Core
