module

public import Zkc.Core.ThreadSound

public section

/-! The structural theorem of a threading step, for a region.

`threadRegion_meaning`: for a side and a handler that fits the region (`Fits`), the image
of a region under `threadRegion` is the region interpreted by the handler from the two
threaded values that the environment holds, followed by returning the final two values
before the region's. The proof is a structural induction on the region, one case per
operation form:

- local work passes (it performs no effect);
- an exchange from the prover to the verifier and a draw between the two are the rule's
  action (`RuleSound`), which is what the handler does there (`Fits`);
- every other exchange, draw and sample is the same operation, which the handler passes;
- a `repeat` or `choose` whose regions contain a rewritten operation carries the two
  values, and its regions are the old regions under the handler (the induction
  hypothesis); a `repeat` that collects returns the same sequences, with the two values
  after them; otherwise its regions are copies, which have the old meaning and which the
  handler passes;
- an `apply` of an image that threads is the callee under the handler (`CalleesThread`);
  an `apply` of the image with the callee's own header is the callee, which the handler
  passes.

The theorem is generic in the rule: Fiat–Shamir and serialize are two instances.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Core

open Zkc.Source

section Theorem

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {old new : List ProtocolHeader} {deployed : Bool} {t : Threads}
  {rule : Rule t operations functions} {sem : RuleMeaning model t operations}
  {functionTable : FunctionTable model functions} {oldTable : ProtocolTable model old}
  {newTable : ProtocolTable model new} {table : CalleeTable t.header old new}
  {fits : Values (CalleeFit model t) old} {place : Place} {side : Side} {label : Nat → Site}
  {handler : ThreadHandler model t (side place.roles.prover) (side place.roles.verifier)}

/-- The image that threads of a callee is the one the table records for its roles. -/
theorem threadedCallee_find {roles : TranscriptRoles} {roleMap : RoleMap} {header : ProtocolHeader}
    {callee : Var old header} {threaded : ThreadedCallee t new roles roleMap header}
    (found : threadedCallee t table roles roleMap callee = some threaded) :
    table.find callee (some threaded.inner) = some threaded.image := by
  unfold threadedCallee at found
  split at found
  · split at found
    · rename_i image recorded
      simp only [Option.some.injEq] at found
      subst found
      exact recorded
    · cases found
  · cases found

/-- The operands of a threaded `repeat` or `choose`, evaluated: the two threaded values
stand between the counts or tags and the other operands. -/
theorem eval_threaded {Value : Located → Type} {Δ : List Located} (env : Environment Value Δ)
    {first second : Located} (firstReference : Var Δ first) (secondReference : Var Δ second)
    (leading : List Located) {rest : List Located} (operands : Operands Δ (leading ++ rest)) :
    Operands.eval env ((Values.split leading operands).1.append
        (.cons firstReference (.cons secondReference (Values.split leading operands).2))) =
      (Values.split leading (Operands.eval env operands)).1.append
        (.cons (env firstReference) (.cons (env secondReference)
          (Values.split leading (Operands.eval env operands)).2)) := by
  rw [eval_append, eval_split]
  rfl

/-- The structural statement for one region: every image of the region under
`threadRegion`, for a handler that fits the region, is the region under the handler. -/
@[expose] def RegionThreads (t : Threads) (rule : Rule t operations functions)
    (sem : RuleMeaning model t operations) (functionTable : FunctionTable model functions)
    (oldTable : ProtocolTable model old) (newTable : ProtocolTable model new)
    (table : CalleeTable t.header old new) (fits : Values (CalleeFit model t) old) (place : Place)
    (side : Side) (label : Nat → Site)
    (handler : ThreadHandler model t (side place.roles.prover) (side place.roles.verifier))
    {Γ out : List Located}
    (region : Region (ProtocolDialect operations functions old deployed) Γ out) : Prop :=
  ∀ {Δ : List Located} (rename : Renaming Γ Δ) (first : Var Δ (t.first place.roles))
    (second : Var Δ (t.second place.roles))
    (image : Region (ProtocolDialect operations functions new deployed) Δ
      (t.states place.roles ++ out)),
    threadRegion t rule table place region rename first second = .ok image →
    Fits t rule sem functionTable oldTable table fits place side label handler region →
    ∀ (env : Environment (SideValue model side) Γ) (env' : Environment (SideValue model side) Δ),
      rename.Agrees env env' →
      image.denote (labelledMeaning model label functionTable newTable side) env' =
        ((region.denote (labelledMeaning model label functionTable oldTable side)
            env).interpretWith handler (env' first, env' second)).bind fun result =>
          .done (threadedValues result)

local notation "Threads[" region "]" =>
  RegionThreads t rule sem functionTable oldTable newTable table fits place side label handler region

/-- A step that the step leaves as it is and that the handler passes. `passed` is the old
operation's process and `copy` the new one's. -/
theorem passed_step {Γ Δ out results : List Located}
    {rest : Region (ProtocolDialect operations functions old deployed) (bindAll Γ results) out}
    (ihRest : Threads[rest])
    {rename : Renaming Γ Δ} {first : Var Δ (t.first place.roles)}
    {second : Var Δ (t.second place.roles)}
    {rest' : Region (ProtocolDialect operations functions new deployed) (bindAll Δ results)
      (t.states place.roles ++ out)}
    (threadsRest : threadRegion t rule table place rest (rename.keepAll results)
      (first.weaken results) (second.weaken results) = .ok rest')
    (fitRest : Fits t rule sem functionTable oldTable table fits place side label handler rest)
    {env : Environment (SideValue model side) Γ} {env' : Environment (SideValue model side) Δ}
    (agrees : rename.Agrees env env')
    (passed copy : PIR.Process (Effects model) (Values (SideValue model side) results))
    (same : copy = passed) (passes : PIR.Passes handler passed) :
    copy.bind (fun values =>
        rest'.denote (labelledMeaning model label functionTable newTable side)
          (Environment.bindAll env' values)) =
      ((passed.bind fun values =>
          rest.denote (labelledMeaning model label functionTable oldTable side)
            (Environment.bindAll env values)).interpretWith handler (env' first, env' second)).bind
        fun result => .done (threadedValues result) := by
  subst same
  refine PIR.thread_step_read handler _ _ _ _ _ threadedValues
    (fun values => (values, (env' first, env' second))) (passes _) ?_
  intro values
  have ih := ihRest _ _ _ rest' threadsRest fitRest (Environment.bindAll env values)
    (Environment.bindAll env' values) (agrees.keepAll values)
  rw [Environment.bindAll_weaken, Environment.bindAll_weaken] at ih
  exact ih

theorem ret_threads {Γ out : List Located} (values : Operands Γ out) :
    Threads[(Region.ret values : Region (ProtocolDialect operations functions old deployed) Γ out)] := by
  intro Δ rename first second image threads _ env env' agrees
  simp only [threadRegion, Except.ok.injEq] at threads
  subst threads
  exact congrArg PIR.Process.done (cons_congr rfl (cons_congr rfl (agrees.operands values)))

theorem stop_threads {Γ out : List Located} (reason : PIR.Stop) :
    Threads[(Region.stop reason : Region (ProtocolDialect operations functions old deployed) Γ out)] := by
  intro Δ rename first second image threads _ env env' agrees
  simp only [threadRegion, Except.ok.injEq] at threads
  subst threads
  rfl

theorem bind_threads {Γ mid out : List Located}
    {body : Region (ProtocolDialect operations functions old deployed) Γ mid}
    {rest : Region (ProtocolDialect operations functions old deployed) (bindAll Γ mid) out}
    (ihBody : Threads[body]) (ihRest : Threads[rest]) : Threads[Region.bind body rest] := by
  intro Δ rename first second image threads fit env env' agrees
  unfold threadRegion at threads
  dsimp only at threads
  split at threads
  · rename_i body' rest' threadsBody threadsRest
    simp only [Except.ok.injEq] at threads
    subst threads
    show (body'.denote (labelledMeaning model label functionTable newTable side) env').bind _ =
      (((body.denote (labelledMeaning model label functionTable oldTable side) env).bind
        _).interpretWith handler _).bind _
    rw [ihBody rename first second body' threadsBody fit.1 env env' agrees, PIR.Process.bind_assoc,
      PIR.Process.interpretWith_bind, PIR.Process.bind_assoc]
    congr 1
    funext result
    have next := afterTwo_agrees agrees (t.first place.roles) (t.second place.roles)
      result.2.1 result.2.2 result.1
    have ih := ihRest _ _ _ rest' threadsRest fit.2 _ _ next.1
    rw [next.2.1, next.2.2] at ih
    exact ih
  · cases threads
  · cases threads

theorem at_threads (quiet : QuietTable functionTable) {Γ out : List Located} {role : Nat}
    {op : LocalOp operations functions deployed}
    {bodies : Regions (LocalDialect operations functions deployed) op.regions}
    {arguments : Operands Γ (Located.atRole role op.arguments)}
    {rest : Region (ProtocolDialect operations functions old deployed)
      (bindAll Γ (Located.atRole role op.results)) out}
    (ihRest : Threads[rest]) :
    Threads[Region.letOp (dialect := ProtocolDialect operations functions old deployed)
      (.at role op bodies) arguments .nil rest] := by
  intro Δ rename first second image threads fit env env' agrees
  unfold threadRegion at threads
  split at threads
  · rename_i rest' threadsRest
    simp only [Except.ok.injEq] at threads
    subst threads
    refine passed_step ihRest threadsRest fit agrees
      (labelledOperation model label functionTable oldTable side (.at role op bodies)
        (Operands.eval env arguments) .nil) _ ?_ ?_
    · show labelledOperation model label functionTable newTable side (.at role op bodies)
          (Operands.eval env' (rename.operands arguments)) .nil = _
      rw [agrees.operands]
      rfl
    · exact (at_quiet quiet label oldTable side role op bodies _).passes handler
  · cases threads

theorem sample_threads {Γ out : List Located} {owner site : Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩} {populated : output.populated = true}
    {arguments : Operands Γ (Located.atRole owner inputs)}
    {rest : Region (ProtocolDialect operations functions old deployed)
      (bindAll Γ [⟨output, owner⟩]) out}
    (ihRest : Threads[rest]) :
    Threads[Region.letOp (dialect := ProtocolDialect operations functions old deployed)
      (.sample owner site law populated) arguments .nil rest] := by
  intro Δ rename first second image threads fit env env' agrees
  unfold threadRegion at threads
  split at threads
  · rename_i rest' threadsRest
    simp only [Except.ok.injEq] at threads
    subst threads
    refine passed_step ihRest threadsRest fit.2 agrees
      (labelledOperation model label functionTable oldTable side (.sample owner site law populated)
        (Operands.eval env arguments) .nil) _ ?_ (fit.1 _ _)
    show labelledOperation model label functionTable newTable side (.sample owner site law populated)
        (Operands.eval env' (rename.operands arguments)) .nil = _
    rw [agrees.operands]
    rfl
  · cases threads

theorem exchange_threads (sound : RuleSound rule sem functionTable) {Γ out : List Located}
    {sender receiver site : Nat} {type : Ty} {arguments : Operands Γ [⟨type, sender⟩]}
    {rest : Region (ProtocolDialect operations functions old deployed)
      (bindAll Γ [⟨type, receiver⟩]) out}
    (ihRest : Threads[rest]) :
    Threads[Region.letOp (dialect := ProtocolDialect operations functions old deployed)
      (.exchange sender receiver site type) arguments .nil rest] := by
  intro Δ rename first second image threads fit env env' agrees
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
        obtain ⟨later, runs, holds⟩ := sound.exchange newTable label side place site type _
          first second emitted emits env'
        rw [runs rest', PIR.Process.bind_assoc]
        refine PIR.thread_step_read handler _ _ _ _ _ threadedValues
          (fun (result : SideValue model side ⟨type, place.roles.verifier⟩ ×
              ThreadState model t (side place.roles.prover) (side place.roles.verifier)) =>
            (Values.cons result.1 .nil, result.2)) ?_ ?_
        · have acts := fit.1 rfl rfl (Operands.eval env arguments) (env' first, env' second)
          have value : (Operands.eval env arguments).get .here =
              env' (rename.rename (arguments.get .here)) :=
            (Operands.get_eval env arguments .here).trans (agrees (arguments.get .here)).symm
          rw [value] at acts
          exact acts
        · intro (result : SideValue model side ⟨type, place.roles.verifier⟩ ×
            ThreadState model t (side place.roles.prover) (side place.roles.verifier))
          obtain ⟨received, stateFirst, stateSecond, kept⟩ := holds result
          have ih := ihRest _ _ _ rest' threadsRest fit.2.2 (Environment.push env result.1)
            (later result)
            (Renaming.Agrees.to (agrees.extend emitted.grows (later result) kept) _ result.1 received)
          rw [stateFirst, stateSecond] at ih
          exact ih
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
        refine passed_step ihRest threadsRest fit.2.2 agrees
          (labelledOperation model label functionTable oldTable side
            (.exchange sender receiver site type) (Operands.eval env arguments) .nil) _ ?_
          (fit.2.1 between _ _)
        show labelledOperation model label functionTable newTable side
            (.exchange sender receiver site type)
            (Operands.eval env' (rename.operands arguments)) .nil = _
        rw [agrees.operands]
        rfl
      · cases threads

/-- The same statement from a state that is equal to the one read. -/
theorem restate {A B S : Type} {handler : PIR.StatefulInterpretation (Effects model) (Effects model) S}
    {source : PIR.Process (Effects model) A} {finish : A × S → PIR.Process (Effects model) B}
    {image : PIR.Process (Effects model) B} {state read : S} (same : read = state)
    (threads : image = (source.interpretWith handler read).bind finish) :
    image = (source.interpretWith handler state).bind finish := by
  subst same
  exact threads

theorem draw_threads (sound : RuleSound rule sem functionTable) {Γ out : List Located}
    {owner site : Nat} {receivers : List Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩} {populated : output.populated = true}
    {arguments : Operands Γ (Located.atRole owner inputs)}
    {rest : Region (ProtocolDialect operations functions old deployed)
      (bindAll Γ (⟨output, owner⟩ :: Located.ofRoles output receivers)) out}
    (ihRest : Threads[rest]) :
    Threads[Region.letOp (dialect := ProtocolDialect operations functions old deployed)
      (.draw owner receivers site law populated) arguments .nil rest] := by
  intro Δ rename first second image threads fit env env' agrees
  -- A draw that the step leaves as it is.
  have plain : ∀ rest', threadRegion t rule table place rest
        (rename.keepAll (⟨output, owner⟩ :: Located.ofRoles output receivers))
        (first.weaken _) (second.weaken _) = .ok rest' →
      OperationPasses (operations := operations) (deployed := deployed) t functionTable oldTable place
        side label handler (.draw owner receivers site law populated) →
      Fits t rule sem functionTable oldTable table fits place side label handler rest →
      (Region.letOp (dialect := ProtocolDialect operations functions new deployed)
          (.draw owner receivers site law populated) (rename.operands arguments) .nil rest').denote
          (labelledMeaning model label functionTable newTable side) env' =
        (((Region.letOp (dialect := ProtocolDialect operations functions old deployed)
            (.draw owner receivers site law populated) arguments .nil rest).denote
            (labelledMeaning model label functionTable oldTable side) env).interpretWith handler
            (env' first, env' second)).bind fun result => .done (threadedValues result) := by
    intro rest' threadsRest passes fitRest
    refine passed_step ihRest threadsRest fitRest agrees
      (labelledOperation model label functionTable oldTable side (.draw owner receivers site law populated)
        (Operands.eval env arguments) .nil) _ ?_ (passes _ _)
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
        exact plain rest' threadsRest fit.1 fit.2
      · cases threads
  | cons receiver others =>
      cases others with
      | cons another more =>
          unfold threadRegion at threads
          split at threads
          · rename_i rest' threadsRest
            have same := Except.ok.inj threads
            subst same
            exact plain rest' threadsRest fit.1 fit.2
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
                obtain ⟨later, runs, holds⟩ := sound.draw newTable label side place site law first
                  second raw emits env'
                show (raw.wrap rest').denote (labelledMeaning model label functionTable newTable side) env' = _
                rw [runs rest', PIR.Process.bind_assoc]
                refine PIR.thread_step_read handler _ _ _ _ _ threadedValues
                  (fun (result : (SideValue model side ⟨output, place.roles.prover⟩ ×
                        SideValue model side ⟨output, place.roles.verifier⟩) ×
                      ThreadState model t (side place.roles.prover) (side place.roles.verifier)) =>
                    (Values.cons result.1.2 (.cons result.1.1 .nil), result.2)) ?_ ?_
                · exact fit.1.1 rfl rfl (Operands.eval env arguments) (env' first, env' second)
                · intro (result : (SideValue model side ⟨output, place.roles.prover⟩ ×
                      SideValue model side ⟨output, place.roles.verifier⟩) ×
                    ThreadState model t (side place.roles.prover) (side place.roles.verifier))
                  obtain ⟨proverCoin, verifierCoin, stateFirst, stateSecond, kept⟩ := holds result
                  have ih := ihRest _ _ _ rest' threadsRest fit.2
                    (Environment.push (Environment.push env result.1.2) result.1.1) (later result)
                    (Renaming.Agrees.to
                      (Renaming.Agrees.to (agrees.extend raw.grows (later result) kept) _ result.1.2
                        verifierCoin) _ result.1.1 proverCoin)
                  refine restate (Prod.ext ?_ ?_) ih
                  · exact (congrArg (later result) ((tail_get _ _).trans (tail_get _ _))).trans
                      stateFirst
                  · exact (congrArg (later result) ((tail_get _ _).trans (tail_get _ _))).trans
                      stateSecond
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
                  obtain ⟨later, runs, holds⟩ := sound.draw newTable label side place site law
                    first second raw emits env'
                  show (raw.wrap rest').denote (labelledMeaning model label functionTable newTable side) env' = _
                  rw [runs rest', PIR.Process.bind_assoc]
                  refine PIR.thread_step_read handler _ _ _ _ _ threadedValues
                    (fun (result : (SideValue model side ⟨output, place.roles.prover⟩ ×
                          SideValue model side ⟨output, place.roles.verifier⟩) ×
                        ThreadState model t (side place.roles.prover) (side place.roles.verifier)) =>
                      (Values.cons result.1.1 (.cons result.1.2 .nil), result.2)) ?_ ?_
                  · exact fit.1.2.1 byVerifier rfl rfl (Operands.eval env arguments)
                      (env' first, env' second)
                  · intro (result : (SideValue model side ⟨output, place.roles.prover⟩ ×
                        SideValue model side ⟨output, place.roles.verifier⟩) ×
                      ThreadState model t (side place.roles.prover) (side place.roles.verifier))
                    obtain ⟨proverCoin, verifierCoin, stateFirst, stateSecond, kept⟩ := holds result
                    have ih := ihRest _ _ _ rest' threadsRest fit.2
                      (Environment.push (Environment.push env result.1.1) result.1.2) (later result)
                      (Renaming.Agrees.to
                        (Renaming.Agrees.to (agrees.extend raw.grows (later result) kept) _
                          result.1.1 proverCoin) _ result.1.2 verifierCoin)
                    refine restate (Prod.ext ?_ ?_) ih
                    · exact (congrArg (later result) ((tail_get _ _).trans (tail_get _ _))).trans
                        stateFirst
                    · exact (congrArg (later result) ((tail_get _ _).trans (tail_get _ _))).trans
                        stateSecond
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
                  exact plain rest' threadsRest (fit.1.2.2 byVerifier byProver) fit.2
                · cases threads

theorem repeat_region_threads (callees : CalleesThread table oldTable newTable fits)
    {Γ out : List Located} {participants : List Nat} {count : RepeatCount}
    {carried collected captures : List Located}
    {covered : Located.heldBy participants collected = true}
    {arguments : Operands Γ (count.operands participants ++ (carried ++ captures))}
    {body : Region (ProtocolDialect operations functions old deployed)
      (bindAll [] (Located.ofRoles .nat participants ++ (carried ++ captures)))
      (collected ++ carried)}
    {rest : Region (ProtocolDialect operations functions old deployed)
      (bindAll Γ (collectedSequencesAt count.size collected ++ carried)) out}
    (ihBody : Threads[body]) (ihRest : Threads[rest]) :
    Threads[Region.letOp (dialect := ProtocolDialect operations functions old deployed)
      (.repeat participants count carried collected captures covered) arguments
      (.cons body .nil) rest] := by
  intro Δ rename first second image threads fit env env' agrees
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
      -- The image of the loop's region: the threaded region, which is the old region under
      -- the handler, with the two values returned after the collected ones.
      have region : ∀ (state : ThreadState model t (side place.roles.prover)
            (side place.roles.verifier))
          (numbers : Values (SideValue model side) (Located.ofRoles .nat participants))
          (values : Values (SideValue model side) (carried ++ captures)),
          (Region.returnAfter (dialect := ProtocolDialect operations functions new deployed)
              (t.states place.roles) collected body').denote
              (labelledMeaning model label functionTable newTable side)
              (Environment.ofValues (numbers.append (.cons state.1 (.cons state.2 values)))) =
            ((body.denote (labelledMeaning model label functionTable oldTable side)
                (Environment.ofValues (numbers.append values))).interpretWith handler state).bind
              fun result => .done (threadedAfter collected result) := by
        intro state numbers values
        have start := afterLeading_agrees (Value := SideValue model side)
          (t.first place.roles) (t.second place.roles) state.1 state.2 values
          (Located.ofRoles .nat participants)
          (rename := Mapping.start (Δ := ([] : List Located)) 0 rfl)
          (old := Environment.empty) (new := Environment.empty)
          (fun reference => reference.elimNil) numbers
        have ih := ihBody _ _ _ body' threadsBody (fit.1 touched).1 _ _ start.1
        rw [Region.returnAfter_denote]
        refine (congrArg (fun process => PIR.Process.bind process _)
          (restate (Prod.ext start.2.1 start.2.2) ih)).trans ?_
        rw [PIR.Process.bind_assoc]
        rfl
      refine PIR.thread_step_made handler _ _ _ _ _ threadedValues
        (threadedAfter (collectedSequencesAt count.size collected)) ?_ ?_
      · show labelledOperation model label functionTable newTable side
            (.repeat participants count (t.states place.roles ++ carried) collected captures covered)
            (Operands.eval env' _)
            ((Regions.cons (Region.returnAfter (t.states place.roles) collected body')
              Regions.nil).denote (labelledMeaning model label functionTable newTable side)) =
          ((labelledOperation model label functionTable oldTable side
            (.repeat participants count carried collected captures covered) (Operands.eval env arguments)
            ((Regions.cons body Regions.nil).denote
              (labelledMeaning model label functionTable oldTable side))).interpretWith
            handler _).bind _
        rw [eval_threaded, ← agrees.operands arguments]
        generalize Operands.eval env' (rename.operands arguments) = evaluated
        obtain ⟨counts, others, rfl⟩ : ∃ counts others, evaluated = Values.append counts others :=
          ⟨_, _, (Values.append_split (count.operands participants) evaluated).symm⟩
        simp only [Values.split_append]
        exact repeat_threads _ _ region counts others (env' first, env' second)
      · intro result
        obtain ⟨results, state⟩ := result
        obtain ⟨sequences, values, rfl⟩ : ∃ sequences values,
            results = Values.append sequences values :=
          ⟨_, _, (Values.append_split (collectedSequencesAt count.size collected) results).symm⟩
        have next := afterLeading_agrees (Value := SideValue model side)
          (t.first place.roles) (t.second place.roles) state.1 state.2 values
          (collectedSequencesAt count.size collected) agrees sequences
        have ih := ihRest _ _ _ rest' threadsRest fit.2.2 _ _ next.1
        show rest'.denote (labelledMeaning model label functionTable newTable side)
            (Environment.bindAll env' (threadedAfter (collectedSequencesAt count.size collected)
              (Values.append sequences values, state))) = _
        rw [show threadedAfter (collectedSequencesAt count.size collected)
            (Values.append sequences values, state) =
              sequences.append (.cons state.1 (.cons state.2 values)) by
          simp only [threadedAfter, Values.split_append]]
        exact restate (Prod.ext next.2.1 next.2.2) ih
    · cases threads
    · cases threads
  · rename_i untouched
    split at threads
    · rename_i bodies' rest' plainBodies threadsRest
      have same := Except.ok.inj threads
      subst same
      refine passed_step ihRest threadsRest fit.2.2 agrees
        (labelledOperation model label functionTable oldTable side
          (.repeat participants count carried collected captures covered) (Operands.eval env arguments)
          ((Regions.cons body Regions.nil).denote
            (labelledMeaning model label functionTable oldTable side))) _ ?_
        (repeat_passes _ _ (fit.2.1 untouched))
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

theorem choose_region_threads (callees : CalleesThread table oldTable newTable fits)
    {Γ out : List Located} {participants : List Nat} {tag : ChoiceTag}
    {captures outputs : List Located} {covered : Located.heldBy participants outputs = true}
    {arguments : Operands Γ (Located.ofRoles tag.type participants ++ captures)}
    {bodies : Regions (ProtocolDialect operations functions old deployed)
      (tag.regions participants captures outputs)}
    {rest : Region (ProtocolDialect operations functions old deployed) (bindAll Γ outputs) out}
    (ihBodies : ∀ images,
      threadRegions t rule table place bodies
        (t.choice place.roles participants captures outputs tag) = .ok images →
      FitsAll t rule sem functionTable oldTable table fits place side label handler bodies →
      RegionsThread handler (t.choice place.roles participants captures outputs tag)
        (bodies.denote (labelledMeaning model label functionTable oldTable side))
        (images.denote (labelledMeaning model label functionTable newTable side)))
    (ihRest : Threads[rest]) :
    Threads[Region.letOp (dialect := ProtocolDialect operations functions old deployed)
      (.choose participants tag captures outputs covered) arguments bodies rest] := by
  intro Δ rename first second image threads fit env env' agrees
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
        have regions := ihBodies bodies' threadsBodies (fit.1 touched)
        refine PIR.thread_step_made handler _ _ _ _ _ threadedValues threadedValues ?_ ?_
        · show labelledOperation model label functionTable newTable side
              (.choose participants tag (t.states place.roles ++ captures)
                (t.states place.roles ++ outputs) held)
              (Operands.eval env' _)
              (bodies'.denote (labelledMeaning model label functionTable newTable side)) =
            ((labelledOperation model label functionTable oldTable side
              (.choose participants tag captures outputs covered) (Operands.eval env arguments)
              (bodies.denote (labelledMeaning model label functionTable oldTable side))).interpretWith
              handler _).bind _
          rw [eval_threaded, ← agrees.operands arguments]
          generalize Operands.eval env' (rename.operands arguments) = evaluated
          obtain ⟨tags, others, rfl⟩ : ∃ tags others, evaluated = Values.append tags others :=
            ⟨_, _, (Values.append_split (Located.ofRoles tag.type participants) evaluated).symm⟩
          simp only [Values.split_append]
          exact choose_threads _ _ regions tags others (env' first, env' second)
        · intro result
          have next := afterTwo_agrees agrees (t.first place.roles) (t.second place.roles)
            result.2.1 result.2.2 result.1
          have ih := ihRest _ _ _ rest' threadsRest fit.2.2 _ _ next.1
          exact restate (Prod.ext next.2.1 next.2.2) ih
      · cases threads
      · cases threads
    · cases threads
  · rename_i untouched
    split at threads
    · rename_i bodies' rest' plainBodies threadsRest
      have same := Except.ok.inj threads
      subst same
      refine passed_step ihRest threadsRest fit.2.2 agrees
        (labelledOperation model label functionTable oldTable side
          (.choose participants tag captures outputs covered) (Operands.eval env arguments)
          (bodies.denote (labelledMeaning model label functionTable oldTable side))) _ ?_
        (choose_passes _ _ (fit.2.1 untouched))
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
@[reducible] def calleeValues (roleMap : RoleMap) (inner : TranscriptRoles) {ports : List Located}
    (first : SideValue model side (Located.rename roleMap (t.first inner)))
    (second : SideValue model side (Located.rename roleMap (t.second inner)))
    (values : Values (SideValue model side) (ports.map (Located.rename roleMap))) :
    Values (SideValue model side) ((t.states inner ++ ports).map (Located.rename roleMap)) :=
  .cons first (.cons second values)

/-- The application of an image that threads is the application of the callee under the
handler: the callee's statement at the preimage side, with the caller's two values held by
the callee's transcript roles. -/
theorem apply_operation_threads (callees : CalleesThread table oldTable newTable fits)
    {header : ProtocolHeader} {callee : Var old header} {roleMap : RoleMap} {site : Nat}
    {permitted : (deployed && header.specificationOnly) = false}
    (threaded : ThreadedCallee t new place.roles roleMap header)
    (found : table.find callee (some threaded.inner) = some threaded.image)
    (fitCallee : (fits.get callee) threaded.inner (label site).below (Side.preimage roleMap side)
      (side place.roles.prover) (side place.roles.verifier) (congrArg side threaded.prover)
      (congrArg side threaded.verifier) handler)
    (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier))
    (arguments : Values (SideValue model side) (header.inputs.map (Located.rename roleMap)))
    (evaluated : Values (SideValue model side)
      ((t.header (some threaded.inner) header).inputs.map (Located.rename roleMap)))
    (same : evaluated = calleeValues roleMap threaded.inner
      (Held.along (X := model.Value t.prover) (congrArg side threaded.prover) state.1)
      (Held.along (X := model.Value t.verifier) (congrArg side threaded.verifier) state.2)
      arguments) :
    labelledOperation model label functionTable newTable side (operations := operations)
        (deployed := deployed) (.apply threaded.image roleMap site permitted) evaluated .nil =
      ((labelledOperation model label functionTable oldTable side (operations := operations)
          (deployed := deployed) (.apply callee roleMap site permitted) arguments
          .nil).interpretWith handler state).bind fun result =>
        .done (calleeValues roleMap threaded.inner
          (Held.along (X := model.Value t.prover) (congrArg side threaded.prover) result.2.1)
          (Held.along (X := model.Value t.verifier) (congrArg side threaded.verifier) result.2.2)
          result.1) := by
  subst same
  have calleeThreads := callees.threaded callee threaded.inner threaded.image found
    (label site).below (Side.preimage roleMap side) (side place.roles.prover)
    (side place.roles.verifier) (congrArg side threaded.prover) (congrArg side threaded.verifier)
    handler fitCallee state.1 state.2
    (unmapValues (F := SideValue model side) (Located.rename roleMap) header.inputs arguments)
  refine Eq.trans (congrArg (fun process => PIR.Process.bind process _) calleeThreads) ?_
  simp only [labelledOperation, PIR.Process.interpretWith_bind, PIR.Process.bind_assoc]
  rfl

theorem apply_threads (callees : CalleesThread table oldTable newTable fits) {Γ out : List Located}
    {header : ProtocolHeader} {callee : Var old header} {roleMap : RoleMap} {site : Nat}
    {permitted : (deployed && header.specificationOnly) = false}
    {arguments : Operands Γ (header.inputs.map (Located.rename roleMap))}
    {rest : Region (ProtocolDialect operations functions old deployed)
      (bindAll Γ (header.outputs.map (Located.rename roleMap))) out}
    (ihRest : Threads[rest]) :
    Threads[Region.letOp (dialect := ProtocolDialect operations functions old deployed)
      (.apply callee roleMap site permitted) arguments .nil rest] := by
  intro Δ rename first second image threads fit env env' agrees
  unfold threadRegion at threads
  split at threads
  · rename_i threaded found
    dsimp only at threads
    split at threads
    · rename_i rest' threadsRest
      have same := Except.ok.inj threads
      subst same
      refine PIR.thread_step_made handler _ _ _ _ _ threadedValues
        (fun result => calleeValues roleMap threaded.inner
          (Held.along (X := model.Value t.prover) (congrArg side threaded.prover) result.2.1)
          (Held.along (X := model.Value t.verifier) (congrArg side threaded.verifier) result.2.2)
          result.1) ?_ ?_
      · exact apply_operation_threads (functionTable := functionTable) callees threaded
          (threadedCallee_find found)
          (fit.1 threaded found) (env' first, env' second) (Operands.eval env arguments) _
          (cons_congr (retype_along threaded.prover env' first)
            (cons_congr (retype_along threaded.verifier env' second) (agrees.operands arguments)))
      · intro result
        have next := afterTwo_agrees agrees
          (Located.rename roleMap (t.first threaded.inner))
          (Located.rename roleMap (t.second threaded.inner))
          (Held.along (X := model.Value t.prover) (congrArg side threaded.prover) result.2.1)
          (Held.along (X := model.Value t.verifier) (congrArg side threaded.verifier) result.2.2) result.1
        have ih := ihRest _ _ _ rest' threadsRest fit.2.2 _ _ next.1
        refine restate (Prod.ext ?_ ?_) ih
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
      refine passed_step ihRest threadsRest fit.2.2 agrees
        (labelledOperation model label functionTable oldTable side
          (.apply callee roleMap site permitted) (Operands.eval env arguments) .nil) _ ?_
        ((fit.2.1 missing _).bind fun _ => PIR.Passes.done handler _)
      show ((newTable.get plainImage) (label site).below (Side.preimage roleMap side)
          (unmapValues (F := SideValue model side) (Located.rename roleMap) header.inputs
            (Operands.eval env' (rename.operands arguments)))).bind _ = _
      rw [agrees.operands, callees.plain callee plainImage foundPlain]
      rfl
    · cases threads
    · cases threads

mutual
  /-- The structural theorem for a region. -/
  theorem threadRegion_meaning (quiet : QuietTable functionTable)
      (sound : RuleSound rule sem functionTable)
      (callees : CalleesThread table oldTable newTable fits) {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out),
        Threads[region]
    | .ret values => ret_threads values
    | .stop reason => stop_threads reason
    | .bind body rest =>
        bind_threads (threadRegion_meaning quiet sound callees body)
          (threadRegion_meaning quiet sound callees rest)
    | .letOp (.at role op bodies) arguments .nil rest =>
        at_threads quiet (threadRegion_meaning quiet sound callees rest)
    | .letOp (.sample owner site law populated) arguments .nil rest =>
        sample_threads (threadRegion_meaning quiet sound callees rest)
    | .letOp (.exchange sender receiver site type) arguments .nil rest =>
        exchange_threads sound (threadRegion_meaning quiet sound callees rest)
    | .letOp (.draw owner receivers site law populated) arguments .nil rest =>
        draw_threads sound (threadRegion_meaning quiet sound callees rest)
    | .letOp (.repeat participants count carried collected captures covered) arguments
        (.cons body .nil) rest =>
        repeat_region_threads callees (threadRegion_meaning quiet sound callees body)
          (threadRegion_meaning quiet sound callees rest)
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest =>
        choose_region_threads callees
          (fun images => threadRegions_meaning quiet sound callees bodies _ images)
          (threadRegion_meaning quiet sound callees rest)
    | .letOp (.apply (header := header) callee roleMap site permitted) arguments .nil rest =>
        apply_threads callees (threadRegion_meaning quiet sound callees rest)

  /-- The structural theorem for the regions of a threaded operation. -/
  theorem threadRegions_meaning (quiet : QuietTable functionTable)
      (sound : RuleSound rule sem functionTable)
      (callees : CalleesThread table oldTable newTable fits)
      {signatures targets : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures)
        (threaded : ThreadedRegions t place.roles signatures targets)
        (images : Regions (ProtocolDialect operations functions new deployed) targets),
        threadRegions t rule table place regions threaded = .ok images →
        FitsAll t rule sem functionTable oldTable table fits place side label handler regions →
        RegionsThread handler threaded
          (regions.denote (labelledMeaning model label functionTable oldTable side))
          (images.denote (labelledMeaning model label functionTable newTable side))
    | regions, threaded, images, threads, fit =>
        match threaded, regions, images, threads, fit with
        | .nil, .nil, _, _, _ => trivial
        | .cons leading added threaded, .cons body tail, images, threads, fit => by
            simp only [threadRegions] at threads
            split at threads
            · rename_i body' tail' threadsBody threadsTail
              have same := Except.ok.inj threads
              subst same
              refine ⟨fun state before values => ?_,
                threadRegions_meaning quiet sound callees tail threaded tail' threadsTail fit.2⟩
              have start := afterLeading_agrees (Value := SideValue model side)
                (t.first place.roles) (t.second place.roles) state.1 state.2 values leading
                (rename := Mapping.start (Δ := ([] : List Located)) 0 rfl)
                (old := Environment.empty) (new := Environment.empty)
                (fun reference => reference.elimNil) before
              have ih := threadRegion_meaning quiet sound callees body _ _ _ body' threadsBody fit.1
                _ _ start.1
              exact ih.trans (congrArg
                (fun held : ThreadState model t (side place.roles.prover) (side place.roles.verifier) =>
                  ((body.denote (labelledMeaning model label functionTable oldTable side)
                    (Environment.ofValues (before.append values))).interpretWith handler held).bind
                      fun result => .done (threadedValues result))
                (Prod.ext start.2.1 start.2.2))
            · cases threads
            · cases threads
end

end Theorem

end Zkc.Core
