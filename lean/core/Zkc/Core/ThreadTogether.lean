module

public import Zkc.Core.EveryRun
public import Zkc.Core.ThreadProgram

public section

/-! A threading step for a side that holds both transcript roles: what it is stated with.

For a side that holds exactly one transcript role the image of a definition is the
definition interpreted by a handler (`Zkc.Core.ThreadTheorem`). For a side that holds both,
an exchange between the two performs no effect, so no handler of effects describes the
image. What holds instead is a refinement.

- `Refines relates old new`: whenever every run of `old` returns a value of which a
  condition holds, every run of `new` returns a value that `relates` to such a value. It is
  closed under sequencing (`Refines.bind`), a process refines itself (`Refines.same`), a
  process that stops is refined by everything (`Refines.halt`), and a draw of the old
  process, every reply to which is allowed, is refined by what refines the process after one
  reply (`Refines.draw`).
- `CoupledState coupled`: the invariant of the two threaded values of the side, as a
  relation `coupled` between the prover's value and the verifier's. `CoupledImage` says that
  a value of the image is a value of the definition packed with a coupled state.
- `RuleCouples`: the obligation on the meaning of a rule. When the rule emitted something
  at an exchange, then from a coupled state the exchange performs no effect, the verifier
  receives the prover's value and the next state is coupled; when it emitted something at a
  draw, then from a coupled state the draw performs no effect, both roles hold one coin and
  the next state is coupled.
- The laws of `repeat` and `choose` under refinement, for regions that the step threads
  (`repeat_refines`, `choose_refines`), and of an agreement (`agreed_related`).
- `CalleesRefine`: the statement for the callees, which the case of `apply` uses.

Nothing here is assumed of a program: `RuleCouples` is a hypothesis of the theorems that
use it and is proved for the Fiat–Shamir rule in `Zkc.Core.ThreadTogetherFiatShamir`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Core

open Zkc.Source

/-! ## Refinement -/

section Refinement

variable {model : Model}

/-- The new process refines the old one: whenever every run of the old process returns a
value of which a condition holds, every run of the new process returns a value that is
related to such a value. -/
@[expose] def Refines {α β : Type} (relates : α → β → Prop)
    (old : PIR.Process (Effects model) α) (new : PIR.Process (Effects model) β) : Prop :=
  ∀ holds : α → Prop, EveryRun holds old →
    EveryRun (fun image => ∃ value, holds value ∧ relates value image) new

namespace Refines

variable {α β γ δ : Type} {relates : α → β → Prop}

/-- Two processes that have returned related values. -/
theorem done {value : α} {image : β} (related : relates value image) :
    Refines relates (.done value : PIR.Process (Effects model) α) (.done image) :=
  fun _ every => ⟨value, every, related⟩

/-- A process that stops is refined by every process: no run of it returns. -/
theorem halt (reason : PIR.Stop) (new : PIR.Process (Effects model) β) :
    Refines relates (.halt reason : PIR.Process (Effects model) α) new :=
  fun _ every => every.elim

/-- A weaker relation. -/
theorem mono {weaker : α → β → Prop}
    (weakens : ∀ value image, relates value image → weaker value image)
    {old : PIR.Process (Effects model) α} {new : PIR.Process (Effects model) β}
    (refines : Refines relates old new) : Refines weaker old new :=
  fun holds every =>
    EveryRun.mono (fun image ⟨value, holding, related⟩ => ⟨value, holding, weakens value image related⟩)
      (refines holds every)

/-- Sequencing: a process followed by a continuation is refined by a refinement of the
process followed by refinements of the continuation on related values. -/
theorem bind {middle : α → β → Prop} {relates : γ → δ → Prop}
    {old : PIR.Process (Effects model) α} {new : PIR.Process (Effects model) β}
    {oldNext : α → PIR.Process (Effects model) γ} {newNext : β → PIR.Process (Effects model) δ}
    (before : Refines middle old new)
    (after : ∀ value image, middle value image → Refines relates (oldNext value) (newNext image)) :
    Refines relates (old.bind oldNext) (new.bind newNext) := by
  intro holds every
  rw [everyRun_bind] at every ⊢
  exact EveryRun.mono
    (fun image ⟨value, continues, related⟩ => after value image related holds continues)
    (before _ every)

/-- A process refines itself, with the same values. -/
theorem same (process : PIR.Process (Effects model) α) :
    Refines (fun value image => image = value) process process :=
  fun _ every => EveryRun.mono (fun value holding => ⟨value, holding, rfl⟩) every

/-- One process on both sides, followed by continuations that refine. -/
theorem bind_same {relates : β → γ → Prop} (process : PIR.Process (Effects model) α)
    {oldNext : α → PIR.Process (Effects model) β} {newNext : α → PIR.Process (Effects model) γ}
    (after : ∀ value, Refines relates (oldNext value) (newNext value)) :
    Refines relates (process.bind oldNext) (process.bind newNext) :=
  bind (same process) fun value image equal => equal ▸ after value

/-- The same statement of two processes that are equal to the ones named. -/
theorem of_eq {old otherOld : PIR.Process (Effects model) α}
    {new otherNew : PIR.Process (Effects model) β} (sameOld : otherOld = old)
    (sameNew : otherNew = new) (refines : Refines relates old new) :
    Refines relates otherOld otherNew := by
  subst sameOld
  subst sameNew
  exact refines

/-- A refinement followed, in the new process only, by something that returns without an
effect a value related to the old one. -/
theorem andThen {middle : α → β → Prop} {relates : α → γ → Prop}
    {old : PIR.Process (Effects model) α} {new : PIR.Process (Effects model) β}
    {newNext : β → PIR.Process (Effects model) γ} (before : Refines middle old new)
    (after : ∀ value image, middle value image →
      ∃ result, newNext image = .done result ∧ relates value result) :
    Refines relates old (new.bind newNext) := by
  have both : Refines relates (old.bind PIR.Process.done) (new.bind newNext) :=
      bind before fun value image related => by
    obtain ⟨result, returns, relatedResult⟩ := after value image related
    rw [returns]
    exact done relatedResult
  rw [PIR.Process.bind_done] at both
  exact both

/-- A draw of the old process, every reply to which is allowed: a process that refines what
follows one reply refines the draw. -/
theorem draw {site : Site} {law : SamplingRow} {inputs : Values model.Value law.inputs}
    {next : model.Value law.output → PIR.Process (Effects model) α}
    {new : PIR.Process (Effects model) β} (reply : model.Value law.output)
    (after : Refines relates (next reply) new) :
    Refines relates (.call (.draw site law inputs) next) new :=
  fun holds every => after holds (every reply)

end Refines

end Refinement

/-! ## The invariant of the two threaded values -/

section Coupled

variable {model : Model} {t : Threads}

/-- The two threaded values of a side that holds both transcript roles are coupled: the
relation holds of the prover's value and the verifier's. The memberships are parameters with
their proofs, so a state of a side is a state of the callee's side without a cast. -/
@[expose] def CoupledState (coupled : model.Value t.prover → model.Value t.verifier → Prop)
    {prover verifier : Bool} (isProver : prover = true) (isVerifier : verifier = true)
    (state : ThreadState model t prover verifier) : Prop :=
  coupled (Held.value prover isProver state.1) (Held.value verifier isVerifier state.2)

/-- A value of an image is a value of the definition packed with a coupled state. -/
@[expose] def CoupledImage (coupled : model.Value t.prover → model.Value t.verifier → Prop)
    {prover verifier : Bool} (isProver : prover = true) (isVerifier : verifier = true)
    {A B : Type} (pack : A × ThreadState model t prover verifier → B) (value : A) (image : B) :
    Prop :=
  ∃ state, CoupledState coupled isProver isVerifier state ∧ image = pack (value, state)

variable {coupled : model.Value t.prover → model.Value t.verifier → Prop}

/-- A state with the components of a coupled state is coupled. -/
theorem CoupledState.of_eq {prover verifier : Bool} {isProver : prover = true}
    {isVerifier : verifier = true} {state other : ThreadState model t prover verifier}
    (holds : CoupledState coupled isProver isVerifier state) (first : other.1 = state.1)
    (second : other.2 = state.2) : CoupledState coupled isProver isVerifier other := by
  obtain ⟨otherFirst, otherSecond⟩ := other
  cases first
  cases second
  exact holds

/-- A coupled state of a side as the state of the callee's side whose transcript roles run
as the side's. -/
theorem CoupledState.along {prover verifier calleeProver calleeVerifier : Bool}
    (sameProver : calleeProver = prover) (sameVerifier : calleeVerifier = verifier)
    {isProver : prover = true} {isVerifier : verifier = true}
    {state : ThreadState model t prover verifier}
    (holds : CoupledState coupled isProver isVerifier state) :
    CoupledState coupled (sameProver.trans isProver) (sameVerifier.trans isVerifier)
      (Held.along (X := model.Value t.prover) sameProver state.1,
        Held.along (X := model.Value t.verifier) sameVerifier state.2) := by
  subst sameProver
  subst sameVerifier
  exact holds

/-- A coupled state of the callee's side as a state of the side. -/
theorem CoupledState.back {prover verifier calleeProver calleeVerifier : Bool}
    (sameProver : calleeProver = prover) (sameVerifier : calleeVerifier = verifier)
    {isProver : prover = true} {isVerifier : verifier = true}
    {state : ThreadState model t calleeProver calleeVerifier}
    (holds : CoupledState coupled (sameProver.trans isProver) (sameVerifier.trans isVerifier)
      state) :
    CoupledState coupled isProver isVerifier
      (Held.back (X := model.Value t.prover) sameProver state.1,
        Held.back (X := model.Value t.verifier) sameVerifier state.2) := by
  subst sameProver
  subst sameVerifier
  exact holds

/-- One step of a threaded region: the image of an operation refines the operation and
returns its results packed with a coupled state, and what follows refines from every
coupled state. -/
theorem Refines.step {prover verifier : Bool} {isProver : prover = true}
    {isVerifier : verifier = true} {A B C D : Type}
    {source : PIR.Process (Effects model) A} {next : A → PIR.Process (Effects model) B}
    {image : PIR.Process (Effects model) C} {imageNext : C → PIR.Process (Effects model) D}
    (pack : B × ThreadState model t prover verifier → D)
    (make : A × ThreadState model t prover verifier → C)
    (acts : Refines (CoupledImage coupled isProver isVerifier make) source image)
    (rest : ∀ value state, CoupledState coupled isProver isVerifier state →
      Refines (CoupledImage coupled isProver isVerifier pack) (next value)
        (imageNext (make (value, state)))) :
    Refines (CoupledImage coupled isProver isVerifier pack) (source.bind next)
      (image.bind imageNext) :=
  Refines.bind acts fun value made ⟨state, holds, equal⟩ => equal ▸ rest value state holds

end Coupled

/-! ## The obligation on the meaning of a rule -/

section Rule

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {t : Threads}

/-- The meaning of a rule keeps the two threaded values of a side that holds both
transcript roles coupled, and performs no effect there. When the rule emitted something at
an exchange from the prover to the verifier, then from a coupled state the exchange returns
without an effect, the verifier receives the prover's value, and the next state is coupled.
When the rule emitted something at a draw between the two, then from a coupled state the
draw returns without an effect, the two roles hold one coin, and the next state is
coupled. -/
structure RuleCouples (rule : Rule t operations functions) (sem : RuleMeaning model t operations)
    (coupled : model.Value t.prover → model.Value t.verifier → Prop) : Prop where
  exchange : ∀ {protocols : List ProtocolHeader} {deployed : Bool} (place : Place) (site : Nat)
    (type : Ty) {Δ : List Located} (value : Var Δ ⟨type, place.roles.prover⟩)
    (first : Var Δ (t.first place.roles)) (second : Var Δ (t.second place.roles))
    (emitted : Emitted (ProtocolDialect operations functions protocols deployed) Δ
      [⟨type, place.roles.verifier⟩, t.first place.roles, t.second place.roles]),
    rule.exchange place site type value first second = .ok emitted →
    ∀ (effects : Site) (sent : model.Value type) (atProver : model.Value t.prover)
      (atVerifier : model.Value t.verifier), coupled atProver atVerifier →
      ∃ (nextProver : model.Value t.prover) (nextVerifier : model.Value t.verifier),
        sem.exchange true true place site effects type sent (atProver, atVerifier) =
            .done (sent, (nextProver, nextVerifier)) ∧
          coupled nextProver nextVerifier
  draw : ∀ {protocols : List ProtocolHeader} {deployed : Bool} (place : Place) (site : Nat)
    {inputs : List Ty} {output : Ty} (law : Var operations ⟨inputs, [output], .sampling⟩)
    {Δ : List Located} (first : Var Δ (t.first place.roles))
    (second : Var Δ (t.second place.roles))
    (emitted : Emitted (ProtocolDialect operations functions protocols deployed) Δ
      [⟨output, place.roles.prover⟩, ⟨output, place.roles.verifier⟩, t.first place.roles,
        t.second place.roles]),
    rule.draw place site law first second = .ok emitted →
    ∀ (effects : Site) (atProver : model.Value t.prover) (atVerifier : model.Value t.verifier),
      coupled atProver atVerifier →
      ∃ (coin : model.Value output) (nextProver : model.Value t.prover)
        (nextVerifier : model.Value t.verifier),
        sem.draw true true place site effects law (atProver, atVerifier) =
            .done ((coin, coin), (nextProver, nextVerifier)) ∧
          coupled nextProver nextVerifier

variable {rule : Rule t operations functions} {sem : RuleMeaning model t operations}
  {coupled : model.Value t.prover → model.Value t.verifier → Prop}

/-- The obligation at an exchange, for memberships that are proved to hold. -/
theorem RuleCouples.exchange_at (couples : RuleCouples rule sem coupled)
    {protocols : List ProtocolHeader} {deployed : Bool} {place : Place} {site : Nat} {type : Ty}
    {Δ : List Located} {value : Var Δ ⟨type, place.roles.prover⟩}
    {first : Var Δ (t.first place.roles)} {second : Var Δ (t.second place.roles)}
    {emitted : Emitted (ProtocolDialect operations functions protocols deployed) Δ
      [⟨type, place.roles.verifier⟩, t.first place.roles, t.second place.roles]}
    (emits : rule.exchange place site type value first second = .ok emitted)
    {prover verifier : Bool} (isProver : prover = true) (isVerifier : verifier = true)
    (effects : Site) (sent : Held (model.Value type) prover)
    (state : ThreadState model t prover verifier)
    (holds : CoupledState coupled isProver isVerifier state) :
    ∃ next, sem.exchange prover verifier place site effects type sent state =
        .done (Held.of verifier (Held.value prover isProver sent), next) ∧
      CoupledState coupled isProver isVerifier next := by
  subst isProver
  subst isVerifier
  obtain ⟨nextProver, nextVerifier, acts, coupledNext⟩ :=
    couples.exchange place site type value first second emitted emits effects sent state.1
      state.2 holds
  exact ⟨(nextProver, nextVerifier), acts, coupledNext⟩

/-- The obligation at a draw, for memberships that are proved to hold. -/
theorem RuleCouples.draw_at (couples : RuleCouples rule sem coupled)
    {protocols : List ProtocolHeader} {deployed : Bool} {place : Place} {site : Nat}
    {inputs : List Ty} {output : Ty} {law : Var operations ⟨inputs, [output], .sampling⟩}
    {Δ : List Located} {first : Var Δ (t.first place.roles)}
    {second : Var Δ (t.second place.roles)}
    {emitted : Emitted (ProtocolDialect operations functions protocols deployed) Δ
      [⟨output, place.roles.prover⟩, ⟨output, place.roles.verifier⟩, t.first place.roles,
        t.second place.roles]}
    (emits : rule.draw place site law first second = .ok emitted)
    {prover verifier : Bool} (isProver : prover = true) (isVerifier : verifier = true)
    (effects : Site) (state : ThreadState model t prover verifier)
    (holds : CoupledState coupled isProver isVerifier state) :
    ∃ (coin : model.Value output) (next : ThreadState model t prover verifier),
      sem.draw prover verifier place site effects law state =
          .done ((Held.of prover coin, Held.of verifier coin), next) ∧
        CoupledState coupled isProver isVerifier next := by
  subst isProver
  subst isVerifier
  obtain ⟨coin, nextProver, nextVerifier, acts, coupledNext⟩ :=
    couples.draw place site law first second emitted emits effects state.1 state.2 holds
  exact ⟨coin, (nextProver, nextVerifier), acts, coupledNext⟩

end Rule

/-! ## Agreement, iteration and selection under refinement -/

/-- A relation that holds of every pair of outcomes of two agreements on the same copies
holds of the two agreements. -/
theorem agreed_related {X α β : Type} (related : α → β → Prop) (same : X → X → Bool) (side : Side)
    {onValue : X → α} {other : X → β} {onDisagree : α} {otherDisagree : β}
    (relatedValue : ∀ value, related (onValue value) (other value))
    (relatedDisagree : related onDisagree otherDisagree) (roles : List Nat)
    (values : Values (fun role => Held X (side role)) roles)
    {onNone : roles.any side = false → α} {otherNone : roles.any side = false → β}
    (relatedNone : ∀ none, related (onNone none) (otherNone none)) :
    related (agreed same side onValue onDisagree roles values onNone)
      (agreed same side other otherDisagree roles values otherNone) := by
  have both := agreed_holds (fun pair : α × β => related pair.1 pair.2) same side
    (fun value => (onValue value, other value)) (onDisagree, otherDisagree) relatedValue
    relatedDisagree roles values (fun none => (onNone none, otherNone none)) relatedNone
  rw [agreed_map same side _ _ Prod.fst, agreed_map same side _ _ Prod.snd] at both
  exact both

section Laws

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {old new : List ProtocolHeader} {deployed : Bool} {t : Threads}
  {functionTable : FunctionTable model functions} {oldTable : ProtocolTable model old}
  {newTable : ProtocolTable model new} {place : Place} {side : Side} {label : Nat → Site}
  {coupled : model.Value t.prover → model.Value t.verifier → Prop}
  {isProver : side place.roles.prover = true} {isVerifier : side place.roles.verifier = true}

/-- The iterations of a threaded loop refine the iterations of the old loop, with the same
collected values and a coupled state before the carried ones, when its step refines the old
step from every coupled state. -/
theorem repeatIterations_refines (carried collected : List Located)
    {step : Nat → Values (SideValue model side) carried →
      PIR.Process (Effects model) (Values (SideValue model side) (collected ++ carried))}
    {image : Nat → Values (SideValue model side) (t.states place.roles ++ carried) →
      PIR.Process (Effects model)
        (Values (SideValue model side) (collected ++ (t.states place.roles ++ carried)))}
    (related : ∀ (iteration : Nat) (values : Values (SideValue model side) carried)
      (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier)),
      CoupledState coupled isProver isVerifier state →
      Refines (CoupledImage coupled isProver isVerifier (threadedAfter collected))
        (step iteration values) (image iteration (.cons state.1 (.cons state.2 values)))) :
    ∀ (remaining done : Nat) (initial : Values (SideValue model side) carried)
      (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier))
      (earlier : Values (SideValue model side) (collectedSequencesAt (some done) collected)),
      CoupledState coupled isProver isVerifier state →
      Refines
        (CoupledImage coupled isProver isVerifier
          (fun final : (Values (SideValue model side) carried ×
              Values (SideValue model side)
                (collectedSequencesAt (some (iterationsAfter remaining done)) collected)) ×
              ThreadState model t (side place.roles.prover) (side place.roles.verifier) =>
            (Values.cons (Value := SideValue model side) (ty := t.first place.roles) final.2.1
              (Values.cons (ty := t.second place.roles) final.2.2 final.1.1), final.1.2)))
        (repeatIterations model side carried collected step remaining done initial earlier)
        (repeatIterations model side (t.states place.roles ++ carried) collected image remaining
          done (.cons state.1 (.cons state.2 initial)) earlier)
  | 0, _, _, state, _, holds => Refines.done ⟨state, holds, rfl⟩
  | remaining + 1, done, initial, state, earlier, holds => by
      rw [repeatIterations_succ, repeatIterations_succ]
      refine Refines.bind (related done initial state holds) ?_
      rintro result made ⟨next, coupledNext, rfl⟩
      show Refines _ _ (repeatIterations model side (t.states place.roles ++ carried) collected
        image remaining (done + 1) (Values.split collected (threadedAfter collected (result, next))).2
        (sideCollectedPush model side collected
          (Values.split collected (threadedAfter collected (result, next))).1 earlier))
      rw [split_threadedAfter]
      exact repeatIterations_refines carried collected related remaining (done + 1) _ next _
        coupledNext

/-- The loop of a threaded `repeat` once its count is agreed refines the old loop, and
returns the coupled state between the sequences of the collected values, which are the old
loop's, and the carried values. -/
theorem repeatProcess_refines (count : RepeatCount) (carried collected : List Located)
    {step : Nat → Values (SideValue model side) carried →
      PIR.Process (Effects model) (Values (SideValue model side) (collected ++ carried))}
    {image : Nat → Values (SideValue model side) (t.states place.roles ++ carried) →
      PIR.Process (Effects model)
        (Values (SideValue model side) (collected ++ (t.states place.roles ++ carried)))}
    (related : ∀ (iteration : Nat) (values : Values (SideValue model side) carried)
      (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier)),
      CoupledState coupled isProver isVerifier state →
      Refines (CoupledImage coupled isProver isVerifier (threadedAfter collected))
        (step iteration values) (image iteration (.cons state.1 (.cons state.2 values))))
    (agreed : Nat) (initial : Values (SideValue model side) carried)
    (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier))
    (holds : CoupledState coupled isProver isVerifier state) :
    Refines
      (CoupledImage coupled isProver isVerifier
        (threadedAfter (collectedSequencesAt count.size collected)))
      (repeatProcess model side count carried collected step agreed initial)
      (repeatProcess model side count (t.states place.roles ++ carried) collected image agreed
        (.cons state.1 (.cons state.2 initial))) := by
  cases count with
  | static number =>
      rw [repeatProcess_static, repeatProcess_static]
      refine Refines.bind
        (repeatIterations_refines carried collected related number 0 initial state _ holds) ?_
      rintro final made ⟨next, coupledNext, rfl⟩
      refine Refines.done ⟨next, coupledNext, ?_⟩
      show _ = threadedAfter _ (Values.append _ _, _)
      simp only [threadedAfter, Values.split_append]
  | runtime maximum =>
      by_cases within : agreed ≤ maximum
      · rw [repeatProcess_within model side within, repeatProcess_within model side within]
        refine Refines.bind
          (repeatIterations_refines carried collected related agreed 0 initial state _ holds) ?_
        rintro final made ⟨next, coupledNext, rfl⟩
        refine Refines.done ⟨next, coupledNext, ?_⟩
        show _ = threadedAfter _ (Values.append _ _, _)
        simp only [threadedAfter, Values.split_append]
      · rw [repeatProcess_beyond model side (Nat.lt_of_not_le within),
          repeatProcess_beyond model side (Nat.lt_of_not_le within)]
        exact Refines.halt _ _

/-- A threaded `repeat` refines the old one: the loop that carries the two values before
its own returns the sequences of the collected values of the old loop, a coupled state after
them and the carried values, when its region, which takes the two values after the iteration
numbers and returns them after the values it collects, refines the old region from every
coupled state. -/
theorem repeat_refines {participants : List Nat} {count : RepeatCount}
    {carried collected captures : List Located}
    {covered : Located.heldBy participants collected = true}
    (regions : Values (RegionFunction (SideValue model side) (Effects model))
      [(Located.ofRoles .nat participants ++ (carried ++ captures), collected ++ carried)])
    (images : Values (RegionFunction (SideValue model side) (Effects model))
      [(Located.ofRoles .nat participants ++ (t.states place.roles ++ (carried ++ captures)),
        collected ++ (t.states place.roles ++ carried))])
    (refines : ∀ (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier))
      (numbers : Values (SideValue model side) (Located.ofRoles .nat participants))
      (values : Values (SideValue model side) (carried ++ captures)),
      CoupledState coupled isProver isVerifier state →
      Refines (CoupledImage coupled isProver isVerifier (threadedAfter collected))
        ((regions.get .here) (numbers.append values))
        ((images.get .here) (numbers.append (.cons state.1 (.cons state.2 values)))))
    (counts : Values (SideValue model side) (count.operands participants))
    (rest : Values (SideValue model side) (carried ++ captures))
    (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier))
    (holds : CoupledState coupled isProver isVerifier state) :
    Refines
      (CoupledImage coupled isProver isVerifier
        (threadedAfter (collectedSequencesAt count.size collected)))
      (labelledOperation model label functionTable oldTable side (operations := operations)
        (deployed := deployed) (.repeat participants count carried collected captures covered)
        (counts.append rest) regions)
      (labelledOperation model label functionTable newTable side (operations := operations)
        (deployed := deployed)
        (.repeat participants count (t.states place.roles ++ carried) collected captures covered)
        (counts.append (.cons state.1 (.cons state.2 rest))) images) := by
  simp only [labelledOperation, repeatOperation, Values.split_append]
  refine agreed_related _ Nat.beq side ?_ (Refines.halt _ _) participants _ ?_
  · intro agreed
    exact repeatProcess_refines count carried collected
      (fun _ _ state holds => refines state _ _ holds) agreed _ state holds
  · intro none
    refine Refines.done ⟨state, holds, ?_⟩
    show _ = threadedAfter _ (Values.append _ _, _)
    simp only [threadedAfter, Values.split_append]
    rfl

/-- The regions of a threaded operation refine the old regions from every coupled state:
each takes the two threaded values after the values that lead its inputs. -/
@[expose] def RegionsRefine (coupled : model.Value t.prover → model.Value t.verifier → Prop)
    (isProver : side place.roles.prover = true) (isVerifier : side place.roles.verifier = true) :
    {signatures targets : List (List Located × List Located)} →
      ThreadedRegions t place.roles signatures targets →
      Values (RegionFunction (SideValue model side) (Effects model)) signatures →
      Values (RegionFunction (SideValue model side) (Effects model)) targets → Prop
  | _, _, .nil, _, _ => True
  | _, _, .cons leading added tail, olds, images =>
      (∀ (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier))
          (before : Values (SideValue model side) leading)
          (values : Values (SideValue model side) added),
        CoupledState coupled isProver isVerifier state →
        Refines (CoupledImage coupled isProver isVerifier (threadedValues (roles := place.roles)))
          ((olds.get .here) (before.append values))
          ((images.get .here) (before.append (.cons state.1 (.cons state.2 values))))) ∧
      RegionsRefine coupled isProver isVerifier tail olds.tail images.tail

/-- The selected arm of a threaded choice refines the selected arm of the old choice. -/
theorem selectArm_refines (captures outputs : List Located) :
    ∀ (count : Nat)
      (olds : Values (RegionFunction (SideValue model side) (Effects model))
        (List.replicate count (captures, outputs)))
      (images : Values (RegionFunction (SideValue model side) (Effects model))
        (List.replicate count
          (t.states place.roles ++ captures, t.states place.roles ++ outputs))),
      RegionsRefine coupled isProver isVerifier (t.arms place.roles captures outputs count) olds
        images →
      ∀ (number : Fin count)
        (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier))
        (values : Values (SideValue model side) captures),
        CoupledState coupled isProver isVerifier state →
        Refines (CoupledImage coupled isProver isVerifier (threadedValues (roles := place.roles)))
          (selectArm (captures, outputs) count olds number values)
          (selectArm (t.states place.roles ++ captures, t.states place.roles ++ outputs) count
            images number (.cons state.1 (.cons state.2 values)))
  | 0, _, _, _, number, _, _, _ => number.elim0
  | _ + 1, _, _, refines, ⟨0, _⟩, state, values, holds => refines.1 state .nil values holds
  | count + 1, olds, images, refines, ⟨number + 1, below⟩, state, values, holds =>
      selectArm_refines captures outputs count olds.tail images.tail refines.2
        ⟨number, Nat.lt_of_succ_lt_succ below⟩ state values holds

/-- The region of an alternative of a threaded choice, which takes the two values after the
payloads, refines the region of that alternative of the old choice. -/
theorem alternativeProcess_refines {participants : List Nat} (captures outputs : List Located) :
    ∀ (alternatives : List Ty)
      (olds : Values (RegionFunction (SideValue model side) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs)))
      (images : Values (RegionFunction (SideValue model side) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ (t.states place.roles ++ captures),
            t.states place.roles ++ outputs))),
      RegionsRefine coupled isProver isVerifier
        (t.alternatives place.roles participants captures outputs alternatives) olds images →
      ∀ (number : Nat)
        (copies : Values (fun role => Held (Ty.Variant model.Carrier alternatives) (side role))
          participants)
        (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier))
        (values : Values (SideValue model side) captures),
        CoupledState coupled isProver isVerifier state →
        Refines (CoupledImage coupled isProver isVerifier (threadedValues (roles := place.roles)))
          (alternativeProcess model side participants captures outputs alternatives olds number
            copies values)
          (alternativeProcess model side participants (t.states place.roles ++ captures)
            (t.states place.roles ++ outputs) alternatives images number copies
            (.cons state.1 (.cons state.2 values)))
  | [], _, _, _, _, _, _, _, _ => Refines.halt _ _
  | payload :: rest, olds, images, refines, 0, copies, state, values, holds => by
      cases found : firstPayloads model side payload rest participants copies with
      | none =>
          rw [alternativeProcess_first_other found, alternativeProcess_first_other found]
          exact Refines.halt _ _
      | some payloads =>
          rw [alternativeProcess_first found, alternativeProcess_first found]
          exact refines.1 state _ values holds
  | payload :: rest, olds, images, refines, number + 1, copies, state, values, holds => by
      cases found : laterCopies model side payload rest participants copies with
      | none =>
          rw [alternativeProcess_later_other number found,
            alternativeProcess_later_other number found]
          exact Refines.halt _ _
      | some later =>
          rw [alternativeProcess_later number found, alternativeProcess_later number found]
          exact alternativeProcess_refines captures outputs rest olds.tail images.tail refines.2
            number later state values holds

/-- The region that a tag selects of a threaded choice refines the region that it selects
of the old choice. -/
theorem chosenRegion_refines {participants : List Nat} (captures outputs : List Located) :
    ∀ (tag : ChoiceTag)
      (olds : Values (RegionFunction (SideValue model side) (Effects model))
        (tag.regions participants captures outputs))
      (images : Values (RegionFunction (SideValue model side) (Effects model))
        (tag.regions participants (t.states place.roles ++ captures)
          (t.states place.roles ++ outputs))),
      RegionsRefine coupled isProver isVerifier
        (t.choice place.roles participants captures outputs tag) olds images →
      ∀ (copies : Values (fun role => Held (model.Value tag.type) (side role)) participants)
        (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier))
        (values : Values (SideValue model side) captures) (value : model.Value tag.type),
        CoupledState coupled isProver isVerifier state →
        Refines (CoupledImage coupled isProver isVerifier (threadedValues (roles := place.roles)))
          (chosenRegion model side participants captures outputs tag olds copies values value)
          (chosenRegion model side participants (t.states place.roles ++ captures)
            (t.states place.roles ++ outputs) tag images copies
            (.cons state.1 (.cons state.2 values)) value)
  | .condition, olds, images, refines, _, state, values, _, holds =>
      selectArm_refines captures outputs 2 olds images refines _ state values holds
  | .arm count, olds, images, refines, _, state, values, _, holds =>
      selectArm_refines captures outputs count olds images refines _ state values holds
  | .alternative _ alternatives, olds, images, refines, copies, state, values, _, holds =>
      alternativeProcess_refines captures outputs alternatives olds images refines _ copies state
        values holds

/-- A threaded `choose` refines the old one: the choice whose arms capture and return the
two values returns the old results after a coupled state, when its arms refine the old arms
from every coupled state. A participant holds the two values, so some participant is in the
side. -/
theorem choose_refines {participants : List Nat} {tag : ChoiceTag}
    {captures outputs : List Located} {covered : Located.heldBy participants outputs = true}
    {held : Located.heldBy participants (t.states place.roles ++ outputs) = true}
    (arms : Values (RegionFunction (SideValue model side) (Effects model))
      (tag.regions participants captures outputs))
    (images : Values (RegionFunction (SideValue model side) (Effects model))
      (tag.regions participants (t.states place.roles ++ captures)
        (t.states place.roles ++ outputs)))
    (refines : RegionsRefine coupled isProver isVerifier
      (t.choice place.roles participants captures outputs tag) arms images)
    (tags : Values (SideValue model side) (Located.ofRoles tag.type participants))
    (rest : Values (SideValue model side) captures)
    (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier))
    (holds : CoupledState coupled isProver isVerifier state) :
    Refines (CoupledImage coupled isProver isVerifier (threadedValues (roles := place.roles)))
      (labelledOperation model label functionTable oldTable side (operations := operations)
        (deployed := deployed) (.choose participants tag captures outputs covered)
        (tags.append rest) arms)
      (labelledOperation model label functionTable newTable side (operations := operations)
        (deployed := deployed)
        (.choose participants tag (t.states place.roles ++ captures)
          (t.states place.roles ++ outputs) held)
        (tags.append (.cons state.1 (.cons state.2 rest))) images) := by
  simp only [labelledOperation, Values.split_append]
  refine agreed_related _ (tag.same model.Carrier) side
    (fun value => chosenRegion_refines captures outputs tag arms images refines _ state rest value
      holds)
    (Refines.halt _ _) participants _ ?_
  intro none
  have absentFirst : side place.roles.prover = false :=
    not_held_of_heldBy (located := t.first place.roles) held none List.mem_cons_self
  exact absurd (absentFirst.symm.trans isProver) Bool.false_ne_true

/-! ## The statement for the callees -/

/-- What the case of `apply` uses, for a side that holds both transcript roles of the
callee. An image that threads refines the callee from every coupled state and returns the
callee's results after a coupled state; the image with the callee's own header has the
callee's meaning. -/
structure CalleesRefine (coupled : model.Value t.prover → model.Value t.verifier → Prop)
    (table : CalleeTable t.header old new) (oldTable : ProtocolTable model old)
    (newTable : ProtocolTable model new) : Prop where
  threaded : ∀ {header : ProtocolHeader} (callee : Var old header) (inner : TranscriptRoles)
    (image : Var new (t.header (some inner) header)), table.find callee (some inner) = some image →
    ∀ (path : List Nat) (side : Side) (isProver : side inner.prover = true)
      (isVerifier : side inner.verifier = true)
      (state : ThreadState model t (side inner.prover) (side inner.verifier))
      (arguments : Values (SideValue model side) header.inputs),
      CoupledState coupled isProver isVerifier state →
      Refines (CoupledImage coupled isProver isVerifier (threadedValues (roles := inner)))
        ((oldTable.get callee) path side arguments)
        ((newTable.get image) path side (.cons state.1 (.cons state.2 arguments)))
  plain : PlainCallees table oldTable newTable

/-- The images of the callees refine after one more protocol of the result. -/
theorem CalleesRefine.weaken {table : CalleeTable t.header old new}
    (callees : CalleesRefine coupled table oldTable newTable) (added : ProtocolHeader)
    (meaning : added.Meaning model) :
    CalleesRefine coupled (table.weaken added) oldTable (.cons meaning newTable) := by
  refine ⟨fun {header} callee inner image named => ?_, PlainCallees.weaken callees.plain added meaning⟩
  rw [CalleeTable.find_weaken] at named
  cases earlier : table.find callee (some inner) with
  | none => rw [earlier] at named; cases named
  | some earlierImage =>
      rw [earlier] at named
      have same : earlierImage.there = image := Option.some.inj named
      subst same
      exact callees.threaded callee inner earlierImage earlier

end Laws

end Zkc.Core
