import Zkc.Tests.Core.Consumers
import Zkc.Tests.Core.Shapes
import Zkc.Core.Projection.Theorem
import Zkc.Core.Evidence.Call

/-!
Controls: examples that exercise the definitions at their edges, each with what it shows, and
the theorems that are the reasons for the definitions' shape.
-/

namespace Zkc.Core.Controls

open Zkc.Core Zkc.Core.Shapes

-- These tests compute the meaning of small programs by Lean's own reduction.
unseal Zkc.Core.fnMeaning Zkc.Core.roleMeaning Zkc.Core.protocolMeaning

set_option maxRecDepth 4000

/-! ## What the world gives -/

/-- No source answers at every type (the empty variant has no value), so `anyOrder` cannot ask for one. -/
theorem no_globally_total_source {V : Vocabulary} (M : Model V) (source : Source M) :
    ¬ (∀ at_ τ, (source at_ τ).isSome) := by
  intro total
  have h := total ⟨[], ⟨0⟩⟩ (.variant ⟨0⟩ .nil)
  cases e : source ⟨[], ⟨0⟩⟩ (.variant ⟨0⟩ .nil) with
  | none => simp [e] at h
  | some v => nomatch v

/-- A source of no values. -/
def emptySource : Source plainModel := fun _ _ => Option.none

/-- A source that answers every natural with `0`. -/
def zeroSource : Source plainModel := fun _ τ =>
  match τ with
  | .nat => some (0 : Nat)
  | _ => Option.none

/-- A protocol of one private sample. -/
def privateSample : Term (protocolDialect Shapes.plain Shapes.none) (Ctx.positional []) [] :=
  .op ⟨1⟩ (.given (.coin ()) 0 [] [] .nat ⟨_, rfl, rfl, rfl⟩
    (fun _ h => nomatch h) (by decide)) .nil (.cons 0 .nil) <| .ret .nil

def sampleHeader : ProtocolHeader Shapes.plain := ⟨⟨44⟩, 2, [], [], shapeOf privateSample⟩

def sampleTyped : Typed Shapes.plain := ⟨⟨[], [sampleHeader]⟩,
  .protocol sampleHeader (Names.counting 0 _) privateSample
    ⟨by simp [Within, ProtocolOp.Within, privateSample, sampleHeader], by decide,
    by simp [Enclosed, privateSample], rfl, rfl, rfl, rfl, by unfold Term.BoundOnce; decide⟩ .nil,
    by decide⟩

/-- The empty source does not feed the private sample, so `complete` asks nothing of it. -/
theorem empty_source_not_fed :
    ¬ Fed plainModel emptySource (protocolMeaning plainModel sampleTyped .head [] .nil) := by
  intro h
  obtain ⟨v, hv, _⟩ := h
  cases hv

/-- A source that answers the sample feeds the protocol. -/
theorem zero_source_fed :
    Fed plainModel zeroSource (protocolMeaning plainModel sampleTyped .head [] .nil) :=
  ⟨(0 : Nat), rfl, trivial⟩

/-- Against that source the protocol returns. -/
theorem zero_source_returns :
    GExec plainModel zeroSource (protocolMeaning plainModel sampleTyped .head [] .nil)
      (.returned (.nil, ())) :=
  ⟨_, .given rfl .done⟩

/-- Against the empty source, the sampling role starves at the sample. -/
theorem sampler_starves :
    Starves plainModel emptySource
      (Statements.projections sampleTyped plainModel .head [] .nil) 0 ⟨[], ⟨1⟩⟩ :=
  ⟨.nat, rfl, .inl ⟨_, _, _, _, _, rfl⟩⟩

/-! ## Progress of the scheduler -/

/-- A protocol of one role that does nothing. -/
def idle : Term (protocolDialect Shapes.plain Shapes.none) (Ctx.positional []) [] := .ret .nil

def idleHeader : ProtocolHeader Shapes.plain := ⟨⟨45⟩, 1, [], [], shapeOf idle⟩

def idleTyped : Typed Shapes.plain := ⟨⟨[], [idleHeader]⟩,
  .protocol idleHeader (Names.counting 0 _) idle ⟨by simp [Within, idle], by decide,
    by simp [Enclosed, idle], rfl, rfl, rfl, rfl, by unfold Term.BoundOnce; decide⟩ .nil, by decide⟩

/-- A scheduler that never takes a step. -/
def neverSchedule {V : Vocabulary} (c : Functions V) : Functions V :=
  { c with schedule := fun _ _ _ _ _ _ _ => ([], fun _ => .limit) }

/-- The projections of the idle protocol can go no further at the start. -/
theorem idle_quiescent (source : Source plainModel) :
    Quiescent plainModel source (Statements.projections idleTyped plainModel .head [] .nil) := by
  intro event next step
  cases step with
  | give h _ => cases h
  | get h _ => cases h
  | own h _ => cases h
  | hear h _ => cases h
  | begin h => cases h
  | settle h => cases h

/-- A scheduler that never takes a step does not satisfy `schedulerRuns`. -/
theorem never_schedule_refused (c : Functions Shapes.plain) :
    ¬ Statements.schedulerRuns (neverSchedule c) := by
  intro h
  exact (h idleTyped plainModel idleHeader .head .nil emptySource).2 [] _ _ .refl
    (idle_quiescent emptySource) 0 (Nat.le_refl 0) 0 rfl

/-! ## A stop keeps what the layers below reached -/

abbrev Request : Sig := ⟨Unit, fun _ => Unit⟩

def stopped : Stop := .declared .abort ⟨[], ⟨17⟩⟩

def noRetry : Retry Request NoSig Stop where
  bound := 0
  begins := fun _ => Option.none
  ends := fun _ => Option.none
  retriable := Stop.isAbort
  mark := fun _ p => p

/-- An upper clause that asks below once and then aborts, leaving its own state. -/
def inner : Handler Request Request Stop Unit where
  clause _ s := .call () fun _ => .halt (stopped, s)
  again _ _ s := .ok s

/-- A lower layer that counts what it answers. -/
def counter : Handler Request NoSig Stop Nat where
  clause _ n := .done ((), n + 1)
  again _ _ n := .ok n

def client : Process Request Stop Unit := .call () fun _ => .done ()

/-- The count below survives the abort above in the composed run. -/
theorem composition_keeps_lower (n : Nat) :
    (inner.over counter).run noRetry client ((), n) = .halt (stopped, ((), n + 1)) := rfl

/-! ## Distinct keys -/

/-- Two sends with one key, from two roles to one. -/
def colliding :
    Term (protocolDialect Shapes.plain Shapes.none) (Ctx.positional [nat [0], nat [2]]) [] :=
  .op ⟨7⟩ (.flow .message 0 [1] (by decide) (by decide)) (.cons (var 0) .nil) (.cons 2 .nil) <|
  .op ⟨7⟩ (.flow .message 2 [1] (by decide) (by decide)) (.cons (var 1) .nil) (.cons 3 .nil) <|
  .ret .nil

/-- They are not `Distinct`, so no program has them. -/
theorem colliding_not_distinct : ¬ Term.Distinct colliding := by
  unfold Term.Distinct
  decide +kernel

abbrev M := plainModel
abbrev B (r : Role) := HList (RV M r) ([] : List (LTy Shapes.plain))

def inputs : HList (LVal M) [nat [0], nat [2]] := .cons (10 : Nat) (.cons (20 : Nat) .nil)

def at_ : Occurrence := ⟨[], ⟨7⟩⟩

def q0 (r : Role) : Program M (B r) := .call (.give .message [1] at_ .nat 10) fun _ => .done .nil
def q1 (r : Role) : Program M (B r) := .call (.get .message 0 at_ .nat) fun _ =>
  .call (.get .message 2 at_ .nat) fun _ => .done .nil
def q2 (r : Role) : Program M (B r) := .call (.give .message [1] at_ .nat 20) fun _ => .done .nil

def initialNet : Net M (fun _ => Stop) B := fun r =>
  if r = 0 then q0 r else if r = 1 then q1 r else if r = 2 then q2 r else .done .nil

def stuckNet : Net M (fun _ => Stop) B := fun r =>
  if r = 0 then q0 r else if r = 1 then q1 r else .done .nil

def occupied : Pending M := (Pending.empty M).post M at_ [1] ⟨2, .message, .nat, 20⟩

/-- The projections of the colliding term, as a bare term. -/
def bareNet : Net M (fun _ => Stop) B := fun r =>
  (project r colliding).denote (roleSem M r noFns noPrograms) [] (restrict M r (Env.positional inputs))

/-- The first and third roles send at one key, and the second receives both there. -/
theorem bare_initial : bareNet = initialNet := by
  funext r
  by_cases h0 : r = 0
  · subst r; rfl
  by_cases h1 : r = 1
  · subst r; rfl
  by_cases h2 : r = 2
  · subst r; rfl
  simp [bareNet, colliding, project, ProtocolOp.project, Term.denote_op, Term.denote_ret, roleSem, initialNet, h0, h1,
    h2, roleOp, Process.bind, Env.all]

/-- The third role may send first and occupy the second role's slot at that key. -/
theorem second_send_first (source : Source M) :
    Step M source (initialNet, Pending.empty M) (.gave 2 .message [1] at_ .nat 20)
      (stuckNet, occupied) := by
  have step := Step.give (M := M) (source := source) (net := initialNet)
    (pending := Pending.empty M) (r := 2) (kind := FlowKind.message) (getters := [1])
    (at_ := at_) (τ := Ty.nat) (x := 20) (k := fun _ => .done (.nil : B 2))
    (by rfl) (by intros; rfl)
  have eq : Net.set M initialNet 2 (.done (.nil : B 2)) = stuckNet := by
    funext r
    simp only [Net.set, initialNet, stuckNet]
    by_cases h0 : r = 0
    · subst r; rfl
    by_cases h1 : r = 1
    · subst r; rfl
    by_cases h2 : r = 2
    · subst r; rfl
    · simp [h0, h1, h2]
  simpa [eq, occupied] using step

/-- Then the second role reads the wrong sender and the first cannot send: no role moves. -/
theorem stuck (source : Source M) : Quiescent M source (stuckNet, occupied) := by
  intro event next step
  cases step with
  | give h free =>
      rename_i r kind getters where_ τ x k
      by_cases h0 : r = 0
      · subst r
        simp only [stuckNet, ite_true, q0] at h
        cases h
        have bad := free 1 (by simp)
        simp [occupied, Pending.post, Pending.put] at bad
      · by_cases h1 : r = 1
        · subst r; simp [stuckNet, q1] at h
        · simp [stuckNet, h0, h1] at h
  | get h pending =>
      rename_i r kind giver where_ τ x k
      by_cases h0 : r = 0
      · subst r; simp [stuckNet, q0] at h
      · by_cases h1 : r = 1
        · subst r
          simp only [stuckNet, ite_true, q1] at h
          cases h
          simp [occupied, Pending.post, Pending.put] at pending
        · simp [stuckNet, h0, h1] at h
  | own h sourceEq =>
      rename_i r kind hearers where_ ins payload τ v k
      by_cases h0 : r = 0
      · subst r; simp [stuckNet, q0] at h
      · by_cases h1 : r = 1
        · subst r; simp [stuckNet, q1] at h
        · simp [stuckNet, h0, h1] at h
  | hear h sourceEq =>
      rename_i r kind owner where_ τ v k
      by_cases h0 : r = 0
      · subst r; simp [stuckNet, q0] at h
      · by_cases h1 : r = 1
        · subst r; simp [stuckNet, q1] at h
        · simp [stuckNet, h0, h1] at h
  | begin h =>
      rename_i r where_ k
      by_cases h0 : r = 0
      · subst r; simp [stuckNet, q0] at h
      · by_cases h1 : r = 1
        · subst r; simp [stuckNet, q1] at h
        · simp [stuckNet, h0, h1] at h
  | settle h =>
      rename_i r where_ k
      by_cases h0 : r = 0
      · subst r; simp [stuckNet, q0] at h
      · by_cases h1 : r = 1
        · subst r; simp [stuckNet, q1] at h
        · simp [stuckNet, h0, h1] at h

/-- The colliding term returns as a protocol. -/
theorem bare_global_returns (source : Source M) :
    GExec M source (colliding.denote (protocolSem M noFns noProtocols) [] (Env.positional inputs))
      (.returned .nil) :=
  ⟨_, .flow (.flow .done)⟩

/-- Its projected network reaches a state where no role can move. -/
theorem bare_reachable_stuck (source : Source M) :
    Reach M source (bareNet, Pending.empty M) [.gave 2 .message [1] at_ .nat 20]
      (stuckNet, occupied) := by
  rw [bare_initial]
  exact .step (second_send_first source) .refl

/-- That state is not the protocol's return, which is why programs carry `Distinct`. -/
theorem bare_not_returned : ¬ Ended M
    (fun r (out : HList (LVal M) ([] : List (LTy Shapes.plain))) mine => mine = hideAll M r out)
    stuckNet (.returned .nil) := by
  intro h
  obtain ⟨b, bad, _⟩ := h 0
  simp [stuckNet, q0] at bad

/-! ## An attempt is a region; its retry runs the body -/

/-- An attempt of the first role whose body samples privately, gives the sample to the second
role, and aborts. -/
def retriedBody : Term (protocolDialect Shapes.plain Shapes.none) (Ctx.positional []) [] :=
  .attempt ⟨80⟩ [0] ⟨0, rfl⟩ (.cons 0 .nil)
    (.op ⟨81⟩ (.given (.coin ()) 0 [] [] .nat ⟨_, rfl, rfl, rfl⟩ (fun _ h => nomatch h)
      (by decide)) .nil (.cons 1 .nil) <|
     .op ⟨84⟩ (.flow .message 0 [1] (by decide) (by decide)) (.cons (var 1) .nil) (.cons 2 .nil) <|
     .op ⟨82⟩ (.compute [0] (.literal .bool [0] rfl) [] rfl (fun _ h => nomatch h)) .nil
      (.cons 3 .nil) <|
     .guard ⟨83⟩ [0] (var 3) ⟨rfl, by decide, by decide⟩ .abort <|
     .ret .nil) .nil <|
  .ret .nil

/-- The retry of two attempts at the site of the attempt `80`. -/
def twoAttempts : Retry (RSig plainModel) (RSig plainModel) Stop :=
  retryOf plainModel (some (2, ⟨[], ⟨80⟩⟩))

/-- The first role's program of a protocol under the retry of two attempts. -/
def retriedRun (t : Term (protocolDialect Shapes.plain Shapes.none) (Ctx.positional []) []) :
    Process (RSig plainModel) (Stop × Unit) (HList (RV plainModel 0) [] × Unit) :=
  (Handler.none (RSig plainModel) Stop).run twoAttempts
    ((project 0 t).denote (roleSem plainModel 0 noFns noPrograms) [] (Env.positional .nil)) ()

/-- The occurrences at which a run asks for private coins, while every coin is `0`. -/
def sampled : Process (RSig plainModel) (Stop × Unit) (HList (RV plainModel 0) [] × Unit) →
    List Occurrence
  | .call (.own (.coin _) [] at_ _ _ .nat) k => at_ :: sampled (k (0 : Nat))
  | .call (.give _ _ _ _ _) k => sampled (k ())
  | _ => []

/-- The occurrences at which a run gives a message, while every coin is `0`. -/
def sent : Process (RSig plainModel) (Stop × Unit) (HList (RV plainModel 0) [] × Unit) →
    List Occurrence
  | .call (.own (.coin _) [] _ _ _ .nat) k => sent (k (0 : Nat))
  | .call (.give _ _ at_ _ _) k => at_ :: sent (k ())
  | _ => []

/-- How a run ends, while every coin is `0`. -/
def ending : Process (RSig plainModel) (Stop × Unit) (HList (RV plainModel 0) [] × Unit) →
    Option Stop
  | .call (.own (.coin _) [] _ _ _ .nat) k => ending (k (0 : Nat))
  | .call (.give _ _ _ _ _) k => ending (k ())
  | .halt stop => some stop.1
  | _ => Option.none

/-- The two attempts ask for the private coin at two different occurrences. -/
theorem retry_samples_twice :
    sampled (retriedRun retriedBody) = [⟨[.attempt ⟨80⟩ 0], ⟨81⟩⟩, ⟨[.attempt ⟨80⟩ 1], ⟨81⟩⟩] :=
  rfl

/-- The message given in the body has one occurrence in both attempts. -/
theorem retry_keeps_give : sent (retriedRun retriedBody) = [⟨[], ⟨84⟩⟩, ⟨[], ⟨84⟩⟩] := rfl

/-- When the attempts run out, the stop is `exhausted` at the occurrence of the attempt. -/
theorem retry_exhausted :
    ending (retriedRun retriedBody) = some (.declared .exhausted ⟨[], ⟨80⟩⟩) := rfl

/-- An attempt whose body does nothing, then a private coin. -/
def coinAfter : Term (protocolDialect Shapes.plain Shapes.none) (Ctx.positional []) [] :=
  .attempt ⟨80⟩ [0] ⟨0, rfl⟩ (.cons 0 .nil) (.ret .nil) .nil <|
  .op ⟨85⟩ (.given (.coin ()) 0 [] [] .nat ⟨_, rfl, rfl, rfl⟩ (fun _ h => nomatch h)
    (by decide)) .nil (.cons 1 .nil) <|
  .ret .nil

/-- A private coin after the region is asked once, at its own occurrence. -/
theorem coin_after_once : sampled (retriedRun coinAfter) = [⟨[], ⟨85⟩⟩] := rfl

/-- An attempt whose body does nothing, then a guard that aborts. -/
def abortAfter : Term (protocolDialect Shapes.plain Shapes.none) (Ctx.positional []) [] :=
  .attempt ⟨80⟩ [0] ⟨0, rfl⟩ (.cons 0 .nil) (.ret .nil) .nil <|
  .op ⟨86⟩ (.compute [0] (.literal .bool [0] rfl) [] rfl (fun _ h => nomatch h)) .nil
    (.cons 1 .nil) <|
  .guard ⟨87⟩ [0] (var 1) ⟨rfl, by decide, by decide⟩ .abort <|
  .ret .nil

/-- An `abort` after the region is not retried: it is the stop. -/
theorem abort_after_not_retried :
    ending (retriedRun abortAfter) = some (.declared .abort ⟨[], ⟨87⟩⟩) := rfl

/-- What a program with an attempt asks below: a mark of its beginning (its reply is the
number), a mark of the end of its body, and a request. -/
inductive Marked where
  | begin
  | settle
  | ask

abbrev MarkedSig : Sig := ⟨Marked, fun | .begin => Nat | .settle => Unit | .ask => Unit⟩

/-- The retry of two attempts of the region between the marks. -/
def markedRetry : Retry MarkedSig NoSig Stop where
  bound := 2
  begins := fun
    | .begin => some (.declared .exhausted ⟨[], ⟨90⟩⟩, fun i => i)
    | _ => Option.none
  ends := fun
    | .settle => some ()
    | _ => Option.none
  retriable := Stop.isAbort
  mark := fun _ p => p

/-- An upper layer that passes every request below. -/
def passing : Handler MarkedSig MarkedSig Stop Unit where
  clause op s := .call op fun reply => .done (reply, s)
  again _ _ s := .ok s

/-- A lower layer that counts the requests that it answers, and starts each attempt from the
count that it reached. -/
def counting : Handler MarkedSig NoSig Stop Nat where
  clause op n :=
    match op with
    | .begin => .done (0, n)
    | .settle => .done ((), n)
    | .ask => .done ((), n + 1)
  again _ _ n := .ok n

/-- A body that asks once and aborts. -/
def askThenAbort : Process MarkedSig Stop Unit :=
  .call .begin fun _ => .call .ask fun _ => .halt stopped

/-- Across the two aborted attempts the lower count keeps what it reached: two requests. -/
theorem counter_survives_retry (n : Nat) :
    (passing.over counting).run markedRetry askThenAbort ((), n) =
      .halt (.declared .exhausted ⟨[], ⟨90⟩⟩, ((), n + 2)) := rfl

/-- The shape of the identification protocol of ML-DSA: an attempt of the first role whose
body has its private coin, a message to the second, a coin of the second that the first hears,
a guard of the first that aborts, and a second message; then a guard of the second. -/
def signing : Term (protocolDialect Shapes.plain Shapes.none) (Ctx.positional []) [] :=
  .attempt ⟨1⟩ [0] ⟨0, rfl⟩ (.cons 0 .nil)
    (.op ⟨2⟩ (.given (.coin ()) 0 [] [] .nat ⟨_, rfl, rfl, rfl⟩ (fun _ h => nomatch h)
      (by decide)) .nil (.cons 1 .nil) <|
     .op ⟨3⟩ (.flow .message 0 [1] (by decide) (by decide)) (.cons (var 1) .nil) (.cons 2 .nil) <|
     .op ⟨4⟩ (.given (.coin ()) 1 [0] [] .nat ⟨_, rfl, rfl, rfl⟩ (fun _ h => nomatch h)
      (by decide)) .nil (.cons 3 .nil) <|
     .op ⟨5⟩ (.compute [0] (.owned .natLess) [nat [0], nat [0]] rfl
      (fun a ha r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> exact hr))
      (.cons (var 0) (.cons (var 1) .nil)) (.cons 4 .nil) <|
     .guard ⟨6⟩ [0] (var 4) ⟨rfl, by decide, by decide⟩ .abort <|
     .op ⟨7⟩ (.flow .message 0 [1] (by decide) (by decide)) (.cons (var 1) .nil) (.cons 5 .nil) <|
     .ret (.cons (var 5) (.cons (var 3) .nil)))
    (.cons 6 (.cons 7 .nil)) <|
  .op ⟨8⟩ (.compute [1] (.owned .natLess) [nat [0, 1], nat [0, 1]] rfl
    (fun a ha r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hr
      rcases ha with rfl | rfl <;> subst hr <;> decide))
    (.cons (var 6) (.cons (var 7) .nil)) (.cons 8 .nil) <|
  .guard ⟨9⟩ [1] (var 8) ⟨rfl, by decide, by decide⟩ .reject <|
  .ret .nil

def signingHeader : ProtocolHeader Shapes.plain := ⟨⟨46⟩, 2, [], [], shapeOf signing⟩

/-- The protocol is accepted: its definition has `within`, `enclosed`, `distinct` and
`shaped`, with the second role acting inside the region of the attempt. -/
def signingTyped : Typed Shapes.plain := ⟨⟨[], [signingHeader]⟩,
  .protocol signingHeader (Names.counting 0 _) signing
    ⟨by simp [Within, ProtocolOp.Within, signing, signingHeader], by decide,
    by simp [Enclosed, signing], rfl, rfl, rfl, rfl, by unfold Term.BoundOnce; decide⟩ .nil,
    by decide⟩

/-- The four properties of its definition, stated. -/
theorem signing_accepted :
    ProtocolConditions signingHeader (inputs := Names.counting 0 _) signing :=
  ⟨by simp [Within, ProtocolOp.Within, signing, signingHeader], by decide,
    by simp [Enclosed, signing], rfl, rfl, rfl, rfl, by unfold Term.BoundOnce; decide⟩

/-! ## Codecs -/

/-- A carrier of functions has no lawful format, so not every model has codecs. -/
theorem no_lawful_function_format (f : Format (List Nat → Bool)) : ¬ f.Lawful := by
  intro h
  let diagonal : List Nat → Bool := fun bytes =>
    match f.read bytes with
    | some (g, _) => !(g bytes)
    | Option.none => false
  have rd : f.read (f.write diagonal) = some (diagonal, []) := by
    simpa using h.reads diagonal []
  have contra : diagonal (f.write diagonal) = !(diagonal (f.write diagonal)) := by
    change (match f.read (f.write diagonal) with
      | some (g, _) => !(g (f.write diagonal))
      | Option.none => false) = _
    rw [rd]
  cases hd : diagonal (f.write diagonal) <;> simp [hd] at contra

def functionVocabulary : Vocabulary where
  TypeKey := Unit
  RowKey := Empty
  LawKey := Empty
  row r := nomatch r
  law r := nomatch r
  literal _ _ := false
  decided r := nomatch r

def functionModel : Model functionVocabulary where
  Carrier _ := List Nat → Bool
  valid _ _ := True
  literal _ _ := Option.none
  apply row _ _ _ := nomatch row
  inDomain row _ _ _ := nomatch row
  defined row _ _ _ := nomatch row
  total row _ _ _ _ := nomatch row
  decides row _ _ _ _ _ := nomatch row
  keeps row _ _ _ _ _ _ := nomatch row
  literals _ _ h := by cases h
  support law _ _ _ _ := nomatch law
  supported law _ _ _ _ _ _ := nomatch law

/-- The model of functions has no codecs, so `formats` asks nothing of it. -/
theorem function_model_has_no_codecs : Codecs functionModel → False :=
  fun codecs => no_lawful_function_format (codecs.format ()) (codecs.lawful ())

/-! ## Linear use -/

/-- `if b then x else 0`, over a truth value and a natural. -/
def ordinaryChoice : Term (localDialect Shapes.plain []) (Ctx.positional [.bool, .nat]) [.nat] :=
  .choose (mid := [.nat]) ⟨1⟩ () (var 0) rfl (fun _ _ => trivial)
    (.ret (.cons (var 1) .nil))
    (.op ⟨2⟩ (.literal .nat [0] rfl) .nil (.cons 2 .nil) (.ret (.cons (var 2) .nil)))
    (.cons 3 .nil)
    (.ret (.cons (var 3) .nil))

/-- Neither input is linear: nothing is counted, and the choice is accepted. -/
theorem ordinary_choice_accepted :
    ordinaryChoice.linearUses (Ty.isLinear Shapes.plain) [] = .ok [] ∧
      ordinaryChoice.UsedOnce (Ty.isLinear Shapes.plain) (Names.counting 0 [.bool, .nat]) :=
  ⟨rfl, by decide⟩

/-! ## Who proves -/

/-- One message in each direction. -/
def twoWay : Term (protocolDialect Shapes.plain Shapes.none) (Ctx.positional [nat [0]]) [] :=
  .op ⟨1⟩ (.flow .message 0 [1] (by decide) (by decide)) (.cons (var 0) .nil) (.cons 1 .nil) <|
  .op ⟨2⟩ (.flow .message 1 [0] (by decide) (by decide)) (.cons (var 1) .nil) (.cons 2 .nil) <|
  .ret .nil

def twoWayHeader : ProtocolHeader Shapes.plain := ⟨⟨42⟩, 2, [nat [0]], [], shapeOf twoWay⟩

def interactiveScheme : Declaration :=
  { derivedScheme ⟨42⟩ [.online, .online] (some 0) with construction := .interactive }

/-- Declared interactive with a written prover, it has its roles. -/
theorem interactive_roles : proverAndVerifier twoWayHeader interactiveScheme = some (0, 1) := by
  decide +kernel

/-- Not declared interactive, nothing is inferred from two senders. -/
theorem derived_two_senders_refused :
    proverAndVerifier twoWayHeader { interactiveScheme with construction := .derived ⟨[]⟩ } =
      Option.none := by
  decide +kernel

/-! ## Forks -/

def forkFields : Fields Shapes.plain :=
  .cons (.key ⟨1⟩) (.record (.cons (.key ⟨2⟩) (.val .nat) .nil))
    (.cons (.key ⟨3⟩) (.val .nat) .nil)

def forkLeft : forkFields.Val plainModel := (((10 : Nat), ()), ((0 : Nat), ()))
def forkRight : forkFields.Val plainModel := (((20 : Nat), ()), ((1 : Nat), ()))

/-- Two records that differ in an earlier nested record are not a fork. -/
theorem nested_prefix_counted :
    ¬ Fields.Fork plainModel (.key ⟨3⟩) forkFields forkLeft forkRight := by
  simp [Fields.Fork, Fields.agreeBefore, forkFields, forkLeft, forkRight]

/-- Two runs with one message and two challenges fork at the challenge. -/
theorem runs_fork :
    Fork plainModel
      [.flow .message 0 [1] ⟨[], ⟨1⟩⟩ .nat (3 : Nat),
        .given (.coin ()) 1 [0] ⟨[], ⟨2⟩⟩ .nat (5 : Nat)]
      [.flow .message 0 [1] ⟨[], ⟨1⟩⟩ .nat (3 : Nat),
        .given (.coin ()) 1 [0] ⟨[], ⟨2⟩⟩ .nat (6 : Nat)] :=
  ⟨[.flow .message 0 [1] ⟨[], ⟨1⟩⟩ .nat (3 : Nat)], _, _, [], [], rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, by decide⟩

/-! ## A layer's start has no effects -/

/-- A clause that answers a sample with the layer's state. -/
def answerSample : Clause Shapes.plain Shapes.none 0 .nat where
  site := ⟨⟨[], ⟨50⟩⟩, .own (.coin ()) [], [], [.nat]⟩
  code := .ret (.cons (var 0) (.cons (var 0) .nil))

/-- A lower layer with that clause, whose start is what it takes. -/
def lowerLayer : Layer Shapes.plain Shapes.none 0 [] where
  line := .construction
  state := .nat
  takes := [.nat]
  gives := []
  clauses := [answerSample]
  again := .ret (.cons (var 0) .nil)
  start := .ret (.cons (var 0) .nil)
  finish := .ret .nil

/-- The start reads what the layer takes, and asks nothing of the world. -/
theorem start_is_pure :
    Stack.start plainModel noFns [lowerLayer] .nil (.cons (7 : Nat) .nil) =
      .done (.cons (7 : Nat) .nil) := rfl

/-- The clause answers the sample with the state. -/
theorem lower_clause_answers :
    (Layer.handler plainModel noFns noPrograms lowerLayer).clause
      (.own (.coin ()) [] ⟨[], ⟨50⟩⟩ [] .nil .nat) (7 : Nat) = .done (7, (7 : Nat)) := rfl

/-! ## A law of a function, installed at its calls -/

def weightedHeader : FnHeader Shapes.plain := ⟨⟨410⟩, [.nat, .nat], [.nat], false, Option.none, Summary.empty⟩
def identityHeader : FnHeader Shapes.plain := ⟨⟨411⟩, [.nat], [.nat], false, Option.none, Summary.empty⟩

/-- `x + (y + y)`, of `x` and `y`. -/
def weightedBody : Fn Shapes.plain [] weightedHeader (Names.counting 0 _) :=
  .op ⟨1⟩ (.owned .natAdd) (.cons (var 1) (.cons (var 1) .nil)) (.cons 2 .nil) <|
  .op ⟨2⟩ (.owned .natAdd) (.cons (var 0) (.cons (var 2) .nil)) (.cons 3 .nil) <|
  .ret (.cons (var 3) .nil)

def identityBody : Fn Shapes.plain [weightedHeader] identityHeader (Names.counting 0 _) :=
  .ret (.cons (var 0) .nil)

/-- The weighted sum, then the identity, which comes later. -/
def library : Defs Shapes.plain ⟨[identityHeader, weightedHeader], []⟩ :=
  .fn identityHeader _ identityBody ⟨by exact rfl, by exact rfl, by exact rfl, by exact rfl,
    by unfold Term.BoundOnce; decide,
    by exact rfl⟩ <|
  .fn weightedHeader _ weightedBody ⟨by exact rfl, by exact rfl, by exact rfl, by exact rfl,
    by unfold Term.BoundOnce; decide,
    by exact rfl⟩ .nil

def libraryTyped : Typed Shapes.plain := ⟨_, library, by decide⟩

def table : FnTable plainModel [identityHeader, weightedHeader] := Defs.fnTable plainModel library

def weightedRef : Member [identityHeader, weightedHeader] weightedHeader := .tail .head

/-- The weighted sum is found by its key, at its position. -/
theorem weighted_found : libraryTyped.find ⟨410⟩ = some (.fn weightedRef) := rfl

def weightedModel : HList plainModel.Val weightedHeader.ins → HList plainModel.Val weightedHeader.outs
  | .cons x (.cons y .nil) => .cons (x + (y + y)) .nil

/-- Its law: its entry in the table gives what the model gives. -/
theorem weightedLaw : Law plainModel table weightedRef weightedModel := by
  constructor
  intro args
  cases args with
  | cons x rest => cases rest with
    | cons y rest => cases rest; rfl

/-- Two calls with different operands. -/
def twice : Term (localDialect Shapes.plain [identityHeader, weightedHeader])
    (Ctx.positional [.nat, .nat]) [.nat] :=
  .op ⟨501⟩ (.call weightedRef) (.cons (var 0) (.cons (var 1) .nil)) (.cons 2 .nil) <|
  .op ⟨502⟩ (.call weightedRef) (.cons (var 2) (.cons (var 1) .nil)) (.cons 3 .nil) <|
  .ret (.cons (var 3) .nil)

/-- A call with a value captured from around it, with the operands in another order. -/
def captured : Term (localDialect Shapes.plain [identityHeader, weightedHeader])
    (Ctx.positional [.nat, .nat, .nat]) [.nat] :=
  .op ⟨601⟩ (.call weightedRef) (.cons (var 1) (.cons (var 2) .nil)) (.cons 3 .nil) <|
  .op ⟨602⟩ (.owned .natAdd) (.cons (var 3) (.cons (var 0) .nil)) (.cons 4 .nil) <|
  .ret (.cons (var 4) .nil)

/-- The law at two calls, for every table that has it: the callee is not unfolded. -/
theorem twice_from_law (t : FnTable plainModel [identityHeader, weightedHeader])
    (law : Law plainModel t weightedRef weightedModel) (x y : Nat) (path : List Frame) :
    twice.denote (localSem plainModel _ t) path (Env.positional (.cons x (.cons y .nil))) =
      .done (.cons (x + (y + y) + (y + y)) .nil) := by
  unfold twice
  erw [Law.call plainModel t weightedRef law, Law.call plainModel t weightedRef law]
  rfl

/-- The same law at a call with a capture. -/
theorem captured_from_law (t : FnTable plainModel [identityHeader, weightedHeader])
    (law : Law plainModel t weightedRef weightedModel) (c x y : Nat) (path : List Frame) :
    captured.denote (localSem plainModel _ t) path
      (Env.positional (.cons c (.cons x (.cons y .nil)))) =
      .done (.cons (x + (y + y) + c) .nil) := by
  unfold captured
  erw [Law.call plainModel t weightedRef law]
  rfl

/-- The program's table has the law, so both calls compute by it. -/
theorem twice_by_the_law (x y : Nat) (path : List Frame) :
    twice.denote (localSem plainModel _ table) path (Env.positional (.cons x (.cons y .nil))) =
      .done (.cons (x + (y + y) + (y + y)) .nil) :=
  twice_from_law table weightedLaw x y path

/-- The weighted sum alone, moved to the first position. -/
def movedLibrary : Defs Shapes.plain ⟨[weightedHeader], []⟩ :=
  .fn weightedHeader _ weightedBody ⟨by exact rfl, by exact rfl, by exact rfl, by exact rfl,
    by unfold Term.BoundOnce; decide,
    by exact rfl⟩ .nil

def movedTyped : Typed Shapes.plain := ⟨_, movedLibrary, by decide⟩

def movedRef : Member [weightedHeader] weightedHeader := .head

/-- Moved, it is found again by its key, and its law holds without being proved again. -/
theorem moved_law : movedTyped.find ⟨410⟩ = some (.fn movedRef) ∧
    Law plainModel (Defs.fnTable plainModel movedLibrary) movedRef weightedModel :=
  ⟨rfl, ⟨weightedLaw.implements⟩⟩

/-- Another body under the same key and signature. -/
def changedBody : Fn Shapes.plain [] weightedHeader (Names.counting 0 _) :=
  .ret (.cons (var 0) .nil)

def changedLibrary : Defs Shapes.plain ⟨[identityHeader, weightedHeader], []⟩ :=
  .fn identityHeader _ identityBody ⟨by exact rfl, by exact rfl, by exact rfl, by exact rfl,
    by unfold Term.BoundOnce; decide,
    by exact rfl⟩ <|
  .fn weightedHeader _ changedBody ⟨by exact rfl, by exact rfl, by exact rfl, by exact rfl,
    by unfold Term.BoundOnce; decide,
    by exact rfl⟩ .nil

/-- A changed body under the same key does not keep the law. -/
theorem changed_body_loses_law :
    ¬ Law plainModel (Defs.fnTable plainModel changedLibrary) weightedRef weightedModel := by
  intro law
  have bad := law.implements (.cons (0 : Nat) (.cons (1 : Nat) .nil))
  change (Process.done (.cons (0 : Nat) .nil) : Local (HList plainModel.Val [.nat])) =
    .done (.cons (2 : Nat) .nil) at bad
  cases bad

/-- A changed dependency changes the unchanged caller. -/
theorem changed_dependency_seen :
    twice.denote (localSem plainModel _ (Defs.fnTable plainModel changedLibrary)) []
      (Env.positional (.cons (0 : Nat) (.cons (1 : Nat) .nil))) ≠ .done (.cons (4 : Nat) .nil) := by
  intro bad
  change (Process.done (.cons (0 : Nat) .nil) : Local (HList plainModel.Val [.nat])) =
    .done (.cons (4 : Nat) .nil) at bad
  cases bad

/-- Two operands of one type, exchanged. -/
def swapped : Term (localDialect Shapes.plain [identityHeader, weightedHeader])
    (Ctx.positional [.nat, .nat]) [.nat] :=
  .op ⟨701⟩ (.call weightedRef) (.cons (var 1) (.cons (var 0) .nil)) (.cons 2 .nil) <|
  .ret (.cons (var 2) .nil)

/-- Exchanged operands of one type are seen. -/
theorem swapped_operands_seen :
    swapped.denote (localSem plainModel _ table) []
      (Env.positional (.cons (0 : Nat) (.cons (1 : Nat) .nil))) ≠ .done (.cons (2 : Nat) .nil) := by
  intro bad
  change (Process.done (.cons (1 : Nat) .nil) : Local (HList plainModel.Val [.nat])) =
    .done (.cons (2 : Nat) .nil) at bad
  cases bad

/-- A function that rejects when its flag is false, and returns its number otherwise. -/
def checkedHeader : FnHeader Shapes.plain := ⟨⟨420⟩, [.bool, .nat], [.nat], true, Option.none, Summary.empty⟩

def checkedBody : Fn Shapes.plain [] checkedHeader (Names.counting 0 _) :=
  .guard ⟨421⟩ () (var 0) rfl .reject (.ret (.cons (var 1) .nil))

def checkedDefs : Defs Shapes.plain ⟨[checkedHeader], []⟩ :=
  .fn checkedHeader _ checkedBody ⟨by exact rfl, by exact rfl, by exact rfl, by exact rfl,
    by unfold Term.BoundOnce; decide,
    by exact rfl⟩ .nil

def checkedTable : FnTable plainModel [checkedHeader] := Defs.fnTable plainModel checkedDefs

def checkedRef : Member [checkedHeader] checkedHeader := .head

def checkedPost : HList plainModel.Val checkedHeader.ins → HList plainModel.Val checkedHeader.outs → Prop
  | .cons flag (.cons n .nil), out => flag = true ∧ out = .cons n .nil

def checkedStop : HList plainModel.Val checkedHeader.ins → Stop → Prop
  | .cons flag (.cons _ .nil), why => flag = false ∧ why = .declared .reject ⟨[], ⟨421⟩⟩

/-- Its contract: it returns its number when the flag is true, and rejects otherwise. -/
theorem checkedContract :
    Contract plainModel checkedTable checkedRef (fun _ => True) checkedPost checkedStop := by
  constructor
  intro args _
  cases args with
  | cons flag rest => cases rest with
    | cons n rest => cases rest; cases flag <;> exact ⟨rfl, rfl⟩

def checkedClient :
    Term (localDialect Shapes.plain [checkedHeader]) (Ctx.positional [.bool, .nat]) [.nat] :=
  .op ⟨422⟩ (.call checkedRef) (.cons (var 0) (.cons (var 1) .nil)) (.cons 2 .nil) <|
  .ret (.cons (var 2) .nil)

/-- The rule of a call installs the contract, for every table that has it: the caller returns
the number when the flag is true, and rejects otherwise. -/
theorem checked_client_from_contract (t : FnTable plainModel [checkedHeader])
    (contract : Contract plainModel t checkedRef (fun _ => True) checkedPost checkedStop)
    (flag : Bool) (n : Nat) (path : List Frame) :
    (checkedClient.denote (localSem plainModel _ t) path
      (Env.positional (.cons flag (.cons n .nil)))).Every (fun _ _ => True)
      (fun out => flag = true ∧ out = .cons n .nil)
      (fun why => flag = false ∧ why = .declared .reject ⟨[], ⟨421⟩⟩) := by
  apply Contract.call plainModel t checkedRef contract
  · trivial
  · intro values h
    cases values with
    | cons value tail => cases tail; exact h
  · intro why h
    exact h

/-- A function that may reject is not treated as one that returns: on a false flag the caller
stops, at the occurrence of the callee's guard. -/
theorem checked_rejects (n : Nat) :
    checkedClient.denote (localSem plainModel _ checkedTable) []
      (Env.positional (.cons false (.cons n .nil))) = .halt (.declared .reject ⟨[], ⟨421⟩⟩) := rfl

/-- So no law of a total function holds of it. -/
theorem checked_not_total :
    ¬ ∀ flag n, checkedClient.denote (localSem plainModel _ checkedTable) []
      (Env.positional (.cons flag (.cons n .nil))) = .done (.cons n .nil) := by
  intro h
  have bad := h false 0
  rw [checked_rejects] at bad
  cases bad

/-- Two definitions with one key, and a key that no definition has, are refused. -/
theorem duplicate_and_missing_refused :
    (⟨[weightedHeader, weightedHeader], []⟩ : Headers Shapes.plain).find ⟨410⟩ = Option.none ∧
      libraryTyped.find ⟨999⟩ = Option.none := ⟨rfl, rfl⟩

def callerHeader : FnHeader Shapes.plain := ⟨⟨412⟩, [.nat, .nat], [.nat], false, Option.none, Summary.empty⟩

/-- A caller of the weighted sum, before the library. -/
def callerTyped : Typed Shapes.plain :=
  ⟨_, .fn callerHeader _ twice ⟨by exact rfl, by exact rfl, by exact rfl, by exact rfl,
    by unfold Term.BoundOnce; decide,
    by exact rfl⟩ library,
    by decide⟩

/-- The closure of the caller has the caller and, twice, the weighted sum that it calls; not
the identity. -/
theorem caller_closure :
    (callerTyped.find ⟨412⟩).map (fun definition => definition.closure) = some [⟨412⟩, ⟨410⟩, ⟨410⟩] :=
  rfl

end Zkc.Core.Controls

#print axioms Zkc.Core.Controls.no_globally_total_source
#print axioms Zkc.Core.Controls.empty_source_not_fed
#print axioms Zkc.Core.Controls.zero_source_fed
#print axioms Zkc.Core.Controls.zero_source_returns
#print axioms Zkc.Core.Controls.sampler_starves
#print axioms Zkc.Core.Controls.never_schedule_refused
#print axioms Zkc.Core.Controls.composition_keeps_lower
#print axioms Zkc.Core.Controls.colliding_not_distinct
#print axioms Zkc.Core.Controls.bare_global_returns
#print axioms Zkc.Core.Controls.bare_reachable_stuck
#print axioms Zkc.Core.Controls.stuck
#print axioms Zkc.Core.Controls.bare_not_returned
#print axioms Zkc.Core.Controls.retry_samples_twice
#print axioms Zkc.Core.Controls.retry_keeps_give
#print axioms Zkc.Core.Controls.retry_exhausted
#print axioms Zkc.Core.Controls.coin_after_once
#print axioms Zkc.Core.Controls.abort_after_not_retried
#print axioms Zkc.Core.Controls.counter_survives_retry
#print axioms Zkc.Core.Controls.signing_accepted
#print axioms Zkc.Core.Controls.no_lawful_function_format
#print axioms Zkc.Core.Controls.function_model_has_no_codecs
#print axioms Zkc.Core.Controls.ordinary_choice_accepted
#print axioms Zkc.Core.Controls.interactive_roles
#print axioms Zkc.Core.Controls.derived_two_senders_refused
#print axioms Zkc.Core.Controls.nested_prefix_counted
#print axioms Zkc.Core.Controls.runs_fork
#print axioms Zkc.Core.Controls.start_is_pure
#print axioms Zkc.Core.Controls.lower_clause_answers
#print axioms Zkc.Core.Controls.weighted_found
#print axioms Zkc.Core.Controls.weightedLaw
#print axioms Zkc.Core.Controls.twice_from_law
#print axioms Zkc.Core.Controls.captured_from_law
#print axioms Zkc.Core.Controls.twice_by_the_law
#print axioms Zkc.Core.Controls.moved_law
#print axioms Zkc.Core.Controls.changed_body_loses_law
#print axioms Zkc.Core.Controls.changed_dependency_seen
#print axioms Zkc.Core.Controls.swapped_operands_seen
#print axioms Zkc.Core.Controls.checkedContract
#print axioms Zkc.Core.Controls.checked_client_from_contract
#print axioms Zkc.Core.Controls.checked_rejects
#print axioms Zkc.Core.Controls.checked_not_total
#print axioms Zkc.Core.Controls.duplicate_and_missing_refused
#print axioms Zkc.Core.Controls.caller_closure
