module

public import Zkc.Executable.Execution

@[expose] public section

/-! Frame cleanup of executable runs.

A run records an entry event when it opens a frame (the participant's, a loop
iteration's or a local call's) and an exit event when it leaves one. Replaying
the events on a stack of open frames checks that each exit leaves the innermost
frame still open. A run is cleaned up when the replay of all its events, from no
open frame, ends with no open frame.

Every run of the executable is cleaned up (`execute_cleaned`), in every monad
and for every challenge function, decoder, budget, data input, transcript and
proof: a normal return leaves the participant frame, and a stop leaves the
frames still active, innermost first. Retiring the live transcript on a stop,
and the returned one on a return, is part of the definitions of `State.stop`
and `State.done`.
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction Zkc.Source

section Definitions
variable {F G : Type}

/-- Replay frame events on a stack of open frames, innermost first: an entry
opens a frame, and an exit must leave the innermost open frame. -/
def replayFrames : List FrameId → List FrameEvent → Option (List FrameId)
  | stack, [] => some stack
  | stack, .enter frame :: rest => replayFrames (frame :: stack) rest
  | top :: stack, .leave frame _ :: rest => if top = frame then replayFrames stack rest else none
  | [], .leave _ _ :: _ => none

/-- Every frame the run entered, the participant's included, was left, and
each exit left the innermost frame still open. -/
def Run.Cleaned (run : Run F G) : Prop :=
  replayFrames [] run.events = some []

instance (run : Run F G) : Decidable run.Cleaned := by
  unfold Run.Cleaned
  infer_instance

/-- The frame events so far leave exactly the active frames open, innermost
first, and the outermost active frame is the participant's. -/
def State.Nested (s : State F G) : Prop :=
  replayFrames [] s.events = some (s.frames.map (·.id)) ∧
    (s.frames.map (·.id)).getLast? = some .participant

/-- `s'` has the frames of `s` below the innermost one, and an innermost frame
of the same identity; only the innermost frame's bindings may differ. -/
def State.Keeps (s' s : State F G) : Prop :=
  s'.frames.tail = s.frames.tail ∧ s'.frames.map (·.id) = s.frames.map (·.id)

theorem State.Keeps.refl (s : State F G) : s.Keeps s := ⟨rfl, rfl⟩

theorem State.Keeps.trans {s s' s'' : State F G} (second : s''.Keeps s') (first : s'.Keeps s) :
    s''.Keeps s :=
  ⟨second.1.trans first.1, second.2.trans first.2⟩

theorem State.bind_keeps (s : State F G) (names : List String) (values : List (Value F G)) :
    (s.bind names values).Keeps s := by
  unfold State.bind
  split <;> simp_all [State.Keeps]

theorem State.bind_events (s : State F G) (names : List String) (values : List (Value F G)) :
    (s.bind names values).events = s.events := by
  unfold State.bind
  split <;> rfl

theorem replayFrames_append (stack : List FrameId) (events more : List FrameEvent) :
    replayFrames stack (events ++ more) = (replayFrames stack events).bind (replayFrames · more) := by
  induction events generalizing stack with
  | nil => rfl
  | cons event rest ih =>
      cases event with
      | enter frame => exact ih _
      | leave frame exit =>
          cases stack with
          | nil => rfl
          | cons top stack =>
              simp only [List.cons_append, replayFrames]
              split
              · exact ih _
              · rfl

theorem replayFrames_leaves (frames : List (Frame F G)) (exit : Exit) :
    replayFrames (frames.map (·.id)) (frames.map fun frame => .leave frame.id exit) = some [] := by
  induction frames with
  | nil => rfl
  | cons frame rest ih => simpa [replayFrames] using ih

theorem State.stop_cleaned {s : State F G} (nested : s.Nested) (cause : Cause)
    (site : Option String) (call : Option (String × String)) : (s.stop cause site call).Cleaned := by
  unfold Run.Cleaned
  simp only [State.stop, replayFrames_append, nested.1, Option.bind_some]
  exact replayFrames_leaves s.frames _

theorem State.done_cleaned {s : State F G} (nested : s.Nested) {frame : Frame F G}
    (single : s.frames = [frame]) (values : List (Value F G)) : (s.done values).Cleaned := by
  obtain ⟨replayed, outermost⟩ := nested
  rw [single] at replayed outermost
  simp only [List.map_cons, List.map_nil, List.getLast?_singleton, Option.some.injEq] at outermost
  unfold Run.Cleaned
  simp [State.done, replayFrames_append, replayed, replayFrames, outermost]

/-- Nesting depends only on the frames' identities and the events. -/
theorem State.Nested.congr {s s' : State F G} (nested : s.Nested)
    (frames : s'.frames.map (·.id) = s.frames.map (·.id)) (events : s'.events = s.events) : s'.Nested := by
  obtain ⟨replayed, outermost⟩ := nested
  exact ⟨by rw [events, frames]; exact replayed, by rw [frames]; exact outermost⟩

theorem State.Nested.charge {s : State F G} (nested : s.Nested) : s.charge.Nested := nested

theorem State.Nested.enter {s : State F G} (nested : s.Nested) (frame : FrameId) (env : Env F G) :
    ({ s with frames := ⟨frame, env⟩ :: s.frames, events := s.events ++ [.enter frame] } :
      State F G).Nested := by
  obtain ⟨replayed, outermost⟩ := nested
  refine ⟨?_, ?_⟩
  · simp [replayFrames_append, replayed, replayFrames]
  · simp [List.getLast?_cons, outermost]

/-- Leaving the innermost frame, when another frame remains active, keeps the
nesting; the remaining frames may rebind their values. -/
theorem State.Nested.leave {s : State F G} (nested : s.Nested) {frame : Frame F G}
    {below frames : List (Frame F G)} (framesEq : s.frames = frame :: below)
    (ids : frames.map (·.id) = below.map (·.id)) (active : below ≠ []) (exit : Exit) :
    ({ s with frames := frames, events := s.events ++ [.leave frame.id exit] } : State F G).Nested := by
  obtain ⟨replayed, outermost⟩ := nested
  rw [framesEq] at replayed outermost
  cases below with
  | nil => exact absurd rfl active
  | cons caller rest =>
      refine ⟨?_, ?_⟩
      · simp [replayFrames_append, replayed, replayFrames, ids]
      · rw [ids]
        simpa [List.getLast?_cons] using outermost

theorem State.Nested.active {s : State F G} (nested : s.Nested) : s.frames ≠ [] := by
  intro empty
  have outermost := nested.2
  simp [empty] at outermost

end Definitions


section Cleanup
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (vocabulary : Vocabulary) (validator : Validator) (context : Context)
  (challenge : History F G → m F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
  (budget : Nat)

/-- A computation of runs every one of which is cleaned up. -/
def Cleans (computation : m (Run F G)) : Prop :=
  (fun result => decide result.Cleaned) <$> computation = (fun _ => true) <$> computation

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem Cleans.stop {s : State F G} (nested : s.Nested) (cause : Cause) (site : Option String)
    (call : Option (String × String)) : Cleans (pure (s.stop cause site call) : m (Run F G)) := by
  simp [Cleans, State.stop_cleaned nested]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem Cleans.bind {β : Type} (first : m β) {rest : β → m (Run F G)} (each : ∀ value, Cleans (rest value)) :
    Cleans (first >>= rest) := by
  unfold Cleans at *
  simp only [map_bind]
  congr 1
  funext value
  exact each value

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Iterating a region that keeps frames and events cleans up. -/
theorem forK_cleaned
    (run : Env F G → State F G → (List (Value F G) → State F G → m (Run F G)) → m (Run F G))
    (runs : ∀ env (s : State F G) exit, s.Nested →
      (∀ values (s' : State F G), s'.frames = s.frames → s'.events = s.events → Cleans (exit values s')) →
      Cleans (run env s exit))
    (site induction : String) (carried : List String) (captured : Env F G) (call : String × String) :
    ∀ (indices : List Nat) (values : List (Value F G)) (s : State F G)
      (done : List (Value F G) → State F G → m (Run F G)), s.Nested →
      (∀ values (s' : State F G), s'.frames = s.frames → s'.events = s.events → Cleans (done values s')) →
      Cleans (forK run site induction carried captured call indices values s done)
  | [], values, s, done, _, dones => dones values s rfl rfl
  | index :: rest, values, s, done, nested, dones => by
      simp only [forK]
      apply runs _ s _ nested
      intro yielded s' frames events
      have nested' : s'.Nested := nested.congr (by rw [frames]) events
      split
      · exact forK_cleaned run runs site induction carried captured call rest yielded s' done nested'
          (fun values s'' frames' events' => dones values s'' (frames'.trans frames) (events'.trans events))
      · exact Cleans.stop nested' _ _ _

mutual
/-- A local body keeps frames and events, and cleans up wherever it stops. -/
theorem localK_cleaned (call : String × String) (top : Bool) (region : Option String) :
    ∀ (steps : List Step) (env : Env F G) (s : State F G)
      (exit : List (Value F G) → State F G → m (Run F G)), s.Nested →
      (∀ values (s' : State F G), s'.frames = s.frames → s'.events = s.events → Cleans (exit values s')) →
      Cleans (localK vocabulary validator context challenge budget call top region steps env s exit)
  | [], _, s, _, nested, _ => Cleans.stop nested _ _ _
  | step :: rest, env, s, exit, nested, exits => by
      simp only [localK]
      apply localStep_cleaned call top region step env s _ exit nested
      · intro env' s' frames events
        exact localK_cleaned call top region rest env' s' exit (nested.congr (by rw [frames]) events)
          (fun values s'' frames' events' => exits values s'' (frames'.trans frames) (events'.trans events))
      · exact exits

theorem localStep_cleaned (call : String × String) (top : Bool) (region : Option String) :
    ∀ (step : Step) (env : Env F G) (s : State F G) (next : Env F G → State F G → m (Run F G))
      (exit : List (Value F G) → State F G → m (Run F G)), s.Nested →
      (∀ env' (s' : State F G), s'.frames = s.frames → s'.events = s.events → Cleans (next env' s')) →
      (∀ values (s' : State F G), s'.frames = s.frames → s'.events = s.events → Cleans (exit values s')) →
      Cleans (localStep vocabulary validator context challenge budget call top region step env s next exit)
  | .operation site binding parameters inputs outputs, env, s, next, exit, nested, nexts, _ => by
      simp only [localStep]
      split
      · split
        · apply Cleans.bind
          intro applied
          split
          · split
            · exact nexts _ _ rfl rfl
            · exact Cleans.stop nested.charge _ _ _
          · exact Cleans.stop nested.charge _ _ _
        · exact Cleans.stop nested.charge _ _ _
      · exact Cleans.stop nested _ _ _
  | .constant site output value, env, s, next, exit, nested, nexts, _ => by
      simp only [localStep]
      split
      · exact nexts _ _ rfl rfl
      · exact Cleans.stop nested _ _ _
  | .cond site condition captures yes no outputs, env, s, next, exit, nested, nexts, _ => by
      simp only [localStep]
      split
      · split
        · exact localK_cleaned call false (some site) yes _ s.charge _ nested.charge
            (fun results s' frames events => by
              split
              · exact nexts _ _ frames events
              · exact Cleans.stop (nested.congr (by rw [frames]; rfl) events) _ _ _)
        · exact localK_cleaned call false (some site) no _ s.charge _ nested.charge
            (fun results s' frames events => by
              split
              · exact nexts _ _ frames events
              · exact Cleans.stop (nested.congr (by rw [frames]; rfl) events) _ _ _)
        · exact Cleans.stop nested.charge _ _ _
      · exact Cleans.stop nested _ _ _
  | .iterate site induction lower upper carried captures body outputs, env, s, next, exit, nested, nexts, _ => by
      simp only [localStep]
      split
      · split
        · split
          · exact forK_cleaned _
              (fun env' s' exit' nested' exits' => localK_cleaned call false (some site) body env' s' exit'
                nested' exits')
              site induction _ _ call _ _ s.charge _ nested.charge
              (fun final s' frames events => by
                split
                · exact nexts _ _ frames events
                · exact Cleans.stop (nested.congr (by rw [frames]; rfl) events) _ _ _)
          · exact Cleans.stop nested.charge _ _ _
        · exact Cleans.stop nested.charge _ _ _
      · exact Cleans.stop nested _ _ _
  | .stop site reason, env, s, next, exit, nested, _, _ => by
      simp only [localStep]
      split
      · split
        · exact Cleans.stop nested.charge _ _ _
        · exact Cleans.stop nested.charge _ _ _
      · exact Cleans.stop nested _ _ _
  | .yield values, env, s, next, exit, nested, _, exits => by
      simp only [localStep]
      split
      · split
        · exact exits _ _ rfl rfl
        · exact Cleans.stop nested.charge _ _ _
      · exact Cleans.stop nested _ _ _
  | .ret values, env, s, next, exit, nested, _, exits => by
      simp only [localStep]
      split
      · split
        · exact exits _ _ rfl rfl
        · exact Cleans.stop nested.charge _ _ _
      · exact Cleans.stop nested _ _ _
  | .unsupported _, env, s, next, exit, nested, _, _ => by
      simp only [localStep]
      exact Cleans.stop nested _ _ _
end

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Iterating a loop body that cleans up and keeps its frames, in frames of its
own, cleans up and ends with the frames it started with. -/
theorem loopK_cleaned
    (run : State F G → (List (Value F G) → State F G → m (Run F G)) → m (Run F G))
    (runs : ∀ (s : State F G) exit, s.Nested →
      (∀ values (s' : State F G), s'.Nested → s'.Keeps s → Cleans (exit values s')) →
      Cleans (run s exit))
    (site induction : String) (carried : List String) (captured : Env F G) :
    ∀ (indices : List Nat) (values : List (Value F G)) (s : State F G)
      (done : List (Value F G) → State F G → m (Run F G)), s.Nested →
      (∀ values (s' : State F G), s'.Nested → s'.frames = s.frames → Cleans (done values s')) →
      Cleans (loopK run site induction carried captured indices values s done)
  | [], values, s, done, nested, dones => dones values s nested rfl
  | index :: rest, values, s, done, nested, dones => by
      simp only [loopK]
      apply runs _ _ (nested.enter _ _)
      intro yielded s' nested' keeps
      obtain ⟨tail, ids⟩ := keeps
      split
      · rename_i inner below framesEq
        rw [framesEq] at tail ids
        simp only [List.tail_cons] at tail
        simp only [List.map_cons, List.cons.injEq] at ids
        obtain ⟨innerId, -⟩ := ids
        split
        · have left := nested'.leave framesEq (frames := below) rfl (by rw [tail]; exact nested.active)
            .returned
          rw [innerId] at left
          exact loopK_cleaned run runs site induction carried captured rest yielded _ done left
            (fun values s'' nested'' frames'' => dones values s'' nested'' (frames''.trans tail))
        · exact Cleans.stop nested' _ _ _
      · exact Cleans.stop nested' _ _ _

mutual
/-- A participant body cleans up wherever it stops, and keeps its frames when
it yields. -/
theorem runK_cleaned :
    ∀ (actions : List Action) (s : State F G) (exit : List (Value F G) → State F G → m (Run F G)), s.Nested →
      (∀ values (s' : State F G), s'.Nested → s'.Keeps s → Cleans (exit values s')) →
      Cleans (runK vocabulary validator context challenge decode budget actions s exit)
  | [], s, _, nested, _ => Cleans.stop nested _ _ _
  | action :: rest, s, exit, nested, exits => by
      simp only [runK]
      apply runStep_cleaned action s _ exit nested
      · intro s' nested' keeps
        exact runK_cleaned rest s' exit nested'
          (fun values s'' nested'' keeps' => exits values s'' nested'' (keeps'.trans keeps))
      · exact exits

theorem runStep_cleaned :
    ∀ (action : Action) (s : State F G) (next : State F G → m (Run F G))
      (exit : List (Value F G) → State F G → m (Run F G)), s.Nested →
      (∀ (s' : State F G), s'.Nested → s'.Keeps s → Cleans (next s')) →
      (∀ values (s' : State F G), s'.Nested → s'.Keeps s → Cleans (exit values s')) →
      Cleans (runStep vocabulary validator context challenge decode budget action s next exit)
  | .receive site schema peer output type, s, next, exit, nested, nexts, _ => by
      simp only [runStep]
      split
      · split
        · exact Cleans.stop nested _ _ _
        · split
          · refine Cleans.stop ?_ _ _ _
            exact nested.congr rfl rfl
          · split
            · apply nexts
              · exact nested.congr (State.bind_keeps _ _ _).2 (State.bind_events _ _ _)
              · exact State.bind_keeps _ _ _
            · refine Cleans.stop ?_ _ _ _
              exact nested.congr rfl rfl
      · exact Cleans.stop nested _ _ _
  | .call site function inputs outputs, s, next, exit, nested, nexts, _ => by
      simp only [runStep]
      split
      · split
        · rename_i frame below callee framesEq calleeEq
          split
          · split
            · exact localK_cleaned vocabulary validator context challenge budget (site, function) true none _ _ _ _
                (nested.enter _ _)
                (fun results s' frames events => by
                  have nested' : s'.Nested := (nested.enter (.call site function) _).congr (by rw [frames]) events
                  split
                  · rename_i top caller rest framesEq'
                    rw [framesEq'] at frames
                    simp only [List.cons.injEq] at frames
                    obtain ⟨topEq, callerEq⟩ := frames
                    split
                    · apply nexts
                      · have left := nested'.leave framesEq'
                          (frames := ⟨caller.id, outputs.zip results ++ caller.env⟩ :: rest) (by simp)
                          (by simp) .returned
                        rw [topEq] at left
                        exact left
                      · refine ⟨?_, ?_⟩
                        · simp [← callerEq]
                        · simp [← callerEq]
                    · exact Cleans.stop nested' _ _ _
                  · exact Cleans.stop nested' _ _ _)
            · exact Cleans.stop nested _ _ _
          · exact Cleans.stop nested _ _ _
        · exact Cleans.stop nested _ _ _
      · exact Cleans.stop nested _ _ _
  | .loop site count maximum induction carried captures body outputs, s, next, exit, nested, nexts, _ => by
      simp only [runStep]
      split
      · split
        · split
          · split
            · exact loopK_cleaned _
                (fun s' exit' nested' exits' => runK_cleaned body s' exit' nested' exits')
                site induction _ _ _ _ s.charge _ nested.charge
                (fun final s' nested' frames => by
                  apply nexts
                  · exact nested'.congr (State.bind_keeps _ _ _).2 (State.bind_events _ _ _)
                  · have keeps := State.bind_keeps s' outputs final
                    unfold State.Keeps at keeps ⊢
                    rw [frames] at keeps
                    exact keeps)
            · exact Cleans.stop nested _ _ _
          · exact Cleans.stop nested _ _ _
        · exact Cleans.stop nested _ _ _
      · exact Cleans.stop nested _ _ _
  | .yield values, s, next, exit, nested, _, exits => by
      simp only [runStep]
      split
      · split
        · split
          · exact exits _ _ nested.charge (State.Keeps.refl s)
          · exact Cleans.stop nested.charge _ _ _
        · exact Cleans.stop nested.charge _ _ _
      · exact Cleans.stop nested _ _ _
  | .ret values, s, next, exit, nested, _, _ => by
      simp only [runStep]
      split
      · split
        · rename_i frame framesEq
          split
          · split
            · simp [Cleans, State.done_cleaned (s := s.charge) nested framesEq]
            · exact Cleans.stop nested.charge _ _ _
          · exact Cleans.stop nested.charge _ _ _
        · exact Cleans.stop nested.charge _ _ _
      · exact Cleans.stop nested _ _ _
  | .unsupported _, s, next, exit, nested, _, _ => by
      simp only [runStep]
      exact Cleans.stop nested _ _ _
end

/-- Every run of the executable leaves every frame it entered, the
participant's, the loop iterations' and the local calls' included, and each
exit leaves the innermost frame still open; on a stop, the frames still active
are left innermost first. -/
theorem execute_cleaned (data : List (Value F G)) (history : History F G) (bytes : List UInt8) :
    (fun result => decide result.Cleaned) <$>
        execute vocabulary validator context challenge decode budget data history bytes =
      (fun _ => true) <$> execute vocabulary validator context challenge decode budget data history bytes := by
  unfold execute
  have nested : (initial validator data history bytes).Nested := ⟨rfl, rfl⟩
  split
  · exact runK_cleaned vocabulary validator context challenge decode budget _ _ _ nested
      (fun values s' nested' _ => Cleans.stop nested' _ _ _)
  · exact Cleans.stop nested _ _ _

end Cleanup

end Zkc.Executable
