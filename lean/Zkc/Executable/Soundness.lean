module

public import Zkc.Executable.Lowering
public import Zkc.Construction.Soundness

@[expose] public section

/-! Soundness of the lowering rule.

For every executable validator that reads back as constructed instructions
(`Validator.read`), every deployment context, challenge function in every
lawful monad, helper table, decoder, budget, data input, initial transcript and
proof byte string, the executable meaning and the metered ideal meaning of the
reading produce the same outcome class and the same interaction with the
challenge function (`execute_metered`). The proof read by the ideal meaning is
the decoding of the message bytes at the receive types. A normal return, a
budget stop and a refusal are distinct classes; the decoding, truncation and
operand failures of the executable, and an occurrence template without a model
occurrence, all correspond to the ideal refusal.

With a budget of at least the total charge, the metered meaning is the ideal
meaning (`metered_eq_ideal`); with a smaller budget it never returns
(`metered_constant`). The relation preserves outcome classes and the
interaction with the challenge function at every budget. It does not relate
stop sites, frame events, instruction counts at a stop or retained-value
ledgers, which are properties of the executable meaning alone.
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction Zkc.Source

variable {F G : Type}

/-- Whether a value has a sort: a data value is the encoding of a value of its
structured type. Transcript values carry no suite and coordinates no length. -/
def HasSort : Value F G → ValueSort → Prop
  | value, .data ty => ∃ decoded, Value.encode ty decoded = value
  | .transcript _, .transcript _ => True
  | .indices _, .indices => True
  | _, _ => False

/-- The outcome class of a run, in the stop vocabulary of the ideal meaning: a
budget stop is exhaustion; decoding, truncation and operand failures are
refusals. -/
def Result.outcome : Result F G → PIR.Outcome (List (Value F G))
  | .returned values => .returned values
  | .stopped .limit _ _ => .stopped .exhausted
  | .stopped _ _ _ => .stopped .refused

/-- What the relation compares: the outcome class and, after a normal return,
whether the whole proof was read. -/
def observation {α : Type} (outcome : PIR.Outcome α) (complete : Bool) : PIR.Outcome α × Bool :=
  match outcome with
  | .returned _ => (outcome, complete)
  | .stopped _ => (outcome, true)

def Run.observe (run : Run F G) : PIR.Outcome (List (Value F G)) × Bool :=
  observation run.result.outcome run.unread.isEmpty

def idealObservation (result : PIR.Outcome (List (Value F G)) × Proof F G) :
    PIR.Outcome (List (Value F G)) × Bool :=
  observation result.1 result.2.isEmpty

/-- A frame and a reading scope agree: every name the scope maps to a
reference is bound in the frame to that reference's value. -/
def FrameAgrees (env : List (Value F G)) (frame : Frame F G) (scope : List (String × Nat)) : Prop :=
  ∀ name reference, List.lookup name scope = some reference →
    reference < env.length ∧ List.lookup name frame.env = env[reference]?

/-- The simulation invariant between a machine state, a reading state and the
ideal environment. -/
structure Simulates (R : Reading) (s : State F G) (env : List (Value F G)) : Prop where
  used : s.used = R.tick
  length : env.length = R.sorts.length
  sorted : ∀ (index : Nat) (value : Value F G) (sort : ValueSort),
    env[index]? = some value → R.sorts[index]? = some sort → HasSort value sort
  live : env[R.current]? = some (.transcript s.live)
  frames : List.Forall₂ (FrameAgrees env) s.frames R.scopes

/-! ## Charges -/

theorem readItems_charges {vocabulary : Vocabulary} {validator : Validator} :
    ∀ {items : List Item} {R : Reading} {L : Lowered},
      readItems vocabulary validator items R = .ok L →
      (∀ entry ∈ L.code, R.tick < entry.2 ∧ entry.2 < L.total) ∧ R.tick < L.total := by
  intro items
  induction items with
  | nil => intro R L read; simp [readItems] at read
  | cons item rest ih =>
    intro R L read
    cases item with
    | receive site schema peer output type =>
        simp only [readItems] at read
        split at read
        · split at read
          · split at read
            · rename_i tail tailRead
              cases read
              obtain ⟨charges, total⟩ := ih tailRead
              refine ⟨?_, by simp only at total ⊢; omega⟩
              intro entry member
              rcases List.mem_cons.mp member with rfl | member
              · simp only at total ⊢; omega
              · have := charges entry member; simp only at this ⊢; omega
            · cases read
          · cases read
        · cases read
    | enter site function arguments formals =>
        simp only [readItems] at read
        split at read
        · split at read
          · split at read
            · obtain ⟨charges, total⟩ := ih read
              exact ⟨fun entry member => by have := charges entry member; simp only at this ⊢; omega,
                by simp only at total; omega⟩
            · cases read
          · cases read
        · cases read
    | operation call function site binding parameters inputs outputs =>
        simp only [readItems] at read
        split at read
        · split at read
          · split at read
            · split at read
              · split at read
                · rename_i tail tailRead
                  cases read
                  obtain ⟨charges, total⟩ := ih tailRead
                  refine ⟨?_, by simp only at total ⊢; omega⟩
                  intro entry member
                  rcases List.mem_cons.mp member with rfl | member
                  · simp only at total ⊢; omega
                  · have := charges entry member; simp only at this ⊢; omega
                · cases read
              · cases read
            · cases read
          · cases read
        · cases read
        · cases read
    | leave call function values outputs results =>
        simp only [readItems] at read
        split at read
        · split at read
          · split at read
            · obtain ⟨charges, total⟩ := ih read
              exact ⟨fun entry member => by have := charges entry member; simp only at this ⊢; omega,
                by simp only at total; omega⟩
            · cases read
          · cases read
        · cases read
    | finish values =>
        simp only [readItems] at read
        split at read
        · split at read
          · split at read
            · cases read
              exact ⟨fun entry member => by simp at member, by simp⟩
            · cases read
          · cases read
        · cases read
    | unsupported name => simp [readItems] at read

section Metered
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (context : Context) (challenge : History F G → m F)
  (table : Structured.Evaluation.Meanings F G Structured.closedInterface)

omit [LawfulMonad m] in
theorem metered_exhausted (returned : List Nat) {total budget : Nat}
    {code : List (Instruction × Nat)} (env : List (Value F G)) (proof : Proof F G)
    (charges : ∀ entry ∈ code, budget < entry.2) (short : budget < total) :
    metered context challenge table returned total budget code env proof =
      pure (.stopped .exhausted, proof) := by
  cases code with
  | nil => simp [metered, Nat.not_le.mpr short]
  | cons entry rest =>
      obtain ⟨instruction, charge⟩ := entry
      have := charges _ List.mem_cons_self
      simp [metered, Nat.not_le.mpr this]

omit [LawfulMonad m] in
theorem metered_eq_ideal (returned : List Nat) {total budget : Nat} (sufficient : total ≤ budget) :
    ∀ (code : List (Instruction × Nat)), (∀ entry ∈ code, entry.2 ≤ total) →
      ∀ env proof, metered context challenge table returned total budget code env proof =
        ideal context challenge table returned (code.map (·.1)) env proof := by
  intro code
  induction code with
  | nil => intro _ env proof; simp [metered, ideal, idealK, sufficient]
  | cons entry rest ih =>
      intro bounded env proof
      obtain ⟨instruction, charge⟩ := entry
      have within : charge ≤ budget := le_trans (bounded _ List.mem_cons_self) sufficient
      simp only [metered, ideal, within, ite_true, List.map_cons, idealK]
      congr 1
      funext env' unread
      exact ih (fun entry member => bounded entry (List.mem_cons_of_mem _ member)) _ _

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Loop iterations whose body returns only stops or results of its
continuation do the same. -/
theorem iterateM_constant {R β : Type} (observer : PIR.Outcome R × Proof F G → β) (constant : β)
    (onStops : ∀ stop proof, observer (.stopped stop, proof) = constant)
    (body : List (Value F G) → Proof F G →
      (List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)) → m (PIR.Outcome R × Proof F G))
    (bodyConstant : ∀ start proof
      (next : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      (∀ env unread, observer <$> next env unread = (fun _ => constant) <$> next env unread) →
      observer <$> body start proof next = (fun _ => constant) <$> body start proof next)
    (env : List (Value F G)) (yielded : List Nat) :
    ∀ (items : List Nat) (carried : List (Value F G)) (proof : Proof F G)
      (next : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      (∀ env unread, observer <$> next env unread = (fun _ => constant) <$> next env unread) →
      observer <$> iterateM body env yielded items carried proof next =
        (fun _ => constant) <$> iterateM body env yielded items carried proof next
  | [], carried, proof, next, continues => continues carried proof
  | index :: rest, carried, proof, next, continues => by
      simp only [iterateM]
      apply bodyConstant
      intro final unread
      split
      · exact iterateM_constant observer constant onStops body bodyConstant env yielded rest _ _ next
          continues
      · simp [onStops]

set_option linter.unusedSectionVars false in
mutual
/-- The ideal meaning returns only stops or results of its continuation: a
function of the result that is constant on stops and on every continuation
result is constant. -/
theorem idealK_constant {R β : Type} (observer : PIR.Outcome R × Proof F G → β) (constant : β)
    (onStops : ∀ stop proof, observer (.stopped stop, proof) = constant) :
    ∀ (instructions : List Instruction) (env : List (Value F G)) (proof : Proof F G)
      (next : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      (∀ env unread, observer <$> next env unread = (fun _ => constant) <$> next env unread) →
      observer <$> idealK context challenge table instructions env proof next =
        (fun _ => constant) <$> idealK context challenge table instructions env proof next
  | [], env, proof, next, continues => by simpa only [idealK] using continues env proof
  | instruction :: rest, env, proof, next, continues => by
      simp only [idealK]
      exact idealStep_constant observer constant onStops instruction env proof _
        (fun env' unread => idealK_constant observer constant onStops rest env' unread next continues)

theorem idealStep_constant {R β : Type} (observer : PIR.Outcome R × Proof F G → β) (constant : β)
    (onStops : ∀ stop proof, observer (.stopped stop, proof) = constant) :
    ∀ (instruction : Instruction) (env : List (Value F G)) (proof : Proof F G)
      (next : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      (∀ env unread, observer <$> next env unread = (fun _ => constant) <$> next env unread) →
      observer <$> idealStep context challenge table instruction env proof next =
        (fun _ => constant) <$> idealStep context challenge table instruction env proof next
  | ⟨operation, operands, results, body⟩, env, proof, next, continues => by
      have stopped : ∀ (stop : PIR.Stop) (unread : Proof F G),
          observer <$> (pure (.stopped stop, unread) : m (PIR.Outcome R × Proof F G)) =
            (fun _ => constant) <$> (pure (.stopped stop, unread) : m (PIR.Outcome R × Proof F G)) := by
        intro stop unread
        simp [onStops]
      cases operation with
      | loop site maximum yielded =>
          cases operands with
          | nil => exact stopped _ _
          | cons count initial =>
              simp only [idealStep]
              split
              · split
                · exact iterateM_constant observer constant onStops _
                    (fun start unread continuation bodyContinues =>
                      idealK_constant observer constant onStops body start unread continuation
                        bodyContinues) env yielded _ _ proof _ (fun final unread => continues _ _)
                · exact stopped _ _
              · exact stopped _ _
      | _ =>
          unfold idealStep
          repeat' split
          all_goals first
            | exact stopped _ _
            | exact continues _ _
            | (simp only [map_bind]
               congr 1
               funext answer
               exact continues _ _)
            | simp_all
end

/-- Below the total charge the metered meaning never returns: every function
of its result that is constant on stops is constant. -/
theorem metered_constant {β : Type} (returned : List Nat) {total budget : Nat} (short : budget < total) :
    ∀ (code : List (Instruction × Nat)) (observer : PIR.Outcome (List (Value F G)) × Proof F G → β)
      (constant : β), (∀ stop proof, observer (.stopped stop, proof) = constant) →
      ∀ env proof, observer <$> metered context challenge table returned total budget code env proof =
        (fun _ => constant) <$> metered context challenge table returned total budget code env proof := by
  intro code
  induction code with
  | nil =>
      intro observer constant onStops env proof
      simp [metered, Nat.not_le.mpr short, onStops]
  | cons entry rest ih =>
      intro observer constant onStops env proof
      obtain ⟨instruction, charge⟩ := entry
      simp only [metered]
      split
      · exact idealStep_constant context challenge table observer constant onStops instruction env proof _
          (fun env' unread => ih observer constant onStops env' unread)
      · simp [onStops]

end Metered

/-! ## Names, frames and scopes -/

theorem lookup_append_some {α β : Type} [BEq α] (name : α) :
    ∀ (first second : List (α × β)),
      List.lookup name (first ++ second) = (List.lookup name first).or (List.lookup name second)
  | [], second => by simp [List.lookup]
  | (key, value) :: first, second => by
      cases h : name == key <;> simp [List.lookup, h, lookup_append_some name first second]

theorem lookupAll_eq {env : List (Value F G)} {frame : Frame F G} {scope : List (String × Nat)}
    (agrees : FrameAgrees env frame scope) :
    ∀ {names : List String} {references : List Nat}, names.mapM (lookupName scope) = .ok references →
      lookupAll frame.env names = references.mapM (fun reference => env[reference]?) ∧
        ∀ reference ∈ references, reference < env.length := by
  intro names
  induction names with
  | nil =>
      intro references read
      change Except.ok [] = Except.ok references at read
      cases read
      simp [lookupAll]
  | cons name names ih =>
      intro references read
      simp only [List.mapM_cons, lookupName] at read
      split at read
      · rename_i reference found
        simp only [bind, Except.bind] at read
        split at read
        · cases read
        · rename_i others othersRead
          cases read
          obtain ⟨bound, same⟩ := agrees name reference found
          obtain ⟨rest, bounds⟩ := ih othersRead
          refine ⟨?_, ?_⟩
          · simp only [lookupAll, List.mapM_cons] at rest ⊢
            rw [same, rest]
          · intro r member
            rcases List.mem_cons.mp member with rfl | member
            · exact bound
            · exact bounds r member
      · cases read

theorem lookup_zip_mapM (env : List (Value F G)) :
    ∀ {formals : List String} {references : List Nat} {values : List (Value F G)},
      references.mapM (fun reference => env[reference]?) = some values →
      ∀ name reference, List.lookup name (formals.zip references) = some reference →
        reference ∈ references ∧ List.lookup name (formals.zip values) = env[reference]?
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | formal :: formals, reference :: references, values, found => by
      simp only [List.mapM_cons] at found
      cases first : env[reference]? with
      | none => simp [first] at found
      | some value =>
          cases others : references.mapM (fun reference => env[reference]?) with
          | none => simp [first, others] at found
          | some rest =>
              simp [first, others] at found
              subst found
              intro name target lookup
              by_cases same : name = formal
              · subst same
                simp at lookup
                subst lookup
                simp [first]
              · have hb : (name == formal) = false := by simpa using same
                simp only [List.zip_cons_cons, List.lookup, hb] at lookup ⊢
                obtain ⟨member, value⟩ := lookup_zip_mapM env others name target lookup
                exact ⟨List.mem_cons_of_mem _ member, value⟩

theorem lookup_zip_range' :
    ∀ {outputs : List String} {results : List (Value F G)} (env : List (Value F G)),
      outputs.length = results.length →
      ∀ name reference,
        List.lookup name (outputs.zip (List.range' env.length results.length)) = some reference →
        reference < env.length + results.length ∧
          List.lookup name (outputs.zip results) = (env ++ results)[reference]?
  | [], _, _, _ => by simp
  | _ :: _, [], _, lengths => by simp at lengths
  | output :: outputs, result :: results, env, lengths => by
      intro name reference found
      simp only [List.length_cons, List.range'_succ, List.zip_cons_cons] at found
      by_cases same : name = output
      · subst same
        simp at found
        subst found
        simp
      · have hb : (name == output) = false := by simpa using same
        simp only [List.lookup, hb] at found
        have tail := lookup_zip_range' (outputs := outputs) (results := results) (env ++ [result])
          (by simpa using lengths) name reference (by simpa [Nat.add_comm] using found)
        simp only [List.length_append, List.length_cons, List.length_nil] at tail
        refine ⟨by simp only [List.length_cons]; omega, ?_⟩
        simp only [List.zip_cons_cons, List.lookup, hb]
        simpa using tail.2

theorem FrameAgrees.extend {env : List (Value F G)} {frame : Frame F G}
    {scope : List (String × Nat)} (agrees : FrameAgrees env frame scope) (more : List (Value F G)) :
    FrameAgrees (env ++ more) frame scope := by
  intro name reference found
  obtain ⟨bound, same⟩ := agrees name reference found
  exact ⟨by simp; omega, by rw [same, List.getElem?_append_left bound]⟩

theorem frames_extend {env : List (Value F G)} {frames : List (Frame F G)}
    {scopes : List (List (String × Nat))} (agree : List.Forall₂ (FrameAgrees env) frames scopes)
    (more : List (Value F G)) : List.Forall₂ (FrameAgrees (env ++ more)) frames scopes := by
  induction agree with
  | nil => exact .nil
  | cons head _ ih => exact .cons (head.extend more) ih

theorem length_of_mapM_some {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → xs.length = ys.length
  | [], ys, found => by
      change some [] = some ys at found
      cases found
      rfl
  | x :: xs, ys, found => by
      simp only [List.mapM_cons] at found
      cases first : f x with
      | none => simp [first] at found
      | some y =>
          cases others : xs.mapM f with
          | none => simp [first, others] at found
          | some zs =>
              simp [first, others] at found
              subst found
              simp [length_of_mapM_some others]

theorem mapM_getElem?_some {α : Type} (env : List α) :
    ∀ {references : List Nat}, (∀ reference ∈ references, reference < env.length) →
      ∃ values, references.mapM (fun reference => env[reference]?) = some values
  | [], _ => ⟨[], rfl⟩
  | reference :: references, bounds => by
      obtain ⟨values, found⟩ := mapM_getElem?_some env (references := references)
        (fun r member => bounds r (List.mem_cons_of_mem _ member))
      refine ⟨env[reference]'(bounds reference List.mem_cons_self) :: values, ?_⟩
      simp [List.mapM_cons, found, List.getElem?_eq_getElem (bounds reference List.mem_cons_self)]

theorem lookup_zip_isNone {α β γ : Type} [BEq α] (name : α) :
    ∀ {keys : List α} {first : List β} {second : List γ},
      keys.length = first.length → keys.length = second.length →
      (List.lookup name (keys.zip first)).isNone = (List.lookup name (keys.zip second)).isNone
  | [], _, _, _, _ => by simp
  | _ :: _, [], _, lengths, _ => by simp at lengths
  | _ :: _, _ :: _, [], _, lengths => by simp at lengths
  | key :: keys, _ :: first, _ :: second, lengths, others => by
      simp only [List.zip_cons_cons, List.lookup]
      cases name == key
      · exact lookup_zip_isNone name (by simpa using lengths) (by simpa using others)
      · rfl

theorem FrameAgrees.pushAll {env : List (Value F G)} {frame : Frame F G}
    {scope : List (String × Nat)} (agrees : FrameAgrees env frame scope) (id : FrameId)
    (outputs : List String) (results : List (Value F G)) (lengths : outputs.length = results.length) :
    FrameAgrees (env ++ results) ⟨id, outputs.zip results ++ frame.env⟩
      (outputs.zip (List.range' env.length results.length) ++ scope) := by
  intro name reference found
  rw [lookup_append_some] at found
  simp only [lookup_append_some]
  cases inner : List.lookup name (outputs.zip (List.range' env.length results.length)) with
  | some target =>
      rw [inner] at found
      simp only [Option.some_or, Option.some.injEq] at found
      subst found
      obtain ⟨bound, same⟩ := lookup_zip_range' env lengths name target inner
      refine ⟨by simp; omega, ?_⟩
      obtain ⟨value, present⟩ : ∃ value, (env ++ results)[target]? = some value :=
        ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
      rw [same, present, Option.some_or]
  | none =>
      rw [inner] at found
      simp only [Option.none_or] at found
      have absent : List.lookup name (outputs.zip results) = none := by
        have := lookup_zip_isNone name (keys := outputs) (first := List.range' env.length results.length)
          (second := results) (by simp [lengths]) lengths
        rw [inner] at this
        simpa using this.symm
      rw [absent, Option.none_or]
      exact (agrees.extend results) name reference found

theorem FrameAgrees.push {env : List (Value F G)} {frame : Frame F G}
    {scope : List (String × Nat)} (agrees : FrameAgrees env frame scope) (id : FrameId)
    (name : String) (value : Value F G) :
    FrameAgrees (env ++ [value]) ⟨id, (name, value) :: frame.env⟩ ((name, env.length) :: scope) := by
  simpa using agrees.pushAll id [name] [value] rfl

theorem FrameAgrees.enter {env : List (Value F G)} {references : List Nat} {values : List (Value F G)}
    (formals : List String) (id : FrameId)
    (bounds : ∀ reference ∈ references, reference < env.length)
    (found : references.mapM (fun reference => env[reference]?) = some values) :
    FrameAgrees env ⟨id, formals.zip values⟩ (formals.zip references) := by
  intro name reference lookup
  obtain ⟨member, same⟩ := lookup_zip_mapM env found name reference lookup
  exact ⟨bounds reference member, same⟩

theorem FrameAgrees.leave {env : List (Value F G)} {caller : Frame F G}
    {scope : List (String × Nat)} (agrees : FrameAgrees env caller scope) (id : FrameId)
    {outputs : List String} {references : List Nat} {values : List (Value F G)}
    (lengths : outputs.length = references.length)
    (bounds : ∀ reference ∈ references, reference < env.length)
    (found : references.mapM (fun reference => env[reference]?) = some values) :
    FrameAgrees env ⟨id, outputs.zip values ++ caller.env⟩ (outputs.zip references ++ scope) := by
  intro name reference lookup
  rw [lookup_append_some] at lookup
  simp only [lookup_append_some]
  have valuesLength : references.length = values.length := length_of_mapM_some found
  cases inner : List.lookup name (outputs.zip references) with
  | some target =>
      rw [inner] at lookup
      simp only [Option.some_or, Option.some.injEq] at lookup
      subst lookup
      obtain ⟨member, same⟩ := lookup_zip_mapM env found name target inner
      refine ⟨bounds target member, ?_⟩
      obtain ⟨value, present⟩ : ∃ value, env[target]? = some value :=
        ⟨_, List.getElem?_eq_getElem (bounds target member)⟩
      rw [same, present, Option.some_or]
  | none =>
      rw [inner] at lookup
      simp only [Option.none_or] at lookup
      have absent : List.lookup name (outputs.zip values) = none := by
        have := lookup_zip_isNone name (keys := outputs) (first := references) (second := values)
          lengths (lengths.trans valuesLength)
        rw [inner] at this
        simpa using this.symm
      rw [absent, Option.none_or]
      exact agrees name reference lookup

theorem sorted_extend {env : List (Value F G)} {sorts : List ValueSort}
    (length : env.length = sorts.length)
    (sorted : ∀ (index : Nat) (value : Value F G) (sort : ValueSort),
      env[index]? = some value → sorts[index]? = some sort → HasSort value sort)
    {more : List (Value F G)} {moreSorts : List ValueSort}
    (moreSorted : ∀ (index : Nat) (value : Value F G) (sort : ValueSort),
      more[index]? = some value → moreSorts[index]? = some sort → HasSort value sort) :
    ∀ (index : Nat) (value : Value F G) (sort : ValueSort),
      (env ++ more)[index]? = some value → (sorts ++ moreSorts)[index]? = some sort →
        HasSort value sort := by
  intro index value sort found sortFound
  rcases Nat.lt_or_ge index env.length with lt | ge
  · rw [List.getElem?_append_left lt] at found
    rw [List.getElem?_append_left (length ▸ lt)] at sortFound
    exact sorted index value sort found sortFound
  · rw [List.getElem?_append_right ge] at found
    rw [List.getElem?_append_right (length ▸ ge), ← length] at sortFound
    exact moreSorted _ value sort found sortFound

theorem forall₂_cons_right {α β : Type} {relation : α → β → Prop} {first : List α} {head : β}
    {tail : List β} (agree : List.Forall₂ relation first (head :: tail)) :
    ∃ top below, first = top :: below ∧ relation top head ∧ List.Forall₂ relation below tail := by
  cases agree with
  | cons related rest => exact ⟨_, _, rfl, related, rest⟩

theorem payloadType_scalar (payload : Payload F G) : scalarType (payloadType payload) = some payload.ty := by
  cases payload <;> rfl

theorem scalarType_payload {ty : Structured.Ty} {payload : Payload F G}
    (scalar : scalarType ty = some payload.ty) : ty = payloadType payload := by
  cases ty <;> cases payload <;> simp_all [scalarType, payloadType, Payload.ty]

/-- A decoded payload has its own structured type as a sort. -/
theorem payload_sorted (payload : Payload F G) : HasSort (.data payload) (.data (payloadType payload)) := by
  cases payload with
  | boolean value => exact ⟨value, rfl⟩
  | field domain value => exact ⟨value, rfl⟩
  | group domain value => exact ⟨value, rfl⟩

/-- A data value of a scalar type is a payload of that type. -/
theorem sorted_payload {value : Value F G} {payload : Payload F G} {ty : Structured.Ty}
    (sorted : HasSort value (.data ty)) (found : value = .data payload) : payloadType payload = ty := by
  obtain ⟨decoded, encoded⟩ := sorted
  subst found
  cases ty <;> simp [Value.encode] at encoded <;> subst encoded <;> rfl

/-- Encoded values have the sorts of their types. -/
theorem encodeValues_sorted :
    ∀ {tys : List Structured.Ty} (values : Values (Structured.assignment F G) tys)
      (index : Nat) (value : Value F G) (sort : ValueSort),
      (encodeValues values)[index]? = some value → (tys.map ValueSort.data)[index]? = some sort →
        HasSort value sort
  | [], .nil, _, _, _, found, _ => by simp [encodeValues] at found
  | ty :: _, .cons head rest, 0, value, sort, found, sortFound => by
      simp only [encodeValues, List.getElem?_cons_zero, Option.some.injEq, List.map_cons] at found sortFound
      subst found sortFound
      exact ⟨head, rfl⟩
  | _ :: _, .cons _ rest, index + 1, value, sort, found, sortFound => by
      simp only [encodeValues, List.getElem?_cons_succ, List.map_cons] at found sortFound
      exact encodeValues_sorted rest index value sort found sortFound

theorem calculate_sorted [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    {calculation : Calculation} {arguments results : List (Value F G)}
    (computed : Zkc.Construction.calculate calculation arguments = .returned results) :
    ∀ (index : Nat) (value : Value F G) (sort : ValueSort), results[index]? = some value →
      (calculation.op.results.map ValueSort.data)[index]? = some sort → HasSort value sort := by
  unfold Zkc.Construction.calculate at computed
  split at computed
  · cases computed
  · split at computed
    · cases computed
      exact encodeValues_sorted _
    · cases computed

theorem evaluate_stopped [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (calculation : Calculation) {values : Values (Structured.assignment F G) calculation.op.arguments}
    {reason : PIR.Stop} (stopped : calculation.evaluate values = .stopped reason) : reason = .refused := by
  cases calculation with
  | boundedAt domain =>
      rcases values with _ | ⟨container, _ | ⟨index, _ | _⟩⟩
      simp only [Calculation.evaluate] at stopped
      split at stopped
      · cases stopped
      · cases stopped
        rfl
  | _ =>
      rcases values with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩
      simp [Calculation.evaluate] at stopped

/-- A calculation stops only by refusing. -/
theorem calculate_stopped [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    {calculation : Calculation} {arguments : List (Value F G)} {reason : PIR.Stop}
    (stopped : Zkc.Construction.calculate calculation arguments = .stopped reason) : reason = .refused := by
  unfold Zkc.Construction.calculate at stopped
  split at stopped
  · cases stopped
    rfl
  · split at stopped
    · cases stopped
    · rename_i stop evaluated
      cases stopped
      exact evaluate_stopped calculation evaluated

theorem readOperation_calculate (sorts : List ValueSort) (current : Nat) (site : String)
    (calculation : Calculation) (operands : List Nat) :
    readOperation sorts current site (.calculate calculation) operands =
      if operands.map (sorts[·]?) = calculation.op.arguments.map (some ∘ .data) then
        .ok (.calculate calculation, calculation.op.results.map .data, false)
      else .error (.operation site) := by
  rcases operands with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;> rfl

theorem Simulates.value {R : Reading} {s : State F G} {env : List (Value F G)}
    (sim : Simulates R s env) {index : Nat} {sort : ValueSort} (sortEq : R.sorts[index]? = some sort) :
    ∃ value, env[index]? = some value ∧ HasSort value sort := by
  have bound : index < env.length := by
    rw [sim.length]
    exact (List.getElem?_eq_some_iff.mp sortEq).1
  exact ⟨_, List.getElem?_eq_getElem bound,
    sim.sorted index _ sort (List.getElem?_eq_getElem bound) sortEq⟩

theorem Simulates.indices {R : Reading} {s : State F G} {env : List (Value F G)}
    (sim : Simulates R s env) {index : Nat} (sortEq : R.sorts[index]? = some .indices) :
    ∃ coordinates, env[index]? = some (.indices coordinates) := by
  obtain ⟨value, found, sorted⟩ := sim.value sortEq
  cases value with
  | indices coordinates => exact ⟨coordinates, found⟩
  | data => cases sorted
  | index => cases sorted
  | vector => cases sorted
  | transcript => cases sorted

theorem not_sorted_transcript {history : History F G} {ty : Structured.Ty} :
    ¬ HasSort (.transcript history) (.data ty) := by
  rintro ⟨decoded, encoded⟩
  cases ty <;> simp [Value.encode] at encoded

theorem custody_of_read [DecidableEq F] [DecidableEq G] {R : Reading} {s : State F G}
    {env : List (Value F G)} (sim : Simulates R s env) :
    ∀ {references : List Nat} {results : List (Value F G)},
      references.mapM (fun reference => env[reference]?) = some results →
      (references.all fun reference =>
        match (R.sorts[reference]? : Option ValueSort) with
        | some (.transcript _) => reference == R.current
        | _ => true) = true →
      custodyKept s.live results = true
  | [], results, found, _ => by
      change some [] = some results at found
      cases found
      rfl
  | reference :: references, results, found, checked => by
      simp only [List.mapM_cons] at found
      cases first : env[reference]? with
      | none => simp [first] at found
      | some value =>
          cases others : references.mapM (fun reference => env[reference]?) with
          | none => simp [first, others] at found
          | some rest =>
              simp [first, others] at found
              subst found
              simp only [List.all_cons, Bool.and_eq_true] at checked
              have tail := custody_of_read sim others checked.2
              simp only [custodyKept, List.all_cons, Bool.and_eq_true] at tail ⊢
              refine ⟨?_, tail⟩
              cases value with
              | transcript history =>
                  have bound : reference < R.sorts.length := by
                    rw [← sim.length]
                    exact (List.getElem?_eq_some_iff.mp first).1
                  obtain ⟨sort, sortFound⟩ : ∃ sort, R.sorts[reference]? = some sort :=
                    ⟨_, List.getElem?_eq_getElem bound⟩
                  have sorted := sim.sorted reference _ sort first sortFound
                  cases sort with
                  | transcript suite =>
                      have current := checked.1
                      simp only [sortFound, beq_iff_eq] at current
                      subst current
                      rw [sim.live] at first
                      simp at first
                      simp [first]
                  | data => exact absurd sorted not_sorted_transcript
                  | indices => cases sorted
              | data => rfl
              | index => rfl
              | vector => rfl
              | indices => rfl

theorem Simulates.operation {R : Reading} {s : State F G} {env : List (Value F G)}
    (sim : Simulates R s env) {scope : List (String × Nat)} {below : List (List (String × Nat))}
    (scopesEq : R.scopes = scope :: below) {top : Frame F G} {rest₀ : List (Frame F G)}
    (framesEq : s.frames = top :: rest₀) {outputs : List String} {values : List (Value F G)}
    {sorts : List ValueSort} (lengths : outputs.length = sorts.length)
    (valuesLength : values.length = sorts.length)
    (valuesSorted : ∀ (index : Nat) (value : Value F G) (sort : ValueSort),
      values[index]? = some value → sorts[index]? = some sort → HasSort value sort)
    {current : Nat} {live : History F G}
    (liveEq : (env ++ values)[current]? = some (.transcript live)) (transitions : Nat) :
    Simulates
      ⟨(outputs.zip (List.range' R.sorts.length sorts.length) ++ scope) :: below, R.sorts ++ sorts,
        current, R.tick + 1⟩
      { s with used := s.used + 1, live := live, transitions := transitions,
               frames := ⟨top.id, outputs.zip values ++ top.env⟩ :: rest₀ }
      (env ++ values) where
  used := by simp [sim.used]
  length := by simp [sim.length, valuesLength]
  sorted := sorted_extend sim.length sim.sorted valuesSorted
  live := liveEq
  frames := by
    have frames := sim.frames
    rw [scopesEq, framesEq] at frames
    cases frames with
    | cons agrees belowAgree =>
        refine .cons ?_ (frames_extend belowAgree _)
        have := agrees.pushAll top.id outputs values (lengths.trans valuesLength.symm)
        rwa [valuesLength, sim.length] at this

theorem admits_sorts {validator : Validator} {data : List (Payload F G)}
    (admitted : validator.admits data = true) :
    ∃ suite, validator.inputs.map (·.2.sort) =
      data.map (fun payload => ValueSort.data (payloadType payload)) ++ [.transcript suite] := by
  unfold Validator.admits at admitted
  simp only [Bool.and_eq_true, beq_iff_eq] at admitted
  obtain ⟨dropped, last⟩ := admitted
  cases lastEq : validator.inputs.getLast? with
  | none => simp [lastEq] at last
  | some pair =>
      obtain ⟨name, type⟩ := pair
      simp only [lastEq] at last
      cases sortEq : type.sort with
      | transcript suite =>
          refine ⟨suite, ?_⟩
          have mapped : (validator.inputs.map (·.2.sort)).getLast? = some (.transcript suite) := by
            simp [List.getLast?_map, lastEq, sortEq]
          obtain ⟨front, frontEq⟩ := List.getLast?_eq_some_iff.mp mapped
          rw [frontEq] at dropped ⊢
          simp only [List.dropLast_concat] at dropped
          rw [dropped]
      | data => simp [sortEq] at last
      | indices => simp [sortEq] at last

/-! ## Simulation -/

section Simulation
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (vocabulary : Vocabulary) (validator : Validator) (context : Context)
  (challenge : History F G → m F) (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
  (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)

theorem run_metered :
    ∀ (items : List Item) (R : Reading) (L : Lowered) (s : State F G) (env : List (Value F G)),
      readItems vocabulary validator items R = .ok L → Simulates R s env →
      Run.observe <$> run vocabulary validator context challenge decode budget items s =
        idealObservation <$> metered context challenge table L.returned L.total budget L.code env
          (decodeProof decode L.receives s.proof) := by
  intro items
  induction items with
  | nil => intro R L s env read; simp [readItems] at read
  | cons item rest ih =>
    intro R L s env read sim
    have stops : ∀ (t : State F G) (cause : Cause) (site : Option String)
        (call : Option (String × String)) (stop : PIR.Stop) (unread : Proof F G),
        cause ≠ .limit → stop = .refused →
        Run.observe <$> (pure (t.stop cause site call) : m (Run F G)) =
          idealObservation <$> (pure (.stopped stop, unread) :
            m (PIR.Outcome (List (Value F G)) × Proof F G)) := by
      intro t cause site call stop unread notLimit refused
      subst refused
      cases cause <;> simp_all [State.stop, Run.observe, idealObservation, observation, Result.outcome]
    cases item with
    | receive site schema peer output type =>
        simp only [readItems] at read
        split at read
        · rename_i ty scope below sortEq scopesEq
          split at read
          · split at read
            · rename_i tail tailRead
              cases read
              simp only [run, metered]
              by_cases within : s.used < budget
              · have charge : R.tick + 1 ≤ budget := by rw [← sim.used]; omega
                simp only [within, charge, ite_true]
                cases frame : readFrame s.proof with
                | none =>
                    simp only [decodeProof, frame, idealStep]
                    cases scalarType ty <;>
                      exact stops _ _ _ _ _ _ (by simp) rfl
                | some pair =>
                    obtain ⟨payload, unread⟩ := pair
                    cases decoded : decode type payload with
                    | none =>
                        simp only [decodeProof, frame, decoded, idealStep]
                        cases scalarType ty <;>
                          exact stops _ _ _ _ _ _ (by simp) rfl
                    | some value =>
                        have frames := sim.frames
                        rw [scopesEq] at frames
                        obtain ⟨top, rest₀, framesEq, agrees, belowAgree⟩ := forall₂_cons_right frames
                        simp only [framesEq]
                        by_cases typed : type.sort = ValueSort.data (payloadType value)
                        · have same : ty = payloadType value := by
                            rw [sortEq] at typed
                            exact ValueSort.data.inj typed
                          simp only [typed, ite_true, decodeProof, frame, decoded, idealStep, same,
                            payloadType_scalar]
                          have current : R.current < env.length :=
                            (List.getElem?_eq_some_iff.mp sim.live).1
                          apply ih _ tail _ _ tailRead
                          exact {
                            used := by simp [sim.used]
                            length := by simp [sim.length]
                            sorted := sorted_extend sim.length sim.sorted (by
                              intro index v sort found sortFound
                              match index, found, sortFound with
                              | 0, found, sortFound =>
                                  simp at found sortFound
                                  subst found sortFound
                                  rw [same]
                                  exact payload_sorted value)
                            live := by
                              simpa [List.getElem?_append_left current] using sim.live
                            frames := by
                              refine .cons ?_ (frames_extend belowAgree _)
                              simpa [sim.length] using agrees.push top.id output (Value.data value) }
                        · have different : ty ≠ payloadType value := by
                            intro same
                            exact typed (by rw [sortEq, same])
                          simp only [typed, ite_false, decodeProof, frame, decoded, idealStep]
                          cases scalar : scalarType ty with
                          | none => exact stops _ _ _ _ _ _ (by simp) rfl
                          | some common =>
                              have mismatch : ¬ value.ty = common := by
                                intro same
                                exact different (scalarType_payload (same ▸ scalar))
                              simp only [mismatch, ite_false]
                              exact stops _ _ _ _ _ _ (by simp) rfl
              · have charge : ¬ R.tick + 1 ≤ budget := by rw [← sim.used]; omega
                simp [within, charge, State.stop, Run.observe, idealObservation, observation, Result.outcome]
            · cases read
          · cases read
        · cases read
    | enter site function arguments formals =>
        simp only [readItems] at read
        split at read
        · rename_i scope others scopesEq
          split at read
          · rename_i references argumentsRead
            split at read
            · rename_i conditions
              have lengths := conditions.1
              have frames := sim.frames
              rw [scopesEq] at frames
              obtain ⟨top, rest₀, framesEq, agrees, belowAgree⟩ := forall₂_cons_right frames
              obtain ⟨lookups, bounds⟩ := lookupAll_eq agrees argumentsRead
              obtain ⟨values, valuesEq⟩ := mapM_getElem?_some env bounds
              simp only [run]
              by_cases within : s.used < budget
              · have lengthsValues : formals.length = values.length :=
                  lengths.trans (length_of_mapM_some valuesEq)
                simp only [within, ite_true, framesEq, lookups, valuesEq, lengthsValues]
                apply ih _ L _ _ read
                exact {
                  used := by simp [sim.used]
                  length := sim.length
                  sorted := sim.sorted
                  live := sim.live
                  frames := by
                    exact .cons (FrameAgrees.enter formals _ bounds valuesEq) (framesEq ▸ sim.frames) }
              · obtain ⟨charges, total⟩ := readItems_charges read
                have exhausted := metered_exhausted (total := L.total) (budget := budget) context challenge
                  table L.returned env (decodeProof decode L.receives s.proof)
                  (fun entry member => by
                    have := (charges entry member).1
                    simp only at this
                    rw [sim.used] at within
                    omega)
                  (by simp only at total; rw [sim.used] at within; omega)
                simp [within, State.stop, Run.observe, idealObservation, observation, Result.outcome, exhausted]
            · cases read
          · cases read
        · cases read
    | operation call function site binding parameters inputs outputs =>
        simp only [readItems] at read
        split at read
        · rename_i scope below resolved scopesEq resolvedEq
          split at read
          · rename_i operands operandsRead
            split at read
            · rename_i operation results advances operationRead
              split at read
              · rename_i lengths
                split at read
                · rename_i tail tailRead
                  cases read
                  have frames := sim.frames
                  rw [scopesEq] at frames
                  obtain ⟨top, rest₀, framesEq, agrees, belowAgree⟩ := forall₂_cons_right frames
                  obtain ⟨lookups, bounds⟩ := lookupAll_eq agrees operandsRead
                  obtain ⟨arguments, argumentsEq⟩ := mapM_getElem?_some env bounds
                  simp only [run, metered]
                  by_cases within : s.used < budget
                  · have charge : R.tick + 1 ≤ budget := by rw [← sim.used]; omega
                    simp only [within, charge, ite_true, framesEq, resolvedEq, lookups, argumentsEq]
                    have current : R.current < env.length :=
                      (List.getElem?_eq_some_iff.mp sim.live).1
                    cases resolved with
                    | indicesEmpty =>
                        cases operands with
                        | cons => simp [readOperation] at operationRead
                        | nil =>
                            simp only [readOperation, Except.ok.injEq, Prod.mk.injEq] at operationRead
                            obtain ⟨rfl, rfl, rfl⟩ := operationRead
                            change some [] = some arguments at argumentsEq
                            cases argumentsEq
                            simp only [Resolved.apply, idealStep, pure_bind, List.length_singleton]
                            simp only [List.length_singleton] at lengths
                            simp only [lengths, ite_true]
                            apply ih _ tail _ _ tailRead
                            simpa using sim.operation scopesEq framesEq (values := [.indices []])
                              (sorts := [.indices]) (by simpa using lengths) rfl
                              (by intro index v sort found sortFound
                                  match index, found, sortFound with
                                  | 0, found, sortFound =>
                                      simp at found sortFound; subst found sortFound; trivial)
                              (current := R.current) (live := s.live)
                              (by simpa [List.getElem?_append_left current] using sim.live)
                              (s.transitions + 0)
                    | observe suite leaf template =>
                        rcases operands with _ | ⟨state, _ | ⟨value, _ | ⟨coordinates, _ | ⟨extra, more⟩⟩⟩⟩
                        all_goals try (simp [readOperation] at operationRead; done)
                        simp only [readOperation] at operationRead
                        split at operationRead
                        · rename_i conditions
                          obtain ⟨stateEq, stateSort, valueSort, coordinatesSort⟩ := conditions
                          simp only [Except.ok.injEq, Prod.mk.injEq] at operationRead
                          obtain ⟨rfl, rfl, rfl⟩ := operationRead
                          subst stateEq
                          obtain ⟨observed, valueFound, valueSorted⟩ := sim.value valueSort
                          obtain ⟨coordinateValues, coordinatesFound⟩ := sim.indices coordinatesSort
                          simp only [List.mapM_cons, sim.live, valueFound, coordinatesFound] at argumentsEq
                          simp only [List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
                            Option.bind_some, Option.some.injEq] at argumentsEq
                          subst argumentsEq
                          simp only [idealStep, transcriptAt, sim.live]
                          cases origin : template.origin context with
                          | none =>
                              cases observed <;> simp only [Resolved.apply, origin, pure_bind] <;>
                                exact stops _ _ _ _ _ _ (by simp) rfl
                          | some occurrence =>
                              cases observed with
                              | data payload =>
                                  have payloadSort := sorted_payload valueSorted rfl
                                  simp only [Resolved.apply, origin, payloadSort, and_self, ite_true,
                                    pure_bind, dataAt, valueFound, List.length_singleton]
                                  simp only [List.length_singleton] at lengths
                                  simp only [lengths, ite_true]
                                  apply ih _ tail _ _ tailRead
                                  simpa using sim.operation scopesEq framesEq
                                    (values := [.transcript (s.live ++ [.message occurrence payload])])
                                    (sorts := [.transcript suite]) (by simpa using lengths) rfl
                                    (by intro index v sort found sortFound
                                        match index, found, sortFound with
                                        | 0, found, sortFound =>
                                            simp at found sortFound; subst found sortFound; trivial)
                                    (current := R.sorts.length)
                                    (live := s.live ++ [.message occurrence payload])
                                    (by simp [← sim.length])
                                    (s.transitions + 1)
                              | index =>
                                  simp only [Resolved.apply, pure_bind, dataAt, valueFound]
                                  exact stops _ _ _ _ _ _ (by simp) rfl
                              | vector =>
                                  simp only [Resolved.apply, pure_bind, dataAt, valueFound]
                                  exact stops _ _ _ _ _ _ (by simp) rfl
                              | transcript =>
                                  simp only [Resolved.apply, pure_bind, dataAt, valueFound]
                                  exact stops _ _ _ _ _ _ (by simp) rfl
                              | indices =>
                                  simp only [Resolved.apply, pure_bind, dataAt, valueFound]
                                  exact stops _ _ _ _ _ _ (by simp) rfl
                        · cases operationRead
                    | challenge suite field template =>
                        rcases operands with _ | ⟨state, _ | ⟨coordinates, _ | ⟨extra, more⟩⟩⟩
                        all_goals try (simp [readOperation] at operationRead; done)
                        simp only [readOperation] at operationRead
                        split at operationRead
                        · rename_i conditions
                          obtain ⟨stateEq, stateSort, coordinatesSort⟩ := conditions
                          simp only [Except.ok.injEq, Prod.mk.injEq] at operationRead
                          obtain ⟨rfl, rfl, rfl⟩ := operationRead
                          subst stateEq
                          obtain ⟨coordinateValues, coordinatesFound⟩ := sim.indices coordinatesSort
                          simp only [List.mapM_cons, sim.live, coordinatesFound] at argumentsEq
                          simp only [List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
                            Option.bind_some, Option.some.injEq] at argumentsEq
                          subst argumentsEq
                          simp only [idealStep, transcriptAt, sim.live]
                          cases origin : template.origin context with
                          | none =>
                              simp only [Resolved.apply, origin, pure_bind]
                              exact stops _ _ _ _ _ _ (by simp) rfl
                          | some occurrence =>
                              simp only [Resolved.apply, origin, ite_true, bind_map_left, map_bind]
                              congr 1
                              funext answer
                              simp only [List.length_cons, List.length_nil] at lengths
                              simp only [List.length_cons, List.length_nil, lengths, ite_true]
                              apply ih _ tail _ _ tailRead
                              simpa using sim.operation scopesEq framesEq
                                (values := [.data (.field field answer),
                                  .transcript (s.live ++ [.challenge occurrence])])
                                (sorts := [.data (.field field), .transcript suite])
                                (by simpa using lengths) rfl
                                (by intro index v sort found sortFound
                                    match index, found, sortFound with
                                    | 0, found, sortFound =>
                                        simp at found sortFound; subst found sortFound
                                        exact ⟨answer, rfl⟩
                                    | 1, found, sortFound =>
                                        simp at found sortFound; subst found sortFound; trivial)
                                (current := R.sorts.length + 1)
                                (live := s.live ++ [.challenge occurrence])
                                (by simp [← sim.length])
                                (s.transitions + 1)
                        · cases operationRead
                    | calculate calculation =>
                        rw [readOperation_calculate] at operationRead
                        split at operationRead
                        · simp only [Except.ok.injEq, Prod.mk.injEq] at operationRead
                          obtain ⟨rfl, rfl, rfl⟩ := operationRead
                          have readEq : read env operands = some arguments := argumentsEq
                          simp only [Resolved.apply, idealStep, readEq, pure_bind]
                          cases computed : Zkc.Construction.calculate calculation arguments with
                          | stopped reason =>
                              simp only
                              exact stops _ _ _ _ _ _ (by simp) (calculate_stopped computed)
                          | returned results =>
                              have resultsLength := calculate_length calculation computed
                              simp only [List.length_map] at lengths
                              have outputsLength : outputs.length = results.length := by
                                rw [lengths, resultsLength]
                              simp only [outputsLength, ite_true]
                              apply ih _ tail _ _ tailRead
                              simpa using sim.operation scopesEq framesEq
                                (values := results) (sorts := calculation.op.results.map ValueSort.data)
                                (by simpa using lengths) (by simp [resultsLength])
                                (calculate_sorted computed)
                                (current := R.current) (live := s.live)
                                (by simpa [List.getElem?_append_left current] using sim.live)
                                (s.transitions + 0)
                        · cases operationRead
                  · have charge : ¬ R.tick + 1 ≤ budget := by rw [← sim.used]; omega
                    simp [within, charge, State.stop, Run.observe, idealObservation, observation, Result.outcome]
                · cases read
              · cases read
            · cases read
          · cases read
        · cases read
        · cases read
    | leave call function values outputs results =>
        simp only [readItems] at read
        split at read
        · rename_i scope callerScope below scopesEq
          split at read
          · rename_i references valuesRead
            split at read
            · rename_i conditions
              obtain ⟨lengths, -⟩ := conditions
              have frames := sim.frames
              rw [scopesEq] at frames
              obtain ⟨top, rest₀, framesEq, agrees, belowAgree⟩ := forall₂_cons_right frames
              obtain ⟨callerFrame, rest₁, restEq, callerAgrees, lowerAgree⟩ :=
                forall₂_cons_right belowAgree
              obtain ⟨lookups, bounds⟩ := lookupAll_eq agrees valuesRead
              obtain ⟨found, foundEq⟩ := mapM_getElem?_some env bounds
              simp only [run]
              by_cases within : s.used < budget
              · have lengthsFound : outputs.length = found.length :=
                  lengths.trans (length_of_mapM_some foundEq)
                simp only [within, ite_true, framesEq, restEq, lookups, foundEq, lengthsFound]
                apply ih _ L _ _ read
                exact {
                  used := by simp [sim.used]
                  length := sim.length
                  sorted := sim.sorted
                  live := sim.live
                  frames := .cons (callerAgrees.leave callerFrame.id lengths bounds foundEq) lowerAgree }
              · obtain ⟨charges, total⟩ := readItems_charges read
                have exhausted := metered_exhausted (total := L.total) (budget := budget) context challenge
                  table L.returned env (decodeProof decode L.receives s.proof)
                  (fun entry member => by
                    have := (charges entry member).1
                    simp only at this
                    rw [sim.used] at within
                    omega)
                  (by simp only at total; rw [sim.used] at within; omega)
                simp [within, State.stop, Run.observe, idealObservation, observation, Result.outcome, exhausted]
            · cases read
          · cases read
        · cases read
    | finish values =>
        simp only [readItems] at read
        split at read
        · rename_i scope scopesEq
          split at read
          · rename_i references valuesRead
            split at read
            · rename_i checked
              cases read
              have frames := sim.frames
              rw [scopesEq] at frames
              obtain ⟨top, rest₀, framesEq, agrees, belowAgree⟩ := forall₂_cons_right frames
              cases belowAgree
              obtain ⟨lookups, bounds⟩ := lookupAll_eq agrees valuesRead
              obtain ⟨found, foundEq⟩ := mapM_getElem?_some env bounds
              have readEq : read env references = some found := foundEq
              simp only [run, metered]
              by_cases within : s.used < budget
              · have charge : R.tick + 1 ≤ budget := by rw [← sim.used]; omega
                have custody := custody_of_read sim foundEq checked
                simp [within, charge, framesEq, lookups, foundEq, custody, State.done, Result.outcome,
                  finish, readEq, Run.observe, idealObservation, observation, decodeProof]
                cases s.proof <;> simp
              · have charge : ¬ R.tick + 1 ≤ budget := by rw [← sim.used]; omega
                simp [within, charge, State.stop, Run.observe, idealObservation, observation, Result.outcome]
            · cases read
          · cases read
        · cases read
    | unsupported name => simp [readItems] at read

/-- The lowering relation: every executable validator that reads back as
constructed instructions has, at every budget, the outcome class and challenge
interaction of the metered ideal meaning of its reading, on the decoded proof. -/
theorem execute_metered {L : Lowered} (read : validator.read vocabulary = .ok L)
    (data : List (Payload F G)) (history : History F G) (bytes : List UInt8)
    (admitted : validator.admits data = true) :
    Run.observe <$> execute vocabulary validator context challenge decode budget data history bytes =
      idealObservation <$> metered context challenge table L.returned L.total budget L.code
        (data.map .data ++ [.transcript history]) (decodeProof decode L.receives bytes) := by
  unfold Validator.read at read
  dsimp only at read
  split_ifs at read with conditions
  · obtain ⟨suite, sortsEq⟩ := admits_sorts admitted
    unfold execute
    simp only [admitted, ite_true]
    apply run_metered vocabulary validator context challenge table decode budget _ _ L _ _ read
    have inputsLength : validator.inputs.length = data.length + 1 := by
      simpa using congrArg List.length sortsEq
    exact {
      used := rfl
      length := by simp [inputsLength]
      sorted := by
        intro index value sort found sortFound
        simp only [sortsEq] at sortFound
        rcases Nat.lt_or_ge index data.length with lt | ge
        · rw [List.getElem?_append_left (by simpa using lt)] at found sortFound
          simp only [List.getElem?_map] at found sortFound
          cases item : data[index]? with
          | none => simp [item] at found
          | some payload =>
              simp [item] at found sortFound
              subst found sortFound
              exact payload_sorted payload
        · rw [List.getElem?_append_right (by simpa using ge)] at found sortFound
          simp only [List.length_map] at found sortFound
          cases offset : index - data.length with
          | zero =>
              simp [offset] at found sortFound
              subst found sortFound
              trivial
          | succ k => simp [offset] at found
      live := by
        simp [inputsLength, initial]
      frames := by
        refine .cons ?_ .nil
        intro name reference found
        have lengths : (validator.inputs.map (·.1)).length = (data.map Value.data ++
            [Value.transcript history]).length := by simp [inputsLength]
        have := lookup_zip_range' (outputs := validator.inputs.map (·.1))
          (results := data.map Value.data ++ [Value.transcript history]) [] lengths name reference
        simp only [List.length_nil, List.nil_append, Nat.zero_add] at this
        rw [List.length_map, List.range_eq_range'] at found
        exact this (by simpa [inputsLength] using found) }

/-- The reading's instructions all charge less than its total. -/
theorem read_charges {vocabulary : Vocabulary} {validator : Validator} {L : Lowered}
    (read : validator.read vocabulary = .ok L) : ∀ entry ∈ L.code, entry.2 ≤ L.total := by
  unfold Validator.read at read
  dsimp only at read
  split_ifs at read
  exact fun entry member => Nat.le_of_lt ((readItems_charges read).1 entry member).2

/-- With a budget of at least the total charge, the executable has the ideal
meaning's observation and challenge interaction. -/
theorem execute_ideal {L : Lowered} (read : validator.read vocabulary = .ok L)
    (sufficient : L.total ≤ budget) (data : List (Payload F G)) (history : History F G)
    (bytes : List UInt8) (admitted : validator.admits data = true) :
    Run.observe <$> execute vocabulary validator context challenge decode budget data history bytes =
      idealObservation <$> ideal context challenge table L.returned (L.code.map (·.1))
        (data.map .data ++ [.transcript history]) (decodeProof decode L.receives bytes) := by
  rw [execute_metered vocabulary validator context challenge table decode budget read data history bytes
    admitted, metered_eq_ideal context challenge table L.returned sufficient L.code (read_charges read)]

/-- Below the total charge every observation the executable can make is a
stop: any function of the observation that is constant on stops is constant. -/
theorem execute_short {β : Type} {L : Lowered} (read : validator.read vocabulary = .ok L)
    (short : budget < L.total) (data : List (Payload F G)) (history : History F G)
    (bytes : List UInt8) (admitted : validator.admits data = true)
    (observer : PIR.Outcome (List (Value F G)) × Bool → β) (constant : β)
    (onStops : ∀ stop, observer (.stopped stop, true) = constant) :
    (fun result => observer result.observe) <$>
        execute vocabulary validator context challenge decode budget data history bytes =
      (fun _ => constant) <$> execute vocabulary validator context challenge decode budget data history bytes := by
  have same := execute_metered vocabulary validator context challenge [] decode budget read data history
    bytes admitted
  have never := metered_constant context challenge [] L.returned short L.code
    (fun result => observer (idealObservation result))
    constant (fun stop proof => by simpa [idealObservation, observation] using onStops stop)
    (data.map .data ++ [.transcript history]) (decodeProof decode L.receives bytes)
  calc (fun result => observer result.observe) <$>
        execute vocabulary validator context challenge decode budget data history bytes
      = observer <$> (Run.observe <$>
          execute vocabulary validator context challenge decode budget data history bytes) := by
        rw [Functor.map_map]
    _ = observer <$> (idealObservation <$>
          metered context challenge [] L.returned L.total budget L.code (data.map .data ++ [.transcript history])
            (decodeProof decode L.receives bytes)) := by rw [same]
    _ = (fun _ => constant) <$> (idealObservation <$>
          metered context challenge [] L.returned L.total budget L.code (data.map .data ++ [.transcript history])
            (decodeProof decode L.receives bytes)) := by
        rw [Functor.map_map, Functor.map_map]
        exact never
    _ = (fun _ => constant) <$> execute vocabulary validator context challenge decode budget data history bytes := by
        rw [← same, Functor.map_map]

end Simulation

/-! ## Cleanup -/

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

theorem nested_enter (s : State F G) (frame : FrameId) (env : Env F G) (nested : s.Nested) :
    ({ s with frames := ⟨frame, env⟩ :: s.frames, events := s.events ++ [.enter frame] } :
      State F G).Nested := by
  obtain ⟨replayed, outermost⟩ := nested
  refine ⟨?_, ?_⟩
  · simp [replayFrames_append, replayed, replayFrames]
  · simp [List.getLast?_cons, outermost]

theorem nested_leave (s : State F G) (frame caller : Frame F G) (below : List (Frame F G))
    (env : Env F G) (framesEq : s.frames = frame :: caller :: below) (nested : s.Nested) :
    ({ s with frames := ⟨caller.id, env⟩ :: below, events := s.events ++ [.leave frame.id .returned] } :
      State F G).Nested := by
  obtain ⟨replayed, outermost⟩ := nested
  rw [framesEq] at replayed outermost
  refine ⟨?_, ?_⟩
  · simp [replayFrames_append, replayed, replayFrames]
  · simpa [List.getLast?_cons] using outermost

section Cleanup
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (vocabulary : Vocabulary) (validator : Validator) (context : Context)
  (challenge : History F G → m F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
  (budget : Nat)

theorem run_cleaned :
    ∀ (items : List Item) (s : State F G), s.Nested →
      (fun result => decide result.Cleaned) <$> run vocabulary validator context challenge decode budget items s =
        (fun _ => true) <$> run vocabulary validator context challenge decode budget items s := by
  intro items
  induction items with
  | nil => intro s nested; simp [run, State.stop_cleaned nested]
  | cons item rest ih =>
      intro s nested
      have stopped : ∀ (t : State F G), t.Nested → ∀ cause site call,
          (fun result => decide result.Cleaned) <$> (pure (t.stop cause site call) : m (Run F G)) =
            (fun _ => true) <$> (pure (t.stop cause site call) : m (Run F G)) := by
        intro t nestedT cause site call
        simp [State.stop_cleaned nestedT]
      cases item with
      | receive site schema peer output type =>
          simp only [run]
          split
          · split
            · exact stopped _ (by exact nested) _ _ _
            · split
              · exact stopped _ (by exact nested) _ _ _
              · rename_i value frame below decodedEq framesEq
                split
                · apply ih
                  unfold State.Nested at nested ⊢
                  rw [framesEq] at nested
                  simpa using nested
                · exact stopped _ (by exact nested) _ _ _
              · exact stopped _ (by exact nested) _ _ _
          · exact stopped _ (by exact nested) _ _ _
      | enter site function arguments formals =>
          simp only [run]
          split
          · split
            · split
              · split
                · exact ih _ (nested_enter { s with used := s.used + 1 } _ _ nested)
                · exact stopped _ (by exact nested) _ _ _
              · exact stopped _ (by exact nested) _ _ _
            · exact stopped _ (by exact nested) _ _ _
          · exact stopped _ (by exact nested) _ _ _
      | operation call function site binding parameters inputs outputs =>
          simp only [run]
          split
          · split
            · rename_i frame below resolved framesEq _
              split
              · simp only [map_bind]
                congr 1
                funext applied
                split
                · split
                  · apply ih
                    unfold State.Nested at nested ⊢
                    rw [framesEq] at nested
                    simpa using nested
                  · exact stopped _ (by exact nested) _ _ _
                · exact stopped _ (by exact nested) _ _ _
              · exact stopped _ (by exact nested) _ _ _
            · exact stopped _ (by exact nested) _ _ _
          · exact stopped _ (by exact nested) _ _ _
      | leave call function values outputs results =>
          simp only [run]
          split
          · split
            · rename_i frame caller below framesEq
              split
              · split
                · exact ih _ (nested_leave { s with used := s.used + 1 } frame caller below _ framesEq nested)
                · exact stopped _ (by exact nested) _ _ _
              · exact stopped _ (by exact nested) _ _ _
            · exact stopped _ (by exact nested) _ _ _
          · exact stopped _ (by exact nested) _ _ _
      | finish values =>
          simp only [run]
          split
          · split
            · rename_i frame framesEq
              split
              · rename_i results resultsEq
                split
                · have cleaned : ({ s with used := s.used + 1 }.done results).Cleaned :=
                    State.done_cleaned (s := { s with used := s.used + 1 }) nested framesEq results
                  simp [cleaned]
                · exact stopped _ (by exact nested) _ _ _
              · exact stopped _ (by exact nested) _ _ _
            · exact stopped _ (by exact nested) _ _ _
          · exact stopped _ (by exact nested) _ _ _
      | unsupported name => exact stopped _ (by exact nested) _ _ _

/-- Every run of the executable leaves every frame it entered, the
participant's included, and each exit leaves the innermost frame still open;
on a stop, the frames still active are therefore left innermost first.
Retiring the live transcript on a stop, and the returned one on a return, is
part of the definitions of `State.stop` and `State.done`, not of this theorem. -/
theorem execute_cleaned (data : List (Payload F G)) (history : History F G) (bytes : List UInt8) :
    (fun result => decide result.Cleaned) <$>
        execute vocabulary validator context challenge decode budget data history bytes =
      (fun _ => true) <$> execute vocabulary validator context challenge decode budget data history bytes := by
  unfold execute
  have nested : (initial validator data history bytes).Nested := ⟨rfl, rfl⟩
  split
  · exact run_cleaned vocabulary validator context challenge decode budget _ _ nested
  · simp [State.stop_cleaned nested]

end Cleanup

/-- The selected Boolean of a returned outcome is true. -/
def Decision (acceptance : Nat) : PIR.Outcome (List (Value F G)) → Bool
  | .returned values => selectedTrue values acceptance
  | .stopped _ => false

/-- Host acceptance of an observation: the whole proof was read and the
selected Boolean is true. -/
def Accepts (acceptance : Nat) (observed : PIR.Outcome (List (Value F G)) × Bool) : Bool :=
  observed.2 && Decision acceptance observed.1

theorem Run.accepts_observe [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (run : Run F G) (acceptance : Nat) : run.accepts acceptance = Accepts acceptance run.observe := by
  rcases run with ⟨result, _, _, _, unread, _, _⟩
  cases result with
  | returned values => rfl
  | stopped cause site call =>
      cases cause <;> simp [Run.accepts, Accepts, Decision, Run.observe, observation, Result.outcome]

section Validation
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (vocabulary : Vocabulary) (validator : Validator) (context : Context)
  (challenge : History F G → m F) (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
  (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)

/-- Host validation, with the expected framing header and a budget of at least
the total charge, is the ideal acceptance of the decoded proof, for every helper
table. -/
theorem validate_ideal {L : Lowered} (read : validator.read vocabulary = .ok L)
    (sufficient : L.total ≤ budget) (binding : List UInt8) (acceptance : Nat)
    (data : List (Payload F G)) (history : History F G) (bytes : List UInt8)
    (admitted : validator.admits data = true) (header : bytes.take 40 = magic ++ binding) :
    validate vocabulary validator context challenge decode budget binding acceptance data history bytes =
      (fun result => Accepts acceptance (idealObservation result)) <$>
        ideal context challenge table L.returned (L.code.map (·.1))
          (data.map .data ++ [.transcript history]) (decodeProof decode L.receives (bytes.drop 40)) := by
  unfold validate
  simp only [header, ↓reduceIte]
  have same := execute_ideal vocabulary validator context challenge table decode budget read sufficient data
    history (bytes.drop 40) admitted
  calc (fun result => result.accepts acceptance) <$>
        execute vocabulary validator context challenge decode budget data history (bytes.drop 40)
      = Accepts acceptance <$> (Run.observe <$>
          execute vocabulary validator context challenge decode budget data history (bytes.drop 40)) := by
        rw [Functor.map_map]
        congr 1
        funext result
        exact Run.accepts_observe result acceptance
    _ = _ := by rw [same, Functor.map_map]

/-- Host validation below the total charge, or with another framing header,
rejects on every path. -/
theorem validate_rejects {L : Lowered} (read : validator.read vocabulary = .ok L)
    (binding : List UInt8) (acceptance : Nat) (data : List (Payload F G)) (history : History F G)
    (bytes : List UInt8) (admitted : validator.admits data = true)
    (short : budget < L.total ∨ bytes.take 40 ≠ magic ++ binding) :
    validate vocabulary validator context challenge decode budget binding acceptance data history bytes =
      (fun _ => false) <$>
        validate vocabulary validator context challenge decode budget binding acceptance data history bytes := by
  unfold validate
  by_cases header : bytes.take 40 = magic ++ binding
  · have below : budget < L.total := short.resolve_right (not_not.mpr header)
    simp only [header, ↓reduceIte]
    have never := execute_short vocabulary validator context challenge decode budget read below data history
      (bytes.drop 40) admitted (Accepts acceptance) false (fun stop => by simp [Accepts, Decision])
    calc (fun result => result.accepts acceptance) <$>
          execute vocabulary validator context challenge decode budget data history (bytes.drop 40)
        = (fun result => Accepts acceptance result.observe) <$>
            execute vocabulary validator context challenge decode budget data history (bytes.drop 40) := by
          congr 1
          funext result
          exact Run.accepts_observe result acceptance
      _ = (fun _ => false) <$>
            execute vocabulary validator context challenge decode budget data history (bytes.drop 40) := never
      _ = (fun _ => false) <$> ((fun result => result.accepts acceptance) <$>
            execute vocabulary validator context challenge decode budget data history (bytes.drop 40)) := by
          rw [Functor.map_map]
  · simp [header]

end Validation

/-- What the per-compile rule establishes when it accepts. -/
theorem checkLowering_sound {vocabulary : Vocabulary} {participant : Participant}
    {validator : Validator} {L : Lowered}
    (accepted : checkLowering vocabulary participant validator = .ok L) :
    validator.read vocabulary = .ok L ∧ L.code.map (·.1) = participant.instructions ∧
      L.returned = participant.returned ∧ validator.inputs.map (·.2.sort) = participant.inputs ∧
      validator.results.map (·.sort) = participant.outputs ∧ validator.symbol = participant.symbol ∧
      validator.entry = participant.policy.entry ∧ validator.role = participant.policy.validator := by
  unfold checkLowering at accepted
  cases read : validator.read vocabulary with
  | error refusal => simp [read] at accepted; cases accepted
  | ok lowered =>
      simp only [read] at accepted
      by_cases symbol : validator.symbol = participant.symbol <;>
      by_cases entry : validator.entry = participant.policy.entry <;>
      by_cases role : validator.role = participant.policy.validator <;>
      by_cases inputs : validator.inputs.map (·.2.sort) = participant.inputs <;>
      by_cases outputs : validator.results.map (·.sort) = participant.outputs <;>
      by_cases code : lowered.code.map (·.1) = participant.instructions <;>
      by_cases returned : lowered.returned = participant.returned <;>
      simp_all [bind, Except.bind, pure, Except.pure]

end Zkc.Executable
