module

public import Zkc.Executable.DomainCompleteness

@[expose] public section

/-! Reusable budget rules for actual Code schedules and Domain Processes. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type}

theorem Continues.bind {A B : Type}
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (next : A → PIR.Process (Domain.effects (Structured.uniformCarriers F G)) B)
    (proof : Proof F G) (holds : B → Proof F G → Prop) :
    Continues (process.bind next) proof holds =
      Continues process proof (fun value unread => Continues (next value) unread holds) := by
  induction process generalizing proof with
  | done => rfl
  | halt => rfl
  | call operation continuation ih =>
      cases operation with
      | receive ty site schema peer =>
          cases proof with
          | nil => rfl
          | cons payload unread =>
              cases decoded : Value.decode ty (.data payload) <;> simp [Continues, PIR.Process.bind, decoded, ih]
      | query => simp only [PIR.Process.bind, Continues]; simp_rw [ih]
      | send | observe | checkpoint => exact ih () proof
      | localService => rfl

theorem Continues.of_yields {A : Type}
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (property : A → Prop) (yields : PIR.Yields property process) (proof : Proof F G) :
    Continues process proof (fun value _ => property value) := by
  induction process generalizing proof with
  | done => exact yields
  | halt => trivial
  | call operation continuation ih =>
      cases operation with
      | receive ty site schema peer =>
          cases proof with
          | nil => trivial
          | cons payload unread =>
              cases decoded : Value.decode ty (.data payload) with
              | none => simp [Continues, decoded]
              | some value => simpa only [Continues, decoded] using ih value (yields value) unread
      | query => exact fun reply => ih reply (yields reply) proof
      | send | observe | checkpoint => exact ih () (yields ()) proof
      | localService => trivial

/-- Proof-independent all-reply invariants can be used at any proof suffix. -/
theorem Continues.of_yields_all_proofs {A : Type}
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (proof : Proof F G) (post : A → Proof F G → Prop)
    (yields : PIR.Yields (fun value => ∀ unread, post value unread) process) :
    Continues process proof post :=
  Continues.mono _ _ _ _ (fun _ unread property => property unread)
    (Continues.of_yields process _ yields proof)

/-- A state-independent continuation bound holds after every returned Process
path, including processes whose reached helpers stop. -/
theorem Continues.of_forall {A : Type}
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (proof : Proof F G) (post : A → Proof F G → Prop)
    (all : ∀ value unread, post value unread) : Continues process proof post := by
  induction process generalizing proof with
  | done => exact all _ _
  | halt => trivial
  | call operation next ih =>
      cases operation with
      | receive ty site schema peer =>
          cases proof with
          | nil => trivial
          | cons payload unread =>
              cases decoded : Value.decode ty (.data payload) <;> simp [Continues, decoded, ih]
      | query => exact fun reply => ih reply proof
      | send | observe | checkpoint => exact ih () proof
      | localService => trivial

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (program : Structured.Program) (context : Context)
  (cost : String → List (Value F G) → Nat) (budget : Nat)

/-- A static segment can be followed by any run-dependent continuation. -/
theorem FitsK.of_static :
    ∀ (code : List Code) {total : Nat}, Code.static code = some total →
      ∀ env proof used post, used + total ≤ budget →
        Continues (Domain.evaluate (Structured.ringModel F G) program context (Code.instructions code) env)
          proof (fun final unread => post final unread (used + total)) →
        FitsK program context cost budget code env proof used post
  | [], total, static, env, proof, used, post, _, continues => by
      simp only [Code.static, Option.some.injEq] at static
      subst total
      simpa only [FitsK, Code.instructions, Domain.evaluate, Continues, Nat.add_zero] using continues
  | .charge count :: rest, total, static, env, proof, used, post, within, continues => by
      cases found : Code.static rest with
      | none => simp [Code.static, found] at static
      | some other =>
          simp only [Code.static, found, Option.map_some, Option.some.injEq] at static
          subst total
          refine ⟨by omega, ?_⟩
          apply FitsK.of_static rest found env proof (used + count) post (by omega)
          simpa only [Code.instructions, Nat.add_assoc] using continues
  | .step instruction charged :: rest, total, static, env, proof, used, post, within, continues => by
      cases found : Code.static rest with
      | none => simp [Code.static, found] at static
      | some other =>
          simp only [Code.static, found, Option.map_some, Option.some.injEq] at static
          subst total
          refine ⟨by omega, ?_⟩
          simp only [Code.instructions, Domain.evaluate, Continues, Continues.bind] at continues
          exact Continues.mono _ _ _ _ (fun final unread reached =>
            FitsK.of_static rest found final unread (used + charged) post (by omega)
              (by simpa only [Nat.add_assoc] using reached)) continues
  | .helper _ :: _, _, static, _, _, _, _, _, _ => by simp [Code.static] at static
  | .loop .. :: _, _, static, _, _, _, _, _, _ => by simp [Code.static] at static

/-- Split a Code schedule without changing helper or charge ordering. -/
theorem FitsK.append (first rest : List Code) (env : Environment F G)
    (proof : Proof F G) (used : Nat) (post : Environment F G → Proof F G → Nat → Prop) :
    FitsK program context cost budget (first ++ rest) env proof used post =
      FitsK program context cost budget first env proof used
        (fun final unread charged => FitsK program context cost budget rest final unread charged post) := by
  induction first generalizing env proof used with
  | nil => rfl
  | cons item first ih => simp only [List.cons_append, FitsK]; congr; funext final unread charged; exact ih final unread charged

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem FitsIterate.mono
    (body : Environment F G → Proof F G → Nat → (Environment F G → Proof F G → Nat → Prop) → Prop)
    (bodyMono : ∀ env proof used first second, (∀ final unread charged, first final unread charged → second final unread charged) →
      body env proof used first → body env proof used second)
    (outer : Environment F G) (yielded : List Nat) (declared : List ValueSort) :
    ∀ items carried proof used first second,
      (∀ final unread charged, first final unread charged → second final unread charged) →
      FitsIterate budget body outer yielded declared items carried proof used first →
      FitsIterate budget body outer yielded declared items carried proof used second
  | [], _, _, _, _, _, weaker, fits => weaker _ _ _ fits
  | _index :: rest, _carried, _proof, _used, first, second, weaker, fits =>
      bodyMono _ _ _ _ _ (fun _final unread charged found =>
        ⟨found.1, fun values readEq sorted =>
          FitsIterate.mono body bodyMono outer yielded declared rest values unread (charged + 1)
            first second weaker (found.2 values readEq sorted)⟩) fits

mutual
theorem FitsK.mono : ∀ code env proof used first second,
    (∀ final unread charged, first final unread charged → second final unread charged) →
    FitsK program context cost budget code env proof used first →
    FitsK program context cost budget code env proof used second
  | [], _, _, _, _, _, weaker, fits => weaker _ _ _ fits
  | item :: rest, env, proof, used, first, second, weaker, fits =>
      FitsStep.mono item env proof used _ _
        (fun final unread charged found => FitsK.mono rest final unread charged first second weaker found) fits

theorem FitsStep.mono : ∀ item env proof used first second,
    (∀ final unread charged, first final unread charged → second final unread charged) →
    FitsStep program context cost budget item env proof used first →
    FitsStep program context cost budget item env proof used second
  | .charge _, _, _, _, _, _, weaker, fits => ⟨fits.1, weaker _ _ _ fits.2⟩
  | .step _ _, _, _, _, _, _, weaker, fits =>
      ⟨fits.1, Continues.mono _ _ _ _ (fun final unread found => weaker _ _ _ found) fits.2⟩
  | .helper instruction, env, proof, used, first, second, weaker, fits => by
      obtain ⟨entry, called⟩ := fits
      refine ⟨entry, ?_⟩
      revert called
      generalize instruction.operation = operation
      generalize Domain.read env instruction.operands = found
      intro called
      cases operation <;> try exact called
      cases found with
      | none => trivial
      | some values =>
          obtain ⟨scalar, encoded, within, reached⟩ := called
          exact ⟨scalar, encoded, within, Continues.mono _ _ _ _ (fun final unread good => weaker _ _ _ good) reached⟩
  | .loop site maximum yielded operands declared body, env, proof, used, first, second, weaker, fits => by
      simp only [FitsStep] at fits ⊢
      cases operands with
      | nil => trivial
      | cons count refs =>
          simp only at fits ⊢
          cases countEq : env[count]? with
          | none => trivial
          | some value =>
              cases value with
              | transcript | indices => trivial
              | data payload =>
                  rcases payload with ⟨ty, eligible, contents⟩
                  cases ty <;> try (solve | trivial)
                  cases readEq : Domain.read env refs with
                  | none => trivial
                  | some carried =>
                      simp only [countEq, readEq] at fits ⊢
                      intro admitted
                      obtain ⟨entry, iterations⟩ := fits admitted
                      exact ⟨entry, FitsIterate.mono budget _
                        (fun start unread charged p q implication good =>
                          FitsK.mono body start unread charged p q implication good)
                        env yielded declared _ _ _ _ _ _
                        (fun final unread charged good sorted => weaker _ _ _ (good sorted)) iterations⟩
end

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Uniform body bounds compose for an arbitrary range of actual loop indices.
The body's postcondition includes the real yield read and its checked sorts. -/
theorem FitsIterate.invariant
    (body : Environment F G → Proof F G → Nat → (Environment F G → Proof F G → Nat → Prop) → Prop)
    (bodyMono : ∀ env proof used first second, (∀ final unread charged, first final unread charged → second final unread charged) →
      body env proof used first → body env proof used second)
    (outer : Environment F G) (yielded : List Nat) (declared : List ValueSort)
    (invariant : Nat → Environment F G → Proof F G → Prop) (bodyCost : Nat)
    (step : ∀ index carried proof used, invariant index carried proof → used + bodyCost + 1 ≤ budget →
      body (outer ++ .data (.index index) :: carried) proof used fun final unread charged =>
        charged ≤ used + bodyCost ∧ ∀ values, Domain.read final yielded = some values →
          Domain.sortsMatch declared values = true → invariant (index + 1) values unread) :
    ∀ count start carried proof used,
      invariant start carried proof → used + count * (bodyCost + 1) ≤ budget →
      FitsIterate budget body outer yielded declared (List.range' start count) carried proof used
        (fun final unread charged => invariant (start + count) final unread ∧
          charged ≤ used + count * (bodyCost + 1)) := by
  intro count
  induction count with
  | zero => intro start carried proof used valid within; exact ⟨by simpa using valid, by omega⟩
  | succ count ih =>
      intro start carried proof used valid within
      simp only [List.range'_succ, FitsIterate]
      apply bodyMono _ _ _ _ _ ?_ (step start carried proof used valid (by
        rw [Nat.succ_mul] at within
        omega))
      intro final unread charged found
      refine ⟨by rw [Nat.succ_mul] at within; omega, ?_⟩
      intro values readEq sorted
      have smaller : charged + 1 + count * (bodyCost + 1) ≤ budget := by
        rw [Nat.succ_mul] at within
        omega
      apply FitsIterate.mono budget body bodyMono outer yielded declared _ _ _ _ _ _ ?_
        (ih (start + 1) values unread (charged + 1) (found.2 values readEq sorted) smaller)
      intro result rest total good
      constructor
      · simpa only [Nat.add_assoc, Nat.add_comm 1 count] using good.1
      · rw [Nat.succ_mul]
        omega

/-- A helper's entry and actual erased-argument price are charged before its
canonical Domain step. Stops carry no continuation obligation. -/
theorem FitsK.helper (name : String) (refs : List Nat) (results : List ValueSort)
    (rest : List Code) (env : Environment F G) (proof : Proof F G) (used : Nat)
    (post : Environment F G → Proof F G → Nat → Prop)
    (values : Environment F G) (scalar : List (Value F G))
    (readEq : Domain.read env refs = some values) (encoded : arguments values = some scalar)
    (within : used + 1 + cost name scalar ≤ budget)
    (continues : Continues (Domain.step (Structured.ringModel F G) program context
      ⟨.call name, refs, results, []⟩ env) proof (fun final unread =>
        FitsK program context cost budget rest final unread (used + 1 + cost name scalar) post)) :
    FitsK program context cost budget (.helper ⟨.call name, refs, results, []⟩ :: rest) env proof used post := by
  simp only [FitsK, FitsStep, readEq]
  exact ⟨by omega, scalar, encoded, within, continues⟩

/-- Range-loop budget assembly using the shared actual Code invariant rule.
Admission precedes entry charging, and every body is followed by its yield. -/
theorem FitsK.loop_invariant (site : String) (maximum : Nat) (yielded : List Nat)
    (countRef : Nat) (refs : List Nat) (declared : List ValueSort) (body rest : List Code)
    (env carried : Environment F G) (proof : Proof F G) (used count : Nat)
    (post : Environment F G → Proof F G → Nat → Prop)
    (countEq : env[countRef]? = some (.data (.index count)))
    (readEq : Domain.read env refs = some carried)
    (invariant : Nat → Environment F G → Proof F G → Prop) (bodyCost : Nat)
    (initial : invariant 0 carried proof)
    (step : ∀ index values unread charged, invariant index values unread → charged + bodyCost + 1 ≤ budget →
      FitsK program context cost budget body (env ++ .data (.index index) :: values) unread charged
        (fun final unread charged' => charged' ≤ charged + bodyCost ∧ ∀ result,
          Domain.read final yielded = some result → Domain.sortsMatch declared result = true →
            invariant (index + 1) result unread))
    (within : count ≤ maximum → used + 1 + count * (bodyCost + 1) ≤ budget)
    (finish : count ≤ maximum → ∀ final unread charged, invariant count final unread →
      charged ≤ used + 1 + count * (bodyCost + 1) → Domain.sortsMatch declared final = true →
      FitsK program context cost budget rest (env ++ final) unread charged post) :
    FitsK program context cost budget
      (.loop site maximum yielded (countRef :: refs) declared body :: rest) env proof used post := by
  simp only [FitsK, FitsStep, countEq, readEq]
  intro admitted
  refine ⟨by have := within admitted.1; omega, ?_⟩
  have iterations := FitsIterate.invariant budget
    (fun start unread charged post => FitsK program context cost budget body start unread charged post)
    (fun start unread charged first second weaker fits =>
      FitsK.mono program context cost budget body start unread charged first second weaker fits)
    env yielded declared invariant bodyCost step count 0 carried proof (used + 1) initial (within admitted.1)
  rw [← List.range_eq_range'] at iterations
  apply FitsIterate.mono budget _
    (fun start unread charged first second weaker fits =>
      FitsK.mono program context cost budget body start unread charged first second weaker fits)
    env yielded declared _ _ _ _ _ _ ?_ iterations
  intro final unread charged good sorted
  exact finish admitted.1 final unread charged (by simpa only [Nat.zero_add] using good.1) good.2 sorted

end Zkc.Executable.DomainVM
