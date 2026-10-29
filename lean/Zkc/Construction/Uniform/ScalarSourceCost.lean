module

public import Zkc.Construction.OriginalSimulation
public import Zkc.Executable.DomainFitsRules
public import Zkc.Executable.DomainSchema

@[expose] public section

/-! Transport source return invariants into the existing metered Code rules.
Only scalar operand schemas and the actual Code charge reading are inspected.
The process meaning comes from the checked connection; no evaluator is added. -/
set_option autoImplicit false
namespace Zkc.Construction.Uniform.ScalarSourceCost
open Zkc.Source Zkc.Executable Zkc.Executable.DomainVM

/-- A complete connection transports all-reply return properties. -/
theorem yields {carriers : Structured.Carriers} {A B : Type} {returns : A → B → Prop}
    {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {source : PIR.Process (Domain.effects carriers) A} {target : PIR.Process (Domain.effects carriers) B}
    (connection : Original.Simulation returns live source target) (property : A → Prop) (post : B → Prop)
    (sourceHolds : PIR.Yields property source)
    (returned : ∀ a b, returns a b → property a → post b) : PIR.Yields post target := by
  induction connection with
  | done related => exact returned _ _ related sourceHolds
  | halt => trivial
  | call operation next ih => exact fun reply => ih reply (sourceHolds reply)
  | checkpoint frame related next ih => exact fun _ => ih sourceHolds

/-- The standard state interpretation also preserves every all-reply return
property of its source, even when an interpreted operation refuses. -/
theorem yields_state {I J : PIR.Signature} {A S : Type} (process : PIR.Process I A)
    (operations : PIR.StateOperationInterpretation I J S) (state : S) (property : A → Prop)
    (holds : PIR.Yields property process) :
    PIR.Yields (fun result => property result.1) (process.interpretState operations state) := by
  have all {B : Type} (body : PIR.Process J B) : PIR.Yields (fun _ => True) body := by
    induction body with
    | done | halt => trivial
    | call _ _ ih => exact fun reply => ih reply
  induction process generalizing state with
  | done => exact holds
  | halt => trivial
  | call operation next ih =>
    apply (all (operations operation state)).bind
    intro result _
    exact ih result.1 result.2 (holds result.1)

variable {F G : Type}

private theorem continues_with_yields {A : Type}
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (proof : Proof F G) (property : A → Prop) (post : A → Proof F G → Prop)
    (sourceHolds : PIR.Yields property process) (continued : Continues process proof post) :
    Continues process proof (fun value unread => property value ∧ post value unread) := by
  induction process generalizing proof with
  | done => exact ⟨sourceHolds, continued⟩
  | halt => trivial
  | call operation next ih =>
    cases operation with
    | receive ty site schema peer =>
      cases proof with
      | nil => trivial
      | cons payload unread =>
        cases decoded : Value.decode ty (.data payload) with
        | none => simp [Continues, decoded]
        | some value =>
          simpa only [Continues, decoded] using
            ih value unread (sourceHolds value) (by simpa only [Continues, decoded] using continued)
    | query => exact fun reply => ih reply proof (sourceHolds reply) (continued reply)
    | send | observe | checkpoint => exact ih () proof (sourceHolds ()) continued
    | localService => trivial

def scalarSort : ValueSort → Bool
  | .data .boolean | .data (.field _) | .data (.group _) | .data .index | .data (.vector _) | .indices => true
  | _ => false

/-- Finite operand-schema checks; charge items have no physical results. -/
def schema : List ValueSort → List Code → Bool
  | _, [] => true
  | sorts, .charge _ :: rest => schema sorts rest
  | sorts, .step instruction _ :: rest => schema (sorts ++ instruction.results) rest
  | sorts, .helper instruction :: rest =>
      instruction.operands.all (fun reference => (sorts[reference]?).any scalarSort) &&
        schema (sorts ++ instruction.results) rest
  | _, .loop .. :: _ => false

private theorem scalar_exists (value : Domain.Value (Structured.uniformCarriers F G))
    (supported : scalarSort value.sort = true) : ∃ scalar, DomainAdapter.readbackData value = some scalar := by
  cases value with
  | data payload =>
    rcases payload with ⟨ty, supportedTy, value⟩
    cases ty <;> simp_all [scalarSort, Domain.Value.sort, DomainAdapter.readbackData]
  | indices => exact ⟨_, rfl⟩
  | transcript => cases supported

private theorem arguments_of_schema (environment : Environment F G) :
    ∀ references, references.all (fun reference => ((environment.map Domain.Value.sort)[reference]?).any scalarSort) = true →
      ∃ nominal scalar, Domain.read environment references = some nominal ∧ arguments nominal = some scalar
  | [], _ => ⟨[], [], rfl, rfl⟩
  | reference :: references, supported => by
    simp only [List.all_cons, Bool.and_eq_true, List.getElem?_map] at supported
    cases found : environment[reference]? with
    | none => simp [found] at supported
    | some value =>
      obtain ⟨scalar, encoded⟩ := scalar_exists value (by simpa [found] using supported.1)
      obtain ⟨nominal, tail, read, encodedTail⟩ := arguments_of_schema environment references (by simpa only [List.getElem?_map] using supported.2)
      change references.mapM (environment[·]?) = some nominal at read
      change nominal.mapM DomainAdapter.readbackData = some tail at encodedTail
      exact ⟨value :: nominal, scalar :: tail, by simp [Domain.read, found, read],
        by simp [arguments, encoded, encodedTail]⟩

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (program : Structured.Program) (context : Context) (cost : String → List (Value F G) → Nat)
    (bounds : String → Option Nat)
    (prices : ∀ name bound, bounds name = some bound → ∀ values, cost name values ≤ bound) (budget : Nat)

include prices

/-- The actual source/target return property and scalar schemas suffice to
bound a loop-free charge segment, for every reply and every proof suffix. -/
theorem fits : ∀ (code : List Code) (total : Nat), Code.charges bounds code = some total →
    ∀ (environment : Environment F G) (proof : Proof F G) (used : Nat) (post : Environment F G → Proof F G → Prop),
    schema (environment.map Domain.Value.sort) code = true → used + total ≤ budget →
    Continues (Domain.evaluate (Structured.ringModel F G) program context (Code.instructions code) environment) proof post →
    FitsK program context cost budget code environment proof used
      (fun final unread charged => charged ≤ used + total ∧ post final unread)
  | [], total, reading, environment, proof, used, post, _, _, continued => by
    simp only [Code.charges, Option.some.injEq] at reading
    subst total
    exact ⟨by omega, by simpa only [Code.instructions, Domain.evaluate, Continues] using continued⟩
  | .charge count :: rest, total, reading, environment, proof, used, post, checked, within, continued => by
    cases tail : Code.charges bounds rest with
    | none => simp [Code.charges, tail] at reading
    | some other =>
      simp only [Code.charges, tail, Option.map_some, Option.some.injEq] at reading
      subst total
      refine ⟨by omega, ?_⟩
      exact FitsK.mono program context cost budget rest environment proof (used + count) _ _
        (fun _ _ _ found => ⟨by omega, found.2⟩)
        (fits rest other tail environment proof (used + count) post checked (by omega) (by simpa only [Code.instructions] using continued))
  | .step instruction charged :: rest, total, reading, environment, proof, used, post, checked, within, continued => by
    cases tail : Code.charges bounds rest with
    | none => simp [Code.charges, tail] at reading
    | some other =>
      simp only [Code.charges, tail, Option.map_some, Option.some.injEq] at reading
      subst total
      simp only [schema] at checked
      simp only [Code.instructions, Domain.evaluate, Continues, Continues.bind] at continued
      refine ⟨by omega, ?_⟩
      apply Continues.mono _ _ _ _ ?_ (continues_with_yields _ proof _ _
        (step_schema (Structured.ringModel F G) program context instruction environment) continued)
      intro final unread found
      obtain ⟨values, rfl, sorted⟩ := found.1
      have sorts : (environment ++ values).map Domain.Value.sort = environment.map Domain.Value.sort ++ instruction.results := by
        simp only [Domain.sortsMatch, beq_iff_eq] at sorted
        simp [sorted]
      exact FitsK.mono program context cost budget rest _ unread (used + charged) _ _
        (fun _ _ _ good => ⟨by omega, good.2⟩)
        (fits rest other tail _ unread (used + charged) post (by simpa only [sorts] using checked) (by omega) found.2)
  | .helper instruction :: rest, total, reading, environment, proof, used, post, checked, within, continued => by
    cases operation : instruction.operation <;> try simp [Code.charges, operation] at reading
    rename_i name
    cases bound : bounds name with
    | none => simp [bound] at reading
    | some most =>
      cases tail : Code.charges bounds rest with
      | none => simp [bound, tail] at reading
      | some other =>
        simp only [bound, tail, Option.some.injEq] at reading
        subst total
        simp only [schema, Bool.and_eq_true] at checked
        obtain ⟨nominal, scalar, read, encoded⟩ := arguments_of_schema environment instruction.operands checked.1
        have price := prices name most bound scalar
        simp only [Code.instructions, Domain.evaluate, Continues, Continues.bind] at continued
        refine ⟨by omega, ?_⟩
        simp only [operation, read]
        refine ⟨scalar, encoded, by omega, ?_⟩
        apply Continues.mono _ _ _ _ ?_ (continues_with_yields _ proof _ _
          (step_schema (Structured.ringModel F G) program context instruction environment) continued)
        intro final unread found
        obtain ⟨values, rfl, sorted⟩ := found.1
        have sorts : (environment ++ values).map Domain.Value.sort = environment.map Domain.Value.sort ++ instruction.results := by
          simp only [Domain.sortsMatch, beq_iff_eq] at sorted
          simp [sorted]
        exact FitsK.mono program context cost budget rest _ unread (used + 1 + cost name scalar) _ _
          (fun _ _ _ good => ⟨by omega, good.2⟩)
          (fits rest other tail _ unread _ post (by simpa only [sorts] using checked.2) (by omega) found.2)
  | .loop .. :: _, _, reading, _, _, _, _, _, _, _ => by simp [Code.charges] at reading

end Zkc.Construction.Uniform.ScalarSourceCost
