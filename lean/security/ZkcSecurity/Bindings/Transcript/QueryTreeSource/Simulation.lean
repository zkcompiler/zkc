module

public import ZkcSecurity.Bindings.Transcript.QueryTreeSource.Reading
public import VCVio.OracleComp.QueryTracking.RandomOracle.Routing

@[expose] public section

/-! Source-key consumers of the pinned cached-tree simulator.
Every adversarial query in the fixed-bound scalar domain is routed, including malformed
segment suffixes and keys outside the segment. Unparsed keys retain their whole identity in a
separate root. Other request ranges require the existing dependent-oracle composition boundary.
-/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.QueryTreeSource
open Zkc.Source Zkc.Construction QueryTree OracleComp OracleSpec Provider MeasureTheory
noncomputable local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- The actual scalar request slice, including arbitrary adversarial histories and origins.
The raw range is uniformly Fin bound after the independently checked positive-bound transport. -/
abbrev ScalarKey (carriers : Structured.Carriers) (bound : Nat) :=
  {key : Key carriers // key.2.request = some (.sampleIndex bound)}

abbrev Root (carriers : Structured.Carriers) (bound : Nat) :=
  Domain.History carriers ⊕ ScalarKey carriers bound

abbrev Coordinate (bound height : Nat) := Node (Fin bound) height ⊕ Unit

/-- Failure to parse is not refusal of an adversary query. Such a query gets its own disjoint
root and remains charged, even when it repeats. Parsed suffixes use the canonical entry root. -/
noncomputable def locate {carriers : Structured.Carriers} {bound height : Nat}
    (segment : Segment) (key : ScalarKey carriers bound) :
    Root carriers bound × Coordinate bound height :=
  match parse (bound := bound) (height := height) segment key.val with
  | some (root, node) => (.inl root, .inl node)
  | none => (.inr key, .inr ())

theorem locate_injective {carriers : Structured.Carriers} {bound height : Nat}
    (segment : Segment) : Function.Injective (@locate carriers bound height segment) := by
  intro first second same
  cases a : parse (bound := bound) (height := height) segment first.val with
  | none =>
    cases b : parse (bound := bound) (height := height) segment second.val with
    | none => simpa only [locate, a, b, Prod.mk.injEq, Sum.inr.injEq, and_true] using same
    | some pair => simp only [locate, a, b, Prod.mk.injEq, Sum.inr_ne_inl, false_and] at same
  | some firstPair =>
    cases b : parse (bound := bound) (height := height) segment second.val with
    | none => simp only [locate, a, b, Prod.mk.injEq, Sum.inl_ne_inr, false_and] at same
    | some secondPair =>
      simp only [locate, a, b] at same
      have roots := Sum.inl.inj (congrArg Prod.fst same)
      have nodes := Sum.inl.inj (congrArg Prod.snd same)
      apply Subtype.ext
      exact (encode_parse segment first.val _ a).symm.trans
        ((congrArg (encode segment) (Prod.ext roots nodes)).trans
          (encode_parse segment second.val _ b))

/-- Actual encoded source keys enter the tree branch, never the fallback branch. -/
theorem locate_encode {carriers : Structured.Carriers} {bound height : Nat}
    (segment : Segment) (request : segment.query.request = some (.sampleIndex bound))
    (pair : Domain.History carriers × Node (Fin bound) height) :
    locate segment ⟨encode segment pair, (segment.queryAt_request _).trans request⟩ =
      (.inl pair.1, .inl pair.2) := by
  simp only [locate, parse_encode]

/-- Expose the actual source query at the key required by the typed FS `ask` operation. -/
def sourceAsk {carriers : Structured.Carriers} {bound : Nat} (key : ScalarKey carriers bound) :
    OracleComp (OracleSpec.ofFn (Typed.ByLast (@Domain.Raw carriers)))
      (Domain.Raw (.challenge key.val.2 : Domain.Event carriers)) :=
  Typed.ask key.val.1 (.challenge key.val.2)

/-- Injective routing into arbitrary roots is exact under the initially empty lazy oracle.
Both sides are finitely restricted over every adaptive response branch before using the
pinned table law. This local routing lemma does not require finite transcript histories. -/
theorem routed_exact {carriers : Structured.Carriers} {bound height : Nat} [NeZero bound]
    (segment : Segment) {α : Type} [MeasurableSpace α]
    (program : OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) α) :
    𝒟[(simulateQ randomOracle
      (RandomOracleRouting.route (@locate carriers bound height segment) program)).run' ∅] =
      𝒟[(simulateQ randomOracle program).run' ∅] := by
  classical
  let cells := possibleQueryKeys program
  let mapped := RandomOracleRouting.route (@locate carriers bound height segment) program
  let image := cells.image (@locate carriers bound height segment)
  have covered : AllQueriesSatisfy program (· ∈ cells) :=
    allQueriesSatisfy_possibleQueryKeys program
  have transport (p : OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) α) :
      AllQueriesSatisfy p (· ∈ cells) →
        AllQueriesSatisfy (RandomOracleRouting.route (@locate carriers bound height segment) p)
          (· ∈ image) := by
    induction p using OracleComp.inductionOn with
    | pure value => intro _; exact allQueriesSatisfy_pure value _
    | query_bind key next ih =>
      intro good
      obtain ⟨member, rest⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp good
      change AllQueriesSatisfy (.queryBind (locate segment key)
        (fun reply ↦ RandomOracleRouting.route (locate segment) (next reply))) _
      apply (allQueriesSatisfy_query_bind_iff
        (spec := (Root carriers bound × Coordinate bound height) →ₒ Fin bound)
        (locate segment key) (fun reply ↦ RandomOracleRouting.route
          (locate segment) (next reply)) _).mpr
      exact ⟨Finset.mem_image.mpr ⟨key, member, rfl⟩, fun reply ↦ ih reply (rest reply)⟩
  have mappedCovered : AllQueriesSatisfy mapped (· ∈ image) := transport program covered
  let cell : cells → image := fun key ↦ ⟨locate segment key.val,
    Finset.mem_image.mpr ⟨key.val, key.property, rfl⟩⟩
  have distinct : Function.Injective cell := by
    intro first second same
    exact Subtype.ext (locate_injective segment (congrArg Subtype.val same))
  let answers := fun table : image → Fin bound ↦
    extendTable (R := fun _ ↦ Fin bound) image table
  have original := randomOracle_finite_cover program cells covered cell distinct
    (fun table key ↦ answers table (locate segment key))
    (by intro table key; exact extendTable_subtype (R := fun _ ↦ Fin bound) image table (cell key))
  have target := randomOracle_finite_cover mapped image mappedCovered id Function.injective_id
    answers (by intro table key; exact extendTable_subtype (R := fun _ ↦ Fin bound) image table key)
  rw [original, target]
  simp only [mapped, RandomOracleRouting.evalWithAnswerFn_route, Function.comp_def]

end ZkcSecurity.FiatShamir.QueryTreeSource
