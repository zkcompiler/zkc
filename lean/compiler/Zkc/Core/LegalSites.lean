module

public import Zkc.Core.Legal

public section

/-! The specification of the uniqueness test of sites.

`unusedSites` sets a bit per site in one numeral. `unusedSites_spec` says what its success
means: the sites are pairwise different, below the site limit, and not among the sites
seen before. `ProtocolDefinition.sites_nodup` is the consequence for a well-formed
definition: its sites are pairwise different.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- The bits of the seen sites after one more site. -/
theorem testBit_mark (seen site other : Nat) :
    (seen ||| (1 <<< site)).testBit other = (seen.testBit other || decide (site = other)) := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

/-- When the test accepts, the sites are pairwise different, each is below the limit, and
none was seen before. -/
theorem unusedSites_spec :
    ∀ (sites : List Nat) (seen : Nat), unusedSites seen sites = none →
      sites.Nodup ∧ ∀ site ∈ sites, seen.testBit site = false ∧ site < siteLimit
  | [], _, _ => ⟨List.nodup_nil, fun _ member => nomatch member⟩
  | site :: rest, seen, clean => by
      unfold unusedSites at clean
      cases below : Nat.blt site siteLimit with
      | false =>
          rw [below] at clean
          cases clean
      | true =>
          rw [below] at clean
          cases used : seen.testBit site with
          | true =>
              rw [used] at clean
              cases clean
          | false =>
              rw [used] at clean
              obtain ⟨nodup, fresh⟩ := unusedSites_spec rest _ clean
              refine ⟨List.nodup_cons.mpr ⟨?_, nodup⟩, ?_⟩
              · intro member
                have marked := (fresh site member).1
                rw [testBit_mark] at marked
                simp at marked
              · intro other member
                rcases List.mem_cons.mp member with rfl | later
                · exact ⟨used, Nat.blt_eq.mp below⟩
                · have marked := (fresh other later).1
                  rw [testBit_mark, Bool.or_eq_false_iff] at marked
                  exact ⟨marked.1, (fresh other later).2⟩

/-- Sites that pass the uniqueness test are pairwise different. -/
theorem sitesViolation_nodup {sites : List Nat} (clean : sitesViolation sites = none) :
    sites.Nodup :=
  (unusedSites_spec sites 0 clean).1

/-- The sites of a well-formed definition are pairwise different. -/
theorem ProtocolDefinition.sites_nodup {operations : List OperationSignature}
    {functions : List FunctionHeader} {protocols : List ProtocolHeader} {typeTable : TypeTable}
    {header : ProtocolHeader}
    {definition : ProtocolDefinition operations functions protocols header}
    (wellFormed : definition.violation typeTable = none) :
    ∃ sites, definition.sites typeTable = .ok sites ∧ sites.Nodup := by
  have body := (earlierViolation_none wellFormed).2
  split at body
  · cases body
  · rename_i sites collected
    exact ⟨sites, collected, sitesViolation_nodup body⟩

end Zkc.Core
