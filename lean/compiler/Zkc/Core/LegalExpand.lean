module

public import Zkc.Core.Expand

public section

/-! Expansion refuses a program only for one of its two limits.

`expandRegion` has three refusals. Two are limits: an expanded definition has at most
`siteLimit` sites, and applications are nested at most `applicationLimit` deep. The third,
`specificationOnly`, says that an applied protocol has no expansion. Expansion is defined
for deployed protocols, and a deployed protocol applies no specification-only one by
typing (`permitted`), so the third refusal cannot occur: the table has an expansion for
every deployed protocol (`ExpansionsDeployed`).

Expansion decides no residual condition again: it reads no role number and no site
number of the program.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- A refusal for a limit of expansion. -/
def ExpandRefusal.Limit (refusal : ExpandRefusal) : Prop :=
  refusal = .siteLimit ∨ refusal = .applicationDepth

section Expand

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader}

/-- The table has an expansion for every deployed protocol. -/
def ExpansionsDeployed (table : ExpandedTable operations functions protocols) : Prop :=
  ∀ {header : ProtocolHeader} (callee : Var protocols header), header.specificationOnly = false →
    ∃ expanded, table.get callee = some expanded

variable {table : ExpandedTable operations functions protocols}

mutual
  /-- A region of a deployed protocol is refused only for a limit. -/
  theorem expandRegion_limit (deployed : ExpansionsDeployed table) (identity : Nat)
      {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions protocols true) Γ out)
        (depth : Depth Γ) (start : Nat) (refusal : ExpandRefusal),
        expandRegion table identity region depth start = .error refusal → refusal.Limit
    | .ret values, _, _, _, refuses => by
        simp only [expandRegion] at refuses
        cases refuses
    | .stop reason, _, _, _, refuses => by
        simp only [expandRegion] at refuses
        cases refuses
    | .bind (mid := mid) body rest, depth, start, refusal, refuses => by
        unfold expandRegion at refuses
        split at refuses
        · rename_i inner failed
          cases refuses
          exact expandRegion_limit deployed identity body _ _ _ failed
        · split at refuses
          · rename_i inner failed
            cases refuses
            exact expandRegion_limit deployed identity rest _ _ _ failed
          · cases refuses
    | .letOp (.at role op bodies) arguments nested rest, depth, start, refusal, refuses => by
        cases nested
        unfold expandRegion at refuses
        split at refuses
        · rename_i inner failed
          cases refuses
          exact expandRegion_limit deployed identity rest _ _ _ failed
        · cases refuses
    | .letOp (.exchange sender receiver site type) arguments nested rest, depth, start, refusal,
        refuses => by
        cases nested
        unfold expandRegion at refuses
        split at refuses
        · rename_i inner failed
          cases refuses
          exact expandRegion_limit deployed identity rest _ _ _ failed
        · cases refuses
    | .letOp (.draw owner receivers site law populated) arguments nested rest, depth, start, refusal,
        refuses => by
        cases nested
        unfold expandRegion at refuses
        split at refuses
        · rename_i inner failed
          cases refuses
          exact expandRegion_limit deployed identity rest _ _ _ failed
        · cases refuses
    | .letOp (.sample owner site law populated) arguments nested rest, depth, start, refusal, refuses => by
        cases nested
        unfold expandRegion at refuses
        split at refuses
        · rename_i inner failed
          cases refuses
          exact expandRegion_limit deployed identity rest _ _ _ failed
        · cases refuses
    | .letOp (.repeat participants count carried collected captures covered) arguments
        bodies rest, depth, start,
        refusal, refuses => by
        unfold expandRegion at refuses
        split at refuses
        · rename_i inner failed
          cases refuses
          exact expandRegions_limit deployed identity bodies _ _ failed
        · split at refuses
          · rename_i inner failed
            cases refuses
            exact expandRegion_limit deployed identity rest _ _ _ failed
          · cases refuses
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest, depth,
        start, refusal, refuses => by
        unfold expandRegion at refuses
        split at refuses
        · rename_i inner failed
          cases refuses
          exact expandRegions_limit deployed identity bodies _ _ failed
        · split at refuses
          · rename_i inner failed
            cases refuses
            exact expandRegion_limit deployed identity rest _ _ _ failed
          · cases refuses
    | .letOp (.apply (header := header) callee roleMap site permitted) arguments nested rest, depth,
        start, refusal, refuses => by
        cases nested
        unfold expandRegion at refuses
        split at refuses
        · rename_i missing
          have notSpecification : header.specificationOnly = false := by
            simpa only [Bool.true_and] using permitted
          obtain ⟨expanded, found⟩ := deployed callee notSpecification
          rw [found] at missing
          cases missing
        · split at refuses
          · cases refuses
            exact Or.inl rfl
          · split at refuses
            · cases refuses
              exact Or.inr rfl
            · split at refuses
              · rename_i inner failed
                cases refuses
                exact expandRegion_limit deployed identity rest _ _ _ failed
              · cases refuses

  /-- Closed regions of a deployed protocol are refused only for a limit. -/
  theorem expandRegions_limit (deployed : ExpansionsDeployed table) (identity : Nat)
      {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions protocols true) signatures)
        (start : Nat) (refusal : ExpandRefusal),
        expandRegions table identity regions start = .error refusal → refusal.Limit
    | .nil, _, _, refuses => by
        simp only [expandRegions] at refuses
        cases refuses
    | .cons body tail, start, refusal, refuses => by
        unfold expandRegions at refuses
        split at refuses
        · rename_i inner failed
          cases refuses
          exact expandRegion_limit deployed identity body _ _ _ failed
        · split at refuses
          · rename_i inner failed
            cases refuses
            exact expandRegions_limit deployed identity tail _ _ failed
          · cases refuses
end

/-- A protocol is refused only for a limit. -/
theorem expandProtocol_limit (deployed : ExpansionsDeployed table) (identity : Nat) :
    ∀ (header : ProtocolHeader) (definition : ProtocolDefinition operations functions protocols header)
      (refusal : ExpandRefusal),
      expandProtocol table identity header definition = .error refusal → refusal.Limit
  | ⟨_, _, _, _, true⟩, _, _, refuses => by
      simp only [expandProtocol] at refuses
      cases refuses
  | ⟨_, inputs, _, _, false⟩, definition, refusal, refuses => by
      simp only [expandProtocol] at refuses
      split at refuses
      · rename_i inner failed
        cases refuses
        exact expandRegion_limit deployed identity definition.body _ 0 _ failed
      · cases refuses

/-- A deployed protocol that is not refused has an expansion. -/
theorem expandProtocol_deployed (identity : Nat) :
    ∀ (header : ProtocolHeader) (definition : ProtocolDefinition operations functions protocols header)
      (entry : Option (Expanded operations functions header)),
      expandProtocol table identity header definition = .ok entry →
        header.specificationOnly = false → ∃ expanded, entry = some expanded
  | ⟨_, _, _, _, true⟩, _, _, _, deployed => nomatch deployed
  | ⟨_, inputs, _, _, false⟩, definition, entry, expands, _ => by
      simp only [expandProtocol] at expands
      split at expands
      · cases expands
      · cases expands
        exact ⟨_, rfl⟩

end Expand

section Programs

variable {typeTable : TypeTable} {operations : List OperationSignature} {functions : List FunctionHeader}

/-- What expansion returns for a program: an expansion for every deployed protocol, or a
refusal for a limit. -/
def ExpansionResult {protocols : List ProtocolHeader} :
    Except ExpandRefusal (ExpandedTable operations functions protocols) → Prop
  | .ok table => ExpansionsDeployed table
  | .error refusal => refusal.Limit

/-- The expansions of a program: one for every deployed protocol; and a program is
refused only for a limit. -/
theorem expandProtocols_result (identities : Identities) :
    ∀ {protocols : List ProtocolHeader}
      (program : Protocols typeTable operations functions protocols),
      ExpansionResult (expandProtocols identities program)
  | _, .nil => fun callee => callee.elimNil
  | _, .snoc (protocols := earlierHeaders) (header := header) earlier definition _ => by
      have earlierResult := expandProtocols_result identities earlier
      unfold expandProtocols
      split
      · rename_i refusal failed
        rw [failed] at earlierResult
        exact earlierResult
      · rename_i table expands
        rw [expands] at earlierResult
        have deployedEarlier : ExpansionsDeployed table := earlierResult
        split
        · rename_i refusal failed
          exact expandProtocol_limit deployedEarlier _ header definition refusal failed
        · rename_i entry expandsEntry
          show ExpansionsDeployed (Values.cons entry table)
          intro other callee deployed
          cases callee with
          | here => exact expandProtocol_deployed _ header definition entry expandsEntry deployed
          | there callee => exact deployedEarlier callee deployed

/-- Expansion refuses a program only for one of its two limits: more than `siteLimit`
sites in an expanded definition, or applications nested `applicationLimit` deep. -/
theorem expandProtocols_limit (identities : Identities) {protocols : List ProtocolHeader}
    (program : Protocols typeTable operations functions protocols) (refusal : ExpandRefusal)
    (refuses : expandProtocols identities program = .error refusal) : refusal.Limit := by
  have result := expandProtocols_result identities program
  rw [refuses] at result
  exact result

/-- The expansions of a program that is not refused: every deployed protocol has one. -/
theorem expandProtocols_deployed (identities : Identities) {protocols : List ProtocolHeader}
    (program : Protocols typeTable operations functions protocols)
    (table : ExpandedTable operations functions protocols)
    (expands : expandProtocols identities program = .ok table) : ExpansionsDeployed table := by
  have result := expandProtocols_result identities program
  rw [expands] at result
  intro header callee deployed
  exact result callee deployed

end Programs

end Zkc.Core
