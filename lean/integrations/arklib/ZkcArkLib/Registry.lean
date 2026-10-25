module

public import ZkcSecurity.Registry

@[expose] public section

/-! Registry schemas supplied by optional ArkLib adapters and subjects. -/
namespace ZkcArkLib.Registry
open Lean (Name)
open ZkcSecurity.Registry

def entries : List Entry := [
  ⟨"family.upstream-realization", .familyProperty, some `ZkcSecurity.FiatShamir.Upstream.Realizes,
    "A participant process realizes an upstream process-form residual operation by \
    operation."⟩,
  ⟨"family.sumcheck-doomed", .familyProperty, some `ZkcSecurity.Examples.SumcheckFiatShamir.Doomed,
    "The doomed residuals of the Sumcheck certificate: phases satisfying the invariant."⟩,
  ⟨"family.sumcheck-doomed-any", .familyProperty,
    some `ZkcSecurity.Examples.SumcheckFiatShamir.DoomedAny,
    "The doomed residuals of the Sumcheck certificate for every table and claim."⟩,
  ⟨"event.sumcheck-false-statement", .event,
    some `ZkcSecurity.Examples.Subjects.Sumcheck.Contract.falseStatement,
    "A Sumcheck policy statement whose claim the retained formula does not confirm as the total of \
    its vector."⟩,
  ⟨"event.gkr-layer-false", .event, some `ZkcSecurity.Examples.GkrFiatShamir.LayerFalse,
    "A false claim about a GKR layer at its point."⟩,
  ⟨"event.gkr-outputs-differ", .event, some `ZkcSecurity.Examples.GkrFiatShamir.OutputsDiffer,
    "The claimed outputs and the circuit's outputs differ at some Boolean completion."⟩,
  ⟨"event.sumcheck-false-claim", .event, some `ZkcSecurity.Examples.SumcheckFiatShamir.FalseClaim,
    "A Sumcheck claim is false at the point."⟩,
  ⟨"event.causal-table-terminal", .event,
    some `ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal.tableTerminal,
    "The terminal check of the causal multilinear Sumcheck against a table."⟩,
  ⟨"wellformed.committed-fri-admissible", .wellFormedness,
    some `ZkcSecurity.Examples.CommittedFri.Admissible,
    "The admissible committed shapes: words of bounded size."⟩,
  ⟨"wellformed.committed-fri-matches", .wellFormedness,
    some `ZkcSecurity.Examples.CommittedFri.Matches,
    "The committed tables from a handle on are the layers' words, in order."⟩,
  ⟨"wellformed.gkr-statement", .wellFormedness,
    some `ZkcSecurity.Examples.CompiledGkrFiatShamir.WellFormed,
    "A GKR statement whose raw public inputs decode to the circuit the plain verifier reads."⟩,
  ⟨"wellformed.gkr-line-coefficients", .wellFormedness,
    some `ZkcSecurity.Examples.GkrFiatShamir.CoefficientsFrom,
    "The remaining coefficients of a line polynomial with a given constant term."⟩,
  ⟨"wellformed.causal-msb-chronology", .wellFormedness,
    some `ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal.MSBChronology,
    "Chronological challenges are in the table's most-significant-first coordinate order."⟩,
  ⟨"hypothesis.fri-folding-proximity", .libraryHypothesis,
    some `ZkcSecurity.ArkLib.Fri.FoldingProximity,
    "Mutual correlated agreement of the line generator on every folded Reed-Solomon code at \
    the radius; proved at the unique-decoding radius, and for folding up to the cube-root \
    radius, and open beyond."⟩,
  ⟨"family.fri-round-by-round", .familyProperty, some `ZkcSecurity.ArkLib.Fri.RoundByRound,
    "The round-by-round soundness certificate of the FRI verifier at the ideal \
    interpretation, with errors per folding round and for the query block."⟩,
  ⟨"family.fri-step", .familyProperty, some `ZkcSecurity.ArkLib.Fri.Step,
    "The local obligations of a doomed set of the FRI verifier."⟩,
  ⟨"family.fri-folding-escapes", .familyProperty, some `ZkcSecurity.ArkLib.Fri.FoldingEscapes,
    "At every folding round and for every committed word, a fresh challenge escapes with \
    probability at most the round's error."⟩,
  ⟨"family.fri-doomed", .familyProperty, some `ZkcSecurity.ArkLib.Fri.Doomed,
    "The doomed residuals of the FRI certificate."⟩,
  ⟨"family.sumcheck-rejecting", .familyProperty,
    some `ZkcSecurity.Examples.Subjects.Sumcheck.Rejecting,
    "The residuals of the Sumcheck rounds followed by a terminal that never accepts, at a point \
    of the round count's length."⟩,
  ⟨"family.sumcheck-doomed-all", .familyProperty,
    some `ZkcSecurity.Examples.Subjects.Sumcheck.DoomedAll,
    "The doomed set of the contract-connected Sumcheck certificate: the residuals of every table \
    and claim, the refused verifier and the rejecting runs."⟩,
  ⟨"event.fri-far", .event, some `ZkcSecurity.ArkLib.Fri.Far,
    "A word at relative distance at least the radius from every codeword."⟩,
  ⟨"event.gkr-false-claim", .event, some `ZkcSecurity.ArkLib.Gkr.FalseClaim,
    "A GKR round claim is false at the challenge prefix."⟩,
  ⟨"wellformed.fri-compatible-roots", .wellFormedness, some `ZkcSecurity.ArkLib.Fri.Compatible,
    "The roots used along the folds are compatible."⟩,
  ⟨"wellformed.fri-honest-layers", .wellFormedness, some `ZkcSecurity.ArkLib.Fri.Honest,
    "Each committed word after the first is ArkLib's fold of the previous word."⟩
]

def table : List (String × String × Option Name × String) :=
  entries.map fun entry => (entry.identifier, entry.category.label, entry.schema, entry.statement)

def audited : List (String × Option Name × Bool) :=
  entries.map fun entry => (entry.identifier, entry.schema, entry.category.proposition)

def endpoints : List (String × String × String × Name) := []

/-- Combined registry context for declaration reports. The owning entry lists
remain disjoint; reports need generic premise schemas and endpoint heads while
examining optional theorems. Readers reject incompatible duplicate metadata. -/
def reportTable : List (String × String × Option Name × String) :=
  ZkcSecurity.Registry.table ++ table

def reportEndpoints : List (String × String × String × Name) :=
  ZkcSecurity.Registry.endpoints ++ endpoints

end ZkcArkLib.Registry
