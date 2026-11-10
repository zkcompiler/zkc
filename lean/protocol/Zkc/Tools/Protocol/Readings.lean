module

public import Zkc.Tools.Protocol.Construction
public import Zkc.Protocol.Logic.WeakestPrecondition

/-! Proposition-valued readings with the common constructor.

The charged and cost readings, their primitive call and stop rules and their adequacy theorems
are ordinary declarations of `Zkc.Protocol.Logic.WeakestPrecondition`. This module adds their
node equations to the constructor's structural normalization. After `construct_region`, what
remains of a primitive call is the mathematical obligation of its absorption: for a receive, every
recovered message; for a query under the exact judgment, every decoded reply; under a bounded
judgment, a probability bound for the replies that escape. An author registers the concrete
interface (`attribute [local construction_simp] absorb`) so that its absorption is exposed. -/

public section
open ZkcSecurity.Obligations ZkcSecurity.Obligations.WeakestPrecondition

-- A query node is normalized only at the two judgments the endpoints use, so the two forms never
-- compete; under another judgment it remains `Absorption.ChargedNode`.
attribute [construction_simp] chargedNode_receive chargedNode_send chargedNode_refuse
  chargedNode_query_exact chargedNode_query_bounded costNode

-- A residual entailment between explicit propositions reads as an implication; the author
-- names its quantified states and hypotheses. The constructor applies this set only to remaining
-- goals that mention `ProtocolProof.Truth`, so the general lemmas below never rewrite an
-- obligation of another reading.
attribute [construction_residual] ProtocolProof.Truth.mk_rel_mk ProtocolProof.Truth.mk_rel_mk_fun
  ProtocolProof.Truth.mk_rel_mk_fun₂ ProtocolProof.Truth.holds_ite ProtocolProof.Truth.holds_dite
  ite_apply dite_apply implies_true true_implies imp_self
