import Zkc.Source.Mathematical.ClosedAssembly
import Zkc.Source.Mathematical.ResolvedInvocations

/-! Source call edges for the actual stored executable bodies.

The execution table is ordered by dependencies; the source graph retains its
canonical preorder. These proofs connect actual intrinsic invocation sites to
the authored call uses and exact closed keys across that permutation.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical

namespace ClosedInstances

def Node.callEdges {source key} (node : Node source key) : List (CallSite × Key) :=
  node.sites.zip (targets node.children)

theorem Node.callEdges_unique {source key} (first second : Node source key) :
    first.callEdges = second.callEdges := by
  obtain ⟨sites, children⟩ := first.determined second
  simp only [Node.callEdges, sites, children]

theorem site_edge {source key parent sites} (children : Values (Call (source := source) (key := key) parent) sites)
    {site : CallSite} (member : site ∈ sites) :
    ∃ edge : Call parent site, (site, edge.target) ∈ sites.zip (targets children) := by
  induction children with
  | nil => cases member
  | cons first rest ih =>
      simp only [List.mem_cons] at member
      rcases member with same | member
      · subst site
        exact ⟨first, by simp [targets]⟩
      · obtain ⟨edge, found⟩ := ih member
        exact ⟨edge, by simp only [targets, List.zip_cons_cons, List.mem_cons]; exact Or.inr found⟩

theorem selected_node {source} {nodes : List (Packed source)} {index : Nat} {key : Key}
    (selected : (keys nodes)[index]? = some key) :
    ∃ node : Node source key, nodes[index]? = some ⟨key, node⟩ := by
  simp only [keys, List.getElem?_map] at selected
  cases lookup : nodes[index]? with
  | none => simp [lookup] at selected
  | some packed =>
      have same : packed.1 = key := by simpa [lookup] using selected
      cases packed with
      | mk actual node =>
          simp only at same
          subst actual
          exact ⟨node, rfl⟩

def edgeReferencesAt {source keys} : {nodes : List (Packed source)} →
    Values (fun node => Values (Reference keys) (targets node.2.children)) nodes →
    {index : Nat} → {node : Packed source} → nodes[index]? = some node →
    Values (Reference keys) (targets node.2.children)
  | _, .nil, _, _, selected => by simp at selected
  | _, .cons first _, 0, _, selected => by
      have same := Option.some.inj selected
      cases same
      exact first
  | _, .cons _ rest, _ + 1, _, selected => edgeReferencesAt rest selected

/-- The stored edge reference uses the unique graph ID of its complete key. -/
theorem Graph.edge_reference {source} (graph : Graph source) {index : Nat} {node : Packed source}
    (selected : graph.nodes[index]? = some node)
    (edge : Fin (targets node.2.children).length) {position : Nat}
    (child : (keys graph.nodes)[position]? = some (targets node.2.children)[edge.val]) :
    (referenceAt (edgeReferencesAt graph.edges selected) edge).val = position := by
  let reference := referenceAt (edgeReferencesAt graph.edges selected) edge
  exact (List.getElem?_inj reference.bound graph.unique).mp (reference.property.trans child.symm)

end ClosedInstances

namespace ClosedAssembly
open ClosedInstances (Key Node)
variable {Payload : ManifestAdmission.Category → Type} {contracts : RegistryAdmission.Contracts Payload}
  {source : Raw.Subject} (header : DeclarationAdmission.Header contracts source)

def invocationEdges (records : List (Record header)) (calls : List Protocol.Invocation) :=
  calls.map fun call => (call.site, call.capabilities, (recordKeys header records)[call.callee]?)

def sourceEdge (edge : ClosedInstances.CallSite × Key) :=
  (edge.1.site, edge.1.use.capabilities.map (·.index), some edge.2)

private theorem resolved_edges {vocabulary} {resolver : ProtocolResolution.Resolver vocabulary}
    {key} (parent : ClosedInstances.Instance source key) (records : List (Record header))
    (calls : List (ProtocolResolution.Invocation resolver)) {sites}
    (children : Values (ClosedInstances.Call parent) sites)
    (same : calls.map ProtocolResolution.Invocation.authored = sites)
    (valid : ∀ call ∈ calls, CallValid header parent records call.source call.callee) :
    invocationEdges header records (calls.map ProtocolResolution.Invocation.lower) =
      (sites.zip (ClosedInstances.targets children)).map sourceEdge := by
  subst sites
  induction calls with
  | nil => cases children; rfl
  | cons first rest ih =>
      cases children with
      | cons edge tail =>
          obtain ⟨otherSite, other, sameUse, selected⟩ := valid first (by simp)
          have targetSame := other.target_eq_of_use edge sameUse
          have lookup := selected.trans (congrArg some targetSame)
          have tailValid : ∀ call ∈ rest, CallValid header parent records call.source call.callee :=
            fun call member => valid call (by simp [member])
          simp only [invocationEdges, List.map_cons, ProtocolResolution.Invocation.lower,
            ClosedInstances.targets, List.zip_cons_cons, sourceEdge, ProtocolResolution.Invocation.authored]
          congr 1
          · exact congrArg (fun key => (first.site, first.source.capabilities.map (·.index), key)) lookup
          · exact ih tailValid tail

/-- Equality of complete ordered edge lists preserves multiplicity, including
identical call uses written at different sites. -/
theorem Prepared.invocation_edges {records key node} (prepared : Prepared header records key node) :
    invocationEdges header records prepared.bound.body.checked.program.invocations =
      node.callEdges.map sourceEdge := by
  rw [prepared.bound.body.invocations]
  have coverage := prepared.bound.body.resolved.invocations_cover
  rw [prepared.bound.body.erasure] at coverage
  exact resolved_edges header node.checked records _ node.children (coverage.functional node.coverage)
    (fun call _ => call.valid)

theorem Prepared.invocation_sites {records key node} (prepared : Prepared header records key node) :
    prepared.bound.body.checked.program.invocations.map (·.site) = node.sites.map (·.site) := by
  rw [prepared.bound.body.invocations, List.map_map]
  have coverage := prepared.bound.body.resolved.invocations_cover
  rw [prepared.bound.body.erasure] at coverage
  rw [← coverage.functional node.coverage, List.map_map]
  rfl

theorem Prepared.call_sites_unique {records key node} (prepared : Prepared header records key node) :
    (node.sites.map (·.site)).Nodup := by
  rw [← prepared.invocation_sites header]
  exact prepared.bound.body.checked.program.invocation_sites_unique

private theorem invocationEdges_append (records suffix : List (Record header)) (calls : List Protocol.Invocation)
    (bounded : ∀ call ∈ calls, call.callee < records.length) :
    invocationEdges header (records ++ suffix) calls = invocationEdges header records calls := by
  apply List.map_congr_left
  intro call member
  simp [recordKeys, List.getElem?_append, bounded call member]

theorem Prepared.invocation_provenance {records key node} (prepared : Prepared header records key node)
    {call : Protocol.Invocation} (member : call ∈ prepared.bound.body.checked.program.invocations) :
    ∃ site target, site.site = call.site ∧ site.use.capabilities.map (·.index) = call.capabilities ∧
      (site, target) ∈ node.callEdges ∧ (recordKeys header records)[call.callee]? = some target := by
  rw [prepared.bound.body.invocations] at member
  obtain ⟨resolved, member, same⟩ := List.mem_map.mp member
  have coverage := prepared.bound.body.resolved.invocations_cover
  rw [prepared.bound.body.erasure] at coverage
  have sites := coverage.functional node.coverage
  have inSites : resolved.authored ∈ node.sites := by
    rw [← sites]
    exact List.mem_map.mpr ⟨resolved, member, rfl⟩
  obtain ⟨edge, edgeMember⟩ := ClosedInstances.site_edge node.children inSites
  obtain ⟨otherSite, other, use, selected⟩ := resolved.valid
  have sameTarget := other.target_eq_of_use edge use
  subst call
  exact ⟨resolved.authored, edge.target, rfl, rfl, edgeMember, selected.trans (congrArg some sameTarget)⟩

def History.invocationTable : {records : List (Record header)} → History header records → List (List Protocol.Invocation)
  | _, .nil => []
  | _, .snoc previous prepared => previous.invocationTable ++ [prepared.bound.body.checked.program.invocations]

theorem History.invocationTable_definitions {records} (history : History header records) :
    history.definitions.invocationTable = history.invocationTable := by
  induction history with
  | nil => rfl
  | snoc previous prepared ih =>
      simp only [History.definitions, History.invocationTable]
      erw [Protocol.Definitions.invocationTable_reindex]
      simp only [Protocol.Definitions.invocationTable, ih]
      rfl

theorem History.invocationTable_length {records} (history : History header records) :
    history.invocationTable.length = records.length := by
  induction history with
  | nil => rfl
  | snoc previous prepared ih => simp [History.invocationTable, ih]

/-- Recover the actual source-bound body and its earlier scope at any stored
position. The record is derived from this body, including its typed target. -/
theorem History.record_body {records} (history : History header records) {index : Nat} {record : Record header}
    (selected : records[index]? = some record) :
    ∃ node : Node source record.key, ∃ earlier : List (Record header),
    ∃ prepared : Prepared header earlier record.key node,
      record = prepared.record ∧ earlier.length = index ∧
      (∃ later, records = earlier ++ [record] ++ later) ∧
      history.invocationTable[index]? = some prepared.bound.body.checked.program.invocations := by
  induction history with
  | nil => simp at selected
  | @snoc records key node previous prepared ih =>
      by_cases earlier : index < records.length
      · have prefixSelected : records[index]? = some record := by
          simpa [List.getElem?_append, earlier] using selected
        obtain ⟨parent, before, body, same, position, ⟨after, partition⟩, calls⟩ := ih prefixSelected
        refine ⟨parent, before, body, same, position, ⟨after ++ [prepared.record], ?_⟩, ?_⟩
        · simpa only [List.append_assoc] using congrArg (fun rest => rest ++ [prepared.record]) partition
        · simpa [History.invocationTable, List.getElem?_append,
            History.invocationTable_length, earlier] using calls
      · have bound := (List.getElem?_eq_some_iff.mp selected).1
        simp only [List.length_append, List.length_singleton] at bound
        have last : index = records.length := by omega
        subst index
        have same : prepared.record = record := by simpa using selected
        subst record
        refine ⟨node, records, prepared, rfl, rfl, ⟨[], by simp⟩, ?_⟩
        simp only [History.invocationTable, ← previous.invocationTable_length header,
          List.getElem?_concat_length]
        rfl

theorem History.invocation_provenance {records} (history : History header records)
    {caller calls} (selected : history.invocationTable[caller]? = some calls)
    {call : Protocol.Invocation} (member : call ∈ calls) :
    call.callee < caller ∧ ∃ key, ∃ node : Node source key, ∃ site target,
      (recordKeys header records)[caller]? = some key ∧
      site.site = call.site ∧ site.use.capabilities.map (·.index) = call.capabilities ∧
      (site, target) ∈ node.callEdges ∧ (recordKeys header records)[call.callee]? = some target := by
  induction history with
  | nil => simp [History.invocationTable] at selected
  | @snoc records key node previous prepared ih =>
      by_cases earlier : caller < records.length
      · have prefixSelected : previous.invocationTable[caller]? = some calls := by
          simpa [History.invocationTable, List.getElem?_append,
            History.invocationTable_length, earlier] using selected
        obtain ⟨bound, parentKey, parent, site, target, parentSelected, sameSite, caps, edge, targetSelected⟩ := ih prefixSelected
        refine ⟨bound, parentKey, parent, site, target, ?_, sameSite, caps, edge, ?_⟩
        · simpa [recordKeys, List.getElem?_append, earlier] using parentSelected
        · have targetEarlier : call.callee < records.length := by omega
          simpa [recordKeys, List.getElem?_append, targetEarlier] using targetSelected
      · have bound := (List.getElem?_eq_some_iff.mp selected).1
        rw [History.invocationTable_length] at bound
        simp only [List.length_append, List.length_singleton] at bound
        have last : caller = records.length := by omega
        subst caller
        have same : prepared.bound.body.checked.program.invocations = calls := by
          simpa [History.invocationTable, List.getElem?_append,
            History.invocationTable_length] using selected
        rw [← same] at member
        have scopeBound := prepared.bound.body.checked.program.invocations_scope call member
        have calleeEarlier : call.callee < records.length := by
          simpa only [scope, recordTargets, List.length_map] using scopeBound
        obtain ⟨site, target, sameSite, caps, edge, targetSelected⟩ := prepared.invocation_provenance header member
        refine ⟨calleeEarlier, key, node, site, target, ?_, sameSite, caps, edge, ?_⟩
        · simp [recordKeys, Prepared.record]
        · simpa [recordKeys, List.getElem?_append, calleeEarlier] using targetSelected

theorem History.invocation_edges {records} (history : History header records)
    {caller : Nat} {calls} (selected : history.invocationTable[caller]? = some calls) :
    ∃ key, ∃ node : Node source key, (recordKeys header records)[caller]? = some key ∧
      invocationEdges header records calls = node.callEdges.map sourceEdge := by
  induction history with
  | nil => simp [History.invocationTable] at selected
  | @snoc records key node previous prepared ih =>
      by_cases earlier : caller < records.length
      · have prefixSelected : previous.invocationTable[caller]? = some calls := by
          simpa [History.invocationTable, List.getElem?_append,
            History.invocationTable_length, earlier] using selected
        obtain ⟨parentKey, parent, parentSelected, edges⟩ := ih prefixSelected
        refine ⟨parentKey, parent, ?_, ?_⟩
        · simpa [recordKeys, List.getElem?_append, earlier] using parentSelected
        · rw [invocationEdges_append header records _ calls]
          · exact edges
          · intro call member
            exact Nat.lt_trans (previous.invocation_provenance header prefixSelected member).1 earlier
      · have bound := (List.getElem?_eq_some_iff.mp selected).1
        rw [History.invocationTable_length] at bound
        simp only [List.length_append, List.length_singleton] at bound
        have last : caller = records.length := by omega
        subst caller
        have same : prepared.bound.body.checked.program.invocations = calls := by
          simpa [History.invocationTable, List.getElem?_append,
            History.invocationTable_length] using selected
        subst calls
        refine ⟨key, node, by simp [recordKeys, Prepared.record], ?_⟩
        rw [invocationEdges_append header records]
        · exact prepared.invocation_edges header
        · intro call member
          simpa only [scope, recordTargets, List.length_map] using
            prepared.bound.body.checked.program.invocations_scope call member

/-- The full stored invocation list, including order and multiplicity,
corresponds to the full source-edge list at the mapped source ID. -/
theorem Result.call_edges (result : Result header)
    (caller : Fin (recordKeys header result.table.records).length) :
    ∃ key, ∃ node : Node source key,
      result.graph.nodes[(Positions.toSource header result.positions caller).val]? = some ⟨key, node⟩ ∧
      (recordKeys header result.table.records)[caller.val]? = some key ∧
      (result.closed.definitions.invocationTable[caller.val]?).map (invocationEdges header result.table.records) =
        some (node.callEdges.map sourceEdge) := by
  have bound : caller.val < result.table.history.invocationTable.length := by
    rw [History.invocationTable_length]
    simpa only [recordKeys, List.length_map] using caller.isLt
  let calls := result.table.history.invocationTable[caller.val]
  have selected : result.table.history.invocationTable[caller.val]? = some calls :=
    List.getElem?_eq_getElem bound
  obtain ⟨key, storedNode, storedSelected, edges⟩ := result.table.history.invocation_edges header selected
  have parentSource := (ClosedInstances.indexMap_key result.positions.backward caller).trans storedSelected
  obtain ⟨node, sourceSelected⟩ := ClosedInstances.selected_node parentSource
  refine ⟨key, node, sourceSelected, storedSelected, ?_⟩
  change (result.table.history.definitions.invocationTable[caller.val]?).map _ = _
  rw [History.invocationTable_definitions, selected, Option.map_some, edges, storedNode.callEdges_unique node]

/-- Each actual executable call selects an earlier stored definition and the
same authored call edge at the mapped source-graph ID. Equality is of complete
closed keys, including the static, role and root tuples. -/
theorem Result.call_provenance (result : Result header)
    (caller : Fin (recordKeys header result.table.records).length)
    {calls call} (selected : result.closed.definitions.invocationTable[caller.val]? = some calls)
    (member : call ∈ calls) :
    call.callee < caller.val ∧
    ∃ callee : Fin (recordKeys header result.table.records).length, callee.val = call.callee ∧
    ∃ key, ∃ node : Node source key, ∃ site target,
      (recordKeys header result.table.records)[caller.val]? = some key ∧
      (recordKeys header result.table.records)[call.callee]? = some target ∧
      result.graph.nodes[(Positions.toSource header result.positions caller).val]? = some ⟨key, node⟩ ∧
      (ClosedInstances.keys result.graph.nodes)[(Positions.toSource header result.positions callee).val]? = some target ∧
      site.site = call.site ∧ site.use.capabilities.map (·.index) = call.capabilities ∧
      (site, target) ∈ node.callEdges := by
  change result.table.history.definitions.invocationTable[caller.val]? = some calls at selected
  rw [History.invocationTable_definitions] at selected
  obtain ⟨earlier, key, storedNode, site, target, parentSelected, sameSite, caps, edge, targetSelected⟩ :=
    result.table.history.invocation_provenance header selected member
  let callee : Fin (recordKeys header result.table.records).length :=
    ⟨call.callee, (List.getElem?_eq_some_iff.mp targetSelected).1⟩
  have parentSource := (ClosedInstances.indexMap_key result.positions.backward caller).trans parentSelected
  have targetSource := (ClosedInstances.indexMap_key result.positions.backward callee).trans targetSelected
  obtain ⟨node, sourceSelected⟩ := ClosedInstances.selected_node parentSource
  refine ⟨earlier, callee, rfl, key, node, site, target, parentSelected, targetSelected,
    sourceSelected, targetSource, sameSite, caps, ?_⟩
  rw [← storedNode.callEdges_unique node]
  exact edge

theorem Result.entry_provenance (result : Result header) :
    (Positions.toSource header result.positions ⟨result.entryPosition.val, result.entryPosition.bound⟩).val =
      result.graph.entry.val := by
  have same := (ClosedInstances.indexMap_key result.positions.backward
    ⟨result.entryPosition.val, result.entryPosition.bound⟩).trans result.entryPosition.property
  exact (List.getElem?_inj (ClosedInstances.indexMap result.positions.backward
    ⟨result.entryPosition.val, result.entryPosition.bound⟩).isLt result.graph.unique).mp
    (same.trans result.graph.entry.property.symm)

theorem Result.entry_roots (result : Result header) :
    result.entry.bindings.roots = (ClosedInstances.entryKey source).roots :=
  (result.entry.bindings.roots_eq_indices header.rootTable).trans result.entry.bindingIndices

end ClosedAssembly
end Zkc.Source.Mathematical
