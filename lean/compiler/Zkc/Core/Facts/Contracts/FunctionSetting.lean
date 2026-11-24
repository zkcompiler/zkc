module

public import Zkc.Core.Facts.Contracts.HeaderTyping
public import Zkc.Core.Facts.Contracts.FunctionLaws
public import Zkc.Core.Facts.Knowledge.Functions
public import Zkc.Core.Facts.Contracts.AssertionReader

@[expose] public section

namespace Zkc.Core.BodyAnalysis
open HeaderContracts
variable {V : Vocabulary} {hs : List (FnHeader V)}
variable (M : Model V) (table : FnTable M hs)
private abbrev Sem := localSem M hs table

private theorem positions_denote {as : List (Sem M table).Dyn} : ∀ {ps vs}, atPositions as ps = some vs →
    (argumentExpressions ps).Denote (Runs M table) as vs
  | [], _, found => by cases found; exact .nil
  | p :: ps, _, found => by
    unfold atPositions at found
    split at found <;> cases found
    exact .cons (.arg ‹_›) (positions_denote ‹_›)

/-- The first result of a length operation is available as an operand of a builtin clause. -/
private theorem length_denotes {item size} (free : Ty.isLinear V item = false)
    {vs : List (Sem M table).Dyn} {xs : M.Val (.seq item size)} (valid : M.Valid _ xs)
    (first : vs[0]? = some ⟨.seq item size,xs⟩) :
    (builtinOperand (.apply (lengthOfType (.seq item size)) [0])).Denotes (Runs M table) vs
      ⟨.nat, (xs : List (M.Val item)).length⟩ :=
  .apply (.cons (.arg first) .nil) (FactCheck.localRun_length_intro free xs valid) rfl

private theorem owned_defined {ins outs} (op : OwnedOp V ins outs) (args : HList M.Val ins)
    (ok : args.All M.Valid) {q} (member : q ∈ (localOpFacts hs).requires (LocalOp.print (fns := hs) (.owned op))) :
    ∃ v, (builtinClause q).assertion.Denotes (Runs M table) ((Sem M table).dyns args) v := by
  cases op
  all_goals simp only [localOpFacts, LocalOp.print, OwnedOp.name, ownedContract] at member
  all_goals try contradiction
  case natSub =>
    obtain ⟨a,b,rfl⟩ := HList.two args
    obtain rfl := List.mem_singleton.mp member
    exact ⟨_,negate_denotes M table (less_denotes M table (.arg (by rfl)) (.arg (by rfl)))⟩
  case natDiv | natRem =>
    obtain ⟨a,b,rfl⟩ := HList.two args
    obtain rfl := List.mem_singleton.mp member
    exact ⟨_,less_denotes M table (number_denotes M table 0) (.arg (by rfl))⟩
  case natBelow n =>
    obtain ⟨a,rfl⟩ := HList.one args
    obtain rfl := List.mem_singleton.mp member
    exact ⟨_,less_denotes M table (.arg (by rfl)) (number_denotes M table n)⟩
  case seqSized item n free =>
    obtain ⟨xs,rfl⟩ := HList.one args
    obtain rfl := List.mem_singleton.mp member
    exact ⟨_,equal_denotes M table (length_denotes M table free (HList.all_cons.mp ok).1 rfl) (number_denotes M table n)⟩
  case seqAt item size free =>
    obtain ⟨xs,i,rfl⟩ := HList.two args
    cases size with
    | none =>
      obtain rfl := List.mem_singleton.mp member
      exact ⟨_,less_denotes M table (.arg (by rfl)) (length_denotes M table free (HList.all_cons.mp ok).1 rfl)⟩
    | some n =>
      obtain rfl := List.mem_singleton.mp member
      exact ⟨_,less_denotes M table (.arg (by rfl)) (number_denotes M table n)⟩
  case seqSlice item size result free =>
    obtain ⟨xs,a,b,rfl⟩ := HList.three args
    have len := length_denotes M table free (HList.all_cons.mp ok).1
      (vs := [⟨.seq item size,xs⟩,⟨.nat,a⟩,⟨.nat,b⟩]) rfl
    cases result with
    | none =>
      simp only [List.append_nil,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact ⟨_,negate_denotes M table (less_denotes M table (.arg (by rfl)) (.arg (by rfl)))⟩
      · exact ⟨_,negate_denotes M table (less_denotes M table len (.arg (by rfl)))⟩
    | some n =>
      simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl
      · exact ⟨_,negate_denotes M table (less_denotes M table (.arg (by rfl)) (.arg (by rfl)))⟩
      · exact ⟨_,negate_denotes M table (less_denotes M table len (.arg (by rfl)))⟩
      · cases n with
        | zero => exact ⟨_,negate_denotes M table (less_denotes M table (.arg (by rfl)) (.arg (by rfl)))⟩
        | succ n => exact ⟨_,equal_denotes M table (add_denotes M table (.arg (by rfl)) (number_denotes M table (n+1))) (.arg (by rfl))⟩

variable (contracts : FunctionContracts hs) (definition : Key) (lemmas : List (Lemma V.Ty (LocalRaw V)))
    (notes : Annotations (LocalRaw V)) (bounds : List (Place × Nat))

/-- Function analysis uses local execution, which has no external requests. -/
def FunctionContracts.setting (guarantees : List (HeaderClause V) := []) : Setting (localDialect V hs) (LocalRaw V) where
  cfg := contracts.config definition lemmas guarantees
  sem := localSem M hs table
  notes := notes
  permitted _ _ := True
  R := localReading M
  Run := LocalReturns M table
  Valid := ValidDyn M
  undefined := (· = .undefined)
  domain := localKnowledgeLawful M table contracts.distinct
  F := bounds

private theorem row_defined {key : V.RowKey} {sig} (found : V.row key = some sig)
    (args : HList M.Val sig.ins) (valid : args.All M.Valid) {q}
    (member : q ∈ rowRequires key) :
    ∃ v, (builtinClause q).assertion.Denotes (Runs M table) ((Sem M table).dyns args) v := by
  simp only [rowRequires, found] at member
  cases kind : sig.kind with
  | pure => simp [kind] at member
  | restricted domain =>
    simp [kind] at member
    subst q
    refine ⟨_, Expr.Denotes.apply (positions_denote M table ?_)
      (FactCheck.localRun_domain_intro found kind args valid) rfl⟩
    rw [← (Sem M table).dyns_length args, atPositions_range _ _ (Nat.le_refl _), List.take_length]

theorem FunctionContracts.readerLawful (callees : Callees M table) (guarantees : List (HeaderClause V) := []) :
    (contracts.config definition lemmas guarantees).assertions.Lawful (contracts.setting M table definition lemmas notes bounds guarantees) := by
  change AssertionTypes.Lawful (contracts.setting M table definition lemmas notes bounds guarantees) contracts.assertionTypes
  rw [contracts.assertionTypes_eq]
  exact AssertionTypes.ofReader_lawful (contracts.lawful M table callees _) (localRules hs) localRules_canonical
    (fun _ => rfl) _ (localAssertionBool M table)

def FunctionContracts.empty (V : Vocabulary) : FunctionContracts (V := V) [] :=
  ⟨.nil, List.nodup_nil⟩

private theorem stableAllowed_eq :
    stableAllowed (V := V) = (FunctionContracts.empty V).assertable := by
  funext raw
  unfold stableAllowed FunctionContracts.assertable
  cases h : resolveLocal [] raw with
  | none => rfl
  | some op =>
    obtain ⟨_, _, op⟩ := op
    cases op with
    | call member => cases member
    | row | owned | literal => rfl

/-- The stable expression reader inherits the typed totality of the ordinary operation laws
on the unique empty table. No semantics or domain facts are required from surrounding callees. -/
theorem HeaderContracts.stableReaderLawful :
    (stableTypes V).Lawful ((FunctionContracts.empty V).setting M (headerTable M) ⟨0⟩ [] [] []) := by
  rw [stableTypes, stableAllowed_eq]
  rw [← (FunctionContracts.empty V).assertionTypes_eq]
  exact (FunctionContracts.empty V).readerLawful M (headerTable M) _ [] [] []
    ⟨List.nodup_nil, (fun _ m => nomatch m), (fun _ m => nomatch m), (fun _ m => nomatch m)⟩

/-- Every inferred result exists at its declared type in every function table. -/
theorem HeaderContracts.inferred_denotes {ctx : List V.Ty} {xs : List (localSem M hs table).Dyn}
    (actual : ArgumentsMatch (TypedValue (localSem M hs table) (ValidDyn M)) xs ctx)
    (e : Assertion V) {ty} (ok : (stableTypes V).infer ctx e = some ty) :
    ∃ v, e.Denotes (Runs M table) xs v ∧ TypedValue (localSem M hs table) (ValidDyn M) v ty := by
  obtain ⟨v, den, typed⟩ := AssertionTypes.infer_sound (stableReaderLawful M) actual e ok
  exact ⟨v, den.transport (validRun_transport M (headerTable M) table) (infer_stable _ ok), typed⟩

theorem HeaderContracts.bound_denotes {ctx : List V.Ty} {xs : List (localSem M hs table).Dyn}
    (actual : ArgumentsMatch (TypedValue (localSem M hs table) (ValidDyn M)) xs ctx)
    {c : Clause V} (w : WellTyped ctx c) {e} (bound : c.staticBound = some e) :
    ∃ v n, e.Denotes (Runs M table) xs v ∧ (localReading M).nat v = some n := by
  obtain ⟨ty, inferred, num⟩ := w.2 e bound
  obtain ⟨⟨u,v⟩, den, _, eq⟩ := inferred_denotes M table actual e inferred
  change u = ty at eq
  subst u
  cases ty <;> first | exact ⟨_, _, den, rfl⟩ | cases num

theorem HeaderContracts.clauses_defined {ctx : List V.Ty} {xs : List (localSem M hs table).Dyn}
    (actual : ArgumentsMatch (TypedValue (localSem M hs table) (ValidDyn M)) xs ctx)
    {cs : List (Clause V)} (typed : ∀ c ∈ cs, WellTyped ctx c) :
    ∀ e ∈ cs.map ContractClause.assertion, ∃ v, e.Denotes (Runs M table) xs v := by
  simp only [List.forall_mem_map]
  intro c listed
  obtain ⟨v, den, _⟩ := inferred_denotes M table actual _ (typed c listed).1
  exact ⟨v, den⟩

theorem FunctionContracts.requiresDefined (guarantees : List (HeaderClause V) := []) :
    RequiresDefined (contracts.setting M table definition lemmas notes bounds guarantees) := by
  intro ins outs op e mem values valid
  have ok := ((Sem M table).dyns_valid_iff values).mp valid
  cases op with
  | call m =>
    rename_i h
    change e ∈ (contracts.contract (.call h.key)).requires at mem
    rw [contracts.call_member m] at mem
    exact clauses_defined M table (ArgumentsMatch.ofValues (sem := Sem M table) values valid)
      (translate_typed (contracts.entry m).property).1 e mem
  | owned op =>
    change e ∈ (((localOpFacts hs).requires (LocalOp.print (fns := hs) (.owned op))).map builtinClause).map ContractClause.assertion at mem
    obtain ⟨c, cm, rfl⟩ := List.mem_map.mp mem
    obtain ⟨q, qm, rfl⟩ := List.mem_map.mp cm
    exact owned_defined M table op values ok qm
  | literal => cases mem
  | row key sig found =>
    change e ∈ ((rowRequires key).map builtinClause).map ContractClause.assertion at mem
    obtain ⟨c, cm, rfl⟩ := List.mem_map.mp mem
    obtain ⟨q, qm, rfl⟩ := List.mem_map.mp cm
    exact row_defined M table found values ok qm

theorem FunctionContracts.settingLawful (callees : Callees M table)
    (sound : ∀ l ∈ lemmas, l.Valid (Runs M table) (localReading M) (TypedValue (localSem M hs table) (ValidDyn M))) (guarantees : List (HeaderClause V) := []) :
    (contracts.setting M table definition lemmas notes bounds guarantees).Lawful :=
  ⟨contracts.lawful M table callees _, sound, contracts.requiresDefined M table definition lemmas notes bounds guarantees⟩

end Zkc.Core.BodyAnalysis
