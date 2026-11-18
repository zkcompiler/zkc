module

public import Zkc.Core.Admission.CheckedTables
public import Zkc.Core.Admission.Check
public import Zkc.Core.Meaning.Stops
public import Zkc.Core.Meaning.Program
public import Zkc.Core.Meaning.Tables

@[expose] public section

/-!
Accepted definitions supply their earlier callee tables with proofs of validity and safety.
The function and protocol loop theorems identify bounds by declaration and role at every
invocation path. Together they establish `Typed.Assured` for mixed programs. Header assertions use a fixed empty callee table. A function that satisfies its
summary against the functions before it also satisfies it in the whole table
(`HeaderSummary.holds_tables`). Validity follows from `Term.denote_valid`.

The callees of a function of a program are the functions before it; that those whose headers say
that they cannot stop stop only `undefined` needs no check of facts
(`Defs.fnTable_stops_undefined`, `Meaning/Stops.lean`).

Two programs over the same headers are compared function by function (`Defs.functionsFollow`):
each function of the second follows the analysis of the function of the first with its header,
under the header's summary, with no refusal and no place that differs; a protocol is not
compared. The second program is
taken apart at each definition by `Defs.followsFn_true` and `Defs.followsProtocol_true`. A
program whose functions follow those of another program over the same headers, of which only
the other is accepted by the check of facts and no summary has a requirement
(`Headers.Unconditional`), gives every function the meaning on valid inputs of the function of the
other with its header, and its functions are safe and keep validity (`Defs.functionsFollow_sound`),
by induction over the definitions: a replaced function follows a
function that the check accepts, so it is safe and means the same against the callees before it
(`TypedFn.follows_assured`), and against its own
callees, which mean the same on valid inputs and keep validity, it is the same term
(`Term.denote_tables`); so is a function that calls a replaced function.
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

open BodyAnalysis.RoleContracts

/-- Every accepted bound belongs to the correct table, selected by the role of its place. -/
theorem accepted_places : ∀ {hs : Headers V} (defs : Defs V hs)
    {bounds : List (Place × Nat)}, Defs.Accepted defs bounds → ∀ q ∈ bounds,
      (q.1.role = none → q.1.definition ∈ hs.fns.map (·.key)) ∧
      (∀ r, q.1.role = some r → q.1.definition ∈ hs.protocols.map (·.key))
  | _, .nil, _, h, q, m => by cases h; cases m
  | _, .fn hdr inputs body ok rest notes, _, h, q, m => by
    obtain ⟨mine, others, checked, accepted, rfl⟩ := h
    rcases List.mem_append.mp m with localBound | previous
    · obtain ⟨key, role⟩ := (TypedFn.mk inputs body ok notes).check_places checked q localBound
      exact ⟨fun _ => key ▸ List.mem_cons_self, fun _ atRole => nomatch role.symm.trans atRole⟩
    · obtain ⟨fn, prot⟩ := accepted_places rest accepted q previous
      exact ⟨fun localRole => List.mem_cons_of_mem _ (fn localRole), prot⟩
  | _, .protocol hdr _ _ _ rest, _, h, q, m => by
    obtain ⟨mine, others, ⟨_, evidence, rfl⟩, accepted, rfl⟩ := h
    rcases List.mem_append.mp m with roleBound | previous
    · obtain ⟨key, r, _, role⟩ := evidence.owned q roleBound
      constructor
      · intro localRole
        exact False.elim (Option.some_ne_none _ (role.symm.trans localRole))
      · intro _ _
        rw [key]
        exact List.mem_cons_self
    · obtain ⟨fn, prot⟩ := accepted_places rest accepted q previous
      exact ⟨fn, fun r atRole => List.mem_cons_of_mem _ (prot r atRole)⟩

/-- Successful executable checks supply the hypotheses of the inductive table theorem. -/
theorem acceptedBodies : ∀ {hs : Headers V} (defs : Defs V hs) {bounds},
    Defs.Accepted defs bounds → CheckedBodies defs
  | _, .nil, _, _ => trivial
  | _, .fn _ inputs body ok rest notes, _, accepted => by
    obtain ⟨_, _, checked, earlier, _⟩ := accepted
    exact ⟨((TypedFn.mk inputs body ok notes).check_assured checked).safe, acceptedBodies rest earlier⟩
  | _, .protocol _ _ _ _ rest, _, accepted => by
    obtain ⟨_, _, ⟨catalog, evidence, _⟩, earlier, _⟩ := accepted
    exact ⟨⟨catalog, fun r mem => (evidence.atRole r mem).elim fun bs h => ⟨bs, h.1⟩⟩, acceptedBodies rest earlier⟩

/-- **The check of facts is sound for the functions of a program.** When the check accepts every
function of a program under its header's summary against the headers before it, and the keys of
the functions are distinct: every function satisfies its summary (on valid inputs that satisfy its
requirements it never stops `undefined` and returns valid values that satisfy its guarantees),
keeps validity, and on valid inputs that satisfy its requirements none of its loops runs more often
than the bound that an annotation gives it, for every annotation whose entries at the functions'
places are among the bounds that the check gives. -/
theorem functions_sound : ∀ {hs : Headers V} (defs : Defs V hs),
    (hs.fns.map (·.key)).Nodup → ∀ {bounds : List (Place × Nat)},
    Defs.Accepted defs bounds → ∀ (M : Model V) (F : List (Place × Nat)),
    (∀ p b, (p, b) ∈ F → p.role = none → p.definition ∈ hs.fns.map (·.key) → (p, b) ∈ bounds) →
    FnTable.SatisfiesSummaries (Defs.fnTable M defs) ∧
      FnTable.KeepsValidity (Defs.fnTable M defs) ∧ Defs.FunctionsRespect M ⟨F⟩ defs
  | _, .nil, _, _, _, M, _, _ =>
      ⟨fun _ f => (nomatch f), fun _ f => (nomatch f), trivial⟩
  | _, .fn (hs := hs) hdr inputs body ok rest notes, distinct, bounds, h, M, F, hF => by
      obtain ⟨mine, others, e1, e2, rfl⟩ := h
      have notIn := (List.nodup_cons.mp distinct).1
      have distinct' := (List.nodup_cons.mp distinct).2
      obtain ⟨satisfiesR, keepsR, respR⟩ := functions_sound rest distinct' e2 M F
        (fun p b m r d => by
          rcases List.mem_append.mp (hF p b m r (List.mem_cons_of_mem _ d)) with m' | m'
          · have := ((TypedFn.mk inputs body ok notes).check_places e1 _ m').1
            simp only at this
            rw [this] at d
            exact absurd d notIn
          · exact m')
      have callees : Callees M (Defs.fnTable M rest) :=
        ⟨distinct', satisfiesR, keepsR, Defs.fnTable_stops_undefined M rest⟩
      have assured := (TypedFn.mk inputs body ok notes).check_assured e1
      have holds := assured.safe M _ callees
      have sound := fun ins valid required =>
        assured.bounded M _ callees F
          (fun p b m d r => by
            rcases List.mem_append.mp (hF p b m r (by rw [d]; exact List.mem_cons_self)) with
              m' | m'
            · exact m'
            · have := (accepted_places rest e2 _ m').1 r
              simp only at this
              rw [d] at this
              exact absurd this notIn)
          ins valid required
      refine ⟨fun hdr' f => ?_, fun hdr' f args results valid e => ?_,
        ⟨sound, respR⟩⟩
      · cases f with
        | head => exact HeaderSummary.holds_tables holds
        | tail f => exact HeaderSummary.holds_tables (satisfiesR _ f)
      · cases f with
        | head =>
            change body.denote (localSem M _ (Defs.fnTable M rest)) []
              (Env.empty.extend inputs args) = .done results at e
            have returned := Term.denote_valid (Defs.fnTable M rest) keepsR body []
              (Env.empty.extend inputs args)
              (Env.extend_valid (fun _ x => nomatch (Ctx.find?_empty x.name).symm.trans x.typed)
                inputs args valid)
            rw [e] at returned
            exact returned
        | tail f => exact keepsR _ f args results valid e
  | _, .protocol _ _ _ _ rest, distinct, _, h, M, F, hF => by
      obtain ⟨_, _, ⟨_, evidence, rfl⟩, earlier, rfl⟩ := h
      exact functions_sound rest distinct earlier M F fun p b m role key => by
        rcases List.mem_append.mp (hF p b m role key) with here | there
        · obtain ⟨_, _, _, other⟩ := evidence.owned _ here
          exact nomatch role.symm.trans other
        · exact there

/-- Each declared projection supplies its own bounds at every invocation path. A role outside
the declaration has no local loop and still receives safety of any earlier callee it enters. -/
theorem protocols_sound (M : Model V) : ∀ {hs : Headers V} (defs : Defs V hs) {bounds},
    (hs.fns.map (·.key)).Nodup → (hs.protocols.map (·.key)).Nodup →
    Defs.Accepted defs bounds → ∀ F : List (Place × Nat),
    (∀ p b, (p,b) ∈ F → ∀ r, p.role = some r → p.definition ∈ hs.protocols.map (·.key) →
      (p,b) ∈ bounds) → Defs.ProtocolsRespect M ⟨F⟩ defs
  | _, .nil, _, _, _, _, _, _ => trivial
  | _, .fn _ inputs body ok rest notes, _, fns, protocols, admitted, F, recorded => by
    obtain ⟨_, _, checked, earlier, rfl⟩ := admitted
    apply protocols_sound M rest (List.nodup_cons.mp fns).2 protocols earlier F
    intro p b m r role key
    rcases List.mem_append.mp (recorded p b m r role key) with here | there
    · have other := ((TypedFn.mk inputs body ok notes).check_places checked _ here).2
      exact nomatch role.symm.trans other
    · exact there
  | _, .protocol hdr inputs body ok rest, _, fns, protocols, admitted, F, recorded => by
    obtain ⟨_, _, ⟨catalog, evidence, rfl⟩, earlier, rfl⟩ := admitted
    obtain ⟨fresh, distinct⟩ := List.nodup_cons.mp protocols
    obtain ⟨callees, roles⟩ := checkedTables M rest fns (acceptedBodies rest earlier)
    constructor
    · intro r path values valid
      by_cases declared : r ∈ List.range hdr.roles
      · obtain ⟨bs, pass, selected⟩ := evidence.atRole r declared
        apply (checkedProjection catalog r hdr body ok pass M _ _ callees roles F ?_ path values valid).1
        intro p b m key atRole
        rcases List.mem_append.mp (recorded p b m r atRole (key ▸ List.mem_cons_self)) with here | there
        · exact selected _ here atRole
        · have older := (accepted_places rest earlier _ there).2 r atRole
          change p.definition ∈ _ at older
          rw [key] at older
          exact False.elim (fresh older)
      · exact (outsideProjection M _ _ declared roles body ok.within path _ (Env.extend_preserves
          (fun _ x => nomatch (Ctx.find?_empty x.name).symm.trans x.typed) inputs values valid)
          (Annotation.Bounded ⟨F⟩ hdr.key (some r)) []).2
    · apply protocols_sound M rest fns distinct earlier F
      intro p b m r atRole key
      rcases List.mem_append.mp (recorded p b m r atRole (List.mem_cons_of_mem _ key)) with here | there
      · have head := (evidence.owned _ here).1
        change p.definition = hdr.key at head
        rw [head] at key
        exact False.elim (fresh key)
      · exact there

/-- Every function and every projected protocol of an accepted mixed program respects the
bounds returned by admission. Functions also meet their stored contracts. -/
theorem typed_program_sound (p : Typed V) {bounds : List (Place × Nat)}
    (accepted : Defs.Accepted p.defs bounds) : p.Assured ⟨bounds⟩ := fun M => by
  obtain ⟨fns, protocols, _⟩ := List.nodup_append.mp p.distinct
  obtain ⟨satisfies, keeps, respect⟩ := functions_sound p.defs fns accepted M bounds (fun _ _ m _ _ => m)
  exact ⟨satisfies, keeps, respect, protocols_sound M p.defs fns protocols accepted bounds
    (fun _ _ m _ _ _ => m)⟩

/-! ## Two programs over the same headers -/

/-- A function of the first program, against a program whose headers are said to be the first's
up to that function: when the second's last definition is a function too, whether it follows
the analysis of the first's, both under the header's summary, with no refusal and no place that
differs (`TypedFn.follows`) and the definitions before it follow (`rest`); a protocol there does
not follow. -/
def Defs.followsFn (fns : List (FnHeader V)) (protocols : List (ProtocolHeader V))
    (hdr : FnHeader V) (source : TypedFn V fns hdr)
    (rest : Defs V ⟨fns, protocols⟩ → Bool) :
    {hs : Headers V} → Defs V hs → hs = ⟨hdr :: fns, protocols⟩ → Bool
  | _, .nil, impossible => nomatch impossible
  | _, .fn _ inputs' body' ok' rest' notes', rfl =>
      (source.follows ⟨inputs', body', ok', notes'⟩).isOk && rest rest'
  | _, .protocol .., _ => false

/-- A protocol of the first program, against a program whose headers are said to be the first's
up to that protocol: when the second's last definition is a protocol too, whether the
definitions before it follow (`rest`); the protocols are not compared. A function there does not
follow. -/
def Defs.followsProtocol (fns : List (FnHeader V)) (protocols : List (ProtocolHeader V))
    (hdr : ProtocolHeader V) (rest : Defs V ⟨fns, protocols⟩ → Bool) :
    {hs : Headers V} → Defs V hs → hs = ⟨fns, hdr :: protocols⟩ → Bool
  | _, .nil, same => nomatch same
  | _, .fn .., _ => false
  | _, .protocol _ _ _ _ rest', rfl => rest rest'

/-- Whether the functions of the second program follow those of the first, one by one: the two
programs have the same headers, and each function follows the analysis of the one with its
header with no refusal and no place that differs. A protocol is not compared. -/
def Defs.functionsFollow : {hs : Headers V} → Defs V hs → Defs V hs → Bool
  | _, .nil, _ => true
  | _, .fn (hs := hs) hdr inputs body ok rest notes, defs' =>
      Defs.followsFn hs.fns hs.protocols hdr ⟨inputs, body, ok, notes⟩
        (fun rest' => Defs.functionsFollow rest rest') defs' rfl
  | _, .protocol (hs := hs) hdr _ _ _ rest, defs' =>
      Defs.followsProtocol hs.fns hs.protocols hdr
        (fun rest' => Defs.functionsFollow rest rest') defs' rfl

/-- A second program that follows at a function of the first ends with a function of the same
header, which follows the analysis of the first's with no refusal and no place that differs,
after definitions that follow. -/
theorem Defs.followsFn_true {fns : List (FnHeader V)} {protocols : List (ProtocolHeader V)}
    {hdr : FnHeader V} {source : TypedFn V fns hdr}
    {rest : Defs V ⟨fns, protocols⟩ → Bool} :
    ∀ {hs : Headers V} (defs' : Defs V hs) (headers : hs = ⟨hdr :: fns, protocols⟩),
      Defs.followsFn fns protocols hdr source rest defs' headers = true →
      ∃ (inputs' : Names hdr.ins) (body' : Fn V fns hdr inputs') (ok' : FnConditions body')
        (rest' : Defs V ⟨fns, protocols⟩) (notes' : BodyAnalysis.Annotations (LocalRaw V)),
        HEq defs' (Defs.fn (hs := ⟨fns, protocols⟩) hdr inputs' body' ok' rest' notes') ∧
          (∃ bounds, source.follows ⟨inputs', body', ok', notes'⟩ = .ok bounds) ∧
          rest rest' = true
  | _, .nil, headers, _ => nomatch headers
  | _, .fn _ inputs' body' ok' rest' notes', rfl, follows => by
      obtain ⟨accepted, restFollows⟩ := Bool.and_eq_true_iff.mp follows
      refine ⟨inputs', body', ok', rest', notes', HEq.rfl, ?_, restFollows⟩
      cases h : source.follows ⟨inputs', body', ok', notes'⟩ with
      | ok bounds => exact ⟨bounds, rfl⟩
      | error e => simp [h, Except.isOk, Except.toBool] at accepted
  | _, .protocol .., _, follows => nomatch follows

/-- A second program that follows at a protocol of the first ends with a protocol of the same
header, after definitions that follow. -/
theorem Defs.followsProtocol_true {fns : List (FnHeader V)} {protocols : List (ProtocolHeader V)}
    {hdr : ProtocolHeader V} {rest : Defs V ⟨fns, protocols⟩ → Bool} :
    ∀ {hs : Headers V} (defs' : Defs V hs) (headers : hs = ⟨fns, hdr :: protocols⟩),
      Defs.followsProtocol fns protocols hdr rest defs' headers = true →
      ∃ (inputs' : Names hdr.ins) (body' : Prot V ⟨fns, protocols⟩ hdr inputs')
        (ok' : ProtocolConditions hdr body') (rest' : Defs V ⟨fns, protocols⟩),
        HEq defs' (Defs.protocol (hs := ⟨fns, protocols⟩) hdr inputs' body' ok' rest') ∧
          rest rest' = true
  | _, .nil, headers, _ => nomatch headers
  | _, .fn .., _, follows => nomatch follows
  | _, .protocol _ inputs' body' ok' rest', rfl, follows =>
      ⟨inputs', body', ok', rest', HEq.rfl, follows⟩

/-- **The functions of a program whose functions were replaced by functions that follow them
mean what they meant, and are safe.** When the first program is accepted by the check of facts,
the keys of its functions are distinct, no summary of its headers has a requirement
(`Headers.Unconditional`), and the functions of the second follow those of the first one by one
(each with no refusal and no place that differs): every function of the second has, on valid
inputs, the meaning of the function of the first with its header, and the functions of the second
never stop `undefined` on valid inputs and keep validity. The functions that call a
replaced function are covered: they call it on valid values, where it means the same. The second
program is not asked to be accepted: each of its functions is safe because it follows a safe
function (`TypedFn.follows_assured`). Nothing is said of the protocols of the two programs,
which are not compared. -/
theorem Defs.functionsFollow_sound : ∀ {hs : Headers V} (defs defs' : Defs V hs),
    (hs.fns.map (·.key)).Nodup → hs.Unconditional → ∀ {bounds : List (Place × Nat)},
    Defs.Accepted defs bounds → Defs.functionsFollow defs defs' = true → ∀ (M : Model V),
      (∀ (hdr : FnHeader V) (f : Member hs.fns hdr) (ins : HList M.Val hdr.ins),
        ins.All M.Valid → Defs.fnTable M defs' hdr f ins = Defs.fnTable M defs hdr f ins) ∧
      FnTable.Safe (Defs.fnTable M defs') ∧ FnTable.KeepsValidity (Defs.fnTable M defs')
  | _, .nil, _, _, _, _, _, _, _ =>
      ⟨fun _ f => (nomatch f), fun _ f => (nomatch f), fun _ f => (nomatch f)⟩
  | _, .fn (hs := hs) hdr inputs body ok rest notes, defs', distinct, unconditional, _, accepted,
      follows, M => by
      obtain ⟨inputs', body', ok', rest', notes', same', followed, restFollows⟩ :=
        Defs.followsFn_true (rest := fun rest' => Defs.functionsFollow rest rest') defs' rfl follows
      cases eq_of_heq same'
      obtain ⟨_, _, checked, restAccepted, -⟩ := accepted
      have distinct' := (List.nodup_cons.mp distinct).2
      have unconditional' : hs.Unconditional :=
        fun hdr' listed => unconditional hdr' (List.mem_cons_of_mem _ listed)
      have required : ∀ ins : HList M.Val hdr.ins,
          FnHeader.Required M (Defs.fnTable M rest) hdr ins :=
        fun _ requirement listed => by
          rw [unconditional hdr List.mem_cons_self] at listed
          cases listed
      obtain ⟨agree, safe', keeps'⟩ :=
        Defs.functionsFollow_sound rest rest' distinct' unconditional' restAccepted restFollows M
      obtain ⟨satisfies, keeps, -⟩ :=
        functions_sound rest distinct' restAccepted M [] (fun _ _ none => nomatch none)
      have callees : Callees M (Defs.fnTable M rest) :=
        ⟨distinct', satisfies, keeps, Defs.fnTable_stops_undefined M rest⟩
      obtain ⟨_, compared⟩ := followed
      have sourceSafe := ((TypedFn.mk inputs body ok notes).check_assured checked).safe
      obtain ⟨targetAssured, equal⟩ := TypedFn.follows_assured sourceSafe compared
      have returns (ins : HList M.Val hdr.ins) (valid : ins.All M.Valid) :=
        targetAssured.safe M _ callees ins (((localSem M _ _).dyns_valid_iff ins).mpr valid)
          (required ins)
      -- against its own callees it is the same term, which calls them on valid values
      have switch : ∀ ins : HList M.Val hdr.ins, ins.All M.Valid →
          body'.denote (localSem M hs.fns (Defs.fnTable M rest')) []
              (Env.empty.extend inputs' ins) =
            body'.denote (localSem M hs.fns (Defs.fnTable M rest)) []
              (Env.empty.extend inputs' ins) :=
        fun ins valid => Term.denote_tables (Defs.fnTable M rest') keeps agree body' [] _
          (Env.extend_valid (fun _ x => nomatch (Ctx.find?_empty x.name).symm.trans x.typed)
            inputs' ins valid)
      refine ⟨fun hdr' f ins valid => ?_, fun hdr' f args valid => ?_,
        fun hdr' f args results valid ran => ?_⟩
      · cases f with
        | head =>
            show body'.denote (localSem M _ (Defs.fnTable M rest')) []
                (Env.empty.extend inputs' ins) =
              body.denote (localSem M _ (Defs.fnTable M rest)) [] (Env.empty.extend inputs ins)
            rw [switch ins valid]
            exact (equal M _ callees ins valid (required ins)).symm
        | tail f => exact agree _ f ins valid
      · cases f with
        | head =>
            show (body'.denote (localSem M _ (Defs.fnTable M rest')) []
              (Env.empty.extend inputs' args)).Stops _
            rw [switch args valid]
            exact Process.every_mono _ _ (fun _ _ => trivial) (fun _ h => h) (returns args valid)
        | tail f => exact safe' _ f args valid
      · cases f with
        | head =>
            change body'.denote (localSem M _ (Defs.fnTable M rest')) []
              (Env.empty.extend inputs' args) = .done results at ran
            rw [switch args valid] at ran
            have returned := (returns args valid)
            simp only [TypedFn.meaning, ran, Process.Every] at returned
            exact ((localSem M _ _).dyns_valid_iff results).mp returned.1
        | tail f => exact keeps' _ f args results valid ran
  | _, .protocol hdr _ _ _ rest, defs', distinct, unconditional, _, accepted, follows, M => by
      obtain ⟨_, _, _, rest', same', restFollows⟩ :=
        Defs.followsProtocol_true (rest := fun rest' => Defs.functionsFollow rest rest') defs' rfl
          follows
      cases eq_of_heq same'
      obtain ⟨_, _, _, earlier, _⟩ := accepted
      exact Defs.functionsFollow_sound rest rest' distinct unconditional earlier restFollows M

end

end Zkc.Core
