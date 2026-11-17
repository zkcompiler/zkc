module

public import Zkc.Core.Admission.Check
public import Zkc.Core.Facts.LocalLaws
public import Zkc.Core.Meaning.Program
public import Zkc.Core.Meaning.Tables

@[expose] public section

/-!
The theorem of the check of facts for a program: by induction over its definitions, when the
check accepts each function under its header's summary against the headers before it
(`Defs.Accepted`), every function satisfies its summary and keeps validity, and no loop of a
function runs more often than its bound on the inputs that satisfy its requirements
(`functions_sound`); so a typed program without protocols that the check accepts is assured with
its bounds (`typed_functions_sound`, `Typed.Assured`). The summary of a function applies no written
operation, so what a function satisfies against the functions before it it satisfies in the whole
table (`Summary.holds_tables`); keeping validity needs no check of facts (`Term.denote_valid`).

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
(`localFollow_assured`), and against its own
callees, which mean the same on valid inputs and keep validity, it is the same term
(`Term.denote_tables`); so is a function that calls a replaced function.
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-- The bounds of the functions of a program are at the places of their definitions. -/
theorem accepted_places : ∀ {hs : Headers V} (defs : Defs V hs)
    {bounds : List (Place × Nat)}, Defs.Accepted defs bounds →
    ∀ q, q ∈ bounds → q.1.definition ∈ hs.fns.map (·.key) ∧ q.1.role = none
  | _, .nil, bounds, h, q, m => by
      have h : bounds = [] := h
      subst h
      cases m
  | _, .fn hdr inputs body ok rest, bounds, h, q, m => by
      obtain ⟨mine, others, e1, e2, rfl⟩ := h
      rcases List.mem_append.mp m with m | m
      · obtain ⟨d, r⟩ :=
          checkFacts_places (localFactRules V _) (localRules _).skel hdr.key none hdr.summary.lift
            inputs body e1 q m
        exact ⟨by rw [d]; exact List.mem_cons_self, r⟩
      · obtain ⟨d, r⟩ := accepted_places rest e2 q m
        exact ⟨List.mem_cons_of_mem _ d, r⟩
  | _, .protocol _ _ _ _ rest, bounds, h, q, m => accepted_places rest h q m

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
  | _, .fn (hs := hs) hdr inputs body ok rest, distinct, bounds, h, M, F, hF => by
      obtain ⟨mine, others, e1, e2, rfl⟩ := h
      have notIn := (List.nodup_cons.mp distinct).1
      have distinct' := (List.nodup_cons.mp distinct).2
      obtain ⟨satisfiesR, keepsR, respR⟩ := functions_sound rest distinct' e2 M F
        (fun p b m r d => by
          rcases List.mem_append.mp (hF p b m r (List.mem_cons_of_mem _ d)) with m' | m'
          · have := (checkFacts_places (localFactRules V _) (localRules _).skel hdr.key none
              hdr.summary.lift inputs body e1 _ m').1
            simp only at this
            rw [this] at d
            exact absurd d notIn
          · exact m')
      have callees : Callees M (Defs.fnTable M rest) :=
        ⟨distinct', satisfiesR, keepsR, Defs.fnTable_stops_undefined M rest⟩
      have holds := checkFacts_holds callees hdr.key hdr.summary inputs body ok.distinct e1
      have sound := fun ins valid required =>
        checkFacts_sound callees hdr.key hdr.summary inputs body ok.distinct e1 F
          (fun p b m d r => by
            rcases List.mem_append.mp (hF p b m r (by rw [d]; exact List.mem_cons_self)) with
              m' | m'
            · exact m'
            · have := (accepted_places rest e2 _ m').1
              simp only at this
              rw [d] at this
              exact absurd this notIn)
          ins valid required
      refine ⟨fun hdr' f => ?_, fun hdr' f args results valid e => ?_,
        ⟨fun ins valid required => (sound ins valid required).1, respR⟩⟩
      · cases f with
        | head => exact Summary.holds_tables holds
        | tail f => exact Summary.holds_tables (satisfiesR _ f)
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
      obtain ⟨satisfiesR, keepsR, respR⟩ := functions_sound rest distinct h M F hF
      exact ⟨satisfiesR, keepsR, respR⟩

/-- **The check of facts is sound for a typed program.** A typed program without protocols each
of whose functions the check accepts under its header's summary is assured with the bounds that
the check gives: for every model, every function satisfies its summary and keeps validity, and
the program respects the annotation of those bounds (`Typed.Assured`). -/
theorem typed_functions_sound (p : Typed V) {bounds : List (Place × Nat)}
    (accepted : Defs.Accepted p.defs bounds) (functions : p.headers.protocols = []) :
    p.Assured ⟨bounds⟩ := fun M => by
  obtain ⟨satisfies, keeps, respect⟩ := functions_sound p.defs
    (List.nodup_append.mp p.distinct).1 accepted M bounds (fun _ _ m _ _ => m)
  exact ⟨satisfies, keeps, Respects.of_functions p functions respect⟩

/-! ## Two programs over the same headers -/

/-- A function of the first program, against a program whose headers are said to be the first's
up to that function: when the second's last definition is a function too, whether it follows
the analysis of the first's, both under the header's summary, with no refusal and no place that
differs (`Exit.accepted`) and the definitions before it follow (`rest`); a protocol there does
not follow. -/
def Defs.followsFn (fns : List (FnHeader V)) (protocols : List (ProtocolHeader V))
    (hdr : FnHeader V) (inputs : Names hdr.ins) (body : Fn V fns hdr inputs)
    (rest : Defs V ⟨fns, protocols⟩ → Bool) :
    {hs : Headers V} → Defs V hs → hs = ⟨hdr :: fns, protocols⟩ → Bool
  | _, .nil, impossible => nomatch impossible
  | _, .fn (hs := hs) _ inputs' body' _ rest', rfl =>
      (Analysis.follow (localFactRules V hs.fns) (localRules hs.fns).skel hdr.key none
          hdr.summary.lift
          (Analysis.analyse (localFactRules V hs.fns) (localRules hs.fns).skel hdr.key none
            hdr.summary.lift inputs body)
          inputs' body').accepted && rest rest'
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
  | _, .fn (hs := hs) hdr inputs body _ rest, defs' =>
      Defs.followsFn hs.fns hs.protocols hdr inputs body
        (fun rest' => Defs.functionsFollow rest rest') defs' rfl
  | _, .protocol (hs := hs) hdr _ _ _ rest, defs' =>
      Defs.followsProtocol hs.fns hs.protocols hdr
        (fun rest' => Defs.functionsFollow rest rest') defs' rfl

open Analysis in
/-- A second program that follows at a function of the first ends with a function of the same
header, which follows the analysis of the first's with no refusal and no place that differs,
after definitions that follow. -/
theorem Defs.followsFn_true {fns : List (FnHeader V)} {protocols : List (ProtocolHeader V)}
    {hdr : FnHeader V} {inputs : Names hdr.ins} {body : Fn V fns hdr inputs}
    {rest : Defs V ⟨fns, protocols⟩ → Bool} :
    ∀ {hs : Headers V} (defs' : Defs V hs) (headers : hs = ⟨hdr :: fns, protocols⟩),
      Defs.followsFn fns protocols hdr inputs body rest defs' headers = true →
      ∃ (inputs' : Names hdr.ins) (body' : Fn V fns hdr inputs') (ok' : FnConditions body')
        (rest' : Defs V ⟨fns, protocols⟩),
        HEq defs' (Defs.fn (hs := ⟨fns, protocols⟩) hdr inputs' body' ok' rest') ∧
          (follow (localFactRules V fns) (localRules fns).skel hdr.key none hdr.summary.lift
            (analyse (localFactRules V fns) (localRules fns).skel hdr.key none hdr.summary.lift
              inputs body) inputs' body').accepted = true ∧
          rest rest' = true
  | _, .nil, headers, _ => nomatch headers
  | _, .fn _ inputs' body' ok' rest', rfl, follows => by
      obtain ⟨accepted, restFollows⟩ := Bool.and_eq_true_iff.mp follows
      exact ⟨inputs', body', ok', rest', HEq.rfl, accepted, restFollows⟩
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
function (`localFollow_assured`). Nothing is said of the protocols of the two programs,
which are not compared. -/
theorem Defs.functionsFollow_sound : ∀ {hs : Headers V} (defs defs' : Defs V hs),
    (hs.fns.map (·.key)).Nodup → hs.Unconditional → ∀ {bounds : List (Place × Nat)},
    Defs.Accepted defs bounds → Defs.functionsFollow defs defs' = true → ∀ (M : Model V),
      (∀ (hdr : FnHeader V) (f : Member hs.fns hdr) (ins : HList M.Val hdr.ins),
        ins.All M.Valid → Defs.fnTable M defs' hdr f ins = Defs.fnTable M defs hdr f ins) ∧
      FnTable.Safe (Defs.fnTable M defs') ∧ FnTable.KeepsValidity (Defs.fnTable M defs')
  | _, .nil, _, _, _, _, _, _, _ =>
      ⟨fun _ f => (nomatch f), fun _ f => (nomatch f), fun _ f => (nomatch f)⟩
  | _, .fn (hs := hs) hdr inputs body ok rest, defs', distinct, unconditional, _, accepted,
      follows, M => by
      obtain ⟨inputs', body', ok', rest', same', followed, restFollows⟩ :=
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
      -- the second's function, against the callees of the first: it follows a safe function
      have head := fun (ins : HList M.Val hdr.ins) (valid : ins.All M.Valid) =>
        localFollow_assured callees hdr.key hdr.key hdr.summary inputs inputs' body body'
          ok'.distinct followed [] (fun _ _ none => nomatch none) ins valid (required ins)
          (Process.every_mono _ _ (fun _ _ => trivial) (fun _ h => h)
            (checkFacts_sound callees hdr.key hdr.summary inputs body ok.distinct checked
              [] (fun _ _ none => nomatch none) ins valid (required ins)).2)
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
            exact ((head ins valid).2.2).symm
        | tail f => exact agree _ f ins valid
      · cases f with
        | head =>
            show (body'.denote (localSem M _ (Defs.fnTable M rest')) []
              (Env.empty.extend inputs' args)).Stops _
            rw [switch args valid]
            exact Process.every_mono _ _ (fun _ _ => trivial) (fun _ h => h) (head args valid).2.1
        | tail f => exact safe' _ f args valid
      · cases f with
        | head =>
            change body'.denote (localSem M _ (Defs.fnTable M rest')) []
              (Env.empty.extend inputs' args) = .done results at ran
            rw [switch args valid] at ran
            have returned := (head args valid).2.1
            rw [ran] at returned
            exact returned.1
        | tail f => exact keeps' _ f args results valid ran
  | _, .protocol hdr _ _ _ rest, defs', distinct, unconditional, _, accepted, follows, M => by
      obtain ⟨_, _, _, rest', same', restFollows⟩ :=
        Defs.followsProtocol_true (rest := fun rest' => Defs.functionsFollow rest rest') defs' rfl
          follows
      cases eq_of_heq same'
      exact Defs.functionsFollow_sound rest rest' distinct unconditional accepted restFollows M

end

end Zkc.Core
